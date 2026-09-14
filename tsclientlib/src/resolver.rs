//! Resolve TeamSpeak server addresses of any kind.
// Changes with TeamSpeak client 3.1:
// https://support.teamspeakusa.com/index.php?/Knowledgebase/Article/View/332

use std::net::{IpAddr, Ipv6Addr, SocketAddr};
use std::str;

use futures::prelude::*;
use hickory_net::proto::rr::RData;
use hickory_resolver::TokioResolver;
use hickory_resolver::config::{CLOUDFLARE, ResolverConfig, ResolverOpts};
use hickory_resolver::net::runtime::TokioRuntimeProvider;
use itertools::Itertools;
use rand::RngExt;
use thiserror::Error;
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::net::{self, TcpStream};
use tokio::time::Duration;
use tracing::{debug, instrument, warn};

const DEFAULT_PORT: u16 = 9987;
const DNS_PREFIX_TCP: &str = "_tsdns._tcp.";
const DNS_PREFIX_UDP: &str = "_ts3._udp.";
/// GreenTeaSpeak / TeaSpeak SRV prefix (queried in addition to `_ts3._udp`).
const DNS_PREFIX_UDP_GTS: &str = "_gts._udp.";
const NICKNAME_LOOKUP_ADDRESS: &str = "https://named.myteamspeak.com/lookup";
/// Wait this amount of seconds before giving up.
const TIMEOUT_SECONDS: u64 = 10;

type Result<T> = std::result::Result<T, Error>;

#[derive(Debug, Error)]
#[non_exhaustive]
pub enum Error {
	#[error("Failed to create resolver: {0}")]
	CreateResolver(#[source] hickory_net::NetError),
	#[error("Invalid IPv4 address")]
	InvalidIp4Address,
	#[error("Invalid IPv6 address")]
	InvalidIp6Address,
	#[error("Invalid IP address")]
	InvalidIpAddress,
	#[error("Not a valid nickname")]
	InvalidNickname,
	#[error("Failed to parse port: {0}")]
	InvalidPort(#[source] std::num::ParseIntError),
	#[error("Failed to contact {0} server: {1}")]
	Io(&'static str, #[source] std::io::Error),
	#[error("Failed to parse url: {0}")]
	NicknameParseUrl(#[source] url::ParseError),
	#[error("Failed to resolve nickname: {0}")]
	NicknameResolve(#[source] reqwest::Error),
	#[error("Failed to resolve hostname: {0}")]
	ResolveHost(#[source] tokio::io::Error),
	#[error("Failed to get SRV record")]
	SrvLookup(#[source] hickory_net::NetError),
	#[error("tsdns did not return an ip address but {0:?}")]
	TsdnsAddressInvalidResponse(String),
	#[error("tsdns server does not know the address")]
	TsdnsAddressNotFound,
	#[error("Failed to parse tsdns response: {0}")]
	TsdnsParseResponse(#[source] std::str::Utf8Error),
}

#[derive(Debug, PartialEq, Eq)]
enum ParseIpResult<'a> {
	Addr(SocketAddr),
	Other(&'a str, Option<u16>),
}

/// Beware that this may be slow because it tries all available methods.
///
/// The following methods are tried (aligned with GreenTeaSpeak):
/// 1. If the address is an ip, the ip is returned
/// 1. If an explicit `:port` is given on a hostname, SRV/TSDNS are skipped (Direct A/AAAA)
/// 1. Server nicknames are resolved by a http request to TeamSpeak
/// 1. SRV `_gts._udp.<host>` then `_gts._udp.<root>` (TeaSpeak / GreenTeaSpeak)
/// 1. SRV `_ts3._udp.<host>` then `_ts3._udp.<root>`
/// 1. The SRV record at `_tsdns._tcp.address.tld` to get the address of a tsdns
///    server, e.g. when the address is `ts3.subdomain.from.com`, the SRV record
///    at `_tsdns._tcp.from.com` is requested
/// 1. Directly resolve the address to an ip address
///
/// If a port is given with `:port`, it overwrites the automatically determined
/// port. IPv6 addresses are put in square brackets when a port is present:
/// `[::1]:9987`
#[instrument]
pub fn resolve(address: String) -> impl Stream<Item = Result<SocketAddr>> {
	debug!("Starting resolve");
	let addr;
	let port;
	match parse_ip(&address) {
		Ok(ParseIpResult::Addr(res)) => {
			return stream::once(future::ok(res)).left_stream();
		}
		Ok(ParseIpResult::Other(a, p)) => {
			addr = a.to_string();
			port = p;
			if let Some(port) = port {
				debug!(port, "Found port");
			}
		}
		Err(res) => return stream::once(future::err(res)).left_stream(),
	}

	// Explicit host:port → Direct only (matches GreenTeaSpeak: skip slow SRV/TSDNS).
	let res = if port.is_some() {
		let addr_direct = addr.clone();
		let port_direct = port.unwrap_or(DEFAULT_PORT);
		stream::once(async move {
			let res = net::lookup_host((addr_direct.as_str(), port_direct))
				.await
				.map_err(Error::ResolveHost)?
				.map(Ok)
				.collect::<Vec<_>>();
			Result::<_>::Ok(stream::iter(res))
		})
		.try_flatten()
		.left_stream()
	} else {
		// Resolve as nickname
		let nick = if !address.contains('.') && addr != "localhost" {
			debug!("Resolving nickname");
			resolve_nickname(address.clone()).left_stream()
		} else {
			stream::once(future::err(Error::InvalidNickname)).right_stream()
		};

		// GreenTeaSpeak order: `_gts._udp` before `_ts3._udp`, exact host only
		// (no apex fallback - see srv_lookup_hosts / issue #9).
		let srv_hosts = srv_lookup_hosts(&addr);
		let nick = nick.chain(resolve_srv_records(srv_hosts.clone(), DNS_PREFIX_UDP_GTS));
		let nick = nick.chain(resolve_srv_records(srv_hosts, DNS_PREFIX_UDP));

		// Try to get the address of a tsdns server by an SRV record
		let addr2 = addr.clone();
		let address_for_tsdns = address.clone();
		let nick = nick.chain(
			stream::once(async move {
				let resolver = create_resolver()?;
				// Trim address to two components
				let name = if let Some(i) = addr2.rfind('.').and_then(|i| addr2[..i].rfind('.')) {
					&addr2[i + 1..]
				} else {
					&addr2
				};
				Result::<_>::Ok(resolve_srv(resolver, format!("{DNS_PREFIX_TCP}{name}.")).and_then(
					move |srv| {
						let address = address_for_tsdns.clone();
						async move {
							let addr = resolve_tsdns(srv, &address).await?;
							Ok(addr)
						}
					},
				))
			})
			.try_flatten(),
		);

		// Interpret as normal address and resolve with system resolver
		let nick = nick.chain(
			stream::once(async move {
				let res = net::lookup_host((addr.as_str(), DEFAULT_PORT))
					.await
					.map_err(Error::ResolveHost)?
					.map(Ok)
					.collect::<Vec<_>>();
				Result::<_>::Ok(stream::iter(res))
			})
			.try_flatten(),
		);
		nick.right_stream()
	};

	// TODO Move current span into stream
	tokio_stream::StreamExt::timeout(res, Duration::from_secs(TIMEOUT_SECONDS))
		.filter_map(move |r: std::result::Result<Result<SocketAddr>, _>| {
			future::ready(match r {
				// Timeout
				Err(_) => None,
				// Error
				Ok(Err(error)) => {
					debug!(%error, "Resolver failed in one step");
					None
				}
				// Success
				Ok(Ok(r)) => Some(Ok(r)),
			})
		})
		.right_stream()
}

/// Hosts to query for `_gts`/`_ts3` SRV: the exact hostname only.
///
/// Used to also fall back to the two-label root (`ts6.example.com` → also
/// `example.com`), but that hijacks a subdomain which has its own A record onto
/// the apex SRV of a *different* server: e.g. `ts6.host` (A → the TS6 box) got
/// routed to `_ts3._udp.host` (→ the TS3 box) before its own A record was tried.
/// The official TS client does SRV on the exact host only; root-walking is
/// TSDNS's job (see the `_tsdns._tcp` step above). See GitHub issue #9.
fn srv_lookup_hosts(host: &str) -> Vec<String> {
	vec![host.trim_end_matches('.').to_string()]
}

/// Resolve SRV for each host under `service` (e.g. `_gts._udp.`).
fn resolve_srv_records(
	hosts: Vec<String>, service: &'static str,
) -> impl Stream<Item = Result<SocketAddr>> {
	stream::iter(hosts)
		.map(move |host| {
			stream::once(async move {
				let resolver = create_resolver()?;
				debug!(%service, %host, "Trying SRV lookup");
				Result::<_>::Ok(resolve_srv(resolver, format!("{service}{host}.")))
			})
			.try_flatten()
		})
		.flatten()
}

// Windows for some reason automatically adds a link-local address to the dns
// resolver. These addresses are usually not reachable and should be filtered out.
// See: https://superuser.com/questions/638566/strange-value-in-dns-shown-in-ipconfig
const FILTERED_IPS: &[IpAddr] = &[
	IpAddr::V6(Ipv6Addr::new(0xfec0, 0, 0, 0xffff, 0, 0, 0, 1)),
	IpAddr::V6(Ipv6Addr::new(0xfec0, 0, 0, 0xffff, 0, 0, 0, 2)),
	IpAddr::V6(Ipv6Addr::new(0xfec0, 0, 0, 0xffff, 0, 0, 0, 3)),
];

fn create_resolver() -> Result<TokioResolver> {
	let (config, options) = match hickory_resolver::system_conf::read_system_conf() {
		Ok((mut config, options)) => {
			config.name_servers.retain(|ns| !FILTERED_IPS.contains(&ns.ip));
			(config, options)
		}
		Err(error) => {
			warn!(%error, "Failed to use system dns resolver config");
			// Fallback
			(ResolverConfig::udp_and_tcp(&CLOUDFLARE), ResolverOpts::default())
		}
	};
	let mut builder = TokioResolver::builder_with_config(config, TokioRuntimeProvider::default());
	*builder.options_mut() = options;
	builder.build().map_err(Error::CreateResolver)
}

fn parse_ip(address: &str) -> Result<ParseIpResult<'_>> {
	let mut addr = address;
	let mut port = None;
	if let Some(pos) = address.rfind(':') {
		// Either with port or IPv6 address
		if address.find(':').unwrap() == pos {
			// Port is appended
			addr = &address[..pos];
			port = Some(&address[pos + 1..]);
			if addr.chars().all(|c| c.is_ascii_digit() || c == '.') {
				// IPv4 address
				return Ok(ParseIpResult::Addr(
					std::net::ToSocketAddrs::to_socket_addrs(address)
						.map_err(|_| Error::InvalidIp4Address)?
						.next()
						.ok_or(Error::InvalidIp4Address)?,
				));
			}
		} else if let Some(pos_bracket) = address.rfind(']') {
			if pos_bracket < pos {
				// IPv6 address and port
				return Ok(ParseIpResult::Addr(
					std::net::ToSocketAddrs::to_socket_addrs(address)
						.map_err(|_| Error::InvalidIp6Address)?
						.next()
						.ok_or(Error::InvalidIp6Address)?,
				));
			} else if pos_bracket == address.len() - 1 && address.starts_with('[') {
				// IPv6 address
				return Ok(ParseIpResult::Addr(
					std::net::ToSocketAddrs::to_socket_addrs(&(
						&address[1..pos_bracket],
						DEFAULT_PORT,
					))
					.map_err(|_| Error::InvalidIp6Address)?
					.next()
					.ok_or(Error::InvalidIp6Address)?,
				));
			} else {
				return Err(Error::InvalidIpAddress);
			}
		} else {
			// IPv6 address
			return Ok(ParseIpResult::Addr(
				std::net::ToSocketAddrs::to_socket_addrs(&(address, DEFAULT_PORT))
					.map_err(|_| Error::InvalidIp6Address)?
					.next()
					.ok_or(Error::InvalidIp6Address)?,
			));
		}
	} else if address.chars().all(|c| c.is_ascii_digit() || c == '.') {
		// IPv4 address
		return Ok(ParseIpResult::Addr(
			std::net::ToSocketAddrs::to_socket_addrs(&(address, DEFAULT_PORT))
				.map_err(|_| Error::InvalidIp4Address)?
				.next()
				.ok_or(Error::InvalidIp4Address)?,
		));
	}
	let port = if let Some(port) = port.map(|p| p.parse().map_err(Error::InvalidPort)) {
		Some(port?)
	} else {
		None
	};
	Ok(ParseIpResult::Other(addr, port))
}

pub fn resolve_nickname(nickname: String) -> impl Stream<Item = Result<SocketAddr>> {
	stream::once(async {
		let nickname = nickname;
		let url =
			reqwest::Url::parse_with_params(NICKNAME_LOOKUP_ADDRESS, Some(("name", &nickname)))
				.map_err(Error::NicknameParseUrl)?;
		let body = reqwest::get(url)
			.await
			.map_err(Error::NicknameResolve)?
			.error_for_status()
			.map_err(Error::NicknameResolve)?
			.text()
			.await
			.map_err(Error::NicknameResolve)?;
		let addrs = body
			.split(&['\r', '\n'][..])
			.filter(|s| !s.is_empty())
			.map(|s| Result::<_>::Ok(s.to_string()))
			.collect::<Vec<_>>();

		Result::<_>::Ok(
			stream::iter(addrs)
				.and_then(|addr| async move {
					match parse_ip(&addr)? {
						ParseIpResult::Addr(a) => Ok(stream::once(future::ok(a)).left_stream()),
						ParseIpResult::Other(a, p) => {
							let addrs = net::lookup_host((a, p.unwrap_or(DEFAULT_PORT)))
								.await
								.map_err(Error::ResolveHost)?
								.collect::<Vec<_>>();
							Ok(stream::iter(addrs).map(Result::<_>::Ok).right_stream())
						}
					}
				})
				.try_flatten(),
		)
	})
	.try_flatten()
}

pub async fn resolve_tsdns<A: net::ToSocketAddrs>(server: A, addr: &str) -> Result<SocketAddr> {
	let mut stream = TcpStream::connect(server).await.map_err(|e| Error::Io("tsdns", e))?;
	stream.write_all(addr.as_bytes()).await.map_err(|e| Error::Io("tsdns", e))?;
	let mut data = Vec::new();
	stream.read_to_end(&mut data).await.map_err(|e| Error::Io("tsdns", e))?;

	let addr = str::from_utf8(&data).map_err(Error::TsdnsParseResponse)?;
	if addr.starts_with("404") {
		return Err(Error::TsdnsAddressNotFound);
	}
	match parse_ip(addr)? {
		ParseIpResult::Addr(a) => Ok(a),
		_ => Err(Error::TsdnsAddressInvalidResponse(addr.to_string())),
	}
}

fn resolve_srv(resolver: TokioResolver, addr: String) -> impl Stream<Item = Result<SocketAddr>> {
	stream::once(async move {
		let lookup = resolver.srv_lookup(addr.clone()).await.map_err(Error::SrvLookup)?;
		let srvs = lookup
			.answers()
			.iter()
			.map(|r| {
				let RData::SRV(srv) = &r.data else { panic!("Unexpected answer") };
				srv.clone()
			})
			.collect::<Vec<_>>();

		let sorted_entries = order_srv_by_priority_weight(&srvs);
		for e in &sorted_entries {
			debug!(
				srv = %addr,
				target = %e.target,
				port = e.port,
				priority = e.priority,
				weight = e.weight,
				"SRV hit"
			);
		}

		let res = sorted_entries
			.into_iter()
			.map(|e| Ok((e.target.to_ascii(), e.port)))
			.collect::<Vec<Result<(String, u16)>>>();
		drop(resolver);
		Ok(stream::iter(res)
			.and_then(|(e, port)| async move {
				let res = net::lookup_host((e.as_str(), port))
					.await
					.map_err(Error::ResolveHost)?
					.map(Ok)
					.collect::<Vec<_>>();
				Ok(stream::iter(res))
			})
			.try_flatten())
	})
	.try_flatten()
}

/// RFC 2782: lower priority first; within a priority, pick by weight; weight 0
/// records are selected only after all positive-weight records (but still used).
fn order_srv_by_priority_weight(
	srvs: &[hickory_net::proto::rr::rdata::SRV],
) -> Vec<hickory_net::proto::rr::rdata::SRV> {
	let prios = srvs.iter().chunk_by(|srv| srv.priority);
	let entries = prios.into_iter().sorted_by_key(|(p, _)| *p);

	let mut sorted_entries = Vec::new();
	for (_, es) in entries {
		let mut zero_entries = Vec::new();
		let mut weighted = Vec::new();
		for e in es {
			if e.weight == 0 {
				zero_entries.push(e.clone());
			} else {
				weighted.push(e.clone());
			}
		}

		while !weighted.is_empty() {
			let weight: u32 = weighted.iter().map(|e| e.weight as u32).sum();
			let mut w = rand::rng().random_range(0..=weight);
			let mut picked = None;
			for i in 0..weighted.len() {
				let ew = weighted[i].weight as u32;
				if w <= ew {
					picked = Some(i);
					break;
				}
				w -= ew;
			}
			sorted_entries.push(weighted.remove(picked.unwrap_or(0)));
		}

		// Critical: GreenTeaSpeak (and many others) publish weight=0 only.
		// Dropping these made SRV resolve to an empty list.
		sorted_entries.extend(zero_entries);
	}
	sorted_entries
}

#[cfg(test)]
mod test {
	use super::*;
	use crate::tests::create_logger;

	#[test]
	fn parse_ip_without_port() {
		let res = parse_ip("127.0.0.1");
		assert_eq!(
			res.unwrap(),
			ParseIpResult::Addr(format!("127.0.0.1:{}", DEFAULT_PORT).parse().unwrap())
		);
	}

	#[test]
	fn parse_ip_with_port() {
		let res = parse_ip("127.0.0.1:1");
		assert_eq!(res.unwrap(), ParseIpResult::Addr("127.0.0.1:1".parse().unwrap()));
	}

	#[test]
	fn parse_ip6_without_port() {
		let res = parse_ip("::");
		assert_eq!(
			res.unwrap(),
			ParseIpResult::Addr(format!("[::]:{}", DEFAULT_PORT).parse().unwrap())
		);
	}

	#[test]
	fn parse_ip6_without_port2() {
		let res = parse_ip("[::]");
		assert_eq!(
			res.unwrap(),
			ParseIpResult::Addr(format!("[::]:{}", DEFAULT_PORT).parse().unwrap())
		);
	}

	#[test]
	fn parse_ip6_with_port() {
		let res = parse_ip("[::]:1");
		assert_eq!(res.unwrap(), ParseIpResult::Addr("[::]:1".parse().unwrap()));
	}

	#[test]
	fn parse_ip_address_without_port() {
		assert_eq!(parse_ip("localhost").unwrap(), ParseIpResult::Other("localhost", None));
	}

	#[test]
	fn parse_ip_address_with_port() {
		assert_eq!(parse_ip("localhost:1").unwrap(), ParseIpResult::Other("localhost", Some(1)));
	}

	#[test]
	fn parse_ip_with_large_port() {
		assert!(parse_ip("127.0.0.1:65536").is_err());
	}

	#[test]
	fn srv_lookup_hosts_exact_only() {
		// Exact host only - no apex fallback, so a subdomain with its own record
		// is never hijacked onto a different server's apex SRV (issue #9).
		assert_eq!(
			srv_lookup_hosts("ts6.rush-zone.com"),
			vec!["ts6.rush-zone.com".to_string()]
		);
		assert_eq!(
			srv_lookup_hosts("greenteaspeak.de."),
			vec!["greenteaspeak.de".to_string()]
		);
		assert_eq!(srv_lookup_hosts("localhost"), vec!["localhost".to_string()]);
	}

	#[test]
	fn parse_hostname_with_port_skips_to_other() {
		assert_eq!(
			parse_ip("ts.greenteaspeak.de:9987").unwrap(),
			ParseIpResult::Other("ts.greenteaspeak.de", Some(9987))
		);
	}

	#[test]
	fn order_srv_keeps_weight_zero() {
		use hickory_net::proto::rr::domain::Name;
		use hickory_net::proto::rr::rdata::SRV;

		let target: Name = "ts.greenteaspeak.de.".parse().unwrap();
		let only_zero = vec![SRV::new(10, 0, 9987, target.clone())];
		let ordered = order_srv_by_priority_weight(&only_zero);
		assert_eq!(ordered.len(), 1);
		assert_eq!(ordered[0].port, 9987);
		assert_eq!(ordered[0].weight, 0);

		let mixed = vec![
			SRV::new(10, 0, 9987, target.clone()),
			SRV::new(10, 50, 9988, "other.example.".parse().unwrap()),
			SRV::new(5, 0, 9990, "first.example.".parse().unwrap()),
		];
		let ordered = order_srv_by_priority_weight(&mixed);
		assert_eq!(ordered.len(), 3);
		// Priority 5 first
		assert_eq!(ordered[0].port, 9990);
		// Then positive weight before weight 0 within priority 10
		assert_eq!(ordered[1].port, 9988);
		assert_eq!(ordered[2].port, 9987);
	}

	#[tokio::test]
	async fn resolve_localhost() {
		create_logger();
		let res: Vec<_> = resolve("127.0.0.1".into()).map(|r| r.unwrap()).collect().await;
		let addr = format!("127.0.0.1:{}", DEFAULT_PORT).parse::<SocketAddr>().unwrap();
		assert_eq!(res.as_slice(), &[addr]);
	}

	#[tokio::test]
	async fn resolve_localhost2() {
		create_logger();
		let res: Vec<_> = resolve("localhost".into()).map(|r| r.unwrap()).collect().await;
		assert!(res.contains(&format!("127.0.0.1:{}", DEFAULT_PORT).parse().unwrap()));
	}

	#[tokio::test]
	async fn resolve_example() {
		create_logger();
		let res: Vec<_> = resolve("example.com".into()).map(|r| r.unwrap()).collect().await;
		assert!(!res.is_empty());
	}

	#[tokio::test]
	async fn resolve_splamy_de() {
		create_logger();

		let res: Vec<_> = tokio::time::timeout(
			Duration::from_secs(5),
			resolve("splamy.de".into()).map(|r| r.unwrap()).collect(),
		)
		.await
		.expect("Resolve takes unacceptable long");
		assert!(res.contains(&format!("37.120.179.68:{}", DEFAULT_PORT).parse().unwrap()));
	}

	#[tokio::test]
	async fn resolve_greenteaspeak_via_srv() {
		create_logger();
		// Root domain A is the web host (.131); SRV points at ts.*:9987 (.129).
		// Without weight-0 handling this falls through to the wrong A record.
		let res: Vec<_> = tokio::time::timeout(
			Duration::from_secs(10),
			resolve("greenteaspeak.de".into()).map(|r| r.unwrap()).collect(),
		)
		.await
		.expect("Resolve takes unacceptable long");
		let expected: SocketAddr = "148.251.103.129:9987".parse().unwrap();
		assert!(
			res.contains(&expected),
			"expected SRV target {}, got {:?}",
			expected,
			res
		);
	}

	#[tokio::test]
	async fn resolve_loc() {
		create_logger();
		let res: Vec<_> = resolve("loc".into()).map(|r| r.unwrap()).collect().await;
		assert!(res.contains(&format!("127.0.0.1:{}", DEFAULT_PORT).parse().unwrap()));
	}
}
