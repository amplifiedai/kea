//! Kea MCP server entry point (stdio transport).

use std::io::IsTerminal;

use kea_mcp::KeaMcpServer;

fn print_help() {
    println!(
        "\
kea-mcp {}

Run the Kea MCP server over stdio transport.
This binary must be started by an MCP client with stdin/stdout pipes.

Usage:
  kea-mcp
  kea-mcp --help
  kea-mcp --version
",
        env!("CARGO_PKG_VERSION")
    );
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut args = std::env::args();
    let _bin = args.next();

    if let Some(arg) = args.next() {
        match arg.as_str() {
            "-h" | "--help" => {
                print_help();
                return Ok(());
            }
            "-V" | "--version" => {
                println!("{}", env!("CARGO_PKG_VERSION"));
                return Ok(());
            }
            _ => {
                eprintln!("kea-mcp: unknown argument `{arg}` (use --help)");
                std::process::exit(2);
            }
        }
    }

    if args.next().is_some() {
        eprintln!("kea-mcp: too many arguments (use --help)");
        std::process::exit(2);
    }

    if std::io::stdin().is_terminal() || std::io::stdout().is_terminal() {
        eprintln!("kea-mcp: refusing interactive TTY mode; start via MCP stdio pipes");
        std::process::exit(64);
    }

    let server = KeaMcpServer::new();
    server.serve_stdio().await?;
    Ok(())
}
