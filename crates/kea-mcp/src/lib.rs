//! Compatibility shim for MCP integration.
//!
//! The MCP server is implemented in the main `kea` crate so the project ships
//! one executable (`kea`) with `kea mcp` as a subcommand.

pub use kea::{KeaMcpServer, serve_mcp_stdio};
