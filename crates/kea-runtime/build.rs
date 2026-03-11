fn main() {
    let arch = std::env::var("CARGO_CFG_TARGET_ARCH").unwrap();
    let os = std::env::var("CARGO_CFG_TARGET_OS").unwrap();

    let asm_file = match (arch.as_str(), os.as_str()) {
        ("aarch64", "macos") => "src/fiber_asm_aarch64.s",
        ("aarch64", _) => "src/fiber_asm_aarch64_linux.s",
        ("x86_64", "macos") => "src/fiber_asm_x86_64_macos.s",
        ("x86_64", _) => "src/fiber_asm_x86_64.s",
        (arch, os) => {
            // No fiber assembly for this platform — fiber operations will panic at runtime.
            println!(
                "cargo:warning=kea-runtime: no fiber assembly for {arch}-{os}; \
                 @deferred handlers will not be available"
            );
            return;
        }
    };

    cc::Build::new().file(asm_file).compile("kea_fiber_asm");

    println!("cargo:rerun-if-changed={asm_file}");
    println!("cargo:rerun-if-changed=build.rs");
}
