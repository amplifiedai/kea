fn fib(n: i64) -> i64 {
    if n < 2 { n } else { fib(n - 1) + fib(n - 2) }
}

fn main() {
    let result = fib(40);
    std::process::exit(if result == 102334155 { 0 } else { 1 });
}
