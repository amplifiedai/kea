function fib(n) {
    if (n < 2) return n;
    return fib(n - 1) + fib(n - 2);
}
const result = fib(40);
process.exit(result === 102334155 ? 0 : 1);
