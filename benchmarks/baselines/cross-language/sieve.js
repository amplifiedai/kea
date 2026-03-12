const n = 1_000_000;
const is_prime = new Uint8Array(n + 1).fill(1);
is_prime[0] = is_prime[1] = 0;
for (let p = 2; p * p <= n; p++) {
    if (is_prime[p]) {
        for (let m = p * p; m <= n; m += p) is_prime[m] = 0;
    }
}
let count = 0;
for (let i = 0; i <= n; i++) if (is_prime[i]) count++;
process.exit(count === 78498 ? 0 : 1);
