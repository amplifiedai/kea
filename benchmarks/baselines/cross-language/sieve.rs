fn sieve(limit: usize) -> Vec<bool> {
    let mut is_prime = vec![true; limit + 1];
    is_prime[0] = false;
    if limit >= 1 { is_prime[1] = false; }
    let mut p = 2;
    while p * p <= limit {
        if is_prime[p] {
            let mut m = p * p;
            while m <= limit {
                is_prime[m] = false;
                m += p;
            }
        }
        p += 1;
    }
    is_prime
}

fn main() {
    let n = 1_000_000;
    let primes = sieve(n);
    let count = primes.iter().filter(|&&b| b).count();
    std::process::exit(if count == 78498 { 0 } else { 1 });
}
