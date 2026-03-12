import sys
def sieve(limit):
    is_prime = [True] * (limit + 1)
    is_prime[0] = is_prime[1] = False
    p = 2
    while p * p <= limit:
        if is_prime[p]:
            for m in range(p * p, limit + 1, p):
                is_prime[m] = False
        p += 1
    return is_prime

primes = sieve(1_000_000)
count = sum(primes)
sys.exit(0 if count == 78498 else 1)
