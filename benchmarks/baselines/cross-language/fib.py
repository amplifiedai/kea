import sys
def fib(n):
    if n < 2: return n
    return fib(n - 1) + fib(n - 2)
result = fib(40)
sys.exit(0 if result == 102334155 else 1)
