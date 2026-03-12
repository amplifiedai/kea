import sys
n = 200
a = [float((i + 1) % 1000) for i in range(n * n)]
b = [float((i + 1) % 1000) for i in range(n * n)]
c = [0.0] * (n * n)
for r in range(n):
    for col in range(n):
        acc = 0.0
        for k in range(n):
            acc += a[r * n + k] * b[k * n + col]
        c[r * n + col] = acc
sys.exit(0 if c[0] > 0.0 else 1)
