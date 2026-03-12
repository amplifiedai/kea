import sys
sys.setrecursionlimit(200000)

def partition(arr, lo, hi):
    pivot = arr[hi]
    i = lo
    for j in range(lo, hi):
        if arr[j] <= pivot:
            arr[i], arr[j] = arr[j], arr[i]
            i += 1
    arr[i], arr[hi] = arr[hi], arr[i]
    return i

def qs(arr, lo, hi):
    if lo < hi:
        p = partition(arr, lo, hi)
        qs(arr, lo, p - 1)
        qs(arr, p + 1, hi)

n = 100_000
arr = list(range(1, n + 1))
seed = 42
for i in range(n - 1, 0, -1):
    seed = (seed * 1103515245 + 12345) & 0x7fffffff
    j = seed % (i + 1)
    arr[i], arr[j] = arr[j], arr[i]

qs(arr, 0, n - 1)
sys.exit(0 if arr[0] == 1 and arr[-1] == n else 1)
