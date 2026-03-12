package main

import "os"

func partition(arr []int64, lo, hi int) int {
	pivot := arr[hi]
	i := lo
	for j := lo; j < hi; j++ {
		if arr[j] <= pivot {
			arr[i], arr[j] = arr[j], arr[i]
			i++
		}
	}
	arr[i], arr[hi] = arr[hi], arr[i]
	return i
}

func qs(arr []int64, lo, hi int) {
	if lo < hi {
		p := partition(arr, lo, hi)
		if p > 0 { qs(arr, lo, p-1) }
		qs(arr, p+1, hi)
	}
}

func main() {
	n := 100000
	arr := make([]int64, n)
	for i := range arr { arr[i] = int64(i + 1) }
	seed := int64(42)
	for i := n - 1; i > 0; i-- {
		seed = (seed*1103515245 + 12345) & 0x7fffffff
		j := int(seed) % (i + 1)
		arr[i], arr[j] = arr[j], arr[i]
	}
	qs(arr, 0, n-1)
	if arr[0] == 1 && arr[n-1] == int64(n) { os.Exit(0) } else { os.Exit(1) }
}
