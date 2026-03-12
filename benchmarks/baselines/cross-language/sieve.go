package main

import "os"

func main() {
	n := 1000000
	isPrime := make([]bool, n+1)
	for i := range isPrime { isPrime[i] = true }
	isPrime[0], isPrime[1] = false, false
	for p := 2; p*p <= n; p++ {
		if isPrime[p] {
			for m := p * p; m <= n; m += p { isPrime[m] = false }
		}
	}
	count := 0
	for _, b := range isPrime { if b { count++ } }
	if count == 78498 { os.Exit(0) } else { os.Exit(1) }
}
