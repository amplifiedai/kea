package main

import "os"

func fib(n int64) int64 {
	if n < 2 { return n }
	return fib(n-1) + fib(n-2)
}

func main() {
	if fib(40) == 102334155 { os.Exit(0) } else { os.Exit(1) }
}
