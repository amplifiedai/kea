package main

import "os"

func main() {
	n := 200
	a := make([]float64, n*n)
	b := make([]float64, n*n)
	for i := range a { a[i] = float64((i+1)%1000); b[i] = float64((i+1)%1000) }
	c := make([]float64, n*n)
	for r := 0; r < n; r++ {
		for col := 0; col < n; col++ {
			acc := 0.0
			for k := 0; k < n; k++ { acc += a[r*n+k] * b[k*n+col] }
			c[r*n+col] = acc
		}
	}
	if c[0] > 0 { os.Exit(0) } else { os.Exit(1) }
}
