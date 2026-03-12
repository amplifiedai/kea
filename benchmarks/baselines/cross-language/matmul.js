const n = 200;
const a = new Float64Array(n * n);
const b = new Float64Array(n * n);
for (let i = 0; i < n * n; i++) { a[i] = (i + 1) % 1000; b[i] = (i + 1) % 1000; }
const c = new Float64Array(n * n);
for (let r = 0; r < n; r++) {
    for (let col = 0; col < n; col++) {
        let acc = 0;
        for (let k = 0; k < n; k++) acc += a[r * n + k] * b[k * n + col];
        c[r * n + col] = acc;
    }
}
process.exit(c[0] > 0 ? 0 : 1);
