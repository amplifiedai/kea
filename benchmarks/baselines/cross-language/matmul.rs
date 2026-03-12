fn main() {
    let n = 200usize;
    let mut a = vec![0.0f64; n * n];
    let mut b = vec![0.0f64; n * n];
    for i in 0..n * n {
        let v = ((i + 1) % 1000) as f64;
        a[i] = v;
        b[i] = v;
    }
    let mut c = vec![0.0f64; n * n];
    for r in 0..n {
        for col in 0..n {
            let mut acc = 0.0;
            for k in 0..n {
                acc += a[r * n + k] * b[k * n + col];
            }
            c[r * n + col] = acc;
        }
    }
    std::process::exit(if c[0] > 0.0 { 0 } else { 1 });
}
