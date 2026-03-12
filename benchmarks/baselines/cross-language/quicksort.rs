fn partition(arr: &mut [i64], lo: usize, hi: usize) -> usize {
    let pivot = arr[hi];
    let mut i = lo;
    for j in lo..hi {
        if arr[j] <= pivot {
            arr.swap(i, j);
            i += 1;
        }
    }
    arr.swap(i, hi);
    i
}

fn qs(arr: &mut [i64], lo: usize, hi: usize) {
    if lo < hi {
        let p = partition(arr, lo, hi);
        if p > 0 { qs(arr, lo, p - 1); }
        qs(arr, p + 1, hi);
    }
}

fn main() {
    let n = 100_000usize;
    let mut arr: Vec<i64> = (1..=n as i64).collect();
    let mut seed: i64 = 42;
    for i in (1..n).rev() {
        seed = (seed.wrapping_mul(1103515245) + 12345) & 0x7fffffff;
        let j = (seed as usize) % (i + 1);
        arr.swap(i, j);
    }
    qs(&mut arr, 0, n - 1);
    std::process::exit(if arr[0] == 1 && arr[n - 1] == n as i64 { 0 } else { 1 });
}
