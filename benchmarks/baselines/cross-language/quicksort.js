function partition(arr, lo, hi) {
    const pivot = arr[hi];
    let i = lo;
    for (let j = lo; j < hi; j++) {
        if (arr[j] <= pivot) {
            [arr[i], arr[j]] = [arr[j], arr[i]];
            i++;
        }
    }
    [arr[i], arr[hi]] = [arr[hi], arr[i]];
    return i;
}

function qs(arr, lo, hi) {
    if (lo < hi) {
        const p = partition(arr, lo, hi);
        qs(arr, lo, p - 1);
        qs(arr, p + 1, hi);
    }
}

const n = 100000;
const arr = Array.from({length: n}, (_, i) => i + 1);
let seed = 42;
for (let i = n - 1; i > 0; i--) {
    seed = (seed * 1103515245 + 12345) & 0x7fffffff;
    const j = seed % (i + 1);
    [arr[i], arr[j]] = [arr[j], arr[i]];
}
qs(arr, 0, n - 1);
process.exit(arr[0] === 1 && arr[n - 1] === n ? 0 : 1);
