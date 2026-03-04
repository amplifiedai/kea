use kea_runtime::Runtime;

fn main() {
    divan::main();
}

#[divan::bench]
fn spawn_join_1k() {
    let runtime = Runtime::new(4);
    let handles = (0..1000)
        .map(|i: usize| runtime.spawn(move || i.wrapping_mul(3)))
        .collect::<Vec<_>>();

    let mut sum = 0usize;
    for handle in handles {
        sum = sum.wrapping_add(handle.join());
    }
    divan::black_box(sum);
}

#[divan::bench]
fn parallel_map_1k() {
    let runtime = Runtime::new(4);
    let input = (0..1000usize).collect::<Vec<_>>();
    let output = runtime.parallel_map(input, |x| x.wrapping_mul(7));
    divan::black_box(output);
}
