use kea_runtime::Runtime;
use rayon::prelude::*;
use serde::Serialize;
use std::env;
use std::fs;
use std::time::{Duration, Instant};

#[derive(Debug, Clone, Serialize)]
struct Sample {
    size: usize,
    iterations: usize,
    kea_runtime_median_ns: u128,
    rayon_median_ns: u128,
    kea_over_rayon: f64,
}

#[derive(Debug, Clone, Serialize)]
struct CompareReport {
    threads: usize,
    timestamp_epoch_ms: u128,
    samples: Vec<Sample>,
}

fn now_epoch_ms() -> u128 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_or(0, |d| d.as_millis())
}

fn median_ns(mut samples: Vec<Duration>) -> u128 {
    samples.sort_unstable();
    samples[samples.len() / 2].as_nanos()
}

fn run_kea_runtime(size: usize, threads: usize) -> Duration {
    let runtime = Runtime::new(threads);
    let input: Vec<u64> = (0..size as u64).collect();

    let start = Instant::now();
    let out = runtime.parallel_map(input, |x| x.wrapping_mul(17).wrapping_add(3));
    let elapsed = start.elapsed();

    let checksum: u64 = out
        .into_iter()
        .fold(0, |acc, value| acc.wrapping_add(value));
    std::hint::black_box(checksum);
    elapsed
}

fn run_rayon(size: usize) -> Duration {
    let input: Vec<u64> = (0..size as u64).collect();

    let start = Instant::now();
    let out: Vec<u64> = input
        .into_par_iter()
        .map(|x| x.wrapping_mul(17).wrapping_add(3))
        .collect();
    let elapsed = start.elapsed();

    let checksum: u64 = out
        .into_iter()
        .fold(0, |acc, value| acc.wrapping_add(value));
    std::hint::black_box(checksum);
    elapsed
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let out_path = args.get(1).cloned();

    let threads = std::thread::available_parallelism()
        .map_or(4, usize::from)
        .max(1);
    let sizes = [1_000usize, 10_000usize, 100_000usize];
    let iterations = 7usize;

    let mut report = CompareReport {
        threads,
        timestamp_epoch_ms: now_epoch_ms(),
        samples: Vec::new(),
    };

    for size in sizes {
        let mut kea_samples = Vec::with_capacity(iterations);
        let mut rayon_samples = Vec::with_capacity(iterations);

        for _ in 0..iterations {
            kea_samples.push(run_kea_runtime(size, threads));
            rayon_samples.push(run_rayon(size));
        }

        let kea_median_ns = median_ns(kea_samples);
        let rayon_median_ns = median_ns(rayon_samples);
        let kea_over_rayon = if rayon_median_ns == 0 {
            0.0
        } else {
            kea_median_ns as f64 / rayon_median_ns as f64
        };

        report.samples.push(Sample {
            size,
            iterations,
            kea_runtime_median_ns: kea_median_ns,
            rayon_median_ns,
            kea_over_rayon,
        });
    }

    let json = serde_json::to_string_pretty(&report).expect("serialize runtime comparison report");

    if let Some(path) = out_path {
        fs::write(&path, json.as_bytes()).expect("write runtime comparison report");
        println!("wrote {}", path);
    } else {
        println!("{json}");
    }
}
