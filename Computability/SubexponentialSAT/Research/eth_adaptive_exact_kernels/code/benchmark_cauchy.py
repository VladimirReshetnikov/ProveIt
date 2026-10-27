"""Fair full-table benchmark; both algorithms include identical initialization."""
import argparse
import csv
import gc
import json
import platform
import statistics
import time
from pathlib import Path
from cauchy_kernel import Parameters, product_tables, recurrent_tables, expected_multiplications


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-a", type=int, default=8)
    parser.add_argument("--repeats", type=int, default=3)
    args = parser.parse_args()
    records = []
    for a in range(2, args.max_a+1):
        n = 1 << (a-1)
        for i in sorted({0, a//2, a-1}):
            params = Parameters(a, i, 1 << i, (0, 1), 4*n+16)
            # Warm both paths symmetrically. Every timed call below still
            # recreates all tables, inverses and prefactor from scratch.
            left, right = product_tables(params), recurrent_tables(params)
            if left["target"] != right["target"] or left["source"] != right["source"]:
                raise ArithmeticError("benchmark correctness mismatch")
            times = {"product": [], "recurrent": []}
            cpu_times = {"product": [], "recurrent": []}
            outputs = {"product": left, "recurrent": right}
            for trial in range(args.repeats):
                order = (("product", product_tables), ("recurrent", recurrent_tables))
                if trial % 2:
                    order = tuple(reversed(order))
                for name, algorithm in order:
                    gc.collect()
                    start = time.perf_counter()
                    cpu_start = time.process_time()
                    outputs[name] = algorithm(params)
                    cpu_times[name].append(time.process_time()-cpu_start)
                    times[name].append(time.perf_counter()-start)
            old, new = outputs["product"]["counts"], outputs["recurrent"]["counts"]
            for name, count in (("product", old), ("recurrent", new)):
                if count["ring_multiplications"] != expected_multiplications(
                        params, count["initialization_multiplications"], name):
                    raise ArithmeticError("benchmark operation count mismatch")
            old_time, new_time = statistics.median(times["product"]), statistics.median(times["recurrent"])
            old_cpu, new_cpu = statistics.median(cpu_times["product"]), statistics.median(cpu_times["recurrent"])
            record = {"a": a, "i": i, "N": n, "precision": params.precision,
                      "product_median_seconds": old_time, "recurrent_median_seconds": new_time,
                      "measured_speedup": old_time/new_time,
                      "product_median_cpu_seconds": old_cpu, "recurrent_median_cpu_seconds": new_cpu,
                      "measured_cpu_speedup": old_cpu/new_cpu,
                      "product_multiplications": old["ring_multiplications"],
                      "recurrent_multiplications": new["ring_multiplications"],
                      "multiplication_ratio": old["ring_multiplications"]/new["ring_multiplications"],
                      "initialization_multiplications": old["initialization_multiplications"],
                      "unit_inversions_each": old["unit_inversions"],
                      "unit_denominators": old["unit_denominators"],
                      "repeats": args.repeats,
                      "product_samples_seconds": times["product"],
                      "recurrent_samples_seconds": times["recurrent"],
                      "product_cpu_samples_seconds": cpu_times["product"],
                      "recurrent_cpu_samples_seconds": cpu_times["recurrent"]}
            records.append(record)
            print(json.dumps(record), flush=True)
    result = {"method": "self-authored modular product reference versus recurrence; no archive code executed",
              "workload": "complete dense target and source N-by-N tables, both including initialization",
              "baseline": "Both share cached denominator unit inverses, batch inversion, known triangular zeros and identical ring arithmetic.",
              "ring": "(Z/2^p Z)[U]/(U^2+U+1), zeta=U, p=4N+16",
              "precision_choice": "p exceeds the last guaranteed target weight; this is not a fixed-small-p truncation benchmark.",
              "environment": {"python": platform.python_version(), "platform": platform.platform(),
                              "processor": platform.processor()},
              "limitations": "Local component timings, not SAT runtimes or claims about partial/on-demand table workloads.",
              "records": records}
    destination = Path(__file__).resolve().parents[1] / "results"
    (destination / "cauchy_benchmark.json").write_text(json.dumps(result, indent=2)+"\n")
    scalar_keys = [key for key in records[0] if not key.endswith("samples_seconds")]
    with (destination / "cauchy_benchmark.csv").open("w", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=scalar_keys, extrasaction="ignore")
        writer.writeheader()
        writer.writerows(records)


if __name__ == "__main__":
    main()
