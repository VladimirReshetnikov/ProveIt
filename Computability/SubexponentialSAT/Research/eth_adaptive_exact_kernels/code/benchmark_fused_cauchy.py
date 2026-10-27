"""Full-preparation benchmark against matched late quadratic algorithm."""
import argparse
import gc
import json
import platform
import statistics
import time
from pathlib import Path
from cauchy_kernel import Parameters
from fused_cauchy import baseline_tables, fused_tables


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-a", type=int, default=9)
    parser.add_argument("--min-a", type=int, default=2)
    parser.add_argument("--repeats", type=int, default=5)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    records = []
    for a in range(args.min_a, args.max_a+1):
        N = 1 << (a-1)
        for i in sorted({0, a//2, a-1}):
            params = Parameters(a, i, 1 << i, (0, 1), 4*N+16)
            old, new = baseline_tables(params), fused_tables(params)
            if old["target"] != new["target"] or old["source"] != new["source"]:
                raise ArithmeticError("warmup output mismatch")
            wall, cpu = {"baseline": [], "fused": []}, {"baseline": [], "fused": []}
            for trial in range(args.repeats):
                order = [("baseline", baseline_tables), ("fused", fused_tables)]
                if trial % 2:
                    order.reverse()
                for name, algorithm in order:
                    gc.collect()
                    start, cpustart = time.perf_counter(), time.process_time()
                    result = algorithm(params)
                    cpu[name].append(time.process_time()-cpustart)
                    wall[name].append(time.perf_counter()-start)
                    if result['target'] != old['target'] or result['source'] != old['source']:
                        raise ArithmeticError('timed output mismatch')
            om, nm = statistics.median(wall["baseline"]), statistics.median(wall["fused"])
            oc, nc = statistics.median(cpu["baseline"]), statistics.median(cpu["fused"])
            record = {"a": a, "i": i, "N": N, "precision": params.precision,
                      "baseline_median_seconds": om, "fused_median_seconds": nm,
                      "wall_speedup": om/nm, "baseline_median_cpu_seconds": oc,
                      "fused_median_cpu_seconds": nc, "cpu_speedup": oc/nc,
                      "baseline_counts": old["counts"], "fused_counts": new["counts"],
                      "wall_samples": wall, "cpu_samples": cpu}
            records.append(record)
            print(json.dumps(record), flush=True)
    output = {"status": "PASS", "records": records, "repeats": args.repeats,
              "python": platform.python_version(), "platform": platform.platform(),
              "method": "full fresh preparation and both dense output tables; symmetric warmup; alternating order; every timed output compared outside timing; no archive code executed",
              "baseline_scope": "self-authored operation-matched reproduction of the late packet's one-inversion quadratic algorithm",
              "workload": "unramified degree-two ring, zeta=U, p=4N+16; not an end-to-end SAT benchmark"}
    dest = args.output or Path(__file__).resolve().parents[1]/"results"/"fused_cauchy_benchmark.json"
    dest.write_text(json.dumps(output, indent=2)+"\n")


if __name__ == "__main__":
    main()
