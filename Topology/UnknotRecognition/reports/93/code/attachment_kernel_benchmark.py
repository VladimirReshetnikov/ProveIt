"""Reproduce complete graph production/replay timings, including provenance.

The examples are finite attachment networks, not knot-recognition timings.
Every graph is realizable as a graph of balls and solid tori.  Source-chart
production and recognition of the labelled vertex manifolds are not timed.
"""

import json
from pathlib import Path
import platform
from statistics import median
import sys
from time import perf_counter

from attachment_kernel import kernelize_attachment_network
from attachment_kernel_verify import verify_attachment_kernel


ROOT = Path(__file__).resolve().parents[1]


def make_chain(n, genus=3):
    marked = {0, n // 2, n - 1} if genus == 3 else set()
    vertices = [{"id": i, "euler_characteristic": 0 if i in marked else 1}
                for i in range(n)]
    edges = [{"id": i, "ends": [i, i + 1]} for i in range(n - 1)]
    if not marked:
        edges += [{"id": n - 1 + j, "ends": [0, n - 1]} for j in range(genus)]
    return vertices, edges


def main():
    rows = []
    for n in (10, 100, 1000, 10000):
        vertices, edges = make_chain(n)
        warm = kernelize_attachment_network(vertices, edges)
        assert verify_attachment_kernel(vertices, edges, warm)
        times, check_times, encoded = [], [], None
        for _ in range(7):
            started = perf_counter()
            cert = kernelize_attachment_network(vertices, edges)
            times.append(perf_counter() - started)
            started = perf_counter()
            assert verify_attachment_kernel(vertices, edges, cert)
            check_times.append(perf_counter() - started)
            encoded = json.dumps(cert, sort_keys=True, separators=(",", ":")).encode()
        rows.append(dict(source_vertices=n, source_edges=len(edges), genus=3,
                         kernel_vertices=len(cert["kernel"]["vertices"]),
                         kernel_edges=len(cert["kernel"]["edges"]),
                         source_provenance_bytes=len(encoded),
                         production_seconds=times, replay_seconds=check_times,
                         median_production_seconds=median(times),
                         median_replay_seconds=median(check_times)))
        print(n, rows[-1]["median_production_seconds"], rows[-1]["median_replay_seconds"])
    out = ROOT / "data/attachment_kernel_benchmarks.json"
    out.write_text(json.dumps(dict(python=sys.version, platform=platform.platform(),
                                  repeats=7, rows=rows), indent=2) + "\n")
    examples = []
    for n, g in ((15, 3), (15, 1), (1, 0)):
        vertices, edges = make_chain(n, g)
        cert = kernelize_attachment_network(vertices, edges)
        assert verify_attachment_kernel(vertices, edges, cert)
        examples.append(dict(vertices=vertices, edges=edges, certificate=cert))
    (ROOT / "certificates/attachment_kernel_examples.json").write_text(
        json.dumps(examples, indent=2) + "\n")


if __name__ == "__main__":
    main()
