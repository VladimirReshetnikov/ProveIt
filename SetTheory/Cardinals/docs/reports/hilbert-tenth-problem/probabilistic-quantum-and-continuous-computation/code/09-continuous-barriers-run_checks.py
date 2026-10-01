"""Reproduce exact-rational checks and manuscript tables (no external packages)."""
from __future__ import annotations

from collections import Counter
from fractions import Fraction as F
from itertools import permutations, product
from pathlib import Path
import json
import random
import sys

from barriers import (BinaryMachine, Box, GridGraph, PackedPWA, Transition,
                      bottleneck, make_grid_graph, norm_inf, quartic_expression,
                      quartic_value, reachable_below, safety_certificate, tape_update)

OUT = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(__file__).resolve().parents[1]/"results"
OUT.mkdir(parents=True, exist_ok=True)
counts: Counter[str] = Counter()
rng = random.Random(20260930)


def checked(category: str, assertion: bool) -> None:
    if not assertion:
        raise AssertionError(category)
    counts[category] += 1


def encode(tape: dict[int, int], head: int) -> tuple[F, F]:
    left = sum((F(2*b, 3**(head-i)) for i, b in tape.items() if i < head), F(0))
    right = sum((F(2*b, 3**(i-head+1)) for i, b in tape.items() if i >= head), F(0))
    return left, right


# Direct finite-tape semantics, independent of the affine update formulas.
for word in product((0, 1), repeat=7):
    tape = dict(zip(range(-3, 4), word))
    u, v = encode(tape, 0)
    for write, move in product((0, 1), ("L", "R", "S")):
        new_tape = dict(tape)
        new_tape[0] = write
        new_head = {"L": -1, "R": 1, "S": 0}[move]
        expected = encode(new_tape, new_head)
        actual = tape_update(u, v, tape[-1], tape[0], write, move)
        checked("finite_tape_updates", actual == expected)

# Mapping of entire digit boxes, including non-Cantor points and boundaries.
for c, a, b, move, tail_u, tail_v in product(
        (0, 1), (0, 1), (0, 1), ("L", "R", "S"),
        (F(0), F(1, 6), F(1, 2), F(5, 6), F(1)),
        (F(0), F(1, 6), F(1, 2), F(5, 6), F(1))):
    u, v = (2*c+tail_u)/3, (2*a+tail_v)/3
    image = tape_update(u, v, c, a, b, move)
    checked("whole_digit_box_images", all(0 <= t <= 1 for t in image))

# Directed bottleneck/cut duality, with exhaustive cuts for small graphs.
for n in range(2, 8):
    for _ in range(20):
        weights = tuple(tuple(F(rng.randrange(13), 12) for _ in range(n))
                        for _ in range(n))
        radius = bottleneck(weights, 0, {n-1})
        cut_values = []
        for mid in product((False, True), repeat=n-2):
            inside = {0} | {i+1 for i, b in enumerate(mid) if b}
            cut_values.append(min(weights[u][v] for u in inside
                                  for v in range(n) if v not in inside))
        checked("exhaustive_bottleneck_cut_duality", radius == max(cut_values))
        cut = reachable_below(weights, 0, radius)
        checked("strict_threshold_optimal_cuts", n-1 not in cut and
                min(weights[u][v] for u in cut for v in range(n) if v not in cut) == radius)

# Scalar maps with analytically known infinite-horizon radius.
table = []
for a, b, mesh in product((F(0), F(1, 4), F(1, 2), F(3, 4)),
                          (F(1, 4), F(1, 2), F(3, 4)), (4, 8, 16, 32, 64)):
    graph = make_grid_graph(lambda p: (a*p[0],), (F(0),),
                            [Box((b,), (F(1),))], mesh, a)
    radius = bottleneck(graph.weights, graph.source, graph.targets)
    exact = (1-a)*b
    checked("analytic_contraction_enclosures", exact <= radius <= exact+graph.error)
    cert = safety_certificate(graph)
    checked("quartic_certificate_iff_threshold", (cert is not None) == (radius >= graph.threshold))
    if cert is not None:
        checked("quartic_certificate_values", quartic_value(graph, cert) == 0)
    if a == F(1, 2) and b == F(3, 4):
        table.append({"N": mesh, "vertices": len(graph.vertices), "r_N": str(radius),
                      "lower": str(max(F(0), radius-graph.error)),
                      "upper": str(radius), "certificate": cert is not None})

for mesh in (2, 4, 8, 16, 32):
    graph = make_grid_graph(lambda p: p, (F(0),),
                            [Box((F(1),), (F(1),))], mesh, F(1))
    radius = bottleneck(graph.weights, graph.source, graph.targets)
    checked("fragile_identity_example", radius == F(1, mesh) and safety_certificate(graph) is None)

for mesh in (4, 8, 16, 32):
    graph = make_grid_graph(lambda p: (p[0]/2,), (F(1, 7),),
                            [Box((F(3, 4),), (F(1),))], mesh, F(1, 2))
    radius = bottleneck(graph.weights, graph.source, graph.targets)
    checked("off_grid_source_enclosures", len(graph.vertices) == mesh+2 and
            F(3, 8) <= radius <= F(3, 8)+graph.error)

small = make_grid_graph(lambda p: (p[0]/2,), (F(0),),
                        [Box((F(3, 4),), (F(1),))], 4, F(1, 2))
for bits in product(range(-1, 3), repeat=len(small.vertices)):
    valid = (all(b in (0, 1) for b in bits) and bits[small.source] == 1
             and all(bits[t] == 0 for t in small.targets)
             and all(not (bits[u] == 1 and bits[v] == 0)
                     for u in range(len(bits)) for v in range(len(bits))
                     if small.weights[u][v] < small.threshold))
    checked("quartic_exhaustive_integer_assignments", (quartic_value(small, bits) == 0) == valid)

# A non-universal sample machine with all three move directions.
sample = BinaryMachine(5, 0, 3, 4, {
    (0, 0): Transition(1, 1, "R"), (0, 1): Transition(2, 0, "L"),
    (1, 0): Transition(3, 0, "S"), (1, 1): Transition(0, 1, "R"),
    (2, 0): Transition(4, 1, "L"), (2, 1): Transition(0, 0, "S")})
compiled = PackedPWA(sample)
for j in (0, 1, 2):
    for c, a, tu, tv, z in product((0, 1), (0, 1),
                                  (F(0), F(1, 2), F(1)),
                                  (F(0), F(1, 2), F(1)),
                                  (F(0), F(1, 6), F(1, 3))):
        u, v = (2*c+tu)/3, (2*a+tv)/3
        point = (compiled.alpha[j]+compiled.beta*u, v, z)
        checked("PWA_prescribed_low_boxes", compiled(point) == compiled.prescribed(point))
    for u, v, z in product((F(0), F(1, 2), F(1)),
                           (F(0), F(1, 2), F(1)), (F(2, 3), F(5, 6), F(1))):
        p = (compiled.alpha[j]+compiled.beta*u, v, z)
        checked("PWA_emergency_boxes", compiled(p) == compiled.sink(sample.accept))
for j in (sample.accept, sample.reject):
    for r, v, z in product((F(-1, 2), F(0), F(1, 2), F(1), F(3, 2)),
                           (F(0), F(1, 2), F(1)), (F(0), F(1, 2), F(1))):
        p = (compiled.alpha[j]+compiled.beta*r, v, z)
        checked("PWA_terminal_slabs", compiled(p) == compiled.sink(j))

# Every simplex of this compiled example: exact affine row-sum bounds.
for indices in product(*(range(len(axis)-1) for axis in compiled.axes)):
    lo = [axis[i] for axis, i in zip(compiled.axes, indices)]
    hi = [axis[i+1] for axis, i in zip(compiled.axes, indices)]
    for order in permutations(range(3)):
        vertex = list(lo)
        prev = compiled.vertex(tuple(vertex))
        columns = {}
        for axis in order:
            vertex[axis] = hi[axis]
            image = compiled.vertex(tuple(vertex))
            columns[axis] = tuple((b-a)/(hi[axis]-lo[axis]) for a, b in zip(prev, image))
            prev = image
        bound = max(sum(abs(columns[j][k]) for j in range(3)) for k in range(3))
        checked("all_sample_simplex_Lipschitz_bounds", bound <= compiled.lipschitz)

for _ in range(200):
    p = tuple(F(rng.randrange(61), 60) for _ in range(3))
    q = tuple(F(rng.randrange(61), 60) for _ in range(3))
    fp, fq = compiled(p), compiled(q)
    checked("PWA_cube_and_global_Lipschitz_samples", all(0 <= t <= 1 for t in fp+fq)
            and norm_inf(fp, fq) <= compiled.lipschitz*norm_inf(p, q))

loop = PackedPWA(BinaryMachine(3, 0, 1, 2,
        {(0, a): Transition(0, a, "S") for a in (0, 1)}))
for exponent in range(1, 16):
    baseline = loop(loop.initial([1]))
    point = (baseline[0], baseline[1], F(2, 3**exponent))
    for step in range(exponent):
        checked("emergency_prefix_avoids_target", not loop.target(point))
        point = loop(point)
    checked("emergency_exact_trigger", loop.target(point))

# Rejecting countdowns: test the upper-bound schedule and bounded noise enclosure.
for T in range(1, 10):
    m = T+2
    table_tm = {(j, a): Transition(j+1 if j < T-1 else T+1, a, "S")
                for j in range(T) for a in (0, 1)}
    counter = PackedPWA(BinaryMachine(m, 0, T, T+1, table_tm))
    start = counter.initial([1])
    nominal = start
    for _ in range(T):
        nominal = counter(nominal)
    checked("countdown_exact_rejection", counter.alpha[T+1] <= nominal[0]
            <= counter.alpha[T+1]+counter.beta and not counter.target(nominal))
    if T >= 2:
        p = counter(start)
        p = (p[0], p[1], F(2, 3**(T-1)))
        for _ in range(T-1):
            p = counter(p)
        checked("rejection_time_upper_radius_schedule", counter.target(p))
    S = sum((counter.lipschitz**j for j in range(T)), F(0))
    epsilon = counter.beta/(4*S)
    for signs in product((-1, 1), repeat=3):
        p = start
        for _ in range(T+4):
            image = counter(p)
            p = tuple(min(F(1), max(F(0), y+sgn*epsilon)) for y, sgn in zip(image, signs))
            checked("rejection_lower_radius_noise_samples", not counter.target(p))

certificate = safety_certificate(small)
assert certificate is not None
(OUT/"small_certificate.json").write_text(json.dumps({
    "map": "f(x)=x/2", "initial": "0", "target": ["3/4", "1"],
    "N": 4, "L": "1/2", "threshold": str(small.threshold),
    "certified_lower_radius": str(small.error),
    "vertices": [str(v[0]) for v in small.vertices],
    "bits": certificate, "polynomial_value": quartic_value(small, certificate)
}, indent=2)+"\n")
(OUT/"small_quartic.txt").write_text(quartic_expression(small))
(OUT/"contraction_table.json").write_text(json.dumps(table, indent=2)+"\n")
report = {"status": "PASS", "arithmetic": "exact Python fractions.Fraction",
          "seed": 20260930, "total_assertions": sum(counts.values()),
          "checks": dict(sorted(counts.items())),
          "scope": "Finite implementation tests; no formal proof, no universal TM table, no MRDP polynomial extraction."}
(OUT/"verification.json").write_text(json.dumps(report, indent=2)+"\n")
print(json.dumps(report, indent=2))
print("\nContraction example:")
print(json.dumps(table, indent=2))
