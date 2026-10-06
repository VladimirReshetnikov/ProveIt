#!/usr/bin/env python3
"""Exact, finite diagnostics for Report152. Standard library only; Python >=3.10.

These checks do not prove uniform asymptotic errors, canonical split-tree
transfer, prime representation uniqueness, or eventual inverse brackets.
"""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from fractions import Fraction as Q
from itertools import combinations, permutations
import json
import os
from pathlib import Path
import stat
import sys

ROOT = Path(__file__).absolute().parent
RESULTS = ROOT / "results"


class VerificationError(RuntimeError):
    pass


def require(condition, message):
    """Never use assert: verification must survive python -O."""
    if not condition:
        raise VerificationError(message)


def exact_equal(actual, expected, label):
    require(actual == expected, f"{label}: actual={actual!r}; claimed={expected!r}")


def rational(value):
    value = Q(value)
    return str(value.numerator) if value.denominator == 1 else str(value)


class Poly:
    """Sparse exact multivariate Laurent polynomial with rational coefficients."""
    def __init__(self, terms=None, n=1):
        self.n = n
        self.terms = {tuple(k): Q(v) for k, v in (terms or {}).items() if v}
        require(all(len(k) == n for k in self.terms), "Polynomial arity mismatch")

    @classmethod
    def constant(cls, value, n=1):
        return cls({(0,) * n: Q(value)}, n)

    @classmethod
    def variable(cls, index=0, n=1, power=1):
        key = [0] * n
        key[index] = power
        return cls({tuple(key): 1}, n)

    def coerce(self, other):
        if isinstance(other, Poly):
            exact_equal(other.n, self.n, "Polynomial arity")
            return other
        return Poly.constant(other, self.n)

    def __add__(self, other):
        other = self.coerce(other)
        terms = self.terms.copy()
        for key, value in other.terms.items():
            terms[key] = terms.get(key, Q(0)) + value
        return Poly(terms, self.n)

    __radd__ = __add__

    def __neg__(self):
        return Poly({k: -v for k, v in self.terms.items()}, self.n)

    def __sub__(self, other):
        return self + -self.coerce(other)

    def __rsub__(self, other):
        return self.coerce(other) + -self

    def __mul__(self, other):
        other = self.coerce(other)
        terms = defaultdict(Q)
        for a, x in self.terms.items():
            for b, y in other.terms.items():
                terms[tuple(u + v for u, v in zip(a, b))] += x * y
        return Poly(terms, self.n)

    __rmul__ = __mul__

    def __truediv__(self, scalar):
        return self * (Q(1) / scalar)

    def __pow__(self, power):
        require(isinstance(power, int) and power >= 0, "Invalid polynomial power")
        result = Poly.constant(1, self.n)
        for _ in range(power):
            result = result * self
        return result

    def evaluate(self, values):
        exact_equal(len(values), self.n, "Evaluation arity")
        return sum((value * product(Q(x) ** k for x, k in zip(values, powers))
                    for powers, value in self.terms.items()), Q(0))

    def encoded(self):
        return {",".join(map(str, k)): rational(v) for k, v in sorted(self.terms.items())}


def product(values):
    result = Q(1)
    for value in values:
        result *= value
    return result


def edge(a, b):
    return tuple(sorted((a, b)))


def atoms(M):
    result = []
    for kind, distance in (("X", 1), ("Y", 2)):
        result.extend((kind, (edge(i, (i + distance) % M),)) for i in range(M))
    for i, j in combinations(range(M), 2):
        a, b, c, d = i, (i + 1) % M, j, (j + 1) % M
        if len({a, b, c, d}) == 4:
            result.append(("Z", tuple(sorted((edge(a, c), edge(b, d))))))
            result.append(("Z", tuple(sorted((edge(a, d), edge(b, c))))))
    require(len(set(result)) == len(result), f"Duplicate atom at M={M}")
    return result


def compatible(chords):
    points = [p for chord in chords for p in chord]
    return len(set(points)) == len(points)


def local_checks():
    rows = []
    for M in (8, 10, 12, 16, 20, 30, 40):
        patterns = atoms(M)
        exact_equal(Counter(t for t, _ in patterns),
                    Counter(X=M, Y=M, Z=M * (M - 3)), f"Atom counts M={M}")
        supports = [frozenset(v for e in es for v in e) for _, es in patterns]
        overlaps = Counter()
        by_chord = defaultdict(list)
        for i, (kind, chords) in enumerate(patterns):
            for chord in chords:
                by_chord[chord].append(i)
            for j, (other_kind, _) in enumerate(patterns):
                if supports[i] & supports[j]:
                    overlaps[kind + other_kind] += 1
        expected_overlap = {
            "XX": 3*M, "YY": 3*M, "XY": 4*M, "YX": 4*M,
            "XZ": M*(6*M-20), "ZX": M*(6*M-20),
            "YZ": M*(8*M-30), "ZY": M*(8*M-30),
            "ZZ": 12*M**3-98*M**2+210*M,
        }
        exact_equal(dict(overlaps), expected_overlap, f"Ordered support overlaps M={M}")
        # Sets of atom indices avoid accidental multiplicity if two atoms share
        # more than one chord. They are distinct atoms, unlike ordered overlaps.
        compatible_atom_pairs = set()
        for ids in by_chord.values():
            for i, j in combinations(ids, 2):
                if compatible(set(patterns[i][1]) | set(patterns[j][1])):
                    compatible_atom_pairs.add((min(i, j), max(i, j)))
        pair_counts = Counter("".join(sorted((patterns[i][0], patterns[j][0])))
                              for i, j in compatible_atom_pairs)
        exact_equal(pair_counts, Counter(XZ=M, YZ=3*M, ZZ=M*(M-5)),
                    f"Unordered compatible shared-chord pairs M={M}")
        singles = {es[0]: kind for kind, es in patterns if kind != "Z"}
        triples = Counter()
        for kind, chords in patterns:
            if kind == "Z" and all(e in singles for e in chords):
                triples["".join(sorted(singles[e] for e in chords)) + "Z"] += 1
        exact_equal(triples, Counter(YYZ=M), f"Two-chord connected triples M={M}")
        # Independently enumerate every compatible three-atom connected set on
        # the support of a Z atom; there are no omitted two-chord polymers.
        exhaustive_two_chord = Counter()
        for kind, chords in patterns:
            if kind != "Z":
                continue
            candidates = [i for i, (_, es) in enumerate(patterns)
                          if set(es).issubset(set(chords))]
            for count in range(2, len(candidates) + 1):
                for ids in combinations(candidates, count):
                    selected = [patterns[i] for i in ids]
                    if not any(t == "Z" for t, _ in selected):
                        continue
                    exhaustive_two_chord["".join(sorted(t for t, _ in selected))] += 1
        exact_equal(exhaustive_two_chord, Counter(XZ=M, YZ=3*M, YYZ=M),
                    f"Exhaustive two-chord polymers M={M}")
        rows.append({"M": M, "atoms": dict(Counter(t for t, _ in patterns)),
                     "ordered_support_overlaps": dict(sorted(overlaps.items())),
                     "unordered_compatible_pairs": dict(sorted(pair_counts.items())),
                     "two_chord_non_elementary_polymers": dict(sorted(exhaustive_two_chord.items()))})
    return rows


def matchings(vertices):
    if not vertices:
        yield ()
        return
    first = vertices[0]
    for i in range(1, len(vertices)):
        for rest in matchings(vertices[1:i] + vertices[i+1:]):
            yield ((first, vertices[i]),) + rest


def interval_checks():
    """Use only within-block adjacency, never adjacency across a gap."""
    rows = []
    for left in range(4):
        blocks = [tuple(range(left)), tuple(range(left, 6))]
        adjacency = {edge(a, b) for block in blocks for a, b in zip(block, block[1:])}
        distance_two = {edge(block[i], block[i+2]) for block in blocks
                        for i in range(len(block)-2)}
        count = 0
        pattern_counts = Counter()
        for matching in matchings(tuple(range(6))):
            chord_set = set(matching)
            kinds = set()
            if chord_set & adjacency:
                kinds.add("X")
            if chord_set & distance_two:
                kinds.add("Y")
            for (a, b), (c, d) in combinations(matching, 2):
                if ((edge(a, c) in adjacency and edge(b, d) in adjacency) or
                    (edge(a, d) in adjacency and edge(b, c) in adjacency)):
                    kinds.add("Z")
            require(kinds, f"Three-chord interval counterexample: {blocks}, {matching}")
            pattern_counts["".join(sorted(kinds))] += 1
            count += 1
        exact_equal(count, 15, f"Matching coverage for {left}+{6-left}")
        rows.append({"interval_sizes": [left, 6-left], "matchings": count,
                     "defect_type_sets": dict(sorted(pattern_counts.items())),
                     "zero_defect_matchings": 0})
    return rows


def graph_checks():
    rows = []
    for n in range(2, 6):
        pairs = list(combinations(range(n), 2))
        edge_index = {p: i for i, p in enumerate(pairs)}
        perms = list(permutations(range(n)))
        maps = [tuple(edge_index[edge(p[u], p[v])] for u, v in pairs) for p in perms]

        def relabel(mask, mapping):
            return sum(1 << mapping[i] for i in range(len(pairs)) if mask >> i & 1)

        canonical = [min(relabel(mask, mapping) for mapping in maps)
                     for mask in range(1 << len(pairs))]

        def connected(mask):
            seen = {0}
            while True:
                previous = len(seen)
                for i, (u, v) in enumerate(pairs):
                    if mask >> i & 1 and (u in seen or v in seen):
                        seen.update((u, v))
                if len(seen) == previous:
                    return len(seen) == n

        classes = sorted({canonical[m] for m in range(1 << len(pairs)) if connected(m)})
        diagram_classes = set()
        diagram_count = 0
        for matching in matchings(tuple(range(2*n))):
            mask = 0
            for i, (u, v) in enumerate(pairs):
                a, b = matching[u]
                c, d = matching[v]
                if (a < c < b) != (a < d < b):
                    mask |= 1 << i
            diagram_classes.add(canonical[mask])
            diagram_count += 1
        require(set(classes).issubset(diagram_classes), f"Non-circle class at order {n}")
        class_rows = []
        rooted_total = 0
        rooted_order_histogram = Counter()
        for representative in classes:
            autos = [p for p, mapping in zip(perms, maps)
                     if relabel(representative, mapping) == representative]
            todo = set(range(n))
            orbits = []
            while todo:
                root = min(todo)
                orbit = {p[root] for p in autos}
                orbits.append(sorted(orbit))
                todo -= orbit
            rooted_total += len(orbits)
            rooted_orders = []
            for orbit in orbits:
                root = min(orbit)
                stabilizer_order = sum(p[root] == root for p in autos)
                exact_equal(stabilizer_order*len(orbit), len(autos),
                            f"Orbit-stabilizer n={n}, mask={representative}, root={root}")
                rooted_orders.append(stabilizer_order)
                rooted_order_histogram[stabilizer_order] += 1
            class_rows.append({"edge_mask": representative,
                               "edges": [list(e) for i, e in enumerate(pairs) if representative >> i & 1],
                               "automorphisms": len(autos), "vertex_orbits": orbits,
                               "root_fixing_automorphism_orders": rooted_orders})
        exact_equal(len(classes), {2: 1, 3: 2, 4: 6, 5: 21}[n], f"Connected classes n={n}")
        exact_equal(diagram_count, {2: 3, 3: 15, 4: 105, 5: 945}[n], f"Diagram coverage n={n}")
        rows.append({"order": n, "all_labeled_graphs_checked": 1 << len(pairs),
                     "all_indexed_matchings_checked": diagram_count,
                     "connected_classes": len(classes), "all_connected_classes_are_circle": True,
                     "rooted_connected_classes": rooted_total,
                     "rooted_automorphism_order_histogram": dict(sorted(rooted_order_histogram.items())),
                     "classes": class_rows})
    return rows


def poisson_moment(power, parameter=Q(3, 2)):
    # Touchard polynomial via an independently generated Stirling recurrence.
    row = [Q(1)]
    for degree in range(1, power + 1):
        next_row = [Q(0)] * (degree + 1)
        for j in range(1, degree + 1):
            next_row[j] = (row[j-1] if j-1 < len(row) else 0) + (j*row[j] if j < len(row) else 0)
        row = next_row
    return sum((coefficient * parameter**j for j, coefficient in enumerate(row)), Q(0))


def poisson_mean(poly, parameter=Q(3, 2)):
    exact_equal(poly.n, 1, "Poisson polynomial arity")
    require(all(k[0] >= 0 for k in poly.terms), "Poisson polynomial has negative powers")
    return sum((v * poisson_moment(k[0], parameter) for k, v in poly.terms.items()), Q(0))


def bounded_weight_checks(graph_rows, ordinary_claims):
    """Bounded reciprocal weights only; no positive automorphism moments."""
    histograms = {row["order"]-2: row["rooted_automorphism_order_histogram"]
                  for row in graph_rows if row["order"] <= 4}
    claims = {}
    for excess, histogram in histograms.items():
        for order, count in histogram.items():
            claims[f"rooted_order_count:{excess},{order}"] = rational(count)
    exact_equal(set(histograms[0]), {1}, "Identity-branch rooted orders")
    exact_equal(set(histograms[1]), {1, 2}, "Excess-one rooted orders")
    exact_equal(set(histograms[2]), {1, 2, 6}, "Excess-two rooted orders")
    rho, sigma = (Poly.variable(i, 2) for i in range(2))
    b1 = histograms[1][1] + histograms[1][2]*rho
    b2 = histograms[2][1] + histograms[2][2]*rho + histograms[2][6]*sigma
    a = Poly.variable()
    A1, _ = factorial_log_coefficients(a, a)
    # Derive the shift by Poisson summation, independently of its compact formula.
    shift = poisson_mean(A1, b1/2) + b2/4
    exact_equal(shift.encoded(), ((b2+b1-b1*b1)/4).encoded(), "Bounded weighted transfer shift")
    alpha = Q(ordinary_claims["prime_first_relative_n"])
    connected = alpha + shift
    all_graphs = connected + Q(1, 2)
    relative = connected-Q(ordinary_claims["connected_first"])
    exact_equal(relative.encoded(),
                (all_graphs-Q(ordinary_claims["all_first"])).encoded(),
                "Connected/all reciprocal-transform coefficient agreement")
    exponent = b1/2-Q(3, 2)
    for name, poly in (("bounded_b1", b1), ("bounded_b2", b2),
                       ("bounded_shift", shift), ("bounded_transform_relative", relative),
                       ("bounded_transform_exponent", exponent)):
        for powers, value in poly.encoded().items():
            claims[f"{name}:{powers}"] = value
    for label, values in (("labeled", (Q(1, 2), Q(1, 6))), ("asymmetric", (0, 0))):
        claims[label+"_b1"] = rational(b1.evaluate(values))
        claims[label+"_b2"] = rational(b2.evaluate(values))
        claims[label+"_connected_first"] = rational(connected.evaluate(values))
        claims[label+"_all_first"] = rational(all_graphs.evaluate(values))
        claims[label+"_relative_first"] = rational(relative.evaluate(values))
        claims[label+"_amplitude_exponent"] = rational(-3+b1.evaluate(values)/2)
    exact_equal(connected.evaluate((1, 1)), Q(ordinary_claims["connected_first"]),
                "Unweighted connected specialization")
    exact_equal(all_graphs.evaluate((1, 1)), Q(ordinary_claims["all_first"]),
                "Unweighted all-graph specialization")
    return claims, {"variables": ["rho=2^(-t)", "sigma=6^(-t)"],
                    "range": "t in [0,infinity], with t=infinity as the rigidity indicator",
                    "b1": b1.encoded(), "b2": b2.encoded(),
                    "connected_first": connected.encoded(), "all_first": all_graphs.encoded(),
                    "relative_transform_first": relative.encoded(),
                    "relative_transform_exponent": exponent.encoded(),
                    "scope": "Exact finite histograms and rational identities; not a uniform-in-t remainder proof"}


def factorial_log_coefficients(k, occupied):
    L1 = k + k*k/2 - occupied*k - occupied*(occupied-1)/2
    L2 = (k*k/2 + k*(4*k*k-1)/24
          - (occupied*k*k + k*occupied*(occupied-1)
             + occupied*(occupied-1)*(2*occupied-1)/6)/2)
    return L1, L2


def direct_factor_series(k, occupied):
    """Expand exact product after removing 2^-k n^(occupied-k).

    The normalized product is (1-k*t)^-1 times product_(j<k)
    (1-(j+1/2)*t)^-1 times product_(j<occupied)(1-(k+j)*t).
    """
    coefficients = [Q(1), Q(0), Q(0)]
    factors = [[Q(1), Q(k), Q(k*k)]]
    factors += [[Q(1), Q(2*j+1, 2), Q((2*j+1)**2, 4)] for j in range(k)]
    factors += [[Q(1), Q(-(k+j)), Q(0)] for j in range(occupied)]
    for factor in factors:
        coefficients = [sum((coefficients[j]*factor[i-j] for j in range(i+1)), Q(0))
                        for i in range(3)]
    return coefficients


def algebra_checks(rooted):
    claims = {}
    x, y, z = (Poly.variable(i, 3) for i in range(3))
    W1 = -3*z + x*z + 3*y*z + y*y*z + z*z
    B1 = 3*x*x + 3*y*y + 8*x*y + 12*x*z + 16*y*z + 12*z*z
    matching_weight = (x+y+2*z)**2 + x+y+4*z
    F = W1 - B1/2 + matching_weight
    for key, value in F.encoded().items():
        claims["local_F:"+key] = value
    zero_M = F.evaluate((-1, -1, -1))
    claims["local_zero_relative_M"] = rational(zero_M)
    alpha = zero_M/2
    claims["prime_first_relative_n"] = rational(alpha)
    for excess, count in enumerate(rooted):
        claims[f"b{excess}"] = rational(count)

    # Independently check the formula against finite products, including ell=0.
    product_rows = []
    for k in range(9):
        for occupied in range(k+1):
            L1, L2 = factorial_log_coefficients(Q(k), Q(occupied))
            series = direct_factor_series(k, occupied)
            exact_equal(series, [Q(1), L1, L2+L1*L1/2], f"Factor series k={k}, ell={occupied}")
            product_rows.append({"k": k, "ell": occupied, "series": list(map(rational, series))})
    a = Poly.variable()
    A1, A_log2 = factorial_log_coefficients(a, a)
    A2 = A_log2 + A1*A1/2
    B1p, _ = factorial_log_coefficients(a+2, a+1)
    means = {"A1": poisson_mean(A1), "A2": poisson_mean(A2),
             "B1": poisson_mean(B1p), "A1_plus_a": poisson_mean(A1+a)}
    for name, value in means.items():
        claims["poisson_mean_"+name] = rational(value)
    connected_shift = means["A1"] + Q(rooted[2], 4)
    all_shift = connected_shift + Q(1, 2)
    connected_first, all_first = alpha+connected_shift, alpha+all_shift
    claims.update({"connected_first_shift": rational(connected_shift),
                   "all_first_shift": rational(all_shift),
                   "connected_first": rational(connected_first),
                   "all_first": rational(all_first)})
    # Conditional on an independent prime coefficient beta; no value is supplied.
    c_second_alpha = means["A1_plus_a"] + Q(rooted[2], 4)
    c_second_constant = (means["A2"] + Q(rooted[2], 4)*means["B1"]
                         + Q(rooted[2]**2, 32) + Q(rooted[3], 8))
    g_second_alpha = c_second_alpha + Q(1, 2)
    g_second_constant = c_second_constant + connected_shift/2 + Q(5, 4)
    claims.update({"conditional_c_second_alpha_multiplier": rational(c_second_alpha),
                   "conditional_c_second_constant": rational(c_second_constant),
                   "conditional_g_second_alpha_multiplier": rational(g_second_alpha),
                   "conditional_g_second_constant": rational(g_second_constant),
                   "conditional_c_second_after_alpha_minus5": rational(c_second_constant+alpha*c_second_alpha),
                   "conditional_g_second_after_alpha_minus5": rational(g_second_constant+alpha*g_second_alpha)})
    disconnected_second = Q(5, 4)+connected_first/2-all_first/2
    claims["connectivity_ratio_second"] = rational(-disconnected_second)
    claims["connectivity_ratio_first"] = "-1/2"

    # Formal Laurent-polynomial residual, with A=log(2u), C=(3+log 2)/2.
    # log(u)+B=A+C, so the constant and 1/u residuals are checked exactly.
    A, C, beta = (Poly.variable(i, 3) for i in range(3))
    Ai = Poly.variable(0, 3, power=-1)
    d0 = 1+C*Ai
    d1 = (Q(13, 24)-beta)*Ai-C*C*Ai**3/2
    residual0 = A*d0-A-C
    residual1 = A*d1+d0*d0/2-d0-Q(1, 24)+beta
    exact_equal(residual0.encoded(), {}, "Inverse residual constant term")
    exact_equal(residual1.encoded(), {}, "Inverse residual 1/u term")
    claims["inverse_universal_numerator"] = "13/24"
    claims["inverse_connected_numerator"] = rational(Q(13, 24)-connected_first)
    claims["inverse_all_numerator"] = rational(Q(13, 24)-all_first)
    claims["inverse_center_gap_multiplier"] = rational(all_first-connected_first)
    return claims, {"local_F": F.encoded(), "A1": A1.encoded(), "A2": A2.encoded(),
                    "B1": B1p.encoded(), "factor_product_checks": product_rows,
                    "inverse_constant_residual": residual0.encoded(),
                    "inverse_first_residual": residual1.encoded(),
                    "inverse_d0": d0.encoded(), "inverse_d1": d1.encoded()}


def load_claims(path):
    """Descriptor-pinned, nonblocking regular-file read; never follow symlinks."""
    raw = Path(path)
    require(".." not in raw.parts, "Claims parent traversal is refused")
    path = Path(os.path.abspath(raw))
    directory_fd = os.open(path.anchor, os.O_RDONLY | os.O_DIRECTORY)
    fd = None
    try:
        try:
            for part in path.parent.parts[1:]:
                next_fd = os.open(part, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW,
                                  dir_fd=directory_fd)
                os.close(directory_fd)
                directory_fd = next_fd
            fd = os.open(path.name, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK,
                         dir_fd=directory_fd)
        except OSError as exc:
            raise VerificationError(f"Claims input cannot be opened safely: {exc}") from exc
        info = os.fstat(fd)
        require(stat.S_ISREG(info.st_mode), "Claims input must be a regular file")
        require(info.st_size <= 1024*1024, "Claims input exceeds one MiB")
        with os.fdopen(fd, "rb") as source:
            fd = None
            data = source.read(1024*1024+1)
            require(len(data) <= 1024*1024, "Claims input exceeds one MiB")
            claims = json.loads(data.decode("utf-8"))
    finally:
        if fd is not None:
            os.close(fd)
        os.close(directory_fd)
    require(isinstance(claims, dict), "Claims must be a JSON object")
    require(all(isinstance(k, str) and isinstance(v, str) for k, v in claims.items()),
            "Every claim must have a string key and exact rational string value")
    for key, value in claims.items():
        require(rational(Q(value)) == value, f"Noncanonical rational claim: {key}")
    return claims


def write_new_json(destination, data):
    """Write a new file only inside results/, with exclusive no-follow opens.

    All parent directories must already exist. Each is opened relative to an
    already-open directory descriptor with O_NOFOLLOW, blocking symlink races.
    Existing files, including inputs, are never overwritten.
    """
    raw = Path(destination)
    require(".." not in raw.parts, "Parent traversal is refused")
    destination = Path(os.path.abspath(raw))
    try:
        relative = destination.relative_to(RESULTS)
    except ValueError as exc:
        raise VerificationError(f"Output must be strictly inside {RESULTS}") from exc
    require(bool(relative.parts) and relative.name.endswith(".json"), "Output must be a new .json file")
    require(all(part not in ("", ".", "..") for part in relative.parts), "Invalid output path")
    # Walk from /, opening every component and holding only the next descriptor.
    parent = destination.parent
    directory_fd = os.open(parent.anchor, os.O_RDONLY | os.O_DIRECTORY)
    try:
        for part in parent.parts[1:]:
            next_fd = os.open(part, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW, dir_fd=directory_fd)
            os.close(directory_fd)
            directory_fd = next_fd
        payload = (json.dumps(data, indent=2, sort_keys=True) + "\n").encode("utf-8")
        fd = os.open(destination.name, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW,
                     0o600, dir_fd=directory_fd)
        try:
            with os.fdopen(fd, "wb") as target:
                fd = None
                target.write(payload)
                target.flush()
                os.fsync(target.fileno())
        finally:
            if fd is not None:
                os.close(fd)
    finally:
        os.close(directory_fd)


def run(claims):
    local = local_checks()
    interval = interval_checks()
    graphs = graph_checks()
    actual, algebra = algebra_checks([row["rooted_connected_classes"] for row in graphs])
    weighted_claims, weighted = bounded_weight_checks(graphs, actual)
    actual.update(weighted_claims)
    exact_equal(set(claims), set(actual), "Claim keys")
    for key in sorted(actual):
        exact_equal(actual[key], claims[key], f"Claim {key}")
    return {"schema": "report152-exact-companion-v2", "status": "passed",
            "arithmetic": "exact Python integers and fractions.Fraction; no third-party packages",
            "scope": "Finite combinatorics and exact coefficient identities only; not an analytic uniformity proof",
            "second_order_status": "Transfer identities are conditional on an independent prime beta; no beta value supplied",
            "claims": actual, "local_atom_cluster_checks": local,
            "three_chord_interval_checks": interval, "rooted_graph_checks": graphs,
            "rational_algebra_checks": algebra, "bounded_automorphism_weight_checks": weighted}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--claims", type=Path, default=ROOT / "claims.json")
    parser.add_argument("--output", type=Path, help="New .json path inside companion/results; never overwritten")
    args = parser.parse_args(argv)
    try:
        data = run(load_claims(args.claims))
        if args.output:
            write_new_json(args.output, data)
        print(json.dumps(data, indent=2, sort_keys=True))
        return 0
    except (VerificationError, ValueError, OSError) as exc:
        print(f"Verification failed: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
