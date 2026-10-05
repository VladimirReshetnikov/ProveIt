#!/usr/bin/env python3
"""Reproduce the finite checks, numerical tables, and publication figures.

Run from any directory: python path/to/code/reproduce.py
Required packages: sympy, mpmath, numpy, matplotlib.

Integer and rational combinatorial checks are exact.  Asymptotic ratios,
transcendental constants, tail thresholds, and plots use floating point;
they provide numerical illustrations, not proofs of limiting assertions.
"""

from __future__ import annotations

import csv
import io
import json
import math
import os
import platform
import re
import tempfile
from collections import defaultdict
from fractions import Fraction
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import mpmath as mp
import numpy as np
import sympy as sp
from sympy.polys.matrices import DomainMatrix


BASE = Path(__file__).resolve().parents[1]
DATA = BASE / "data"
FIGURES = BASE / "figures"
DATA.mkdir(parents=True, exist_ok=True)
FIGURES.mkdir(parents=True, exist_ok=True)
mp.mp.dps = 70
ZETA2 = math.pi**2 / 6
MOMENT_LIMITS = {
    2: float(mp.zeta(3) / (4 * mp.pi**2)),
    4: float(mp.zeta(5) / (600 * mp.pi**2)),
}
FIRST_MOMENT_CONSTANT = float((mp.euler - mp.log(mp.pi) - mp.mpf(5) / 6
                               + mp.diff(mp.zeta, 2) / mp.zeta(2)) / mp.pi)
COUNTS: dict[str, int] = {}


def write_csv(filename: str, rows: list[dict]) -> None:
    if not rows:
        raise ValueError("Cannot infer fields from an empty table")
    with (DATA / filename).open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)


def weighted_row(k: int, nmax: int, u, domain):
    """Compute A and inclusion--exclusion T directly, without factorization."""
    a = [[domain.zero] * (nmax + 1) for _ in range(k + 1)]
    for j in range(k + 1):
        a[j][0] = domain.one
    for j in range(1, k + 1):
        coefficients = [0] + [math.comb(h + j - 1, j - 1)
                              for h in range(1, nmax + 1)]
        for n in range(1, nmax + 1):
            a[j][n] = u * sum((coefficients[h] * a[j][n - h]
                              for h in range(1, n + 1)), domain.zero)
    return [sum(((-1) ** (k - j) * math.comb(k, j) * a[j][n]
                 for j in range(k + 1)), domain.zero)
            for n in range(nmax + 1)]


def determinant_product(k: int, s: int, u):
    d = k * (k + 1) // 2
    c = math.comb(k + 1, 3)
    result = u ** (d + 2 * c) * (1 + u) ** (k * (s - 1) + 2 * c)
    for j in range(1, k + 1):
        result *= math.comb(k, j) ** j
    for i in range(1, k):
        for j in range(i + 1, k + 1):
            g = math.gcd(i, j)
            q = (j - i) // g
            result *= ((1 + u) ** q - u**q) ** (2 * g)
    return result


def check_determinants() -> None:
    symbol = sp.Symbol("u")
    polynomial_domain = sp.QQ.poly_ring(symbol)
    cases = [
        ("symbolic", "u", polynomial_domain.gens[0], polynomial_domain)
    ]
    rational_values = [Fraction(-2), Fraction(-1), Fraction(-1, 2),
                       Fraction(-1, 3), Fraction(0), Fraction(1, 2),
                       Fraction(1), Fraction(2)]
    cases += [("rational", str(value), sp.QQ(value.numerator, value.denominator),
               sp.QQ) for value in rational_values]
    records = []
    for kind, label, u, domain in cases:
        for k in range(1, 5):
            d = k * (k + 1) // 2
            row = weighted_row(k, 3 + 2 * (d - 1), u, domain)
            for s in range(1, 4):
                matrix = DomainMatrix([[row[s + p + q] for q in range(d)]
                                       for p in range(d)], (d, d), domain)
                actual = matrix.det()
                expected = determinant_product(k, s, u)
                assert actual == expected, (kind, label, k, s)
                record = {"kind": kind, "u": label, "k": k, "s": s,
                          "matrix_size": d, "passed": True,
                          "degree": actual.degree() if kind == "symbolic" else "",
                          "determinant": str(domain.to_sympy(actual))}
                records.append(record)

    # The q=3 nonreal roots first appear for k=4.  Arithmetic here is in
    # QQ(sqrt(3)*I), so a zero determinant is an exact algebraic check.
    domain = sp.QQ.algebraic_field(sp.sqrt(3) * sp.I)
    u = domain.from_sympy((-1 + sp.I / sp.sqrt(3)) / 2)
    k, d = 4, 10
    row = weighted_row(k, 3 + 2 * (d - 1), u, domain)
    for s in range(1, 4):
        actual = DomainMatrix([[row[s + p + q] for q in range(d)]
                               for p in range(d)], (d, d), domain).det()
        expected = determinant_product(k, s, u)
        assert actual == expected == domain.zero
        records.append({"kind": "algebraic", "u": "(-1+I/sqrt(3))/2",
                        "k": k, "s": s, "matrix_size": d, "passed": True,
                        "degree": "", "determinant": "0"})

    write_csv("determinant_checks.csv", records)
    for kind in ["symbolic", "rational", "algebraic"]:
        COUNTS[f"{kind}_determinant_checks"] = sum(r["kind"] == kind for r in records)


def phi_sieve(n: int) -> list[int]:
    values = list(range(n + 1))
    if n:
        values[1] = 1
    for p in range(2, n + 1):
        if values[p] == p:
            for r in range(p, n + 1, p):
                values[r] -= values[r] // p
    return values


def pair_aggregates(requested: set[int]) -> dict[int, dict]:
    """Aggregate weights 2*g by q=(j-i)/g using direct pair enumeration."""
    maximum = max(requested)
    w = [0] * maximum
    gcd_sum = 0
    result = {}
    for j in range(2, maximum + 1):
        for i in range(1, j):
            g = math.gcd(i, j)
            gcd_sum += g
            w[(j - i) // g] += 2 * g
        if j in requested:
            weights = w[:j]
            multiplicity = [0] * j
            for m in range(2, j):
                multiplicity[m] = sum(weights[m::m])
            degree = sum(weights[q] * (q - 1) for q in range(1, j))
            result[j] = {"k": j, "W": weights, "M": multiplicity,
                         "G": gcd_sum, "N": degree}
    return result


def farey_interior(order: int):
    """Yield all reduced a/b with 0<a<b<=order, in increasing order."""
    a, b, c, d = 0, 1, 1, order
    while c < d:
        yield c, d
        quotient = (order + b) // d
        a, b, c, d = c, d, quotient * c - a, quotient * d - b


def exact_discrepancy(aggregate: dict) -> dict:
    k, multiplicity, degree = aggregate["k"], aggregate["M"], aggregate["N"]
    total = 0
    best_numerator, best_denominator = 0, 1
    maximizing_angle, side = Fraction(0), "left"
    for a, b in farey_interior(k - 1):
        mass = multiplicity[b]
        for cumulative, label in [(total, "left"), (total + mass, "right")]:
            numerator = abs(cumulative * b - a * degree)
            if numerator * best_denominator > best_numerator * b:
                best_numerator, best_denominator = numerator, b
                maximizing_angle, side = Fraction(a, b), label
        total += mass
    assert total == degree
    discrepancy = Fraction(best_numerator, degree * best_denominator)
    lower_bound = Fraction(multiplicity[2], 2 * degree)
    return {"k": k, "degree_N": degree,
            "D_exact": str(discrepancy), "D": float(discrepancy),
            "D_times_k_over_log_k": float(discrepancy) * k / math.log(k),
            "maximizing_angle": str(maximizing_angle), "side": side,
            "half_order_2_atom_exact": str(lower_bound),
            "half_order_2_atom": float(lower_bound)}


def merged_product_roots(aggregate: dict) -> dict[Fraction, int]:
    """Independent root merging: enumerate every l/q from product factors."""
    merged = defaultdict(int)
    for q, weight in enumerate(aggregate["W"]):
        if q > 1:
            for ell in range(1, q):
                merged[Fraction(ell, q)] += weight
    return dict(merged)


def check_degrees_and_merging(aggregates: dict[int, dict], phi: list[int]) -> None:
    degree_rows = []
    for k, aggregate in sorted(aggregates.items()):
        degree = aggregate["N"]
        gcd_degree = 2 * (math.comb(k + 1, 3) - aggregate["G"])
        primitive_degree = sum(phi[m] * aggregate["M"][m] for m in range(2, k))
        assert degree == gcd_degree == primitive_degree
        degree_rows.append({"k": k, "G": aggregate["G"], "N": degree,
                            "two_times_c_minus_G": gcd_degree,
                            "sum_phi_times_M": primitive_degree, "passed": True})
    COUNTS["degree_and_primitive_multiplicity_checks"] = len(degree_rows)
    write_csv("degree_checks.csv", degree_rows)

    for k in range(3, 21):
        aggregate = aggregates[k]
        roots = merged_product_roots(aggregate)
        expected = {Fraction(a, b): aggregate["M"][b]
                    for a, b in farey_interior(k - 1)}
        assert roots == expected
        assert sum(roots.values()) == aggregate["N"]
        cumulative = 0
        discrepancy = Fraction(0)
        for angle, weight in sorted(roots.items()):
            discrepancy = max(discrepancy,
                              abs(Fraction(cumulative, aggregate["N"]) - angle),
                              abs(Fraction(cumulative + weight, aggregate["N"]) - angle))
            cumulative += weight
        assert str(discrepancy) == exact_discrepancy(aggregate)["D_exact"]
    COUNTS["independent_root_merging_and_CDF_checks"] = 18


def cotangent_checks() -> None:
    records = []
    for q in range(2, 41):
        values = [mp.cot(mp.pi * ell / q) for ell in range(1, q)]
        expected2 = mp.mpf((q - 1) * (q - 2)) / 3
        expected4 = mp.mpf((q - 1) * (q - 2) * (q * q + 3 * q - 13)) / 45
        for p, expected in [(2, expected2), (4, expected4)]:
            actual = sum(v**p for v in values)
            error = abs(actual - expected) / max(mp.mpf(1), abs(expected))
            assert error < mp.mpf("1e-60")
            records.append({"q": q, "p": p, "relative_or_absolute_error":
                            mp.nstr(error, 10), "tolerance": "1e-60", "passed": True})
    COUNTS["high_precision_cotangent_identity_checks"] = len(records)
    write_csv("cotangent_identity_checks.csv", records)


def scaled_moment(aggregate: dict, p: int) -> Fraction:
    k, w, degree = aggregate["k"], aggregate["W"], aggregate["N"]
    if p == 2:
        return Fraction(sum(w[q] * (q - 1) * (q - 2) for q in range(1, k)),
                        12 * degree * k)
    if p == 4:
        return Fraction(sum(w[q] * (q - 1) * (q - 2) * (q * q + 3 * q - 13)
                            for q in range(1, k)), 720 * degree * k**3)
    raise ValueError("The exact implementation here covers p=2 and p=4")


def psi(m: int) -> Fraction:
    result = Fraction(m)
    for prime in sp.factorint(m):
        result *= Fraction(prime + 1, prime)
    return result


def first_moment_table(aggregates: dict[int, dict], table_ks: list[int]) -> None:
    """Numerical first moments; cotangent sums use NumPy extended precision."""
    maximum = max(table_ks)
    pi_extended = np.longdouble(str(mp.pi))
    sums = np.zeros(maximum, dtype=np.longdouble)
    for q in range(2, maximum):
        ell = np.arange(1, (q - 1) // 2 + 1, dtype=np.longdouble)
        # Opposite roots each contribute half a cotangent; their pair
        # contributes one.  A possible central root contributes zero.
        sums[q] = np.sum(1 / np.tan(pi_extended * ell / q), dtype=np.longdouble)
    rows = []
    for k in table_ks:
        weights = np.asarray(aggregates[k]["W"], dtype=np.longdouble)
        value = np.dot(weights, sums[:k]) / aggregates[k]["N"]
        residual = float(value) - math.log(k) / math.pi
        rows.append({"k": k, "first_absolute_moment": float(value),
                     "M1_minus_log_k_over_pi": residual,
                     "predicted_constant": FIRST_MOMENT_CONSTANT,
                     "residual_after_constant": residual - FIRST_MOMENT_CONSTANT,
                     "error_times_k_over_log_k_squared":
                     (residual - FIRST_MOMENT_CONSTANT) * k / math.log(k)**2})
    for k in [12, 40]:
        direct = sum(weight * abs(mp.cot(mp.pi * angle.numerator / angle.denominator) / 2)
                     for angle, weight in merged_product_roots(aggregates[k]).items())
        direct /= aggregates[k]["N"]
        weights = np.asarray(aggregates[k]["W"], dtype=np.longdouble)
        value = np.dot(weights, sums[:k]) / aggregates[k]["N"]
        assert abs(float(direct) - float(value)) < 1e-13
    COUNTS["independent_high_precision_first_moment_checks"] = 2
    write_csv("first_absolute_moment.csv", rows)


def tail_counts(aggregate: dict, xvalues: np.ndarray) -> np.ndarray:
    """Exact integer masses with float thresholds |Y|>k*x.

    Values at a numerically exact boundary use the strict inequality via
    nextafter. Plotting and verification grids deliberately avoid atoms.
    """
    k = aggregate["k"]
    q = np.arange(1, k, dtype=np.float64)
    weights = np.asarray(aggregate["W"][1:], dtype=np.int64)
    result = np.empty(len(xvalues), dtype=np.int64)
    for index, x in enumerate(xvalues):
        cutoff = math.atan(1 / (2 * k * float(x))) / math.pi
        admissible = np.floor(np.nextafter(q * cutoff, -np.inf)).astype(np.int64)
        result[index] = 2 * np.dot(weights, admissible)
    return result


def edge_profile(xvalues: np.ndarray) -> np.ndarray:
    smallest = float(np.min(xvalues))
    if smallest <= 0:
        raise ValueError("The edge profile is evaluated only for x>0")
    limit = math.floor(1 / (2 * math.pi * smallest))
    sigma = np.zeros(limit + 1)
    for divisor in range(1, limit + 1):
        sigma[divisor::divisor] += 1 / divisor
    indices = np.arange(1, limit + 1)
    return np.asarray([6 / ZETA2 * np.dot(sigma[1:],
                                        np.maximum(1 - 2 * math.pi * indices * x, 0)**2)
                       for x in xvalues])


def check_tail_counts(aggregates: dict[int, dict]) -> None:
    records = []
    xvalues = np.asarray([0.011, 0.037, 0.071, 0.113, 0.151])
    for k in [8, 12, 40, 150]:
        aggregate = aggregates[k]
        direct = merged_product_roots(aggregate)
        fast_counts = tail_counts(aggregate, xvalues)
        for index, x in enumerate(xvalues):
            threshold = k * mp.mpf(str(x))
            count = sum(weight for angle, weight in direct.items()
                        if abs(mp.cot(mp.pi * angle.numerator / angle.denominator) / 2)
                        > threshold)
            assert count == int(fast_counts[index]), (k, x, count, fast_counts[index])
            records.append({"k": k, "x": x, "direct_high_precision_mass": count,
                            "aggregated_mass": int(fast_counts[index]), "passed": True})
    COUNTS["independent_tail_count_checks"] = len(records)
    write_csv("tail_count_checks.csv", records)


def root_cdf_arrays(aggregate: dict):
    fractions = list(farey_interior(aggregate["k"] - 1))
    angle = np.asarray([a / b for a, b in fractions])
    weights = np.asarray([aggregate["M"][b] for _, b in fractions], dtype=np.int64)
    cumulative = np.cumsum(weights, dtype=np.int64) / aggregate["N"]
    y = -0.5 / np.tan(math.pi * angle)
    return angle, weights, cumulative, y


PALETTE = ["#164B6B", "#C36435", "#439487", "#786391"]


def style_figures() -> None:
    plt.rcParams.update({
        "font.family": "DejaVu Serif", "font.size": 8.5,
        "mathtext.fontset": "dejavuserif", "axes.titlesize": 9.3,
        "axes.labelsize": 8.8, "legend.fontsize": 7.5,
        "xtick.labelsize": 7.4, "ytick.labelsize": 7.4,
        "axes.spines.top": False, "axes.spines.right": False,
        "axes.edgecolor": "#55616C", "axes.linewidth": 0.7,
        "grid.color": "#DCE2E6", "grid.linewidth": 0.5,
        "lines.linewidth": 1.35, "savefig.facecolor": "white",
        "pdf.fonttype": 42, "ps.fonttype": 42,
    })


def validate_pdf_structure(payload: bytes) -> None:
    """Validate the classic xref format emitted by Matplotlib's PDF backend.

    This dependency-free check rejects incomplete streams, missing trailers,
    incorrect object offsets, and an unexpected page count before publication.
    Full PDF-reader validation is additionally performed in the article QA.
    """
    if not payload.startswith(b"%PDF-"):
        raise ValueError("The rendered figure does not have a PDF header")
    ending = re.search(rb"startxref\s+(\d+)\s+%%EOF\s*\Z", payload)
    if ending is None:
        raise ValueError("The rendered PDF is incomplete: no final xref/EOF marker")
    offset = int(ending.group(1))
    lines = payload[offset:].splitlines()
    if not lines or lines[0] != b"xref":
        raise ValueError("The rendered PDF has an invalid cross-reference offset")
    header = lines[1].split()
    if len(header) != 2 or header[0] != b"0":
        raise ValueError("Unexpected PDF cross-reference format")
    count = int(header[1])
    if len(lines) < count + 3 or lines[count + 2] != b"trailer":
        raise ValueError("The PDF cross-reference table is incomplete")
    for object_number, line in enumerate(lines[2:count + 2]):
        fields = line.split()
        if len(fields) != 3:
            raise ValueError("An invalid PDF cross-reference entry was emitted")
        if fields[2] == b"n":
            position, generation = int(fields[0]), int(fields[1])
            expected = f"{object_number} {generation} obj".encode("ascii")
            if not payload[position:].startswith(expected + b"\n"):
                raise ValueError("A PDF cross-reference entry points to the wrong object")
    pages = re.findall(rb"/Type\s+/Pages\b[^>]*?/Count\s+(\d+)\b", payload)
    if pages != [b"1"]:
        raise ValueError("Expected exactly one page in a figure PDF")


def atomic_write(path: Path, payload: bytes) -> None:
    temporary = None
    try:
        with tempfile.NamedTemporaryFile(mode="wb", dir=path.parent,
                                         prefix=path.name + ".", suffix=".tmp",
                                         delete=False) as handle:
            temporary = Path(handle.name)
            handle.write(payload)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary, path)
    finally:
        if temporary is not None and temporary.exists():
            temporary.unlink()


def finish(fig, stem: str) -> None:
    """Render fully, validate, then publish each figure without partial files."""
    try:
        pdf_buffer = io.BytesIO()
        fig.savefig(pdf_buffer, format="pdf", bbox_inches="tight", pad_inches=0.035,
                    metadata={"Title": stem.replace("_", " "),
                              "Subject": "Reproducible finite computations; see code/reproduce.py"})
        pdf_payload = pdf_buffer.getvalue()
        validate_pdf_structure(pdf_payload)
        png_buffer = io.BytesIO()
        fig.savefig(png_buffer, format="png", bbox_inches="tight", pad_inches=0.035,
                    dpi=300)
        atomic_write(FIGURES / f"{stem}.pdf", pdf_payload)
        atomic_write(FIGURES / f"{stem}.png", png_buffer.getvalue())
        validate_pdf_structure((FIGURES / f"{stem}.pdf").read_bytes())
        COUNTS["one_page_PDF_structure_checks"] = (
            COUNTS.get("one_page_PDF_structure_checks", 0) + 1)
    finally:
        plt.close(fig)


def cdf_figure(aggregates: dict[int, dict]) -> None:
    fig, axes = plt.subplots(1, 2, figsize=(6.8, 2.75), layout="constrained")
    grid = np.linspace(-3, 3, 1001)
    for color, k in zip(PALETTE, [12, 40, 150]):
        angle, weights, cumulative, y = root_cdf_arrays(aggregates[k])
        extent = max(3.1, abs(float(y[0])) + 1)
        axes[0].step(np.r_[-extent, y, extent], np.r_[0, cumulative, 1], where="post",
                     color=color, label=f"$k={k}$", linewidth=1.05)
        doubled_t = np.repeat(angle, 2)
        before = cumulative - weights / aggregates[k]["N"]
        doubled_cdf = np.column_stack([before, cumulative]).ravel()
        axes[1].plot(doubled_t, doubled_cdf - doubled_t, color=color,
                     label=f"$k={k}$", linewidth=0.85)
    axes[0].plot(grid, 0.5 + np.arctan(2 * grid) / math.pi, color="#18232A",
                 linestyle="--", linewidth=1.4, label="Cauchy limit")
    axes[0].set(xlim=(-3, 3), ylim=(0, 1), xlabel="Imaginary coordinate $y$",
                ylabel="Cumulative mass $F_k(y)$", title="Central zero distribution")
    axes[0].legend(loc="lower right", frameon=False)
    axes[1].axhline(0, color="#68747E", linewidth=0.65)
    axes[1].set(xlim=(0.2, 0.8), ylim=(-0.125, 0.125),
                xlabel=r"Cauchy probability $t=F_{\rm C}(y)$",
                ylabel=r"$F_k(y)-F_{\rm C}(y)$", title="Arithmetic jumps in the CDF")
    axes[1].set_xticks([0.25, 1 / 3, 0.5, 2 / 3, 0.75],
                       ["$1/4$", "$1/3$", "$1/2$", "$2/3$", "$3/4$"])
    for ax in axes:
        ax.grid(axis="y")
    finish(fig, "central_cdf")


def edge_figure(aggregates: dict[int, dict]) -> None:
    xvalues = np.linspace(0.006, 0.162, 1201)
    profile = edge_profile(xvalues)
    fig, axes = plt.subplots(1, 2, figsize=(6.8, 2.75), layout="constrained")
    rows = []
    for color, k in zip(PALETTE, [32, 128, 512, 2048]):
        counts = tail_counts(aggregates[k], xvalues)
        scaled = k * counts / aggregates[k]["N"]
        for ax in axes:
            ax.plot(xvalues, scaled, color=color, linewidth=1.05, label=f"$k={k}$")
        for x, count, value, theory in zip(xvalues, counts, scaled, profile):
            rows.append({"k": k, "x": format(float(x), ".15g"),
                         "integer_tail_mass": int(count), "degree_N": aggregates[k]["N"],
                         "k_times_tail_probability": format(float(value), ".15g"),
                         "edge_limit_E": format(float(theory), ".15g")})
    for ax in axes:
        ax.plot(xvalues, profile, color="#18232A", linestyle="--", linewidth=1.4,
                label=r"Limit $E(x)$")
        ax.set_xlabel(r"Edge scale $x$ in $|Y|>kx$")
        ax.grid(axis="y")
    axes[0].set(xlim=(0.006, 0.162), ylim=(0.008, 65), yscale="log",
                ylabel=r"$k\,\nu_k(|Y|>kx)$", title="Tail profile on the linear edge scale")
    axes[0].legend(frameon=False, loc="upper right", ncol=1)
    axes[1].set(xlim=(0.075, 0.162), ylim=(0, 1.2),
                ylabel=r"$k\,\nu_k(|Y|>kx)$", title="Outer edge: finite support emerges")
    axes[1].axvline(1 / (2 * math.pi), color="#74808A", linewidth=0.7, linestyle=":")
    axes[1].annotate(r"$1/(2\pi)$", xy=(1 / (2 * math.pi), 0.08),
                     xytext=(0.147, 0.25), fontsize=8, ha="right",
                     arrowprops={"arrowstyle": "-", "linewidth": 0.7, "color": "#74808A"})
    finish(fig, "edge_tail")
    write_csv("edge_tail_grid.csv", rows)


def convergence_figures(discrepancy_rows: list[dict], moment_rows: list[dict],
                        multiplicity_rows: list[dict]) -> None:
    fig, axes = plt.subplots(1, 2, figsize=(6.8, 2.7), layout="constrained")
    rows = [r for r in discrepancy_rows if r["k"] >= 16]
    ks = np.asarray([r["k"] for r in rows])
    axes[0].plot(ks, [r["D_times_k_over_log_k"] for r in rows], "o-",
                 color=PALETTE[0], markersize=3, label="Exact CDF discrepancy")
    axes[0].plot(ks, [r["half_order_2_atom"] * r["k"] / math.log(r["k"]) for r in rows],
                 "s-", color=PALETTE[1], markersize=2.8, label="Half the order-2 jump")
    axes[0].axhline(9 / math.pi**2, color="#68747E", linestyle="--", linewidth=1)
    axes[0].axhline(3 / math.pi**2, color="#68747E", linestyle=":", linewidth=1)
    axes[0].text(19, 0.94, r"Exact limit $9/\pi^2$", fontsize=7.3, color="#42505B")
    axes[0].text(19, 0.327, r"Lower-bound limit $3/\pi^2$", fontsize=7.3, color="#42505B")
    axes[0].set(xscale="log", xlabel="$k$", ylabel=r"Discrepancy $\times\ k/\log k$",
                title="The logarithmic discrepancy scale", ylim=(0.25, 0.99))
    axes[0].legend(loc="lower left", bbox_to_anchor=(0.01, 0.62), frameon=False,
                    fontsize=7.0)
    for color, p in zip(PALETTE, [2, 4]):
        subset = [r for r in moment_rows if r["p"] == p and r["k"] >= 16]
        axes[1].plot([r["k"] for r in subset], [r["ratio_to_limit"] for r in subset],
                     "o-", color=color, markersize=3, label=f"$p={p}$")
    axes[1].axhline(1, color="#68747E", linestyle="--", linewidth=1)
    axes[1].set(xscale="log", xlabel="$k$", ylabel=r"$k^{1-p}\,\mathbb{E}|Y|^p\,/\,C_p$",
                title="Scaled moments approach their constants", ylim=(0.91, 1.38))
    axes[1].legend(frameon=False, loc="upper right")
    for ax in axes:
        ax.grid(axis="y")
    finish(fig, "discrepancy_moments")

    fig, ax = plt.subplots(figsize=(4.6, 2.7), layout="constrained")
    for color, m in zip(PALETTE, [2, 3, 5, 6]):
        subset = [r for r in multiplicity_rows if r["m"] == m and r["k"] >= 16]
        ax.plot([r["k"] for r in subset], [r["ratio_to_leading_term"] for r in subset],
                 "o-", color=color, markersize=3, label=f"$m={m}$")
    ax.axhline(1, color="#68747E", linestyle="--", linewidth=1)
    ax.set(xscale="log", xlabel="$k$",
           ylabel=r"$E_m(k)\,\zeta(2)\psi(m)/(k^2\log k)$",
           title="Fixed primitive orders: a slow logarithmic approach", ylim=(0.30, 1.025))
    ax.legend(frameon=False, ncol=4, loc="lower right")
    ax.grid(axis="y")
    finish(fig, "fixed_order_multiplicities")


def main() -> None:
    check_determinants()
    cotangent_checks()
    table_ks = [8, 12, 16, 24, 32, 48, 64, 96, 128, 150, 192, 256, 384,
                512, 768, 1024, 1536, 2048, 3072, 4096]
    discrepancy_ks = [k for k in table_ks if k <= 2048]
    requested = set(range(3, 81)) | set(table_ks) | {40}
    aggregates = pair_aggregates(requested)
    phi = phi_sieve(max(requested))
    check_degrees_and_merging(aggregates, phi)
    check_tail_counts(aggregates)

    discrepancy_rows = [exact_discrepancy(aggregates[k]) for k in discrepancy_ks]
    write_csv("exact_CDF_discrepancies.csv", discrepancy_rows)
    COUNTS["exact_full_support_CDF_computations"] = len(discrepancy_rows)

    moment_rows = []
    multiplicity_rows = []
    primitive_rows = []
    for k in table_ks:
        aggregate = aggregates[k]
        for p in [2, 4]:
            value = scaled_moment(aggregate, p)
            moment_rows.append({"k": k, "p": p, "scaled_moment_exact": str(value),
                                "scaled_moment": float(value),
                                "predicted_limit": MOMENT_LIMITS[p],
                                "ratio_to_limit": float(value) / MOMENT_LIMITS[p]})
        for m in [2, 3, 5, 6]:
            leading = k * k * math.log(k) / (ZETA2 * float(psi(m)))
            value = aggregate["M"][m]
            multiplicity_rows.append({"k": k, "m": m, "M_exact": value,
                                      "psi_m_exact": str(psi(m)),
                                      "leading_term": leading,
                                      "ratio_to_leading_term": value / leading})
        for m in range(2, k):
            primitive_rows.append({"k": k, "m": m, "phi_m": phi[m],
                                   "M_k_m": aggregate["M"][m],
                                   "W_k_m": aggregate["W"][m]})
    write_csv("scaled_moments.csv", moment_rows)
    write_csv("fixed_order_multiplicities.csv", multiplicity_rows)
    write_csv("primitive_multiplicities.csv", primitive_rows)
    first_moment_table(aggregates, table_ks)

    # Full polynomial degrees: multiplicities at 0 and -1 plus N.
    full_rows = []
    for k in [32, 128, 512, 2048]:
        aggregate = aggregates[k]
        for sigma in [0, 0.5, 1, 2]:
            s = max(1, int(sigma * k * k))
            c = math.comb(k + 1, 3)
            d = k * (k + 1) // 2
            at_zero = d + 2 * c
            at_minus_one = k * (s - 1) + 2 * c
            degree = at_zero + at_minus_one + aggregate["N"]
            full_rows.append({"k": k, "sigma": sigma, "shift_s": s,
                              "degree_full": degree, "mass_zero_exact": str(Fraction(at_zero, degree)),
                              "mass_minus_one_exact": str(Fraction(at_minus_one, degree)),
                              "mass_reduced_exact": str(Fraction(aggregate["N"], degree)),
                              "mass_zero": at_zero / degree,
                              "mass_minus_one": at_minus_one / degree,
                              "mass_reduced": aggregate["N"] / degree,
                              "limit_zero": 1 / (3 * (1 + sigma)),
                              "limit_minus_one": (sigma + 1 / 3) / (1 + sigma),
                              "limit_reduced": 1 / (3 * (1 + sigma))})
    write_csv("full_zero_measure_weights.csv", full_rows)

    style_figures()
    cdf_figure(aggregates)
    edge_figure(aggregates)
    convergence_figures(discrepancy_rows, moment_rows, multiplicity_rows)

    summary = {
        "checks": COUNTS,
        "constants": {"zeta2": ZETA2, "C2": MOMENT_LIMITS[2], "C4": MOMENT_LIMITS[4],
                      "first_moment_constant": FIRST_MOMENT_CONSTANT,
                      "discrepancy_scaled_limit": 9 / math.pi**2,
                      "order2_half_jump_scaled_limit": 3 / math.pi**2,
                      "edge_support_endpoint": 1 / (2 * math.pi)},
        "versions": {"python": platform.python_version(), "sympy": sp.__version__,
                     "mpmath": mp.__version__, "numpy": np.__version__,
                     "matplotlib": matplotlib.__version__},
        "scope": {
            "symbolic": "QQ[u], k=1..4, s=1..3; independently recurrence-derived Hankel matrices",
            "rational": "k=1..4, s=1..3; u=-2,-1,-1/2,-1/3,0,1/2,1,2",
            "algebraic": "QQ(sqrt(3)*I), k=4, s=1..3; u=(-1+I/sqrt(3))/2",
            "exact_CDF": "All rational support angles, both left and right limits; selected k through 2048",
            "exact_moments": "Rational scaled moments for p=2,4; selected k through 4096",
            "floating_point": "Asymptotic ratios, transcendental constants, tail thresholds, and figures",
        },
        "limitations": [
            "Finite computations do not prove a determinant identity for arbitrary k or any limiting law.",
            "CDF discrepancies are exact on the complete finite support, not sampled on a plotting grid.",
            "The identity degree=N and primitive multiplicities checks share the direct pair aggregation; independent root merging is additionally checked for k=3..20.",
            "The constant 9/pi^2 in the discrepancy figure is established by the article's proof; the finite values are well below it, and do not by themselves establish it. Maximizers need not be the order-2 atom.",
            "Edge-tail masses are integer counts, but deciding a transcendental threshold uses floating point; the independent 70-digit checks use generic thresholds away from atoms.",
            "PNG rendering and PDF metadata can vary across library versions; exact CSV values are reproducible.",
        ],
    }
    (DATA / "verification_summary.json").write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    text_lines = ["VERIFICATION SUMMARY", "", "Every listed check passed."]
    text_lines += [f"{key}: {value}" for key, value in COUNTS.items()]
    text_lines += ["", "Moment constants:",
                   f"C_2 = zeta(3)/(4*pi^2) = {MOMENT_LIMITS[2]:.16g}",
                   f"C_4 = zeta(5)/(600*pi^2) = {MOMENT_LIMITS[4]:.16g}", "",
                   f"First-moment constant = {FIRST_MOMENT_CONSTANT:.16g}",
                   f"Exact discrepancy scaled limit = 9/pi^2 = {9 / math.pi**2:.16g}", "",
                   "Selected exact CDF discrepancies:"]
    for record in discrepancy_rows:
        if record["k"] in [64, 128, 256, 512, 1024, 2048]:
            text_lines.append(f"k={record['k']}: D={record['D']:.12g}; "
                              f"D*k/log(k)={record['D_times_k_over_log_k']:.9g}; "
                              f"maximizer={record['maximizing_angle']} ({record['side']} limit)")
    text_lines += ["", "Limitations:"] + [f"- {item}" for item in summary["limitations"]]
    (DATA / "verification_summary.txt").write_text("\n".join(text_lines) + "\n", encoding="utf-8")
    print("\n".join(text_lines))
    print(f"\nWrote tables to {DATA}")
    print(f"Wrote four PDF/PNG figure pairs to {FIGURES}")


if __name__ == "__main__":
    main()
