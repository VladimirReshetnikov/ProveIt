"""Exact weighted distribution grids and rational normal forms.

The symbols are e_(j/q), 0 <= j < q.  A multiplier m | q gives rows

    sum_{b=0}^{m-1} e_((a+b*q/m)/q) - m**exponent * e_(m*a/q).

All arithmetic is rational.  This module studies the displayed formal
relations; it does not assert numerical independence of special values.
Requires Python 3.10+ and SymPy.  Running the file writes validation
receipts and normal-form certificates to the adjacent results directory.
"""

from collections import defaultdict
from fractions import Fraction
from functools import lru_cache
from math import gcd, isqrt
from pathlib import Path
import csv
import json
import platform
import time

import sympy
from sympy import QQ
from sympy.polys.matrices import DomainMatrix


def divisors(q):
    """Positive divisors, in increasing order."""
    return [d for d in range(1, q + 1) if q % d == 0]


def prime_divisors(q):
    """Distinct prime divisors, in increasing order."""
    return [d for d in divisors(q) if d > 1
            and all(d % p for p in range(2, isqrt(d) + 1))]


def units(q):
    """Residues of exact denominator q; U_1 is represented by residue 0."""
    return [a for a in range(q) if gcd(a, q) == 1]


def clean(row):
    return {j: Fraction(c) for j, c in row.items() if c}


def distribution_rows(q, exponent, all_divisors=False):
    """Sparse rational coefficient rows for prime or all divisor laws."""
    if q < 1 or not isinstance(exponent, int):
        raise ValueError("q must be positive and exponent must be an integer")
    multipliers = divisors(q)[1:] if all_divisors else prime_divisors(q)
    rows = []
    for m in multipliers:
        scale = Fraction(m) ** exponent
        for a in range(q // m):
            row = defaultdict(Fraction)
            for b in range(m):
                row[a + b * (q // m)] += 1
            row[(m * a) % q] -= scale
            rows.append(clean(row))
    return rows


def relation_rows(q, exponent, *, pin=False, parity=None,
                  all_divisors=False):
    """Add e_0=0 and/or e_(-x)=parity*e_x to distribution rows."""
    if parity not in (None, -1, 1):
        raise ValueError("parity must be None, -1, or +1")
    rows = distribution_rows(q, exponent, all_divisors)
    if pin:
        rows.append({0: Fraction(1)})
    if parity is not None:
        for a in range(q):
            row = defaultdict(Fraction)
            row[(-a) % q] += 1
            row[a] -= parity
            if clean(row):
                rows.append(clean(row))
    return rows


def rational_rref(rows, ncols):
    """Reduced rows and pivots over QQ; zero input rows are harmless."""
    entries = {}
    for i, row in enumerate(rows):
        converted = {j: QQ(c.numerator, c.denominator)
                     for j, c in clean(row).items()}
        if converted:
            entries[i] = converted
    matrix = DomainMatrix(entries, (len(rows), ncols), QQ)
    reduced, pivots = matrix.rref()
    out = []
    data = reduced.to_sdm()
    for i in range(len(pivots)):
        out.append({j: Fraction(int(c.numerator), int(c.denominator))
                    for j, c in data.get(i, {}).items() if c})
    return out, pivots


def exact_rank(rows, ncols):
    return len(rational_rref(rows, ncols)[1])


def row_remainder(row, reduced, pivots):
    """Exact remainder modulo a row space, using its actual RREF."""
    remainder = defaultdict(Fraction, clean(row))
    for pivot, basis_row in zip(pivots, reduced):
        coefficient = remainder[pivot]
        if coefficient:
            for j, value in basis_row.items():
                remainder[j] -= coefficient * value
    return clean(remainder)


def expected_residual(q, *, pin=False, parity=None):
    """The theorem's prediction, separate from the matrix computation."""
    if q < 3:
        raise ValueError("the parity count in this helper assumes q >= 3")
    dimension = len(units(q))
    if parity is not None:
        dimension //= 2
    if pin and parity in (None, 1):
        dimension -= 1
    return dimension


def primitive_normal_form(q, exponent):
    """Express every grid symbol in the primitive q-level symbols.

    Returns a list of sparse rows indexed by the original q-grid residues;
    each row maps a primitive residue modulo q to its exact coefficient.
    The top-level basis exists for nonzero integer exponent.  The zero
    exponent case can have vanishing character factors and is rejected.
    """
    if q < 1 or not isinstance(exponent, int) or exponent == 0:
        raise ValueError("normal forms require q >= 1 and nonzero integer exponent")
    q_primes = prime_divisors(q)

    @lru_cache(None)
    def reduce_symbol(d, a):
        a %= d
        if gcd(a, d) != 1:
            raise ValueError("internal symbol is not in lowest terms")
        if d == q:
            return {a: Fraction(1)}
        p = next(p for p in q_primes if (q // d) % p == 0)
        pd = p * d
        scale = Fraction(p) ** exponent
        answer = defaultdict(Fraction)

        def add_lifts(c, coefficient):
            for j in range(p):
                b = c + j * d
                if gcd(b, pd) == 1:
                    for residue, value in reduce_symbol(pd, b).items():
                        answer[residue] += coefficient * value

        if d % p == 0:
            add_lifts(a, 1 / scale)
        else:
            if d == 1:
                inverse, order = 0, 1
            else:
                inverse, order = pow(p, -1, d), 1
                t = p % d
                while t != 1:
                    t = t * p % d
                    order += 1
            denominator = scale**order - 1
            c = a
            for r in range(order):
                add_lifts(c, scale**(order - 1 - r) / denominator)
                c = c * inverse % d
        return clean(answer)

    result = []
    for j in range(q):
        common = gcd(j, q)
        result.append(reduce_symbol(q // common, j // common))
    return result


def sparse_product_row(row, normal_form):
    result = defaultdict(Fraction)
    for j, coefficient in row.items():
        for a, value in normal_form[j].items():
            result[a] += coefficient * value
    return clean(result)


def serialized_rows(rows):
    return [{str(j): str(c) for j, c in sorted(row.items()) if c}
            for row in rows]


def certify_normal_form(q, exponent):
    """Check R*N=0 and every reconstruction row against the actual RREF."""
    primitive = units(q)
    normal = primitive_normal_form(q, exponent)
    prime_rows = distribution_rows(q, exponent)
    all_rows = distribution_rows(q, exponent, all_divisors=True)
    reduced, pivots = rational_rref(prime_rows, q)
    assert len(pivots) == q - len(primitive)
    assert all(normal[a] == {a: Fraction(1)} for a in primitive)
    assert all(not sparse_product_row(row, normal) for row in prime_rows)
    assert all(not sparse_product_row(row, normal) for row in all_rows)
    assert all(not row_remainder(row, reduced, pivots) for row in all_rows)

    reconstruction_rows = []
    for j, expansion in enumerate(normal):
        row = defaultdict(Fraction, {j: Fraction(1)})
        for a, coefficient in expansion.items():
            row[a] -= coefficient
        row = clean(row)
        reconstruction_rows.append(row)
        assert not row_remainder(row, reduced, pivots)

    all_rank = exact_rank(all_rows, q)
    assert all_rank == len(pivots)
    return {
        "q": q, "exponent": exponent,
        "primitive_residues": primitive,
        "prime_relation_rows": serialized_rows(prime_rows),
        "all_divisor_relation_rows": serialized_rows(all_rows),
        "normal_form_rows": serialized_rows(normal),
        "reconstruction_rows": serialized_rows(reconstruction_rows),
        "prime_rank": len(pivots), "all_divisor_rank": all_rank,
        "primitive_submatrix_is_identity": True,
        "prime_rows_times_normal_form_are_zero": True,
        "all_divisor_rows_times_normal_form_are_zero": True,
        "all_divisor_rows_belong_to_prime_row_space": True,
        "all_reconstruction_rows_belong_to_prime_row_space": True,
    }


def run_validation(output_dir):
    """Reproduce the finite checks reported alongside the mathematical proof."""
    started = time.monotonic()
    output_dir = Path(output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)
    records = []

    def check(family, q, exponent, pin, parity):
        rows = relation_rows(q, exponent, pin=pin, parity=parity)
        rank = exact_rank(rows, q)
        expected = expected_residual(q, pin=pin, parity=parity)
        actual = q - rank
        assert actual == expected, (family, q, exponent, actual, expected)
        records.append({
            "family": family, "q": q, "exponent": exponent,
            "pin": pin, "parity": parity if parity is not None else "none",
            "row_count": len(rows), "rank": rank,
            "residual_dimension": actual, "expected_dimension": expected,
            "passed": True,
        })

    higher = [105, 120, 144, 180, 210]
    for q in list(range(3, 101)) + higher:
        for k in range(1, 7):
            check("negative_zeta_jet", q, -k, True, (-1)**(k + 1))
    for q in range(3, 101):
        check("first_stieltjes", q, 1, True, 1)
        for k in range(1, 4):
            check("stieltjes_parameter_derivative", q, k + 1, True, None)
    for q in [3, 8, 12, 18, 30, 60, 84, 105, 120, 144, 210]:
        for exponent in [-6, -2, -1, 0, 1, 2, 7]:
            check("unpinned_weighted_distribution", q, exponent, False, None)

    fieldnames = list(records[0])
    with (output_dir / "distribution_rank_checks.csv").open("w", newline="") as out:
        writer = csv.DictWriter(out, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(records)

    certificate_specs = [(12, -1), (18, -2), (30, -3), (45, 1),
                         (60, 2), (84, -2), (105, -1), (120, 3)]
    certificates = [certify_normal_form(q, exponent)
                    for q, exponent in certificate_specs]
    certificate_path = output_dir / "primitive_normal_form_certificates.json"
    certificate_path.write_text(json.dumps(certificates, indent=2) + "\n")

    family_counts = defaultdict(int)
    for record in records:
        family_counts[record["family"]] += 1
    summary = {
        "arithmetic": "exact rational QQ; no floating-point rank decisions",
        "python_version": platform.python_version(),
        "sympy_version": sympy.__version__,
        "matrix_cases": len(records),
        "family_case_counts": dict(family_counts),
        "negative_jet_range": "q=3..100 and q in {105,120,144,180,210}; k=1..6",
        "all_matrix_cases_passed": all(r["passed"] for r in records),
        "normal_form_certificates": len(certificates),
        "prime_vs_all_divisor_span_checks": len(certificates),
        "reconstructed_grid_symbols": sum(c["q"] for c in certificates),
        "reconstructed_nonprimitive_symbols": sum(
            c["q"] - len(c["primitive_residues"]) for c in certificates),
        "normal_form_cases": [{"q": q, "exponent": exponent}
                              for q, exponent in certificate_specs],
        "all_normal_form_checks_passed": True,
        "elapsed_seconds": round(time.monotonic() - started, 3),
        "interpretation": "finite checks accompany an all-q proof; neither proves period independence",
    }
    (output_dir / "distribution_validation_summary.json").write_text(
        json.dumps(summary, indent=2) + "\n")
    return summary


if __name__ == "__main__":
    destination = Path(__file__).resolve().parents[1] / "results"
    print(json.dumps(run_validation(destination), indent=2))
