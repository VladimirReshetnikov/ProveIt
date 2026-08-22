#!/usr/bin/env python3
"""Exact p-adic experiments for the mixed Alaoglu--Erdos block determinant.

This script intentionally has no third-party dependencies.  It computes

* the first N pairs (u,v), ordered by u + log_2(3) v;
* the exact 2- and 3-adic determinant valuations by elimination over Z/p^R;
* the tropical assignment minima;
* the exact first-fiber Vandermonde valuations and first assignment gaps;
* for small N, truncated signed/unit-weighted tropical layer coefficients.

The synthetic parameters satisfy gcd(6MA)=1 and beta=log_2(M).  They do not
assert that A=3^beta; that would be the unknown arithmetic situation.
"""

from __future__ import annotations

import argparse
import json
import math
from decimal import Decimal, localcontext


def v_p(x: int, p: int, cap: int | None = None) -> int:
    """p-adic valuation of an integer, capped when x=0 modulo p^cap."""
    if x == 0:
        if cap is None:
            raise ValueError("valuation of zero requires a cap")
        return cap
    if p == 2:
        return (abs(x) & -abs(x)).bit_length() - 1
    x = abs(x)
    v = 0
    while x % p == 0:
        x //= p
        v += 1
    return v


def high_precision_logs(M: int) -> tuple[Decimal, Decimal]:
    with localcontext() as ctx:
        ctx.prec = 100
        ln2 = Decimal(2).ln()
        return +(Decimal(M).ln() / ln2), +(Decimal(3).ln() / ln2)


def first_pairs(N: int) -> list[tuple[int, int]]:
    """Return the first N pairs ordered by u + log_2(3)v, exactly.

    Ordering the additive weights is equivalent to ordering the distinct
    integers 2^u 3^v.  The N candidates (u, 0), 0 <= u < N, show that every
    needed point has 2^u 3^v <= 2^(N-1).
    """
    pts = []
    cutoff = 1 << (N - 1)
    for u in range(N):
        two_part = 1 << u
        three_part = 1
        v = 0
        while two_part * three_part <= cutoff:
            pts.append((u, v))
            v += 1
            three_part *= 3
    pts.sort(key=lambda uv: (1 << uv[0]) * pow(3, uv[1]))
    assert len(pts) >= N
    return pts[:N]


def block_data(T: int, M: int, A: int) -> dict:
    beta, theta = high_precision_logs(M)
    # K=floor((T+1)/log_2(M)) is decided by the exact equivalent inequality
    # M^K <= 2^(T+1), and floor(k log_2(M)) is an integer bit length.
    K = 0
    M_power = 1
    cutoff = 1 << (T + 1)
    while M_power * M <= cutoff:
        M_power *= M
        K += 1
    N = K + 1
    pairs = first_pairs(N)
    n = [T - (pow(M, k).bit_length() - 1) for k in range(N)]
    assert all(n[k] > n[k + 1] for k in range(N - 1))
    assert n[-1] >= 0
    return {
        "T": T,
        "M": M,
        "A": A,
        "beta": beta,
        "theta": theta,
        "N": N,
        "pairs": pairs,
        "n": n,
    }


def tropical_min(n: list[int], weights: list[int]) -> int:
    """Minimum of sum n_k*w_sigma(k), with n strictly decreasing."""
    return sum(a * b for a, b in zip(n, sorted(weights)))


def first_assignment_gap(n: list[int], weights: list[int]) -> int | None:
    """Smallest positive rank-one assignment excess over the tied minimum."""
    ws = sorted(weights)
    candidates = [
        (ws[i + 1] - ws[i]) * (n[i] - n[i + 1])
        for i in range(len(n) - 1)
        if ws[i] < ws[i + 1]
    ]
    return min(candidates) if candidates else None


def fiber_row_blocks(weights: list[int]) -> list[tuple[int, range]]:
    """Optimal consecutive row blocks for equal sorted column weights."""
    counts: dict[int, int] = {}
    for w in weights:
        counts[w] = counts.get(w, 0) + 1
    out = []
    start = 0
    for w in sorted(counts):
        stop = start + counts[w]
        out.append((w, range(start, stop)))
        start = stop
    return out


def first_fiber_valuation(data: dict, p: int) -> int:
    """Valuation of the product of first-layer fiber Vandermondes."""
    M, A, n, pairs = data["M"], data["A"], data["n"], data["pairs"]
    weights = [u if p == 2 else v for u, v in pairs]
    total = 0
    for _w, rows in fiber_row_blocks(weights):
        rr = list(rows)
        for ii, i in enumerate(rr):
            for j in rr[ii + 1 :]:
                d = j - i
                h = n[i] - n[j]
                z = pow(A, d) - pow(3, h) if p == 2 else pow(M, d) - pow(2, h)
                if z == 0:
                    raise ArithmeticError("synthetic parameters produced a zero row difference")
                total += v_p(z, p)
    return total


def factorial_valuation(n: int, p: int) -> int:
    total = 0
    while n:
        n //= p
        total += n
    return total


def unit_ordering_weight(j: int, p: int) -> int:
    """The fixed-divisor weights formalized in AllLayerUnitBasis.lean."""
    if p == 2:
        return j + factorial_valuation(j, 2)
    if p == 3:
        q = j // 2
        return q + factorial_valuation(q, 3)
    raise ValueError("only p=2,3")


def unit_basis_gain(data: dict, p: int) -> int:
    weights = [uv[0 if p == 2 else 1] for uv in data["pairs"]]
    return sum(
        sum(unit_ordering_weight(j, p) for j in range(len(rows)))
        for _weight, rows in fiber_row_blocks(weights)
    )


def entry_mod(data: dict, k: int, j: int, modulus: int) -> int:
    u, v = data["pairs"][j]
    n, M, A = data["n"][k], data["M"], data["A"]
    m = pow(2, n, modulus) * pow(M, k, modulus) % modulus
    a = pow(3, n, modulus) * pow(A, k, modulus) % modulus
    return pow(m, u, modulus) * pow(a, v, modulus) % modulus


def assignment_dual(data: dict, p: int) -> tuple[list[int], list[int], list[int]]:
    """Sorted columns and an integral optimal dual for the rank-one cost."""
    pairs, n = data["pairs"], data["n"]
    weights = [uv[0] if p == 2 else uv[1] for uv in pairs]
    order = sorted(range(len(weights)), key=lambda j: (weights[j], j))
    w = [weights[j] for j in order]
    colpot = [0] * len(w)
    for j in range(len(w) - 1):
        colpot[j + 1] = colpot[j] + n[j] * (w[j + 1] - w[j])
    rowpot = [n[i] * w[i] - colpot[i] for i in range(len(w))]
    assert sum(rowpot) + sum(colpot) == tropical_min(n, weights)
    for i in range(len(w)):
        for j in range(len(w)):
            assert n[i] * w[j] - rowpot[i] - colpot[j] >= 0
    return order, rowpot, colpot


def unit_entry_mod(data: dict, p: int, k: int, j: int, modulus: int) -> int:
    """Entry after removing its full p-power."""
    u, v = data["pairs"][j]
    nk, M, A = data["n"][k], data["M"], data["A"]
    if p == 2:
        return (
            pow(M, k * u, modulus)
            * pow(3, nk * v, modulus)
            * pow(A, k * v, modulus)
        ) % modulus
    return (
        pow(2, nk * u, modulus)
        * pow(M, k * u, modulus)
        * pow(A, k * v, modulus)
    ) % modulus


def det_val_mod(data: dict, p: int, precision: int) -> int | None:
    """Exact v_p(det) if it is < precision, via DVR Gaussian elimination.

    At every stage choose an entry of minimum valuation in the remaining
    submatrix, swap it to the pivot, and clear its column using its unit part.
    """
    N, n = data["N"], data["n"]
    modulus = pow(p, precision)
    order, rowpot, colpot = assignment_dual(data, p)
    weights = [data["pairs"][j][0 if p == 2 else 1] for j in order]
    # This is the integral dual-normalized matrix.  Its determinant differs
    # from the original one by exactly p^tau, despite possibly negative
    # individual row potentials.
    a = []
    for i in range(N):
        row = []
        for jj, j in enumerate(order):
            exponent = n[i] * weights[jj] - rowpot[i] - colpot[jj]
            row.append(pow(p, exponent, modulus) * unit_entry_mod(data, p, i, j, modulus) % modulus)
        a.append(row)
    total = 0
    for k in range(N):
        best = precision
        bi = bj = -1
        for i in range(k, N):
            for j in range(k, N):
                vv = v_p(a[i][j], p, precision)
                if vv < best:
                    best, bi, bj = vv, i, j
                    if best == 0:
                        break
            if best == 0:
                break
        if best == precision:
            return None
        total += best
        if total >= precision:
            return None
        if bi != k:
            a[k], a[bi] = a[bi], a[k]
        if bj != k:
            for row in a:
                row[k], row[bj] = row[bj], row[k]
        pivot = a[k][k]
        unit_modulus = pow(p, precision - best)
        unit = (pivot // pow(p, best)) % unit_modulus
        inv_unit = pow(unit, -1, unit_modulus)
        for i in range(k + 1, N):
            assert a[i][k] % pow(p, best) == 0
            coeff = (a[i][k] // pow(p, best)) * inv_unit % unit_modulus
            for j in range(k, N):
                a[i][j] = (a[i][j] - coeff * a[k][j]) % modulus
            assert a[i][k] == 0
    return total


def exact_det_valuation(data: dict, p: int, tau: int, cushion: int = 64) -> tuple[int, int]:
    # det_val_mod works after removing the whole tropical factor p^tau.
    precision = cushion
    while True:
        val = det_val_mod(data, p, precision)
        if val is not None:
            return tau + val, precision
        precision *= 2


def height(data: dict) -> float:
    return data["T"] * sum(u * math.log(2) + v * math.log(3) for u, v in data["pairs"])


def layer_coefficients(data: dict, p: int, max_excess: int, coeff_precision: int = 12) -> dict[int, int]:
    """Signed unit-weighted coefficient C_delta modulo p^coeff_precision.

    det/p^tau = sum_delta p^delta C_delta.  The subset DP is exponential,
    so this is intended only for N <= about 17.
    """
    N = data["N"]
    if N > 20:
        raise ValueError("layer DP intentionally capped at N=20")
    weights = [uv[0] if p == 2 else uv[1] for uv in data["pairs"]]
    n = data["n"]
    tau = tropical_min(n, weights)
    modulus = pow(p, coeff_precision)

    costs = [[n[k] * weights[j] for j in range(N)] for k in range(N)]
    units = [[0] * N for _ in range(N)]
    M, A = data["M"], data["A"]
    for k in range(N):
        nk = n[k]
        for j, (u, v) in enumerate(data["pairs"]):
            if p == 2:
                units[k][j] = (
                    pow(M, k * u, modulus)
                    * pow(3, nk * v, modulus)
                    * pow(A, k * v, modulus)
                ) % modulus
            else:
                units[k][j] = (
                    pow(2, nk * u, modulus)
                    * pow(M, k * u, modulus)
                    * pow(A, k * v, modulus)
                ) % modulus

    full = (1 << N) - 1
    dp: dict[int, dict[int, int]] = {0: {0: 1}}

    def remaining_min(mask: int, next_row: int) -> int:
        unused = sorted(weights[j] for j in range(N) if not (mask >> j) & 1)
        return sum(n[next_row + i] * w for i, w in enumerate(unused))

    cutoff = tau + max_excess
    for k in range(N):
        nxt: dict[int, dict[int, int]] = {}
        for mask, poly in dp.items():
            for j in range(N):
                if (mask >> j) & 1:
                    continue
                mask2 = mask | (1 << j)
                lb = remaining_min(mask2, k + 1) if k + 1 < N else 0
                sign = -1 if ((mask >> (j + 1)).bit_count() & 1) else 1
                shift = costs[k][j]
                unit = units[k][j]
                dest = nxt.setdefault(mask2, {})
                for degree, coefficient in poly.items():
                    degree2 = degree + shift
                    if degree2 + lb <= cutoff:
                        dest[degree2] = (dest.get(degree2, 0) + sign * coefficient * unit) % modulus
        dp = nxt
    return {degree - tau: c for degree, c in sorted(dp[full].items())}


def analyze(T: int, M: int, A: int, layers: bool = False) -> dict:
    if T < 0 or M <= 2 or A <= 0 or math.gcd(6, M * A) != 1:
        raise ValueError("need T >= 0, M > 2, A > 0, and gcd(6MA)=1")
    data = block_data(T, M, A)
    result = {
        "T": T,
        "M": M,
        "A": A,
        "beta": str(data["beta"]),
        "N": data["N"],
        "pairs": data["pairs"],
        "n": data["n"],
        "H": height(data),
    }
    for p in (2, 3):
        weights = [uv[0] if p == 2 else uv[1] for uv in data["pairs"]]
        tau = tropical_min(data["n"], weights)
        gap = first_assignment_gap(data["n"], weights)
        initial = first_fiber_valuation(data, p)
        actual, precision = exact_det_valuation(data, p, tau)
        rec = {
            "tau": tau,
            "actual": actual,
            "excess": actual - tau,
            "gap": gap,
            "initial": initial,
            "unit_basis_gain": unit_basis_gain(data, p),
            "guaranteed": min(gap, initial) if gap is not None else initial,
            "precision": precision,
        }
        if layers and data["N"] <= 20:
            # Include every tropical layer that can affect the observed valuation,
            # plus two layers for context.  Coefficients are returned modulo p^12.
            coeffs = layer_coefficients(data, p, actual - tau + 2, 12)
            rec["layers_mod_p12"] = coeffs
            rec["nonzero_layers_mod_p"] = [d for d, c in coeffs.items() if c % p]
            rec["term_layer_support"] = list(coeffs)
        result[f"p{p}"] = rec
    return result


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--M", type=int, default=5)
    ap.add_argument("--A", type=int, default=7)
    ap.add_argument("--T", type=int, nargs="+", default=[8, 12, 16, 20])
    ap.add_argument("--layers", action="store_true")
    ap.add_argument("--table", action="store_true")
    args = ap.parse_args()
    results = [analyze(T, args.M, args.A, args.layers) for T in args.T]
    if args.table:
        print("T N tau2 v2det e2 U2 I2 tau3 v3det e3 U3 I3 weighted_excess_over_H")
        for result in results:
            p2, p3 = result["p2"], result["p3"]
            ratio = (
                p2["excess"] * math.log(2) + p3["excess"] * math.log(3)
            ) / result["H"]
            print(
                result["T"], result["N"],
                p2["tau"], p2["actual"], p2["excess"],
                p2["unit_basis_gain"], p2["initial"],
                p3["tau"], p3["actual"], p3["excess"],
                p3["unit_basis_gain"], p3["initial"],
                f"{ratio:.12g}",
            )
    else:
        for result in results:
            print(json.dumps(result, sort_keys=True))


if __name__ == "__main__":
    main()
