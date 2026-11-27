#!/usr/bin/env python3
"""Finite rational proof from moment enclosures. See --help and CERTIFICATE.md."""
import argparse
import json
from fractions import Fraction as F
from math import isqrt
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ValueError(message)


def polynomial_product(a, b):
    c = [F(0)] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        for j, bj in enumerate(b):
            c[i + j] += ai * bj
    return c


def integral(coefficients, moments):
    """Integral against sum m_i y_i delta(y_i), using rational moment boxes."""
    lo, hi = F(0), F(0)
    for c, (a, b) in zip(coefficients, moments):
        lo += c * (a if c >= 0 else b)
        hi += c * (b if c >= 0 else a)
    require(len(coefficients) <= len(moments), "Insufficient moments")
    return lo, hi


def divide_positive(num, den):
    require(den[0] > 0, "Unresolved denominator")
    corners = [x / y for x in num for y in den]
    return min(corners), max(corners)


def ordinate_bounds(lo, hi, scale, digits):
    factor = 10 ** digits
    def floor_sqrt(x):
        return isqrt((x.numerator * factor * factor) // x.denominator)
    lb = max(F(0), scale / hi - F(1, 4))
    ub = scale / lo - F(1, 4)
    return floor_sqrt(lb), floor_sqrt(ub) + 1


def decimal(integer, digits):
    whole, rest = divmod(integer, 10 ** digits)
    return f"{whole}.{rest:0{digits}d}"


def verify(moments, witness, scale):
    """All operations from this point are exact (integers and rational numbers)."""
    cuts = [F(row["cut"]) for row in witness]
    vectors = [[F(x) for x in row["polynomial"]] for row in witness]
    require(all(x > 0 for x in cuts), "Nonpositive lower bound")
    boxes = []
    for j, row in enumerate(witness):
        q, cut = vectors[j], cuts[j]
        # Strict diagonal dominance of the real symmetric restricted form proves
        # a j+1 dimensional positive subspace for multiplication by y-cut.
        for i in range(j + 1):
            off_diagonal = F(0)
            for k in range(j + 1):
                product = polynomial_product(vectors[i], vectors[k])
                form = polynomial_product([-cut, 1], product)
                lo, hi = integral(form, moments)
                if i == k:
                    diagonal = lo
                else:
                    off_diagonal += max(abs(lo), abs(hi))
            require(diagonal > off_diagonal, f"Unresolved inertia at cut {j+1}")
        # Trace moments and unit lower bounds on atom multiplicities separate the
        # next distinct atom from the Rayleigh quotient for the j+1-st atom.
        k = int(row["order"])
        sep = F(row["separator"])
        require(0 < k <= len(moments) and sep > 0, "Invalid separator")
        remainder = moments[k - 1][1] - sum(x ** k for x in cuts[:j])
        require(remainder <= 2 * sep ** k, f"Unverified separator {j+1}")
        require(sep < cut, f"Multiplicity is unresolved at {j+1}")
        q2 = polynomial_product(q, q)
        norm = integral(q2, moments)
        R = divide_positive(integral([0] + q2, moments), norm)
        require(R[0] > sep, f"Missing spectral separation {j+1}")
        trial = F(row["center"])
        shifted = polynomial_product([-trial, 1], q)
        residual = divide_positive(integral(polynomial_product(shifted, shifted), moments), norm)
        require(residual[1] >= 0, "Inconsistent moment enclosure")
        outer = R[1] + residual[1] / (R[0] - sep)
        require(outer >= cut, "Reversed interval")
        boxes.append(ordinate_bounds(cut, outer, scale, 14))
    return boxes


def propose(moments, count):
    """Untrusted suggestions. No floating-point value is accepted by verify()."""
    from mpmath import mp
    mp.dps = 100
    def real(x):
        return mp.mpf(x.numerator) / x.denominator
    def quantize(x, digits, rounding):
        return F(int(rounding(x * 10 ** digits)), 10 ** digits)
    midpoint = [real((a + b) / 2) for a, b in moments]
    dim = (len(moments) - 1) // 2
    H = mp.matrix(dim, dim)
    J = mp.matrix(dim, dim)
    for i in range(dim):
        for j in range(dim):
            H[i, j], J[i, j] = midpoint[i + j], midpoint[1 + i + j]
    inv = mp.inverse(mp.cholesky(H))
    A = inv * J * inv.T
    eig, V = mp.eigsy((A + A.T) / 2)
    witness, cuts = [], []
    for j in range(count):
        r = eig[dim - 1 - j]
        center = quantize(r, 40, mp.floor)
        cut = quantize(r, 18, mp.floor) - F(1, 10 ** 18)
        vector = inv.T * V[:, dim - 1 - j]
        qs = [str(quantize(w, 45, mp.nint)) for w in vector]
        candidate = []
        for k in range(1, 2 * dim + 1):
            rem = moments[k - 1][1] - sum(y ** k for y in cuts)
            candidate.append((mp.root(real(rem / 2), k), k))
        best, k = min(candidate)
        sep = quantize(best, 18, mp.ceil) + F(1, 10 ** 18)
        witness.append(dict(cut=str(cut), center=str(center), polynomial=qs,
                            order=k, separator=str(sep)))
        cuts.append(cut)
    return witness


def load_moments(path):
    raw = json.loads(path.read_text())
    scale = F(raw["scale"])
    require(all(row["k"] == k for k, row in enumerate(raw["moments"], 1)),
            "Moments must be in ascending order from k=1")
    moments = [(F(row["lower"]), F(row["upper"])) for row in raw["moments"]]
    require(scale > 0 and all(a <= b for a, b in moments), "Invalid moment input")
    return scale, moments


def main():
    here = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--moments", type=Path, default=here / "certified_moments.json")
    parser.add_argument("--witness", type=Path, default=here / "witness.json")
    parser.add_argument("--propose", action="store_true", help="generate a replacement witness (mpmath)")
    parser.add_argument("--count", type=int, default=4, help="number of bounds to propose")
    args = parser.parse_args()
    scale, moments = load_moments(args.moments)
    if args.propose:
        witness = propose(moments, args.count)
    else:
        witness = json.loads(args.witness.read_text())
    intervals = verify(moments, witness, scale)
    if args.propose:
        args.witness.write_text(json.dumps(witness, indent=2) + "\n")
    print("Fourteen-decimal outward rational enclosures. Each listed zero has multiplicity one.")
    for j, (lo, hi) in enumerate(intervals, start=1):
        print(f"{j}  [{decimal(lo, 14)}, {decimal(hi, 14)}]")


if __name__ == "__main__":
    main()
