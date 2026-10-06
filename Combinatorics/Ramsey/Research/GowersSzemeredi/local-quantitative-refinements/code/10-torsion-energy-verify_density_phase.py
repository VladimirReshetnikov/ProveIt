"""Exact checks of density inequalities and constructive phase partitions.

The general proofs are in density_phase.tex.  These finite checks exercise
strict tail thresholds, exceptional sets, small scales, circular gaps,
integer block lengths, and the chord-midpoint disc construction.
Only the final complex-distance check uses floating-point arithmetic;
the partition coverage, Dirichlet inequality and angle bounds are exact.
"""
from cmath import exp
from fractions import Fraction as F
from itertools import product
from math import cos, floor, isqrt, pi, sin


def fsqrt_floor(x):
    return isqrt(x.numerator // x.denominator)


def centered(x):
    return x - floor(x + F(1, 2))


def phase_partition(N, theta, scale):
    """lambda = pi * scale, where 0 < scale <= 1/2."""
    L = max(1, fsqrt_floor(N * scale / 2))
    if L == 1:
        return [[x] for x in range(N)], L, F(0)
    Q = N // L
    q = next(q for q in range(1, Q + 1)
             if abs(centered(q * theta)) <= F(1, Q + 1))
    t = centered(q * theta)
    cells = []
    for r in range(q):
        residue = list(range(r, N, q))
        n = len(residue)
        assert n >= L
        a, b = divmod(n, L)
        sizes = [L + b] + [L] * (a - 1)
        offset = 0
        for size in sizes:
            cells.append(residue[offset:offset + size])
            offset += size
        assert offset == n
    return cells, L, t


def check_phase_case(N, theta, scale):
    cells, L, t = phase_partition(N, theta, scale)
    assert sorted(x for P in cells for x in P) == list(range(N))
    for P in cells:
        assert L <= len(P) <= 2 * L - 1
        if len(P) > 2:
            assert all(P[i] - P[i - 1] == P[1] - P[0]
                       for i in range(2, len(P)))
        # H/pi = (m-1)*|t|. This comparison is exact.
        H_over_pi = (len(P) - 1) * abs(t)
        assert H_over_pi <= scale <= F(1, 2)
        H = pi * float(H_over_pi)
        middle = (theta * P[0] + F(len(P) - 1, 2) * t) % 1
        z = cos(H) * exp(2j * pi * float(middle))
        assert abs(z) <= 1 + 1e-13
        for x in P:
            value = exp(2j * pi * float((theta * x) % 1))
            assert abs(value - z) <= sin(pi * float(scale)) + 1e-12
    return len(cells)


def density_checks():
    profiles = tails = exceptions = sharp = 0
    weights = [(F(i, 6), F(j, 6), F(6 - i - j, 6))
               for i in range(1, 5) for j in range(1, 6 - i)]
    values = [F(i, 4) for i in range(5)]
    for w in weights:
        for u in product(values, repeat=3):
            delta = sum(x * y for x, y in zip(w, u))
            if not 0 < delta < 1:
                continue
            S = sum(x * abs(y - delta) for x, y in zip(w, u))
            V = sum(x * (y - delta) ** 2 for x, y in zip(w, u))
            M = max(u)
            assert S <= 2 * delta * (M - delta) / M
            assert M >= delta + delta * S / (2 * delta - S)
            assert M >= delta + V / delta
            assert S <= 2 * delta * (1 - delta)
            profiles += 1
            for tau in (F(i, 8) for i in range(1, 8)):
                if not delta < tau < 1:
                    continue
                q = sum(x for x, y in zip(w, u) if y > tau)
                bound = max(F(0), (tau * S - 2 * delta * (tau - delta))
                            / (2 * delta * (1 - tau)))
                assert q >= bound
                tails += 1
            # phi = sign(u-delta), rho = 0, hence eta = s = S.
            for mask in range(8):
                epsilon = sum(w[i] for i in range(3) if mask >> i & 1)
                if not (epsilon < delta and S > 2 * (1-delta) * epsilon):
                    continue
                retained = [u[i] for i in range(3) if not (mask >> i & 1)]
                bound = delta + delta * (S - 2 * (1-delta) * epsilon) / (
                    2 * delta * (1-epsilon) - S)
                assert max(retained) >= bound
                exceptions += 1
    for delta in (F(1, 4), F(1, 2), F(3, 4)):
        for tau in (F(i, 8) for i in range(1, 8)):
            if not delta < tau < 1:
                continue
            for q in (delta * F(i, 4) for i in range(5)):
                wt = (delta - q) / tau
                w0 = 1 - q - wt
                assert w0 >= 0 and wt >= 0
                S = w0 * delta + wt * (tau-delta) + q * (1-delta)
                lower = (tau*S - 2*delta*(tau-delta))/(2*delta*(1-tau))
                assert lower == q
                sharp += 1
    return profiles, tails, exceptions, sharp


def main():
    counts = density_checks()
    scales = [F(1, 512), F(1, 128), F(1, 32), F(1, 8), F(1, 4),
              F(3, 8), F(1, 2)]
    frequencies = sorted({F(s, d) for d in range(1, 14) for s in range(d)})
    partition_cases = 0
    total_cells = 0
    for N in range(1, 97):
        for theta in frequencies:
            for scale in scales:
                total_cells += check_phase_case(N, theta, scale)
                partition_cases += 1
    for N in (127,128,129,255,256,257,511,512,513,1023,1024,1025):
        for d in (257,997):
            for s in (1,d//3,d//2,d-1):
                for scale in scales:
                    total_cells += check_phase_case(N, F(s,d), scale)
                    partition_cases += 1
    print(f"PASS: {counts[0]} exact density profiles; {counts[1]} tail bounds")
    print(f"PASS: {counts[2]} exact exceptional-set bounds; {counts[3]} sharp-tail equalities")
    print(f"PASS: {partition_cases} phase partitions, covering {total_cells} cells")
    print("Coverage, length, circular approximation and half-angle checks are exact.")
    print("Complex disc distances were checked with floating-point tolerance 1e-12.")


if __name__ == "__main__":
    main()
