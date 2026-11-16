"""Exact bounded border-closure certificates and rational zero enumeration.

This is reference code, not an iPRA proof checker. All loops have explicit
input-derived finite bounds. Failed closure means only that the supplied
degree caps did not establish closure.
"""
from fractions import Fraction as Q
from itertools import product
from math import lcm, prod


def clean(p):
    return {tuple(a): Q(c) for a, c in p.items() if c}


def add(p, q):
    out = dict(p)
    for a, c in q.items():
        out[a] = out.get(a, Q(0)) + c
    return clean(out)


def scale(c, p):
    return clean({a: c * b for a, b in p.items()})


def mulmon(a, p):
    return {tuple(x + y for x, y in zip(a, b)): c for b, c in p.items()}


def mons(r, d):
    if d < 0:
        return []
    return sorted((a for a in product(range(d + 1), repeat=r) if sum(a) <= d),
                  key=lambda a: (sum(a), tuple(-x for x in a)))


def evaluate(p, xs):
    return sum((c * prod(x ** e for x, e in zip(xs, a)) for a, c in p.items()), Q(0))


def linear_solve(A, b):
    """Return a solution or a separating row u with uA=0 and ub!=0."""
    m, n = len(A), len(A[0]) if A else 0
    R = [[Q(x) for x in row] + [Q(b[i])] for i, row in enumerate(A)]
    U = [[Q(i == j) for j in range(m)] for i in range(m)]
    pivots, row = [], 0
    for col in range(n):
        choices = [i for i in range(row, m) if R[i][col]]
        if not choices:
            continue
        j = choices[0]
        R[row], R[j] = R[j], R[row]
        U[row], U[j] = U[j], U[row]
        t = R[row][col]
        R[row] = [v / t for v in R[row]]
        U[row] = [v / t for v in U[row]]
        for i in range(m):
            if i != row:
                t = R[i][col]
                R[i] = [a - t * c for a, c in zip(R[i], R[row])]
                U[i] = [a - t * c for a, c in zip(U[i], U[row])]
        pivots.append((row, col))
        row += 1
        if row == m:
            break
    for i in range(m):
        if not any(R[i][:n]) and R[i][n]:
            u = U[i]
            assert all(sum(u[k] * A[k][j] for k in range(m)) == 0 for j in range(n))
            assert sum(u[k] * b[k] for k in range(m)) != 0
            return {"success": False, "separator": u}
    x = [Q(0)] * n
    for i, j in pivots:
        x[j] = R[i][n]
    assert all(sum(A[i][j] * x[j] for j in range(n)) == b[i] for i in range(m))
    return {"success": True, "solution": x}


def produce(polynomials, r, d, D):
    if r < 1 or d < 0 or D < d + 1:
        return {"accepted": False, "reason": "invalid caps"}
    fs = [clean(f) for f in polynomials]
    B, ambient = mons(r, d), mons(r, D)
    if any(len(a) != r for f in fs for a in f):
        return {"accepted": False, "reason": "invalid arity"}
    mults, columns = [], [{b: Q(1)} for b in B]
    for i, f in enumerate(fs):
        degree = max((sum(a) for a in f), default=0)
        for a in mons(r, D - degree):
            mults.append((i, a))
            columns.append(mulmon(a, f))
    A = [[p.get(a, Q(0)) for p in columns] for a in ambient]
    border = mons(r, d + 1)[len(B):]
    reductions = {}
    for b in border:
        result = linear_solve(A, [Q(a == b) for a in ambient])
        if not result["success"]:
            return {"accepted": False, "reason": "closure failed", "failed_monomial": b,
                    "ambient": ambient, "separator": result["separator"]}
        reductions[b] = result["solution"]
    n = len(B)
    M = [[[Q(0)] * n for _ in range(n)] for _ in range(r)]
    witnesses = {}
    for k in range(r):
        for j, b in enumerate(B):
            a = tuple(b[t] + int(t == k) for t in range(r))
            if a in B:
                M[k][B.index(a)][j] = Q(1)
                witnesses[k, j] = [dict() for _ in fs]
            else:
                coeffs = reductions[a]
                for i in range(n):
                    M[k][i][j] = coeffs[i]
                hs = [dict() for _ in fs]
                for c, (i, exponent) in zip(coeffs[n:], mults):
                    hs[i][exponent] = hs[i].get(exponent, Q(0)) + c
                witnesses[k, j] = [clean(h) for h in hs]
    certificate = {"accepted": True, "r": r, "d": d, "D": D, "polynomials": fs,
                   "B": B, "matrices": M, "witnesses": witnesses}
    check_certificate(certificate)
    return certificate


def check_certificate(cert):
    fs, B, M, r = cert["polynomials"], cert["B"], cert["matrices"], cert["r"]
    assert tuple([0] * r) in B
    for k in range(r):
        for j, b in enumerate(B):
            a = tuple(b[t] + int(t == k) for t in range(r))
            lhs = {a: Q(1)}
            for i, base in enumerate(B):
                lhs = add(lhs, {base: -M[k][i][j]})
            rhs = {}
            for h, f in zip(cert["witnesses"][k, j], fs):
                for mon, c in h.items():
                    rhs = add(rhs, scale(c, mulmon(mon, f)))
            assert clean(lhs) == clean(rhs), (k, j, lhs, rhs)


def enumerate_rational_zeros(cert):
    check_certificate(cert)
    M, n = cert["matrices"], len(cert["B"])
    deltas = [lcm(*(x.denominator for row in mat for x in row)) for mat in M]
    ranges = [max(sum(abs(int(delta * mat[i][j])) for i in range(n)) for j in range(n))
              for mat, delta in zip(M, deltas)]
    roots = []
    for zs in product(*(range(-R, R + 1) for R in ranges)):
        p = tuple(Q(z, delta) for z, delta in zip(zs, deltas))
        if all(evaluate(f, p) == 0 for f in cert["polynomials"]):
            roots.append(p)
    return {"deltas": deltas, "ranges": ranges, "candidate_count": prod(2 * R + 1 for R in ranges),
            "roots": roots}


def commute(M, N):
    n = len(M)
    return all(sum(M[i][k] * N[k][j] for k in range(n)) ==
               sum(N[i][k] * M[k][j] for k in range(n))
               for i in range(n) for j in range(n))


def summarize(cert):
    if not cert["accepted"]:
        return {k: v for k, v in cert.items() if k not in ("ambient", "separator")}
    out = enumerate_rational_zeros(cert)
    out["roots"] = [[str(x) for x in p] for p in out["roots"]]
    out.update(accepted=True, d=cert["d"], D=cert["D"], spanning_size=len(cert["B"]),
               matrices_commute=all(commute(M, N) for M in cert["matrices"] for N in cert["matrices"]))
    return out


def main():
    import json
    from pathlib import Path
    hidden = [{(1, 1): 1, (0, 0): -1}, {(2, 0): 1, (0, 1): -1}]
    rational = [
        {(2, 0): 2, (1, 1): 4, (0, 2): 2, (1, 0): -1, (0, 1): -1},
        {(2, 0): 3, (1, 1): -6, (0, 2): 3, (1, 0): -1, (0, 1): 1},
        {(2, 0): 1, (0, 2): -1},
    ]
    irrational = [{(2, 0): 1, (0, 0): -2}, {(0, 1): 1, (1, 0): -1}]
    noncommuting = [{(2, 0): 1, (0, 0): -1}, {(0, 1): 1, (1, 0): -1}]
    cases = [("hidden_degree_insufficient", hidden, 1, 2),
             ("hidden_degree_sufficient", hidden, 1, 3),
             ("three_rational_points", rational, 1, 2),
             ("redundant_spanning_family", rational, 2, 3),
             ("noncommuting_redundant_certificate", noncommuting, 1, 2),
             ("finite_algebra_no_rational_points", irrational, 1, 2)]
    report = {name: summarize(produce(fs, 2, d, D)) for name, fs, d, D in cases}
    assert report["hidden_degree_insufficient"]["accepted"] is False
    assert report["hidden_degree_sufficient"]["roots"] == [["1", "1"]]
    expected = [["0", "0"], ["1/6", "-1/6"], ["1/4", "1/4"]]
    assert report["three_rational_points"]["roots"] == expected
    assert report["redundant_spanning_family"]["roots"] == expected
    assert report["noncommuting_redundant_certificate"]["roots"] == [["-1", "-1"], ["1", "1"]]
    assert report["noncommuting_redundant_certificate"]["matrices_commute"] is False
    assert report["finite_algebra_no_rational_points"]["roots"] == []
    # Linear solver checks cover success and a verifiable dual failure certificate.
    assert linear_solve([[1, 2], [2, 4]], [3, 6])["success"]
    assert not linear_solve([[1, 2], [2, 4]], [3, 7])["success"]
    result = json.dumps(report, indent=2) + "\n"
    print(result, end="")
    (Path(__file__).resolve().parents[1] / "validation" / "macaulay_checks.json").write_text(result)


if __name__ == "__main__":
    main()
