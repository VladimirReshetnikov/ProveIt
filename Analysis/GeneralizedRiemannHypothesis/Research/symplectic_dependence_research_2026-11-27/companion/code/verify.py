#!/usr/bin/env python3
"""Independent exact finite-field checks for the many-frame critical profile.

Only Python's standard library is used. GF(4) is F_2[x]/(x^2+x+1),
not arithmetic modulo four. Enumeration creates actual vectors and matrices;
the analytic formulas never generate the enumerated probability laws.
"""

from collections import Counter
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json


class Field:
    def __init__(self, q):
        assert q in (2, 3, 4, 5)
        self.q = q
        self.add = [[(a ^ b) if q == 4 else (a + b) % q
                     for b in range(q)] for a in range(q)]
        self.neg = [a if q == 4 else (-a) % q for a in range(q)]
        self.mul = [[self._mul(a, b) for b in range(q)] for a in range(q)]
        self.inv = [0] + [next(b for b in range(1, q)
                                if self.mul[a][b] == 1)
                          for a in range(1, q)]

    def _mul(self, a, b):
        if self.q != 4:
            return (a * b) % self.q
        ans = 0
        while b:
            if b & 1:
                ans ^= a
            b >>= 1
            a <<= 1
            if a & 4:
                a ^= 7
        return ans

    def rank(self, matrix):
        a = [list(row) for row in matrix]
        if not a:
            return 0
        nr, nc, r = len(a), len(a[0]), 0
        for c in range(nc):
            pivot = next((i for i in range(r, nr) if a[i][c]), None)
            if pivot is None:
                continue
            a[r], a[pivot] = a[pivot], a[r]
            inv = self.inv[a[r][c]]
            a[r] = [self.mul[inv][x] for x in a[r]]
            for i in range(nr):
                if i == r or not a[i][c]:
                    continue
                scale = self.neg[a[i][c]]
                a[i] = [self.add[x][self.mul[scale][y]]
                        for x, y in zip(a[i], a[r])]
            r += 1
            if r == nr:
                break
        return r

    def pairing(self, u, v):
        ans = 0
        for i in range(0, len(u), 2):
            ans = self.add[ans][self.mul[u[i]][v[i + 1]]]
            ans = self.add[ans][self.neg[self.mul[u[i + 1]][v[i]]]]
        return ans


def qpow(q, e):
    return F(q ** e) if e >= 0 else F(1, q ** (-e))


def eta(q, n):
    assert n >= 0
    ans = F(1)
    for j in range(1, n + 1):
        ans *= 1 - qpow(q, -2 * j)
    return ans


def gamma(q, n):
    assert n >= 0
    ans = F(1)
    for j in range(1, n + 1):
        ans *= 1 - qpow(q, -j)
    return ans


def gaussian(q, n, k):
    if not 0 <= k <= n:
        return F(0)
    ans = F(1)
    for j in range(k):
        ans *= F(q ** (n - j) - 1, q ** (k - j) - 1)
    assert ans.denominator == 1
    return ans


def gram_density(q, n, D, k):
    assert (D - k) % 2 == 0
    c = D - 2 * n
    low = max(0, (c + k) // 2)
    ans = F(0)
    for t in range(low, k + 1):
        ans += (gaussian(q, k, t) * qpow(q, c * t - t * (t + 1) // 2)
                / eta(q, t - (c + k) // 2))
    return eta(q, n) * ans


def alternating_law(q, D, k):
    if not 0 <= k <= D or (D - k) % 2:
        return F(0)
    return (qpow(q, -k * (k - 1) // 2) * gamma(q, D)
            / (gamma(q, k) * eta(q, (D - k) // 2)))


def exact_distance(q, n, D):
    d, eps = divmod(D, 2)
    if d <= n:
        return alternating_law(q, D, eps) * (1 - eta(q, n) / eta(q, n - d))
    return sum((alternating_law(q, D, k)
                for k in range(eps, D - 2 * n, 2)), F(0))


def alternating_from_upper(field, D, upper):
    a = [[0] * D for _ in range(D)]
    t = 0
    for i in range(D):
        for j in range(i + 1, D):
            a[i][j] = upper[t]
            a[j][i] = field.neg[upper[t]]
            t += 1
    return a


def check_gram_case(q, n, D):
    field = Field(q)
    N = 2 * n
    vectors = list(product(range(q), repeat=N))
    pairing = [[field.pairing(u, v) for v in vectors] for u in vectors]
    hist = Counter()
    for columns in product(range(len(vectors)), repeat=D):
        key = tuple(pairing[columns[i]][columns[j]]
                    for i in range(D) for j in range(i + 1, D))
        hist[key] += 1
    M = D * (D - 1) // 2
    nx, nt = q ** (N * D), q ** M
    assert sum(hist.values()) == nx
    uniform_nullity = Counter()
    gram_nullity = Counter()
    difference = F(0)
    densities = {}
    for upper in product(range(q), repeat=M):
        k = D - field.rank(alternating_from_upper(field, D, upper))
        count = hist[upper]
        actual_density = F(count * nt, nx)
        predicted = gram_density(q, n, D, k)
        assert actual_density == predicted, (q, n, D, k, upper, actual_density, predicted)
        uniform_nullity[k] += 1
        gram_nullity[k] += count
        densities[k] = predicted
        difference += abs(F(count, nx) - F(1, nt))
    for k, count in uniform_nullity.items():
        assert F(count, nt) == alternating_law(q, D, k)
        if k >= 2 and k >= D - N:
            assert densities[k] > 1
    tv = difference / 2
    assert tv == exact_distance(q, n, D)
    return {
        "q": q, "ambient_dimension": N, "total_dimension": D,
        "vector_arrays_enumerated": nx, "gram_fibers_checked": nt,
        "tv": str(tv), "tv_decimal": float(tv),
        "likelihood_by_nullity": {str(k): str(v) for k, v in sorted(densities.items())},
        "uniform_nullity_law": {str(k): str(F(v, nt))
                                for k, v in sorted(uniform_nullity.items())},
        "gram_nullity_law": {str(k): str(F(v, nx))
                             for k, v in sorted(gram_nullity.items())},
    }


def block_setup(field, sizes, ranks):
    assert len(sizes) == len(ranks)
    D = sum(sizes)
    block = []
    fixed = [[0] * D for _ in range(D)]
    start = 0
    for i, (d, rank) in enumerate(zip(sizes, ranks)):
        assert rank % 2 == 0 and rank <= d
        block.extend([i] * d)
        for j in range(0, rank, 2):
            fixed[start + j][start + j + 1] = 1
            fixed[start + j + 1][start + j] = field.neg[1]
        start += d
    return block, fixed


def check_bordering(q, sizes, ranks):
    field = Field(q)
    D = sum(sizes)
    block, fixed = block_setup(field, sizes, ranks)
    rows = []
    n_good_matrices = n_columns = 0
    for m in range(D):
        same = [i for i in range(m) if block[i] == block[m]]
        free_new = [i for i in range(m) if block[i] != block[m]]
        free_old = [(i, j) for i in range(m) for j in range(i + 1, m)
                    if block[i] != block[j]]
        bad = total = good = 0
        for labels in product(range(q), repeat=len(free_old)):
            a = [row[:m] for row in fixed[:m]]
            for (i, j), v in zip(free_old, labels):
                a[i][j], a[j][i] = v, field.neg[v]
            total += 1
            if field.rank([[a[i][j] for j in same] for i in range(m)]) < len(same):
                bad += 1
                continue
            good += 1
            k = m - field.rank(a)
            hist = Counter()
            for newlabels in product(range(q), repeat=len(free_new)):
                z = [fixed[i][m] for i in range(m)]
                for i, v in zip(free_new, newlabels):
                    z[i] = v
                enlarged = [a[i] + [z[i]] for i in range(m)]
                enlarged.append([field.neg[v] for v in z] + [0])
                newk = m + 1 - field.rank(enlarged)
                hist[newk] += 1
                n_columns += 1
            samples = q ** len(free_new)
            assert F(hist[k + 1], samples) == qpow(q, -k), (q, sizes, ranks, m, a)
            assert F(hist[k - 1], samples) == 1 - qpow(q, -k)
            assert sum(hist.values()) == hist[k + 1] + hist[k - 1]
        union_bound = (q ** len(same) - 1) * qpow(q, -(m - len(same)))
        assert F(bad, total) <= union_bound
        n_good_matrices += good
        rows.append({"prefix_dimension": m, "matrices": total,
                     "bad_matrices": bad, "good_matrices": good,
                     "bad_probability": str(F(bad, total)),
                     "kernel_union_bound": str(union_bound)})
    return {"q": q, "block_sizes": sizes, "block_ranks": ranks,
            "good_matrices_checked": n_good_matrices,
            "border_columns_enumerated": n_columns, "prefixes": rows}


def check_markov_coupling(q, max_start=24, max_steps=60):
    # Exact recurrence for the upper nullity chain killed on first hitting 1.
    r, lam = F(6, 5), F(37, 40)
    comparisons = 0
    worst_ratio = F(0)
    for m in range(2, max_start + 1):
        law = {m: F(1)}
        for L in range(max_steps + 1):
            survival = sum(law.values(), F(0))
            bound = r ** (m - 2) * lam ** L
            assert survival <= bound
            if bound:
                worst_ratio = max(worst_ratio, survival / bound)
            comparisons += 1
            new = Counter()
            for k, probability in law.items():
                up = qpow(q, -k)
                new[k + 1] += probability * up
                if k - 1 >= 2:
                    new[k - 1] += probability * (1 - up)
            law = new
    return {"q": q, "exact_survival_bound_checks": comparisons,
            "max_survival_over_bound": str(worst_ratio)}


def check_conditioning(q, n, sizes, ranks):
    field = Field(q)
    N, D = 2 * n, sum(sizes)
    block, fixed = block_setup(field, sizes, ranks)
    vectors = list(product(range(q), repeat=N))
    pairing = [[field.pairing(u, v) for v in vectors] for u in vectors]
    constrained = [(i, j) for i in range(D) for j in range(i + 1, D)
                   if block[i] == block[j]]
    cross = [(i, j) for i in range(D) for j in range(i + 1, D)
             if block[i] != block[j]]
    maps, frames = Counter(), Counter()
    for columns in product(range(len(vectors)), repeat=D):
        if any(pairing[columns[i]][columns[j]] != fixed[i][j]
               for i, j in constrained):
            continue
        labels = tuple(pairing[columns[i]][columns[j]] for i, j in cross)
        maps[labels] += 1
        offset, injective = 0, True
        for size in sizes:
            matrix = [[vectors[columns[j]][i]
                       for j in range(offset, offset + size)] for i in range(N)]
            injective = injective and field.rank(matrix) == size
            offset += size
        if injective:
            frames[labels] += 1
    map_total, frame_total, targets = sum(maps.values()), sum(frames.values()), q ** len(cross)
    normalizer = F(1)
    for d, rank in zip(sizes, ranks):
        normalizer *= gram_density(q, n, d, d - rank)
    expected_total = qpow(q, N * D - len(constrained)) * normalizer
    assert map_total == expected_total
    p_to_q = pprime_to_q = p_to_pprime = F(0)
    for labels in product(range(q), repeat=len(cross)):
        a = [row[:] for row in fixed]
        for (i, j), value in zip(cross, labels):
            a[i][j], a[j][i] = value, field.neg[value]
        k = D - field.rank(a)
        actual = F(maps[labels] * targets, map_total)
        assert actual == gram_density(q, n, D, k) / normalizer
        p, pp, u = F(frames[labels], frame_total), F(maps[labels], map_total), F(1, targets)
        p_to_q += abs(p - u)
        pprime_to_q += abs(pp - u)
        p_to_pprime += abs(p - pp)
    p_to_q /= 2
    pprime_to_q /= 2
    p_to_pprime /= 2
    lost_mass = 1 - F(frame_total, map_total)
    assert p_to_pprime <= lost_mass
    return {"q": q, "ambient_dimension": N, "block_sizes": sizes,
            "block_ranks": ranks, "arrays_enumerated": q ** (N * D),
            "conditioned_maps": map_total, "isometric_frame_tuples": frame_total,
            "target_cross_matrices": targets, "normalizer_Z": str(normalizer),
            "tv_frames_vs_uniform": str(p_to_q), "tv_gram_conditioned_vs_uniform": str(pprime_to_q),
            "tv_injectivity_correction": str(p_to_pprime),
            "conditional_noninjective_probability": str(lost_mass)}


def main():
    gram_cases = [(2, 1, d) for d in range(1, 7)]
    gram_cases += [(2, 2, d) for d in (2, 3, 4, 5)]
    gram_cases += [(q, 1, d) for q in (3, 4, 5) for d in (3, 4)]
    gram = []
    for case in gram_cases:
        result = check_gram_case(*case)
        gram.append(result)
        print("Gram", case, "TV", result["tv"], flush=True)
    bordering = [
        check_bordering(2, [2, 2, 2], [0, 2, 0]),
        check_bordering(2, [2, 2, 1], [2, 0, 0]),
        check_bordering(2, [3, 2], [0, 2]),
        check_bordering(3, [3, 2], [2, 0]),
        check_bordering(3, [2, 2, 1], [0, 2, 0]),
        check_bordering(4, [2, 2], [0, 2]),
        check_bordering(4, [2, 1, 1], [2, 0, 0]),
        check_bordering(5, [2, 1, 1], [0, 0, 0]),
    ]
    print("Bordering cases:", len(bordering), flush=True)
    markov = [check_markov_coupling(q) for q in (2, 3, 4, 5)]
    conditioning = [check_conditioning(2, 2, [2, 2], ranks)
                    for ranks in ([0, 0], [0, 2], [2, 2])]
    conditioning.append(check_conditioning(2, 2, [2, 1, 1], [0, 0, 0]))
    summary = {
        "status": "all checks passed",
        "arithmetic": "exact rational probabilities; actual GF(2), GF(3), GF(4), GF(5) enumeration",
        "gf4_definition": "F_2[x]/(x^2+x+1)",
        "gram_cases": len(gram),
        "vector_arrays_enumerated": sum(r["vector_arrays_enumerated"] for r in gram),
        "gram_fibers_checked": sum(r["gram_fibers_checked"] for r in gram),
        "bordering_cases": len(bordering),
        "good_prefix_matrices_checked": sum(r["good_matrices_checked"] for r in bordering),
        "border_columns_enumerated": sum(r["border_columns_enumerated"] for r in bordering),
        "exact_markov_bound_checks": sum(r["exact_survival_bound_checks"] for r in markov),
        "conditioning_cases": len(conditioning),
        "conditioning_arrays_enumerated": sum(r["arrays_enumerated"] for r in conditioning),
        "isometric_frame_tuples_checked": sum(r["isometric_frame_tuples"] for r in conditioning),
    }
    output = Path(__file__).resolve().parent.parent / "results"
    output.mkdir(exist_ok=True)
    (output / "verification.json").write_text(json.dumps({"summary": summary,
        "gram": gram, "bordering": bordering, "markov": markov,
        "conditioning": conditioning}, indent=2) + "\n")
    (output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
