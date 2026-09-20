#!/usr/bin/env python3
"""Exhaustive tests; no floating point and no external packages.

python code/verify.py --max-n 8 --independent-through 7
Natural labellings are not isomorphism classes. Every isomorphism class occurs.
"""
from __future__ import annotations
import argparse, json, itertools, time
from pathlib import Path
from fractions import Fraction
from lattice_tools import *


def verify_lattice(L: Lattice, independent: bool) -> dict:
    labels = principal_labels(L)
    congruences = all_congruences(L, labels)
    q, count = len(set(labels.values())), len(congruences)
    assert count <= 1 << q
    assert q <= len(L.ji) == L.n - 1 - len(L.jr)
    assert all(is_congruence(L, p) for p in congruences)
    if independent:
        brute = {p for p in all_partitions(L.n) if is_congruence(L, p)}
        assert brute == congruences, (L.down, 'independent mismatch')
    fans, equality, mixed, distinct = 0, 0, 0, 0
    profiles = set()
    for u, covers in enumerate(L.upper):
        # Every subset, not only the full cover set.
        for k in range(3, len(covers)+1):
            for selected in itertools.combinations(covers, k):
                fans += 1
                alpha = [principal_congruence(L, u, a) for a in selected]
                r = len(set(alpha))
                profiles.add((k, r))
                h = {L.join[a][b] for a, b in itertools.combinations(selected, 2)}
                assert h.issubset(set(L.jr))
                assert len(L.jr) >= r
                assert q <= L.n - 1 - len(L.jr) - k + r
                assert count <= 1 << (L.n - 1 - k)
                # The join-collision identities, checked directly.
                pairs = list(itertools.combinations(range(k), 2))
                for (i,j), (s,t) in itertools.combinations(pairs,2):
                    if L.join[selected[i]][selected[j]] != L.join[selected[s]][selected[t]]:
                        continue
                    overlap = {i,j} & {s,t}
                    if overlap:
                        common = overlap.pop()
                        a, b = tuple(({i,j}|{s,t}) - {common})
                        assert alpha[a] == alpha[b]
                        assert partition_le(alpha[a], alpha[common])
                    else:
                        assert len({alpha[i],alpha[j],alpha[s],alpha[t]}) == 1
                # Refined fan-profile bound.
                unique = list(dict.fromkeys(alpha))
                ideals = 0
                for mask in range(1 << r):
                    if all(not(mask >> i & 1) or all(
                        not partition_le(unique[j],unique[i]) or mask >> j & 1
                        for j in range(r)) for i in range(r)):
                        ideals += 1
                assert count <= ideals * (1 << (len(L.ji)-k))
                is_eq = count == 1 << (L.n - 1 - k)
                assert is_eq == is_chain_glued_Mk(L, u, k), (L.down, u, k)
                if not is_eq:
                    assert L.n >= k + 3
                    assert count <= 3 * (1 << (L.n - k - 3))
                equality += is_eq
                mixed += r == 2
                distinct += r >= 3
    # Dual fan bound checked directly, too.
    for covers in L.lower:
        d = len(covers)
        if d >= 3:
            assert count <= 1 << (L.n - 1 - d)
    density = Fraction(count, 1 << (L.n-1))
    t = 0
    while Fraction(1, 1 << (t+1)) >= density:
        t += 1
    assert len(L.jr) <= t and len(L.mr) <= t
    assert len(L.skeleton) <= 2*t*(max(2,t)+1)
    return dict(congruences=count, fans=fans, equality_fans=equality,
                r2_fans=mixed, r_ge3_fans=distinct, profiles=sorted(profiles))


def run(n: int, independent_through: int) -> dict:
    start = time.monotonic()
    totals = dict(n=n, natural_posets=0, natural_lattices=0, congruences=0,
                  fans=0, equality_fans=0, r2_fans=0, r_ge3_fans=0,
                  independent_lattices=0)
    max_density = {}
    for L, index in bounded_lattices(n):
        totals['natural_lattices'] += 1
        result = verify_lattice(L, n <= independent_through)
        totals['independent_lattices'] += n <= independent_through
        for key in ('congruences','fans','equality_fans','r2_fans','r_ge3_fans'):
            totals[key] += result[key]
        for k in range(3, max(map(len, L.upper),default=0)+1):
            max_density[k] = max(max_density.get(k,Fraction(0)),
                Fraction(result['congruences'],1 << (n-1)))
    # Independently count the underlying natural poset enumeration.
    totals['natural_posets'] = sum(1 for _ in natural_posets(max(n-2,0)))
    totals['max_density_by_fan_size'] = {str(k):str(v) for k,v in sorted(max_density.items())}
    totals['elapsed_seconds'] = round(time.monotonic()-start,3)
    totals['status'] = 'PASS'
    return totals


if __name__ == '__main__':
    if not __debug__:
        raise SystemExit('Run without -O: verification requires assertions.')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--min-n', type=int, default=1)
    parser.add_argument('--max-n', type=int, default=8)
    parser.add_argument('--independent-through', type=int, default=7)
    args = parser.parse_args()
    if not 1 <= args.min_n <= args.max_n:
        parser.error('Require 1 <= min-n <= max-n')
    root = Path(__file__).resolve().parents[1]
    for n in range(args.min_n, args.max_n+1):
        result = run(n,args.independent_through)
        (root/'data'/f'verification_n{n}.json').write_text(json.dumps(result,indent=2)+'\n')
        print(json.dumps(result),flush=True)
