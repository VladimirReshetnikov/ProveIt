#!/usr/bin/env python3
"""Exact, degree-bounded, integral monic elimination experiments.

No solver is used.  Each step deletes a coordinate with unit coefficient in
one residual, recording its unique integral restoration polynomial.
"""
import argparse
import json
import random
import hashlib
from pathlib import Path


def norm(p):
    return {tuple(m): c for m, c in p.items() if c}


def add(p, q, a=1):
    r = p.copy()
    for m, c in q.items():
        r[m] = r.get(m, 0) + a*c
        if not r[m]:
            del r[m]
    return r


def mul(p, q):
    r = {}
    for m, c in p.items():
        for n, d in q.items():
            k = tuple(sorted(m+n))
            r[k] = r.get(k, 0) + c*d
    return norm(r)


def deg(p):
    return max(map(len, p), default=-1)


def subst(p, v, f):
    r = {}
    powers = {0: {(): 1}, 1: f}
    for m, c in p.items():
        k = m.count(v)
        if not k:
            r[m] = r.get(m, 0)+c
            continue
        for j in range(2, k+1):
            if j not in powers:
                powers[j] = mul(powers[j-1], f)
        rest = tuple(i for i in m if i != v)
        r = add(r, mul({rest: c}, powers[k]))
    return norm(r)


def serial(p):
    return [[c, list(m)] for m, c in sorted(p.items())]


def scan(rows, cap, maxterms=20000):
    uses = {}
    for ri, p in rows.items():
        for m in p:
            for v in set(m):
                uses.setdefault(v, set()).add(ri)
    candidates = []
    for ri, p in rows.items():
        for m, c in p.items():
            if len(m) != 1 or abs(c) != 1:
                continue
            v = m[0]
            if any(v in n for n in p if n != m):
                continue
            f = {n: -d*c for n, d in p.items() if n != m}
            fd = deg(f)
            # Sound conservative bound; exact cancellation can only help.
            if any(len(n)+n.count(v)*(fd-1)>cap
                   for rj in uses[v] if rj != ri for n in rows[rj]):
                continue
            changed = {rj: subst(rows[rj], v, f)
                       for rj in uses[v] if rj != ri}
            if any(deg(q)>cap or len(q)>maxterms for q in changed.values()):
                continue
            termdiff = sum(len(q)-len(rows[j]) for j, q in changed.items())-len(p)
            cubicdiff = sum(sum(len(n)==cap for n in q)-sum(len(n)==cap for n in rows[j])
                            for j, q in changed.items())
            candidates.append((termdiff, cubicdiff, len(uses[v]), ri, v, f, changed))
    return candidates


def optimize(data, cap, seed, mode):
    rows = {i: {tuple(m): c for c, m in r['terms']} for i, r in enumerate(data['residuals'])}
    steps = []
    rng = random.Random(seed)
    while True:
        candidates = scan(rows, cap)
        if not candidates:
            break
        if mode == 0:
            candidates.sort(key=lambda c: (c[0], c[1], c[2], c[4]))
            best = candidates[0]
        elif mode == 1:
            candidates.sort(key=lambda c: (c[1], c[0], c[2], c[4]))
            best = candidates[0]
        elif mode == 2:
            candidates.sort(key=lambda c: (c[2], c[0], c[1], c[4]))
            best = candidates[0]
        else:
            candidates.sort(key=lambda c: (c[0]+rng.random()*max(3, abs(c[0])*0.6), c[2]))
            best = candidates[rng.randrange(min(4, len(candidates)))]
        _, _, _, ri, v, f, changed = best
        steps.append({'row': ri, 'variable': v, 'coefficient': rows[ri][(v,)],
                      'restoration': serial(f)})
        del rows[ri]
        rows.update(changed)
    return rows, steps


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('source', type=Path)
    ap.add_argument('--cap', type=int, default=3)
    ap.add_argument('--trials', type=int, default=10)
    ap.add_argument('--start-trial', type=int, default=0)
    ap.add_argument('--out', type=Path, default=Path('degree_search_result.json'))
    a = ap.parse_args()
    data = json.loads(a.source.read_text())
    best = None
    for trial in range(a.start_trial, a.start_trial+a.trials):
        rows, steps = optimize(data, a.cap, trial, trial if trial < 3 else 3)
        key = (-len(steps), sum(map(len, rows.values())), max(abs(c) for p in rows.values() for c in p.values()))
        if best is None or key < best[0]:
            best = key, rows, steps
            out = {'source': str(a.source.resolve()),
                   'source_sha256': hashlib.sha256(a.source.read_bytes()).hexdigest(),
                   'cap': a.cap, 'trial': trial,
                   'variables_remaining': len(data['variables'])-len(steps),
                   'residuals_remaining': len(rows), 'residual_terms': key[1],
                   'residual_height': key[2], 'steps': steps,
                   'rows': [{'source_row': i, 'terms': serial(p)} for i, p in sorted(rows.items())]}
            a.out.parent.mkdir(parents=True, exist_ok=True)
            a.out.write_text(json.dumps(out, indent=2)+'\n')
            print(json.dumps({k: out[k] for k in ['trial','cap','variables_remaining','residuals_remaining','residual_terms','residual_height']}), flush=True)


if __name__ == '__main__':
    main()
