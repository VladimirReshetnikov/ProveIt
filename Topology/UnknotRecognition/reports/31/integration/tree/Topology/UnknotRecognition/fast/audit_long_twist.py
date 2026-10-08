"""Independent adversarial checks of the exact one-run recurrence.

This script does not call the tail implementation. It independently constructs
the recurrence formulas and compares them with the existing, unmodified macro builder and small crossing
cubes, and brute-forces the selection sets for the signature certificate.
"""
from __future__ import annotations
from collections import Counter, defaultdict
from pathlib import Path
import json
import random
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT))
from fastunknot.twist.core import Run, homology, components
from fastunknot.twist.reference import cube_homology


def predicted(seed, sign, a, b, m0, m):
    delta = m-m0
    out = defaultdict(int)
    h0 = b+1 if sign > 0 else a-2
    dim = seed['chain_dimensions'][h0]
    eta = dim-2*seed['boundary_ranks'][h0]
    assert eta >= 0
    if sign > 0:
        for h, r in seed['by_degree'].items():
            out[h if h <= b+1 else h+delta] += r
        for h in range(b+2, a+m):
            out[h] += eta
    else:
        for h, r in seed['by_degree'].items():
            out[h-delta if h <= a-2 else h] += r
        for h in range(b-m+1, a-1):
            out[h] += eta
    return {h:r for h,r in out.items() if r}, eta


def signature_bound(strands, runs):
    n = sum(abs(r.exponent) for r in runs)
    ranks = []
    for sign in (-1, 1):
        counts = Counter()
        for r in runs:
            if r.exponent*sign > 0:
                counts[r.generator] += abs(r.exponent)
        best = 0
        for subset in range(1 << (strands-1)):
            selected = [i+1 for i in range(strands-1) if subset >> i & 1]
            if any(y-x == 1 for x,y in zip(selected, selected[1:])):
                continue
            best = max(best, sum(max(counts[i]-1, 0) for i in selected))
        ranks.append(best)
    return max(0, 2*max(ranks)-(n-strands+1))


def main():
    rng = random.Random(20261008)
    cases = []
    # Explicit empty, adjacent-opposite, nonadjacent and unused-strand contexts.
    contexts = [(b, []) for b in range(2, 6)]
    for b in range(2, 6):
        for _ in range(25):
            left = rng.randrange(5)
            seq = []
            while left:
                k = rng.randint(1, min(2,left))
                seq.append(Run(rng.randrange(1,b), rng.choice((-1,1))*k))
                left -= k
            contexts.append((b,seq))
    macro_count = cube_count = knots = unknot_checks = sig_hits = 0
    for strands, context in contexts:
        a = -sum(-r.exponent for r in context if r.exponent < 0)
        b = sum(r.exponent for r in context if r.exponent > 0)
        m0 = b-a+2
        at = rng.randrange(len(context)+1)
        generator = rng.randrange(1,strands)
        for sign in (-1,1):
            def make(m):
                return context[:at]+[Run(generator,sign*m)]+context[at:]
            seed = homology(strands,make(m0),check_d2=True)
            for delta in (0,1,2,5):
                m = m0+delta
                expected,eta = predicted(seed,sign,a,b,m0,m)
                got = homology(strands,make(m),check_d2=True)
                macro_count += 1
                assert expected == got['by_degree'], (strands,make(m),expected,got)
                assert got['reduced_rank'] == seed['reduced_rank']+eta*delta
                ncomp = components(strands,make(m))
                if ncomp == 1:
                    knots += 1
                    assert eta % 2 == 1, (strands,context,eta)
                    bound = signature_bound(strands,make(m))
                    if bound:
                        sig_hits += 1
                        assert got['reduced_rank'] > 1, (strands,make(m),bound)
                    if got['reduced_rank'] == 1:
                        unknot_checks += 1
                if (b-a <= 2 and delta in (0,1) and strands <= 4):
                    word = [r.generator*(1 if r.exponent>0 else -1)
                            for r in make(m) for _ in range(abs(r.exponent))]
                    cube = cube_homology(strands,word,max_crossings=10)
                    assert cube['by_degree'] == got['by_degree'], (strands,word,cube,got)
                    cube_count += 1
            cases.append({'strands':strands,'context':[(r.generator,r.exponent) for r in context],
                          'index':at,'generator':generator,'sign':sign,'threshold':m0,'eta':eta})
    result = {'seed':20261008,'contexts':len(contexts),'families':len(cases),
              'macro_comparisons':macro_count,'independent_cube_comparisons':cube_count,
              'one_component_members':knots,'signature_certificate_hits':sig_hits,
              'rank_one_members':unknot_checks,'all_checks_passed':True,'cases':cases}
    (Path(sys.argv[1])).write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k != 'cases'},sort_keys=True))


if __name__ == '__main__':
    main()
