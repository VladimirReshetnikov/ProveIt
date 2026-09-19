#!/usr/bin/env python3
"""Reproducible exact checks. These are tests, not a proof assistant certificate."""
from __future__ import annotations
import argparse
from collections import Counter
from itertools import combinations_with_replacement, product
import json
from pathlib import Path
import random
from ordinals import (Ord, ZERO, ONE, OMEGA, finite, omega_power, natural_sum,
    difference, evaluate_n, evaluate_s, evaluate_n_via_correction, evaluate_block,
    successor_exponent_block)


def sample_ordinals() -> list[Ord]:
    w2 = omega_power(finite(2))
    w3 = omega_power(finite(3))
    ww = omega_power(OMEGA)
    wwp = omega_power(OMEGA + ONE)
    bases = [ZERO, OMEGA, omega_power(ONE,2), w2, w2 + OMEGA,
             w3, ww, omega_power(OMEGA,2), ww + OMEGA, ww + w2,
             wwp, wwp + ww, omega_power(omega_power(OMEGA))]
    return sorted(set(b + finite(n) for b in bases for n in range(6)))


def finite_profile_below(a: tuple[int, tuple[int,...]],
                         b: tuple[int, tuple[int,...]]) -> bool:
    """Embedding order on bounded multiset profiles (article's finite audit)."""
    n, E = a
    m, F = b
    if n > m:
        return False
    surviving = sorted((x for x in E if x >= m), reverse=True)
    target = sorted(F, reverse=True)
    return len(surviving) <= len(target) and all(x <= y for x, y in zip(surviving, target))


def audit_finite_ranks(max_value: int = 5, capacity: int = 4) -> dict:
    states = []
    for n in range(max_value + 2):
        for k in range(capacity + 1):
            for E in combinations_with_replacement(range(n, max_value + 1), k):
                states.append((n,E))
    def expected(state):
        n,E = state
        return n * (capacity + 1) + sum(t - n + 1 for t in E)
    # A linear topological ordering, not obtained using the formula being tested:
    # epsilon first, then multiset size, then sum of entries.
    states.sort(key=lambda s: (s[0], len(s[1]), sum(s[1]), s[1]))
    ranks = {}
    edges = 0
    for index, state in enumerate(states):
        predecessors = [p for p in states[:index] if finite_profile_below(p, state)]
        edges += len(predecessors)
        rank = max((ranks[p] + 1 for p in predecessors), default=0)
        assert rank == expected(state), (state, rank, expected(state))
        ranks[state] = rank
    return {'max_entry': max_value, 'capacity': capacity, 'states': len(states),
            'strict_comparisons': edges, 'max_rank': max(ranks.values()),
            'formula': 'n*(K+1) + sum(t-n+1 for t in E)'}


def examples() -> list[dict]:
    w2 = omega_power(finite(2))
    w3 = omega_power(finite(3))
    ww = omega_power(OMEGA)
    wwp = omega_power(OMEGA+ONE)
    cases = [
        ('all zeros', ONE, [], ZERO),
        ('finite support: w^2, w, 3', ONE, [w2,OMEGA,finite(3)], natural_sum([w2,OMEGA,finite(3)])),
        ('constant 2', finite(3), [], omega_power(ONE,2)),
        ('unbounded finite tail', OMEGA, [], w2),
        ('one w above an unbounded finite tail', OMEGA, [OMEGA], w2+ONE),
        ('near exceptions w, w+3, w+7', OMEGA, [OMEGA,OMEGA+finite(3),OMEGA+finite(7)], w2+finite(13)),
        ('constant w', OMEGA+ONE, [], w2+OMEGA),
        ('constant w+1', OMEGA+finite(2), [], w2+omega_power(ONE,2)),
        ('constant w, with exceptional w^2+5', OMEGA+ONE, [w2+finite(5)], omega_power(finite(2),2)+OMEGA+finite(5)),
        ('cofinal below w^2, one w^2+4', w2, [w2+finite(4)], w3+finite(5)),
        ('cofinal below w^w', ww, [], ww),
        ('cofinal below w^w, two copies of w^w', ww, [ww,ww], omega_power(OMEGA,3)),
        ('constant w^w', ww+ONE, [], wwp),
        ('constant w^w+7', ww+finite(8), [], wwp+omega_power(ONE,7)),
        ('constant w^(w+1)', wwp+ONE, [], omega_power(OMEGA+finite(2))+OMEGA),
    ]
    out = []
    for label,e,es,expected in cases:
        n=evaluate_n(e,es)
        assert n==expected,(label,n,expected)
        out.append({'sequence':label,'epsilon':str(e),'prefix':[str(x) for x in es],
                    'S':str(evaluate_s(e,es)),'N':str(n)})
    return out


def verify(seed: int, random_trials: int) -> dict:
    rng=random.Random(seed)
    pool=sample_ordinals()
    thresholds=[e for e in pool if e]
    counters=Counter()
    for a in pool:
        for b in pool:
            assert a.natural(b)==b.natural(a)
            counters['natural_commutativity']+=1
            if a<=b:
                assert a+difference(a,b)==b
                counters['ordinal_difference']+=1
    # Exhaustive two-entry tests, including crossing omega, omega^2, omega^omega.
    small=[ZERO,ONE,finite(2),OMEGA,OMEGA+ONE,OMEGA+finite(2),
           omega_power(finite(2)),omega_power(OMEGA),omega_power(OMEGA)+ONE]
    for e in [ONE,finite(2),OMEGA,OMEGA+ONE,OMEGA+finite(2),
              omega_power(finite(2)),omega_power(OMEGA),omega_power(OMEGA)+ONE]:
        for es in product(small,repeat=2):
            assert evaluate_n(e,es)==evaluate_n_via_correction(e,es)
            assert evaluate_s(e,es)<=evaluate_n(e,es)
            counters['exhaustive_formula_agreement']+=1
    for _ in range(random_trials):
        e,f=sorted(rng.sample(thresholds,2)) if rng.randrange(2) else (rng.choice(thresholds),)*2
        length=rng.randrange(8)
        left=[];right=[]
        for __ in range(length):
            a,b=sorted(rng.choices(pool,k=2))
            left.append(a);right.append(b)
        a_val=evaluate_n(e,left); b_val=evaluate_n(f,right)
        expected_strict=(e<f or any(a<b and b>=e for a,b in zip(left,right)))
        assert a_val<=b_val,(e,f,left,right,a_val,b_val)
        assert (a_val<b_val)==expected_strict,(e,f,left,right,a_val,b_val)
        counters['comparable_profile_pairs']+=1
        counters['strict_profile_pairs' if expected_strict else 'equal_profile_pairs']+=1
        for threshold,es in [(e,left),(f,right)]:
            val=evaluate_n(threshold,es)
            assert val==evaluate_n_via_correction(threshold,es)
            assert evaluate_s(threshold,es)<=val<=evaluate_s(threshold,es).natural(OMEGA)
            counters['random_formula_agreement']+=1
            lam,n=threshold.split_finite()
            if lam and successor_exponent_block(lam):
                assert val==evaluate_block(lam,n,es)
                counters['independent_block_formula']+=1
            shuffled=list(es);rng.shuffle(shuffled)
            assert evaluate_n(threshold,shuffled+[ZERO]*3)==val
            counters['permutation_zero_invariance']+=1
    return {'status':'PASS','seed':seed,'random_trials':random_trials,
            'ordinal_pool_size':len(pool),'checks':dict(counters),
            'finite_rank_models':[audit_finite_ranks(m,k) for m,k in [(3,3),(5,4),(4,5)]],
            'examples':examples(),
            'limits':['Finite CNF notation below epsilon_0 only.',
                      'Thresholds and finite exceptional lists are assumed certified.',
                      'No numerical tests establish the transfinite theorem.',
                      'No Lean or other proof-assistant formalization is claimed.']}


def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--seed',type=int,default=20260919)
    parser.add_argument('--trials',type=int,default=10000)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    if args.trials<0:
        parser.error('--trials must be nonnegative')
    report=verify(args.seed,args.trials)
    text=json.dumps(report,indent=2)+'\n'
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(text,encoding='utf-8')
    print(text)

if __name__=='__main__':
    main()
