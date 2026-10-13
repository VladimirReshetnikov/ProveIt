#!/usr/bin/env python3
"""Finite theorem audits. Counts are executed roles, not distinct knot samples."""
from __future__ import annotations
import argparse
import itertools
import json
import platform
import random
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from cycleblocks import *
from tests.oracles import (brute_private, arbitrary_positive_optimum, literal_transport,
                           path_oracle, spanning_forests, cactus_counts)

LIMITS = Limits(max_block_rank=None, max_work=20_000_000)


def exhaustive():
    records = []
    total = arbitrary = 0
    t0 = time.perf_counter()
    for nr, nc, alphabet in [(2, 3, 3), (3, 3, 2), (3, 3, 3), (2, 4, 3), (3, 4, 2)]:
        count = 0; t = time.perf_counter()
        for word in itertools.product(range(alphabet), repeat=nr*nc):
            a = {r: {c: word[r*nc+c] for c in range(nc) if word[r*nc+c]} for r in range(nr)}
            expected = brute_private(a)
            for pre in (False, True):
                p = optimize_counts(a, prepeel=pre, limits=LIMITS)
                assert p['status'] == 'OPTIMAL_MATRIX_PLAN', p
                assert p['matched_weight'] == expected, (a, p, expected)
                assert verify_plan(a, p)
            if (nr,nc,alphabet) in [(2,3,3),(3,3,2)]:
                assert arbitrary_positive_optimum(a) == expected
                arbitrary += 1
            count += 1
        total += count
        records.append(dict(rows=nr, columns=nc, alphabet=alphabet, cases=count,
                            seconds=time.perf_counter()-t))
    return dict(families=records, matrix_roles=total, optimized_plans=2*total,
                arbitrary_positive_comparisons=arbitrary,
                seconds=time.perf_counter()-t0, discrepancies=0)


def randomized():
    rng = random.Random(20261012)
    records = dict(weighted=0, restricted=0, relabelled=0, transports=0,
                   forest_contexts=0, spanning_forests_tested=0, path_tables=0)
    t0 = time.perf_counter()
    for case in range(1000):
        nr,nc=4,5
        a = {r: {c: v for c in range(nc) if (v := rng.choices([0,1,2,7],[5,4,2,1])[0])}
             for r in range(nr)}
        w = {r: rng.randrange(11) + ((1 << 256) if case % 100 == 0 else 0) for r in a}
        p = optimize_counts(a,w,limits=LIMITS)
        assert p['status'] == 'OPTIMAL_MATRIX_PLAN' and p['matched_weight'] == brute_private(a,w)
        records['weighted'] += 1
        cir = transport_circuit(a,p,w)
        literal = literal_transport(a,p['cancellations'])
        assert expand_circuit(cir) == literal
        z={c:rng.randrange(-9,10) for c in range(nc)}
        assert evaluate_circuit(cir,z)=={r:sum(v*z[c] for c,v in row.items()) for r,row in literal.items()}
        records['transports'] += 1
        if case < 500:
            allowed = {(r,c) for r,row in a.items() for c,v in row.items() if v==1 and rng.randrange(2)}
            q = optimize_counts(a,w,allowed=allowed,limits=LIMITS)
            assert q['matched_weight']==brute_private(a,w,allowed)
            records['restricted'] += 1
            rr = rng.sample(range(100,200),nr); cc = rng.sample(range(300,400),nc)
            aa={rr[r]:{cc[c]:v for c,v in row.items()} for r,row in a.items()}
            ww={rr[r]:w[r] for r in a}
            q=optimize_counts(aa,ww,limits=LIMITS)
            assert q['matched_weight']==p['matched_weight']
            records['relabelled'] += 1
    # Closed walks in K4, retaining true multiplicities (including backtracking).
    edges={0:(0,1),1:(0,2),2:(0,3),3:(1,2),4:(1,3),5:(2,3)}
    lookup={frozenset(pair):c for c,pair in edges.items()}
    forests=list(spanning_forests(4,edges))
    witness=None
    for case in range(300):
        a={}
        for r in range(4):
            start=rng.randrange(4); walk=[start]
            for _ in range(rng.randrange(2,8)):
                walk.append(rng.choice([v for v in range(4) if v!=walk[-1]]))
            if walk[-1]!=start: walk.append(start)
            row={}
            for x,y in zip(walk,walk[1:]):
                c=lookup[frozenset((x,y))]; row[c]=row.get(c,0)+1
            a[r]=row
        w={r:rng.randrange(1,10) for r in a}
        p=optimize_counts(a,w,limits=LIMITS)
        f=deferred_forest(4,edges,a,p,weights=w)
        values=[]
        for tree in forests:
            aa={r:{c:v for c,v in row.items() if c not in tree} for r,row in a.items()}
            values.append(brute_private(aa,w))
            records['spanning_forests_tested']+=1
        assert p['matched_weight']==max(values)
        assert not set(f['forest']) & set(f['pivot_edges'])
        records['forest_contexts']+=1
        if witness is None and min(values)<max(values):
            witness=dict(counts=a,weights=w,edges=edges,plan=p,forest=f,
                         forest_scores=[dict(forest=sorted(t),score=s) for t,s in zip(forests,values)])
    if witness:
        (ROOT/'examples'/'forest_choice_witness.json').write_text(json.dumps(witness,indent=2)+'\n')
    for length in range(1,11):
        for first in (False,True):
            for eligibility in itertools.product((False,True),repeat=2):
                for _ in range(3):
                    weight=rng.randrange(1,10)
                    potentials=[]
                    for _ in range(2):
                        u=rng.randrange(5); potentials.append((u,u+rng.randrange(5)))
                    p=periodic_path_table(length,weight=weight,first_is_row=first,
                        eligibility=eligibility,potentials=potentials,certificate=True)
                    got={(x['first'],x['last'],x['direction']):x['score'] for x in p['table']}
                    assert got==path_oracle(length,weight,first,eligibility,potentials)
                    assert verify_power_certificate(p['certificate'])
                    records['path_tables']+=1
    records.update(seconds=time.perf_counter()-t0,discrepancies=0,
                   found_forest_choice_witness=witness is not None)
    return records


def large():
    t0=time.perf_counter()
    p=periodic_cycle_optimum(1<<1024,certificate=True)
    assert verify_power_certificate(p['certificate'])
    assert p['matched_weight']==(1<<1024)-1 and p['deferred_weight']==1
    proofpath=ROOT/'results'/'binary_cycle_2pow1024.json'
    proofpath.write_text(json.dumps(p,separators=(',',':'))+'\n')
    counts,weights=cactus_counts(1000,weights=True)
    q=optimize_counts(counts,weights,prepeel=False,limits=LIMITS)
    assert q['matched_weight']==sum(2*i+3 for i in range(1000))
    assert q['deferred_weight']==sum(i+1 for i in range(1000))
    return dict(symbolic_cycle_half_length_bits=1025,
                symbolic_matrix_products=p['matrix_products'],
                proof_nodes=len(p['certificate']['nodes']), proof_bytes=proofpath.stat().st_size,
                cactus_blocks=1000,cactus_rows=2000,cactus_matched_weight=q['matched_weight'],
                cactus_deferred_weight=q['deferred_weight'],cactus_stats=q['stats'],
                seconds=time.perf_counter()-t0,discrepancies=0)


def main():
    parser=argparse.ArgumentParser(); parser.add_argument('--suite',choices=['exhaustive','randomized','large','all'],default='all')
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    result=dict(python=sys.version,platform=platform.platform(),seed=20261012,
                scope='synthetic unsigned matrices, closed-walk graph data and symbolic paths; not native knots')
    for name,fn in [('exhaustive',exhaustive),('randomized',randomized),('large',large)]:
        if args.suite in (name,'all'):
            result[name]=fn(); print(name,json.dumps(result[name]),flush=True)
    output=args.output or ROOT/'results'/f'audit_{args.suite}.json'
    output.write_text(json.dumps(result,indent=2)+'\n')

if __name__=='__main__': main()
