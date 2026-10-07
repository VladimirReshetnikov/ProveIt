"""Reproducible independent-cube validation; run from the package root."""
from __future__ import annotations
import hashlib
import json
import platform
import random
import sys
import time
from itertools import product
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from twistkh import homology, runs_from_word, size_estimate
from twistkh.reference import cube_homology
from twistkh.preflight import basis_size, generator_basis_bound, degree_profile


def main():
    rng=random.Random(20261007)
    cases=[]
    for n in range(8):
        for w in product((-1,1),repeat=n): cases.append(('exhaustive-B2',2,list(w)))
    for n in range(4):
        for w in product((-2,-1,1,2),repeat=n): cases.append(('exhaustive-B3',3,list(w)))
    for _ in range(400):
        b=rng.randrange(2,5); n=rng.randrange(10)
        w=[rng.choice((-1,1))*rng.randrange(1,b) for _ in range(n)]
        cases.append(('random',b,w))
    for _ in range(160):
        b=rng.randrange(2,5); w=[]
        for j in range(rng.randrange(1,5)):
            x=rng.choice((-1,1))*rng.randrange(1,b)
            w += [x]*rng.randrange(1,5)
        cases.append(('blocked',b,w[:8]))
    start=time.perf_counter(); rows=[]
    for label,b,w in cases:
        runs=runs_from_word(b,w)
        macro=homology(b,runs,check_d2=True)
        cube=cube_homology(b,w,check_d2=True)
        if macro['by_degree'] != cube['by_degree']:
            raise AssertionError((label,b,w,macro,cube))
        estimate=size_estimate(b,runs)
        if estimate['exact_basis'] != macro['stats']['basis'] or basis_size(b,runs)['exact_basis'] != macro['stats']['basis']:
            raise AssertionError('size polynomial mismatch')
        if generator_basis_bound(b,runs) < macro['stats']['basis']:
            raise AssertionError('generator-sensitive bound failure')
        if degree_profile(b,runs)['chain_dimensions'] != macro['chain_dimensions']:
            raise AssertionError('dimension-profile failure')
        rows.append({'family':label,'strands':b,'word':w,'by_degree':macro['by_degree'],
                     'macro_basis':macro['stats']['basis'],'cube_basis':cube['basis'],
                     'components':macro['components']})
    report={'seed':20261007,'python':sys.version,'platform':platform.platform(),
            'cases':len(rows),'mismatches':0,'d_squared_checked_in_both':True,
            'exact_basis_formula_checks':len(rows),'temperley_lieb_size_checks':len(rows),
            'generator_bound_checks':len(rows),'degree_profile_checks':len(rows),'seconds':time.perf_counter()-start,
            'rows':rows}
    Path('results').mkdir(exist_ok=True)
    Path('results/validation.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k!='rows'},indent=2))

if __name__=='__main__': main()
