"""Finite source pilot for two-row nonnegative matching consequences."""
from fractions import Fraction
from hashlib import sha256
from itertools import combinations,product
import json
from pathlib import Path
import random
import sys
import time
ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'fast'))
from fastunknot.sector_sparse import PreparedSectorSource
from fastunknot.sector_matching_support import _closure,_kernel_equations


def pair_step(rows,forced):
    for i,j in combinations(range(len(rows)),2):
        for sa,sb in product((1,-1),repeat=2):
            lower=Fraction(0);upper=None
            for k,(a,b)in enumerate(zip(rows[i],rows[j])):
                if k in forced:continue
                a*=sa;b*=sb
                if not b:
                    if a<0:break
                elif b>0:lower=max(lower,-a/b)
                else:upper=-a/b if upper is None else min(upper,-a/b)
                if upper is not None and lower>upper:break
            else:
                scale=lower+1 if upper is None else (lower+upper)/2
                added=[k for k,(a,b)in enumerate(zip(rows[i],rows[j]))
                       if k not in forced and sa*a+scale*sb*b>0]
                if added:return i,j,Fraction(sa),scale*sb,added
    return None


def pair_closure(rows):
    forced,_=_closure(rows,lambda:None);steps=[]
    while True:
        step=pair_step(rows,forced)
        if step is None:return forced,steps
        i,j,a,b,added=step
        forced.update(added);steps.append(step)
        # Apply every ordinary sign implication with the new known zeros.
        while True:
            old=len(forced)
            for row in rows:
                active=[(k,x)for k,x in enumerate(row)if x and k not in forced]
                if active and (all(x>0 for _,x in active)or all(x<0 for _,x in active)):
                    forced.update(k for k,_ in active)
            if len(forced)==old:break

if __name__=='__main__':
    bank=json.loads((ROOT/'reports/57/results/discovery_corpus.json').read_text())['records']
    rng=random.Random(20261010);summaries=[];hits=[];total=high=missed=0
    start=time.perf_counter()
    for case in bank:
        source=PreparedSectorSource(case['triangulation']);t=len(case['triangulation']['tetrahedra'])
        assignments=set(tuple(vertex['full_sector_quad_types'])for vertex in case['standard_vertices'])
        assignments.update(tuple(rng.randrange(3)for _ in range(t))for _ in range(64))
        count=useful=0
        for assignment in sorted(assignments):
            support=list(enumerate(assignment));kernel=source.build(support)
            rows=_kernel_equations(kernel.basis,t,lambda:None)
            old,_=_closure(rows,lambda:None)
            new,steps=pair_closure(rows)
            present=set()
            for vertex in case['standard_vertices']:
                occupied=[(i,q)for i,row in enumerate(vertex['coordinates'])for q in range(3)if row[4+q]]
                if all(assignment[i]==q for i,q in occupied):present.update(i for i,q in occupied)
            oracle=set(range(t))-present
            assert old<=new<=oracle,(case['id'],assignment,old,new,oracle)
            total+=1;count+=1
            if len(kernel.basis)>3:high+=1
            if new!=oracle:missed+=1
            if new!=old:
                useful+=1
                hits.append(dict(id=case['id'],support=support,raw_nullity=len(kernel.basis),
                    old_forced=sorted(old),new_forced=sorted(new),oracle_forced=sorted(oracle),
                    steps=[dict(rows=[i,j],coefficients=[[a.numerator,a.denominator],[b.numerator,b.denominator]],
                                added=added)for i,j,a,b,added in steps]))
        summaries.append(dict(id=case['id'],tested=count,improved=useful))
        print(case['id'],count,useful,flush=True)
    report=dict(seed=20261010,random_assignments_per_source=64,source_cases=len(bank),sector_cases=total,
        high_nullity_cases=high,strict_pair_improvements=len(hits),remaining_incomplete_cases=missed,
        summaries=summaries,hits=hits,seconds=time.perf_counter()-start,
        corpus_sha256=sha256((ROOT/'reports/57/results/discovery_corpus.json').read_bytes()).hexdigest(),
        driver_sha256=sha256(Path(__file__).read_bytes()).hexdigest())
    (ROOT/'synthesis/data/matching-pair-pilot.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items()if k not in ('summaries','hits')}))
