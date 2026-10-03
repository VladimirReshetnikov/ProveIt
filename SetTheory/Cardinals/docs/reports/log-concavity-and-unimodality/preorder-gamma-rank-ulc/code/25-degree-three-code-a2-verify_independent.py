#!/usr/bin/env python3
"""Independent audit: no imports from the production generators or matchers.

Enumerate every labeled reflexive transitive relation on 2..5 points; place the
marked attachments at vertices 0,1; exhaust the four common-orientation choices.
Compare canonical structural orbits.  Independently count actual labeled
(A,B) supports by Hall's theorem on the population cube {0,1,2,3}^d, using C++.
Forward differences on {0,1,2}^d recover the binomial-basis coefficient array.
"""
from pathlib import Path
from itertools import product, permutations
from collections import Counter
from math import comb
import hashlib, json, subprocess, tempfile, time

ROOT=Path(__file__).resolve().parent


def reflexive_transitive(rows):
    n=len(rows)
    rel=[row | (1 << i) for i,row in enumerate(rows)]
    for i in range(n):
        for j in range(n):
            if rel[i] >> j & 1:
                if rel[j] & ~rel[i]:
                    return False
    return True


def all_labeled_preorders(n):
    # Each row independently ranges over every off-diagonal subset.  No quotient
    # poset, topological labelling, compositions, or production code is used.
    alternatives=[]
    for i in range(n):
        targets=[j for j in range(n) if j!=i]
        alternatives.append([sum(1<<j for t,j in enumerate(targets) if m>>t&1)
                             for m in range(1<<(n-1))])
    for rows in product(*alternatives):
        if reflexive_transitive(rows):
            yield rows


def add_exterior(rows, signs, types, populations):
    out=list(rows)
    for mask,count in zip(types,populations):
        for _ in range(count):
            j=len(out);out.append(0)
            for a in (0,1):
                if mask>>a&1:
                    if signs[a]==-1: out[a]|=1<<j
                    else: out[j]|=1<<a
    return tuple(out)


def allowed_masks(rows,signs):
    return tuple(m for m in (1,2,3)
                 if reflexive_transitive(add_exterior(rows,signs,(m,),(1,))))


def orbit_key(rows, signs, types):
    # Canonicalization is independently implemented from a relation matrix.
    n=len(rows)
    matrix=[[bool(rows[i]>>j&1) for j in range(n)] for i in range(n)]
    candidates=[]
    for left,right in ((0,1),(1,0)):
        for tail in permutations(range(2,n)):
            order=(left,right)+tail
            for dual in (False,True):
                newrows=[]
                for i in order:
                    newrows.append(sum(1<<c for c,j in enumerate(order)
                        if (matrix[j][i] if dual else matrix[i][j])))
                new_signs=tuple(signs[a]*(-1 if dual else 1) for a in (left,right))
                newtypes=tuple(sorted(sum(1<<i for i,a in enumerate((left,right))
                                         if m>>a&1) for m in types))
                candidates.append((tuple(newrows),new_signs,newtypes))
    return min(candidates)


def load_poly(serialized,d):
    out={}
    for q,v in serialized:
        q=tuple(q)
        assert len(q)==d and q not in out and all(a>=0 for a in q)
        assert isinstance(v,int) and v>0
        out[q]=v
    return out


def finite_difference(values,q,k):
    return sum((-1)**(sum(q)-sum(p))
               * __import__('math').prod(comb(a,b) for a,b in zip(q,p))
               * values[p][k]
               for p in product(*(range(a+1) for a in q)))


def main():
    start=time.monotonic()
    source=ROOT/'templates.json'
    data=json.loads(source.read_text())
    records=data['templates']
    assert len({r['id'] for r in records})==len(records)
    recorded={}
    for r in records:
        rows=tuple(r['core_rows']);signs=tuple(r['signs']);types=tuple(r['types'])
        assert 2<=len(rows)<=5 and reflexive_transitive(rows)
        assert len(signs)==2 and set(signs)<= {-1,1}
        assert types==allowed_masks(rows,signs), ('allowed type mismatch',r['id'])
        key=(rows,signs,types)
        assert key==orbit_key(rows,signs,types),('not canonical',r['id'])
        assert key not in recorded, ('duplicate structure',r['id'])
        recorded[key]=r['id']
    labeled_counts={}; orbit_counts={}; coverage_counts={}
    for n in range(2,6):
        found=set();seen=0;valid=0
        for rows in all_labeled_preorders(n):
            seen+=1
            for signs in product((-1,1),repeat=2):
                types=allowed_masks(rows,signs)
                if not types: continue
                valid+=1
                found.add(orbit_key(rows,signs,types))
        expected={key for key in recorded if len(key[0])==n}
        assert found==expected, ('coverage mismatch',n,len(found-expected),len(expected-found))
        labeled_counts[n]=seen;orbit_counts[n]=len(found);coverage_counts[n]=valid
        print('COVERAGE',n,'labeled preorders',seen,'orbits',len(found),flush=True)
    # Actual vertex-level graphs for every sample.  The external points are all
    # separately labeled here; no binomial weights enter the Hall counting.
    samples=[]
    for r in records:
        d=len(r['types'])
        for pop in product(range(4),repeat=d):
            graph=add_exterior(r['core_rows'],r['signs'],r['types'],pop)
            assert reflexive_transitive(graph),('nontransitive blowup',r['id'],pop)
            samples.append((r['id'],pop,graph))
    print('POPULATION SAMPLES',len(samples),flush=True)
    with tempfile.TemporaryDirectory(prefix='preorder_hall_') as tmp:
        exe=Path(tmp)/'hall_count'
        subprocess.run(['c++','-O3','-std=c++17',str(ROOT/'verify_hall.cpp'),'-o',str(exe)],check=True)
        payload=str(len(samples))+'\n'+''.join(str(len(g))+' '+' '.join(map(str,g))+'\n' for _,_,g in samples)
        process=subprocess.run([str(exe)],input=payload,text=True,capture_output=True,check=True)
    countlines=process.stdout.splitlines()
    assert len(countlines)==len(samples)
    grouped={r['id']:{} for r in records}
    for (rid,pop,graph),line in zip(samples,countlines):
        counts=tuple(map(int,line.split()))
        assert len(counts)==5 and counts[0]==1 and counts[4]==0, ('degree test',rid,pop,counts)
        grouped[rid][pop]=counts
    checked_coefficients=0;hist=Counter();degree_hist=Counter()
    for r in records:
        d=len(r['types']);values=grouped[r['id']]
        stored=[load_poly(p,d) for p in r['gamma']]
        assert len(stored)==4
        for k in range(4):
            assert all(sum(q)<=2 for q in stored[k])
            if k==1: assert all(sum(q)<=1 for q in stored[k])
            independent={}
            for q in product(range(3),repeat=d):
                v=finite_difference(values,q,k);checked_coefficients+=1
                if v: independent[q]=v
            assert independent==stored[k], ('coefficient mismatch',r['id'],k,independent,stored[k])
            for pop,counts in values.items():
                evaluated=sum(v*__import__('math').prod(comb(a,b) if b<=a else 0 for a,b in zip(pop,q))
                              for q,v in stored[k].items())
                assert evaluated==counts[k], ('sample mismatch',r['id'],pop,k,evaluated,counts[k])
        degree_hist[max(k for k,p in enumerate(stored) if p)]+=1
        hist[d]+=1
    report={
        'result':'PASS',
        'templates_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
        'structural_templates':len(records),
        'labeled_preorder_counts':labeled_counts,
        'marked_signed_labeled_structures_with_nonempty_type_set':coverage_counts,
        'structural_orbits_by_core_size':orbit_counts,
        'templates_by_number_of_types':dict(hist),
        'population_grid':[0,1,2,3],
        'actual_labeled_graphs_checked':len(samples),
        'forward_difference_coefficient_checks':checked_coefficients,
        'actual_gamma_degrees_by_template':dict(degree_hist),
        'hall_support_counts_sha256':hashlib.sha256(process.stdout.encode()).hexdigest(),
        'all_blowups_transitive':True,
        'all_degree_four_hall_support_counts_zero':True,
        'all_gamma_coefficients_equal_independent_forward_differences':True,
        'all_gamma_evaluations_equal_direct_hall_counts':True,
        'seconds':time.monotonic()-start,
    }
    (ROOT/'independent_verification.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2),flush=True)

if __name__=='__main__':main()
