#!/usr/bin/env python3
"""Independent ordinary-strong projection proof checks; saved data only."""
import argparse
import hashlib
import json
from math import gcd
from pathlib import Path

AUTHOR_PINS = {'complete86_ordinary_auxiliary_projection.py': '130c8a09570866f3b510f4092aef3ab7fd61154f6c8776fcdba870d80a59019d', 'complete86_ordinary_auxiliary_projection.json': 'f46dd919a038b6dd646489e64585331de30b8c91a380cf9611afbf288122a9a6', 'complete86_ordinary_auxiliary_projection.md': 'cc3230f10c193d35df2820dad73b71f03b09493dfeca52618b1b23e9e0e59570'}
PINS = {'complete86_transport_quotient_shear.py': 'c1cb668ae5538d168652c07627c00255d9c00a7d6373feb45da8c7c3806c9c45', 'complete86_transport_quotient_shear.json': '77ec7894c68f16e8d2dbb48f7c444bf7ab5e2c08f895bdad877f61b8c9c96efc', 'complete86_transport_quotient_shear.md': 'fd0254d6cb0a35686cd824e3f29384c9aed8141444256ce0a9442133a2785541', 'review_complete85_auxiliary_bezout_math.md': '77a4071be471db23642cabddc5bd4880debfa53441bf3640c3c45523e9bdb36d', '../../1980/PELL_RELAXED_AUXILIARY_PROOF.md': '9849260ea2776d26e9b615e0e1ed6fcd9b1c9e0e4cedb6cd8aaa2c0346ecbc90', 'complete75_coupled_index_linear88.md': '1533ef2411347335704f46a8a1020d8d46dea1147b03e9c9d35684a687172e39', '../../1980/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md': '47a2c5b69f3c87b7a1ddc61ef84757023de291b63d1330e2c8dc9b40e811ab8b'}

def need(ok, message):
    if not ok:
        raise ValueError(message)

def sha(b):
    return hashlib.sha256(b).hexdigest()

def same(a, b):
    if type(a) is not type(b):
        return False
    if isinstance(a, dict):
        return a.keys() == b.keys() and all(same(a[k], b[k]) for k in a)
    if isinstance(a, list):
        return len(a) == len(b) and all(same(x, y) for x, y in zip(a, b))
    return a == b

def pell(a,n):
    # Binary powering in Z[sqrt(a^2-1)], distinct from linear recurrence.
    delta=a*a-1
    def mul(x,y):
        return x[0]*y[0]+delta*x[1]*y[1], x[0]*y[1]+x[1]*y[0]
    v=(1,0);b=(a,1)
    while n:
        if n&1:
            v=mul(v,b)
        b=mul(b,b);n//=2
    return v

def residues():
    norm_cases=0;aux_cases=0
    for a in range(4):
        d=a*a+4*a+3
        need(d%4 in (0,3), 'discriminant residue')
        for c in range(4):
            for i in range(4):
                for f in range(4):
                    ns=i*i*c**4-d*(f*f-1)+1
                    need(ns%4!=3, 'ordinary strong cannot be minus one')
                    norm_cases+=1
        for root in range(4):
            for ordinate in range(4):
                need((root*root-d*ordinate*ordinate)%4!=3,
                     'main and input cannot be minus one')
    for kroot in range(4):
        for v in range(4):
            for y in range(4):
                need((kroot*kroot*(v*v-y*y)+y*y)%4!=3,
                     'auxiliary cannot be minus one after strong restoration')
                aux_cases+=1
    return dict(ordinary_strong_cases=norm_cases, square_base_auxiliary_cases=aux_cases)

def fixtures():
    results=[]
    for a,p in [(2,3),(3,3),(4,3),(2,7)]:
        delta=a*a-1;D,c=pell(a,p);g=gcd(c,delta);m=p*c//g
        f,psi=pell(a,m);qaux=delta*psi
        need(p%4==3 and m>2*p and m%c==0 and m%p==0, 'component index conditions')
        need(qaux%(c*c)==0 and (f*f-1)%(c*c)==0, 'ordinary divisibilities')
        i=qaux//(c*c)
        root,y=pell(qaux,p)
        need(root%qaux==0, 'odd quotient integral')
        V=root//qaux
        need((V+p)%c==0 and (V+c)%f==0, 'both positive fixed-minus quotients')
        j=(V+p)//c;o=(V+c)//f
        need(min(f,i,V,y,j,o)>0, 'positive full auxiliary tuple')
        need((o+p*f)%c==0, 'forward quotient divisibility')
        T=(o+p*f)//c
        child_V=c*(T*f-1)-p*f*f
        need(T>0 and child_V==V and o==c*T-p*f,
             'forward and inverse auxiliary maps')
        need(j==T*f-1-p*((f*f-1)//c), 'inverse j has correct ordinary formula')
        strong=(i*c*c)**2-delta*(f*f-1)+1
        aux=delta*(f*f-1)*(V*V-y*y)+y*y
        need(strong==aux==1, 'both literal ordinary factors equal one')
        need(o*f-c==j*c-p==V, 'literal parent linear identity')
        need((c*(T*f-1)-p*f*f)%f==(-c)%f, 'child excludes tiny signed auxiliary roots')
        results.append(dict(A=a,p=p,c=c,g=g,m=m,
             rank_size_hypothesis=c>a*delta*delta,
             normalized_strong_witness_integral=psi%(c*c)==0,
             largest_coordinate_bits=max(v.bit_length() for v in (T,j,o,f,i,y)),
             ordinary_factors_one=True, inverse_auxiliary_maps=True,
             full_compiler_zero=False))
    need(any(r['g']>1 and not r['normalized_strong_witness_integral'] for r in results),
         'strictly ordinary component examples retained')
    need(any(r['rank_size_hypothesis'] for r in results), 'large-rank component covered')
    return results

def gap_bounds():
    # These integer inequalities are intentionally checked separately from
    # auxiliary fixtures; the proof covers every large c, not just this grid.
    cases=0
    for a in range(4,36):
        A=a+2;delta=A*A-1
        for c in (A*delta*delta+1, A*delta*delta+2):
            need(c*c>4*delta and c*c>delta+c, 'large-rank consequences')
            for R in (1,a-3,a-2):
                need(delta>R and c**4>delta*(delta+c), 'ordinary norm lower bound for f')
                # f^2 >= 1+c^4/Delta: multiply the desired gap by Delta.
                need((delta-R)*(delta+c**4)-delta*(delta+c)>0,
                     'cleared strict K-R*f^2-c lower bound')
                cases+=1
    return dict(exact_integer_inequality_cases=cases,
                uniform_argument='c>A*Delta^2 gives c^2>4Delta and c^2>Delta+c; f^2>=1+c^4/Delta>Delta+c and >4c^2. Delta-R>=1 then K-Rf^2-c>0.')

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--root',type=Path,required=True)
    ap.add_argument('--author-root',type=Path)
    ap.add_argument('--output',type=Path)
    ap.add_argument('--expect',type=Path)
    a=ap.parse_args();author=a.author_root or a.root
    need(len(AUTHOR_PINS)==3 and len(PINS)>=3, 'frozen source and proof inventory required')
    for root,pins in [(author,AUTHOR_PINS),(a.root,PINS)]:
        for name,pin in pins.items():
            need(sha((root/name).read_bytes())==pin, 'pinned '+name)
    r=dict(status='PASS',source_sha256=sha(Path(__file__).read_bytes()),
           author_pins=AUTHOR_PINS,proof_pins=PINS,residues=residues(),
           component_fixtures=fixtures(),gap_bounds=gap_bounds(),
           scope='Independent bounded mathematical checks, full proof assessment in note; no author or historical Python executed, no complete compiler zero materialized. Auxiliary fixtures do not satisfy the entire input/first/main interface.')
    if a.expect:
        need(same(r,json.loads(a.expect.read_text())), 'exact typed receipt')
    if a.output:
        a.output.write_text(json.dumps(r,indent=2,sort_keys=True)+'\n')
    print(json.dumps(dict(status='PASS',residues=r['residues'],component_fixtures=r['component_fixtures'],gap_bounds=r['gap_bounds'])))
if __name__=='__main__':
    main()
