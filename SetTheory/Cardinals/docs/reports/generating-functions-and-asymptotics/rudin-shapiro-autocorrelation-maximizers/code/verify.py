#!/usr/bin/env python3
"""Exact certificate verifier for eventual Rudin--Shapiro autocorrelation maxima.

Python 3.9+; standard library only. Run from any directory:
    python code/verify.py

No floating-point computation, convex-hull package, numerical eigenvalue,
external theorem prover, or precomputed maximum is trusted by this verifier.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
import random
import sys
import time
from typing import Any, Dict, List, Sequence, Tuple

Vec = Tuple[int, int, int]
Poly = Dict[Tuple[int, int], Q]
ROOT = Path(__file__).resolve().parents[1]
U = ((1, 0, 2), (-1, 0, 2), (0, 1, 0))
V = ((0, 1, 0), (0, -1, 0), (1, 0, 0))
BASE = (1, -1, 1)
WORDS = ('', '0', '00', '10', '110', '1100', '100', '1110',
         '0110', '11100', '11110', '011110', '1011110')
EXCEPTIONS = {3:-2, 5:-8, 7:-34, 8:2, 9:22, 10:8, 12:34, 13:86,
              14:136, 15:-8, 17:1110, 19:4352, 20:2, 22:8, 24:34,
              25:-2, 27:-8, 29:-34, 32:2, 34:8, 39:-2}


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def dot(a, b):
    return sum(x*y for x, y in zip(a, b))


def mv(a, v):
    return tuple(dot(row, v) for row in a)


def rm(v, a):
    return tuple(sum(v[i]*a[i][j] for i in range(3)) for j in range(3))


def mm(a, b):
    return tuple(tuple(sum(a[i][k]*b[k][j] for k in range(3))
                       for j in range(3)) for i in range(3))


def ident():
    return ((1,0,0),(0,1,0),(0,0,1))


def mpow(a, n):
    out = ident()
    while n:
        if n & 1:
            out = mm(out, a)
        a = mm(a, a)
        n >>= 1
    return out


def scaled(a, c):
    return tuple(tuple(c*x for x in row) for row in a)


def inverse(a):
    aug = [[Q(a[i][j]) for j in range(3)] +
           [Q(int(i==j)) for j in range(3)] for i in range(3)]
    for i in range(3):
        pivot = next((j for j in range(i,3) if aug[j][i]), None)
        require(pivot is not None, 'singular matrix')
        aug[i], aug[pivot] = aug[pivot], aug[i]
        d = aug[i][i]
        aug[i] = [x/d for x in aug[i]]
        for j in range(3):
            if j != i:
                d = aug[j][i]
                aug[j] = [a-d*b for a,b in zip(aug[j],aug[i])]
    return tuple(tuple(row[3:]) for row in aug)


def det(a, b, c):
    return (a[0]*(b[1]*c[2]-b[2]*c[1])
            - a[1]*(b[0]*c[2]-b[2]*c[0])
            + a[2]*(b[0]*c[1]-b[1]*c[0]))


def tetra_contains(p, a, b, c):
    d = det(a,b,c)
    if not d:
        return False
    ns = [det(p,b,c), det(a,p,c), det(a,b,p)]
    if d < 0:
        d, ns = -d, [-x for x in ns]
    return min(ns) >= 0 and sum(ns) <= d


def load_finite(data: Path):
    obj = json.loads((data/'finite_certificate.json').read_text())
    require(obj['initial'] == list(BASE), 'wrong base vector')
    require(len(obj['stages']) == 400, 'expected exactly 400 stages')
    previous = [BASE, tuple(-x for x in BASE)]
    hulls = [previous]
    tetra_count = 0
    for m, stage in enumerate(obj['stages'], 3):
        require(stage['m'] == m, 'nonconsecutive stage')
        candidates = [mv(t,v) for t in (U,V) for v in previous]
        keep = stage['keep']
        require(all(type(i) is int and 0 <= i < len(candidates) for i in keep),
                f'invalid kept index at m={m}')
        vertices = [candidates[i] for i in keep]
        require(len(set(vertices)) == len(vertices), 'duplicate retained vertex')
        require(set(vertices) == {tuple(-x for x in v) for v in vertices},
                f'retained set is not centrally symmetric at m={m}')
        reps = stage['representations']
        require(len(reps) == len(candidates), 'missing containment witness')
        for p, rep in zip(candidates,reps):
            require(all(type(i) is int and 0 <= i < len(vertices) for i in rep),
                    'invalid witness index')
            if len(rep) == 0:
                good = p == (0,0,0)
            elif len(rep) == 1:
                good = p == vertices[rep[0]]
            elif len(rep) == 3:
                good = tetra_contains(p, *(vertices[i] for i in rep))
                tetra_count += 1
            else:
                good = False
            require(good, f'failed finite containment at m={m}')
        # The candidates generate exactly U K +conv V K. Every retained point
        # is a candidate and every candidate is certified inside their hull.
        previous = vertices
        hulls.append(vertices)
    return hulls, tetra_count


def support(vertices, row):
    return max(abs(dot(v,row)) for v in vertices)


def verify_finite_uniqueness(hulls):
    rows = []
    for m in range(3,403):
        n = m-2
        heights = [support(hulls[n],r) for r in ((1,0,0),(0,1,0))]
        require(heights[0] != heights[1], f'coordinate tie at m={m}')
        coordinate = int(heights[1] > heights[0])
        value = max(heights)
        row = (1,0,0) if coordinate==0 else (0,1,0)
        letters = []
        # Strict sibling inequalities certify the unique word, including
        # words whose vectors were discarded during convex-hull reduction.
        for j in range(n,0,-1):
            next_rows = [rm(row,t) for t in (U,V)]
            heights = [support(hulls[j-1],r) for r in next_rows]
            choices = [i for i,h in enumerate(heights) if h==value]
            require(max(heights)==value and len(choices)==1,
                    f'nonunique maximizing path at m={m}, depth={j}')
            choice = choices[0]
            letters.append('1' if choice==0 else '0')
            row = next_rows[choice]
        correlation = dot(row,BASE)
        require(abs(correlation)==value, 'wrong terminal value')
        k = 1
        for step, letter in enumerate(reversed(letters),1):
            if letter=='1':
                k = 2**(step+1)-k
        shift = k if coordinate==0 else 2**m-k
        ell = (2**(m+1)+(-1)**m)//3
        delta = shift-ell
        require(delta==EXCEPTIONS.get(m,0), f'wrong exception at m={m}')
        if m>=40:
            require(correlation==(-1)**(m-1)*value, 'wrong eventual sign')
        rows.append(dict(m=m,value=value,shift=shift,ell=ell,delta=delta,
                         correlation=correlation,vertices=len(hulls[n]),
                         word=''.join(letters),coordinate=coordinate))
    return rows


def padd(a: Poly, b: Poly, sign=1) -> Poly:
    out = a.copy()
    for e,v in b.items():
        out[e] = out.get(e,Q(0)) + sign*v
    return {e:v for e,v in out.items() if v}


def pmul(a: Poly, b: Poly) -> Poly:
    out: Poly = {}
    for (i,j),v in a.items():
        for (k,l),w in b.items():
            e = (i+k,j+l)
            out[e] = out.get(e,Q(0))+v*w
    return {e:v for e,v in out.items() if v}


def pvector(matrix):
    return [{(1,0):Q(r[0]),(0,0):Q(r[1]),(0,1):Q(r[2])}
            for r in matrix]


def pdet(a,b,c):
    a,b,c = map(pvector,(a,b,c))
    out: Poly = {}
    for i,j,k,sign in ((0,1,2,1),(1,2,0,1),(2,0,1,1),
                       (0,2,1,-1),(2,1,0,-1),(1,0,2,-1)):
        out = padd(out,pmul(pmul(a[i],b[j]),c[k]),sign)
    return out


def interval_product(a,b):
    vals = [x*y for x in a for y in b]
    return min(vals),max(vals)


def interval_power(a,n):
    out = (Q(1),Q(1))
    for _ in range(n):
        out = interval_product(out,a)
    return out


def polynomial_bounds(p,box):
    low = high = Q(0)
    for (i,j),v in p.items():
        term = interval_product(interval_power(box[0],i),
                                interval_power(box[1],j))
        term = interval_product(term,(v,v))
        low += term[0]
        high += term[1]
    return low,high


def linear_bounds(row,box):
    low = high = Q(row[1])
    for a,(l,h) in zip((row[0],row[2]),box):
        low += min(a*l,a*h)
        high += max(a*l,a*h)
    return low,high


def projective_inclusion(matrix,source,target):
    # The denominator is row 1. Cross-multiplication retains correlations
    # between numerator and denominator; interval division is not needed.
    margins = [linear_bounds(matrix[1],source)[0]]
    for i,(l,h) in zip((0,2),target):
        margins.append(linear_bounds(
            [matrix[i][j]-l*matrix[1][j] for j in range(3)],source)[0])
        margins.append(linear_bounds(
            [h*matrix[1][j]-matrix[i][j] for j in range(3)],source)[0])
    require(min(margins)>0, 'failed projective box inclusion')
    return margins


def template_matrices():
    inv = inverse(U)
    require(mm(U,inv)==ident(), 'bad matrix inverse')
    result = []
    for word in WORDS:
        product = ident()
        for letter in word:
            product = mm(product,U if letter=='1' else V)
        result.append(mm(product,mpow(inv,len(word))))
    return result


def verify_parametric(data, hulls):
    cert = json.loads((data/'polytope_certificate.json').read_text())
    require(cert['entry_word_length']==400 and cert['entry_level']==402,
            'wrong induction entry')
    require(cert['block_length']==6, 'wrong block length')
    center = (Q(453397651521,10**12),Q(-602784715201,10**12))
    outer = tuple((c-Q(1,10**7),c+Q(1,10**7)) for c in center)
    inner = tuple((c-Q(1,10**9),c+Q(1,10**9)) for c in center)
    require([[str(x) for x in pair] for pair in outer]==cert['box'],
            'unexpected outer box')
    require([[str(x) for x in pair] for pair in inner]==cert['inner_box'],
            'unexpected inner box')
    z = mv(mpow(U,400),BASE)
    ratios = (Q(z[0],z[1]),Q(z[2],z[1]))
    require(all(l<=x<=h for x,(l,h) in zip(ratios,inner)),
            'orbit does not enter inner box')
    require(all(abs(x-c)<Q(1,10**12) for x,c in zip(ratios,center)),
            'entry ratio error exceeds the displayed bound')
    minus_u = scaled(U,-1)
    box_margins = []
    for j in range(6):
        box_margins.append(projective_inclusion(mpow(minus_u,j),inner,outer))
    return_margins = projective_inclusion(mpow(minus_u,6),inner,inner)

    templates = template_matrices()
    target_entry = {mv(l,z) for l in templates}
    target_entry |= {tuple(-x for x in p) for p in target_entry}
    require(len(target_entry)==26,'expected 26 distinct entry points')
    require(target_entry==set(hulls[400]), 'entry hull differs from template hull')

    targets = [scaled(mm(l,U),sign) for l in templates for sign in (1,-1)]
    require(len(cert['transitions'])==26, 'missing parametric transitions')
    seen = set()
    identity_count = 0
    tetra_count = 0
    lowest_positive = None
    for item in cert['transitions']:
        ti,i = item['T'],item['i']
        require(ti in (0,1) and 0<=i<13 and (ti,i) not in seen,
                'invalid or duplicate transition')
        seen.add((ti,i))
        image = mm((U,V)[ti],templates[i])
        if 'identity' in item:
            require(image==targets[item['identity']], 'failed matrix identity')
            identity_count += 1
            continue
        ids = item['tetra']
        require(len(ids)==3 and all(0<=j<26 for j in ids), 'bad tetra indices')
        a,b,c = [targets[j] for j in ids]
        den = pdet(a,b,c)
        nums = [pdet(image,b,c),pdet(a,image,c),pdet(a,b,image)]
        nums.append(padd(padd(padd(den,nums[0],-1),nums[1],-1),nums[2],-1))
        sign = item['orientation']
        require(sign in (-1,1), 'bad orientation')
        polynomials = [{e:sign*v for e,v in p.items()} for p in [den]+nums]
        lower = [polynomial_bounds(p,outer)[0] for p in polynomials]
        require(lower[0]>0 and min(lower[1:])>=0,
                f'failed polynomial containment T={ti}, i={i}')
        require([str(x) for x in lower]==item['lower_bounds'],
                'recorded polynomial margins disagree')
        for x in lower:
            if x>0 and (lowest_positive is None or x<lowest_positive):
                lowest_positive=x
        tetra_count += 1
    require(len(seen)==26, 'incomplete transition set')
    coordinate_margins=[]
    for i,l in enumerate(templates):
        for r in (0,1):
            if i==0 and r==1:
                continue
            for sign in (-1,1):
                p=padd({(0,0):Q(1)},pvector(l)[r],sign)
                margin=polynomial_bounds(p,outer)[0]
                require(margin>0,'nonunique coordinate extremum')
                coordinate_margins.append(margin)
    gap=min(coordinate_margins)
    require(gap>Q(7,50),'uniform coordinate gap too small')
    require(str(gap)==cert['minimum_coordinate_margin'],'coordinate margin mismatch')
    # V-images have x+y=0; the distinguished vector has x+y != 0.
    require(outer[0][0]+1>0,'distinguished vector lies in V-image plane')
    require(det(*U)==-4,'wrong determinant of U')
    return dict(identity_transitions=identity_count,
                tetrahedron_transitions=tetra_count,
                minimum_coordinate_margin=str(gap),
                smallest_positive_polynomial_margin=str(lowest_positive),
                block_length=6,entry_level=402,
                return_box_margins=[str(x) for x in return_margins],
                intermediate_box_margins=[[str(x) for x in row] for row in box_margins])


def verify_direct(rows,maximum_level=10):
    previous=None
    previous2=None
    counts=0
    for m in range(1,maximum_level+1):
        rs=[-1 if bin(j & (j>>1)).count('1') % 2 else 1 for j in range(2**m)]
        corr=[sum(rs[j]*rs[j+k] for j in range(len(rs)-k)) for k in range(len(rs))]
        if m>=2:
            require(all(corr[k]==0 for k in range(2,len(rs),2)), 'even shift not zero')
        if m>=3:
            half=2**(m-1)
            for k in range(1,2**m):
                if k==half:
                    expected=0
                else:
                    t=abs(k-half)
                    expected=(1 if k<half else -1)*previous[t]
                    if t<len(previous2):
                        expected+=2*previous2[t]
                require(corr[k]==expected,'direct scalar recurrence mismatch')
                counts+=1
            best=max(abs(v) for v in corr[1:])
            shifts=[k for k in range(1,len(corr)) if abs(corr[k])==best]
            result=rows[m-3]
            require(shifts==[result['shift']] and best==result['value'],
                    'direct definition disagrees with certificate')
        previous2,previous=previous,corr
    return counts


def verify_selection(data):
    selection=json.loads((data/'selection.json').read_text())
    # Inspect the saved schema rather than introducing any additional draw.
    seed=int(selection['seed'])
    areas=selection['areas']
    index=random.Random(seed).randrange(len(areas))
    require(len(areas)==100 and index==44 and areas[index]=='Harmonic analysis',
            'area draw does not replay')
    require(selection['redraws']==0,'recorded redraw')


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--data',type=Path,default=ROOT/'data')
    parser.add_argument('--output',type=Path,default=None,
                        help='write the verification summary as JSON')
    args=parser.parse_args()
    started=time.monotonic()
    verify_selection(args.data)
    print('PASS: reproducible single area draw (45/100: Harmonic analysis).',flush=True)
    hulls, finite_tetras=load_finite(args.data)
    print('PASS: exact convex-hull certificates, levels 3 through 402.',flush=True)
    rows=verify_finite_uniqueness(hulls)
    expected=json.loads((args.data/'certified_maxima.json').read_text())
    require(rows==expected,'recorded maxima differ from recomputation')
    print('PASS: unique maximizing word and shift at every level 3 through 402.',flush=True)
    facts=verify_parametric(args.data,hulls)
    print('PASS: all 26 parametric transitions and strict coordinate separation.',flush=True)
    print('PASS: entry at level 402 and rational six-step invariant-box certificate.',flush=True)
    direct_count=verify_direct(rows)
    print('PASS: independent defining-sum checks through level 10.',flush=True)
    summary=dict(status='PASS',arithmetic='Python integers and fractions.Fraction only',
                 direct_recurrence_checks=direct_count,finite_tetrahedron_witnesses=finite_tetras,
                 finite_levels=[3,402],exception_deltas=EXCEPTIONS,
                 maximum_retained_vertices=max(map(len,hulls)),**facts)
    summary['elapsed_seconds']=round(time.monotonic()-started,3)
    print('PASS: eventual nearest-integer formula for every m >= 40; 39 is an exception.',flush=True)
    print('PASS: general uniqueness for m >= 3; the elementary m=2 tie is excluded.',flush=True)
    print(json.dumps(summary,indent=2),flush=True)
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(json.dumps(summary,indent=2)+'\n')


if __name__=='__main__':
    try:
        main()
    except (ValueError,KeyError,IndexError,TypeError,ZeroDivisionError,OSError) as error:
        print(f'VERIFICATION FAILED: {error}',file=sys.stderr)
        sys.exit(1)
