#!/usr/bin/env python3
"""Exact finite certificates for the new 843/100 odd-order U4/U2 gap.

Standard library only. Mathematical dependencies and normalization are
explained in the accompanying article. The finite dual-coefficient enumeration
is the face-split algorithm of ProveIt source49, here reproduced so that this
certificate is self-contained. The new ingredients are the retuned test,
the phase-coupled order-five certificate, and the profiled scalar bound.
This file checks integer/rational identities and inequalities; no floating
point value is used by an assertion.
"""
from collections import Counter, defaultdict
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json

if not __debug__:
    raise RuntimeError('Do not run with python -O: assertions are required.')

V3 = tuple(product((0, 1), repeat=3))
FREQUENCIES = (-3, -1, 1, 3)

def trim(p):
    p = list(p)
    while len(p) > 1 and p[-1] == 0:
        p.pop()
    return p

def padd(p, q):
    r = [F(0)] * max(len(p), len(q))
    for i, x in enumerate(p): r[i] += x
    for i, x in enumerate(q): r[i] += x
    return trim(r)

def pscale(p, c):
    return trim([c*x for x in p])

def pmul(p, q):
    r = [F(0)] * (len(p)+len(q)-1)
    for i, a in enumerate(p):
        for j, b in enumerate(q): r[i+j] += a*b
    return trim(r)

def peval(p, x):
    r = F(0)
    for a in reversed(p): r = r*x+a
    return r

def chebyshev(n):
    n = abs(n)
    if n == 0: return [F(1)]
    old, current = [F(1)], [F(0), F(1)]
    for _ in range(1, n):
        old, current = current, padd(pmul([0, 2], current), pscale(old, -1))
    return current

def zero(value, order):
    return value == 0 if order is None else value % order == 0

def residue(value, order):
    return value if order is None else value % order

def enumerate_dual(order):
    top = defaultdict(Counter)
    for fs in product(FREQUENCIES, repeat=8):
        total = sum(fs)
        if not zero(total, order): continue
        key = tuple(residue(sum(f*v[j] for f,v in zip(fs,V3)),order)
                    for j in range(3))
        degree = sum(abs(f) == 3 for f in fs)
        top[key][total, degree] += 1
    answer = defaultdict(Counter)
    for fs in product(FREQUENCIES, repeat=7):
        key = tuple(residue(-sum(f*v[j] for f,v in zip(fs,V3[1:])),order)
                    for j in range(3))
        total = sum(fs)
        degree = sum(abs(f) == 3 for f in fs)
        for (other_total, other_degree), count in top.get(key,{}).items():
            answer[total+other_total][degree+other_degree] += count
    assert 0 not in answer
    assert all(k % 2 for k in answer)
    assert all(dict(answer[k]) == dict(answer[-k]) for k in answer)
    return answer

def evaluate_dual(coefficients, t):
    return {k: sum((F(v)*t**j for j,v in row.items()), F(0))
            for k,row in coefficients.items()}

def old_style_bounds(d, order, t):
    d = {k:v for k,v in d.items() if k>0}
    alias = sum((abs(v) for k,v in d.items() if k != 1 and
                 (zero(k-1,order) or zero(k+1,order))), F(0))
    main = d[1]-alias
    tail = sum((abs(v) for k,v in d.items() if not zero(k,order)
                and not zero(k-1,order) and not zero(k+1,order)), F(0))
    norm_cosines = defaultdict(F)
    for k,v in d.items():
        for j,a in ((1,F(1)),(3,t)):
            for sign in (-1,1):
                l = k+sign*j
                if zero(l,order): norm_cosines[abs(l)] += 2*a*v
    norm = norm_cosines[0]+sum((abs(v) for k,v in norm_cosines.items() if k), F(0))
    return main,tail,norm

def phase_five_polynomials(d):
    main, norm, tail_square = [F(0)], [F(0)], [F(0)]
    for k,v in d.items():
        if k % 5 == 1:
            assert (k-1) % 10 == 0
            main = padd(main, pscale(chebyshev((k-1)//10),v))
        for j,a in ((1,F(1)),(-1,F(1)),(3,F(-7,50)),(-3,F(-7,50))):
            if (k+j) % 5 == 0:
                assert (k+j) % 10 == 0
                norm = padd(norm,pscale(chebyshev((k+j)//10),v*a))
    tail = {k:v for k,v in d.items() if k % 5 == 3}
    for k,v in tail.items():
        for l,w in tail.items():
            assert (k-l) % 10 == 0
            tail_square = padd(tail_square,pscale(chebyshev((k-l)//10),v*w))
    assert len(main) == len(norm) == 5 and len(tail_square) == 8
    return main,norm,tail_square

def encode(value):
    if isinstance(value,F): return str(value)
    if isinstance(value,dict): return {str(k):encode(v) for k,v in value.items()}
    if isinstance(value,(list,tuple)): return [encode(v) for v in value]
    return value

def main():
    report = {'theorem':'Q4(f) >= (843/100) Q2(f)^4',
              'scope':'real centered functions on finite odd-order abelian groups',
              'arithmetic':'exact integers and fractions only', 'retuned_rows':{}}
    main_lower,tail_upper,norm_upper = F(164447,2000), F(313,1000), F(1644551,10000)
    C,eta = F(1027,100), F(381,100000)
    assert (2*main_lower)**16 > 16*C*norm_upper**15
    assert tail_upper < eta*main_lower
    for order in (None,7,9,11):
        coeff = enumerate_dual(order)
        if order is None:
            assert sorted(k for k in coeff if k>0) == [1,3,5,7,9,11,13,15]
        d = evaluate_dual(coeff,F(-1441,10000))
        m,e,w = old_style_bounds(d,order,F(-1441,10000))
        assert m>main_lower and e<tail_upper and 0<w<norm_upper
        report['retuned_rows']['integer' if order is None else str(order)] = {
            'main':m,'tail':e,'norm_upper':w}
        print('Retuned dual row',order,'passed.',flush=True)
    report['retuned_common_bounds'] = {'main_lower':main_lower,'tail_upper':tail_upper,
                                      'norm_upper':norm_upper,'C_lower':C,'eta_upper':eta}

    # Entire order-five phase family, u=cos(10 theta).
    d = evaluate_dual(enumerate_dual(5),F(-7,50))
    m,q,e = phase_five_polynomials(d)
    assert all(x>0 for x in m)
    assert m[0]-m[1]-m[3]>F(82581,1000)
    assert all(x>0 for x in q)
    assert q[0]-q[1]-q[3]>0
    tangent = padd(pscale(m,2),pscale(q,F(-15,16)))
    assert all(x<0 for x in tangent[1:])
    assert sum(tangent)>F(10297,1000)>C
    assert e[1]<0 and e[2]<0 and all(x>0 for x in e[3:])
    assert e[2]+sum(e[3:])>0
    assert e[1]+e[2]+sum(e[3:])<0
    a,b = -e[1],-(e[2]+e[4]+e[6])
    assert b>0 and e[0]+a*a/(4*b)<F(651,10000)
    assert F(651,10000)<F(31,10000)**2*F(82581,1000)**2
    assert F(31,10000)<eta
    report['order_five'] = {'t':'-7/50','main_polynomial':m,'norm_polynomial':q,
        'tail_square_polynomial':e,'tangent_polynomial':tangent,
        'main_lower':F(82581,1000),'tail_square_upper':F(651,10000),
        'C_lower':F(10297,1000),'eta_upper':F(31,10000)}
    print('Order-five full phase certificate passed.',flush=True)

    # Order-three projection certificate.
    vertices = tuple(product((0,1),repeat=4))
    counts = Counter()
    for fs in product((-1,1),repeat=16):
        if sum(fs)%3: continue
        if any(sum(f*v[j] for f,v in zip(fs,vertices))%3 for j in range(4)): continue
        counts[sum(fs)] += 1
    assert dict(counts)=={-12:8,-6:16,0:286,6:16,12:8}
    assert F(131,8)>C
    report['order_three_frequency_counts'] = dict(counts)

    # The profiled scalar identity (u here denotes p(1-p), not cos(10 theta)).
    v,bmoment,amoment = [F(3,2),3],[F(5,2),15],[F(35,8),F(105,2),F(105,4)]
    a0,b0=F(99,676),F(33,26)
    square=padd(pscale(v,F(3,4)),[b0-a0-1])
    fprofile=padd(padd(pscale(amoment,F(7,8)),pscale(bmoment,F(33,26))),
                 pscale(v,F(-2277,676)))
    fprofile=padd(fprofile,[4*a0*b0-2*a0*a0])
    fprofile=padd(fprofile,pscale(pmul(square,square),2))
    assert fprofile==[F(4795,832),F(13749,208),F(1059,32)]
    assert all(x>0 for x in fprofile)
    cutoff=F(23,24)
    moment_at_cutoff=peval(fprofile,cutoff*(1-cutoff))
    assert moment_at_cutoff>F(42,5)
    assert F(4947,5000)**4<cutoff
    assert F(113,250)**4>1-cutoff
    bracket=F(4947,5000)-eta*F(113,250)
    dual_at_cutoff=C*bracket**16
    assert bracket>0 and dual_at_cutoff>F(42,5)
    assert F(15505,1024)>F(42,5)
    report['profile']={'coefficients_in_p_times_one_minus_p':fprofile,
        'cutoff':cutoff,'moment_at_cutoff':moment_at_cutoff,
        'dual_lower_at_cutoff':dual_at_cutoff,'small_p_bound':F(15505,1024)}
    # The stronger headline certificate; retain both cutoffs and the legacy JSON key.
    p=F(4793,5000)
    assert F(24737,25000)**4<p and F(4511,10000)**4>1-p
    stronger_dual=C*(F(24737,25000)-eta*F(4511,10000))**16
    assert peval(fprofile,p*(1-p))>F(843,100) and stronger_dual>F(843,100)
    report['optional_843_over_100']={'cutoff':p,'dual_lower':stronger_dual,
                                    'moment_lower':peval(fprofile,p*(1-p))}
    destination=Path(__file__).resolve().parent.parent/'data'/'norm_certificate.json'
    destination.parent.mkdir(parents=True,exist_ok=True)
    destination.write_text(json.dumps(encode(report),indent=2)+'\n')
    print('Every exact certificate passed; wrote',destination,flush=True)

if __name__=='__main__':
    main()
