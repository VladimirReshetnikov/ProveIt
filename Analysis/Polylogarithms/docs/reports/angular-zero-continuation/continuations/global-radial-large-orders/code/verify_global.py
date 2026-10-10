#!/usr/bin/env python3
"""Exact certificates for the all-radius a >= 8 theorem.

Python 3.10+ standard library only. No floating-point acceptance tests.
Analytic tail estimates and their use are proved in article.tex.
"""
from __future__ import annotations

if not __debug__:
    raise RuntimeError('Run without -O: exact assertion checks are required.')
from fractions import Fraction as Q
from math import comb
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parents[1]

def add(*ps: list[Q]) -> list[Q]:
    out = [Q(0)] * max(map(len, ps))
    for p in ps:
        for i, c in enumerate(p): out[i] += c
    return out

def mul(p: list[Q], q: list[Q]) -> list[Q]:
    out = [Q(0)] * (len(p) + len(q) - 1)
    for i, x in enumerate(p):
        for j, y in enumerate(q): out[i+j] += x*y
    return out

def scale(p: list[Q], t: Q) -> list[Q]:
    return [x*t for x in p]

def power(p: list[Q], n: int) -> list[Q]:
    r = [Q(1)]
    for _ in range(n): r = mul(r, p)
    return r

def bernstein(p: list[Q], degree: int) -> list[Q]:
    return [sum((p[k]*Q(comb(j,k),comb(degree,k))
                 for k in range(min(j,len(p)-1)+1)),Q(0))
            for j in range(degree+1)]

def dec_interval(x: Q, digits: int = 15) -> list[str]:
    t=10**digits; k=x.numerator*t//x.denominator
    def fmt(n: int) -> str:
        sign='-' if n<0 else ''; n=abs(n)
        return f'{sign}{n//t}.{n%t:0{digits}d}'
    return [fmt(k), fmt(k+1)]

def rat(x: Q) -> str:
    return f'{x.numerator}/{x.denominator}'

def run() -> dict:
    A=8; C=Q(11,10); M=2*C*Q(2,3)**A; N=100
    assert M < Q(1,10)
    assert 2*C*Q(8,9)**A < 1
    assert Q(22,15)*Q(8,9)**A < 1
    # Root confinement and the derivative of the zero equation.
    B=sum((Q(n*(n-1))*Q(2,n)**A for n in range(3,N+1)),Q(0))
    B += Q(2**A,5*N**5)
    assert B < Q(1,3)
    # Candidate upper root M(a,b)=C*c_3/c_2.
    odd=sum((Q(n-1,2)*Q(3,n)**A for n in range(3,N+1,2)),Q(0))
    odd += Q(3**A,12*N**6)
    even=sum((Q(n*(n-1))*Q(2,n)**A for n in range(4,N+1,2)),Q(0))
    even += Q(2**A,5*N**5)
    loc=C*(1-Q(101,200)*even)-Q(101,100)*odd
    assert loc > Q(1,50)
    # Tail in the radial derivative, n >= 7. Parities use different bounds.
    tail=Q(0)
    for n in range(7,N+1):
        if n%2:
            bn=Q(101,200)*(n-3)+Q(11,40)*M*n
        else:
            bn=M*n*Q(101*n-193,400)
        tail += Q(n-1,4)*Q(5,n)**A*bn
    odd_tail=Q(5**A,4)*(Q(101,200)+Q(11,40)*M)*Q(1,5*N**5)
    even_tail=Q(5**A*101,1600)*M*Q(1,4*N**4)
    tail += odd_tail+even_tail
    assert tail < Q(39,100)
    # Finite certificate for the low-mode contribution E(8,b) >= 2/5.
    u=[Q(1),Q(1)]
    certificates=[]
    denominator=7230196133913600
    expected=[
        [1351861016318884,1121529834868342,1434025919811540,
         1462870427049383,221755156299224],
        [1351861016318884,1261248688948063,977124901564326,
         617821376075897,221755156299224],
    ]
    for index,y in enumerate(([Q(0),Q(0),Q(1)],[Q(0),Q(1)])):
        v=add(u,y); w=add(v,[Q(0),Q(0),Q(1)])
        p=add(scale(w,Q(3,5)),
              scale(mul(u,v),-2*C*Q(5,6)**A),
              scale(power(u,3),C*C*Q(20,27)**A),
              scale(mul(power(u,2),w),-6*C*C*Q(4,9)**A))
        bs=bernstein(p,4)
        assert all(x>0 for x in bs)
        assert [x*denominator for x in bs] == expected[index]
        certificates.append({'boundary':'y=x^2' if index==0 else 'y=x',
                             'power_coefficients':[rat(x) for x in p],
                             'bernstein_coefficients':[rat(x) for x in bs]})
    # Explicit large-b thresholds. These are sufficient, not sharp.
    thresholds=[]
    for a in range(1,9):
        delta=Q(2,5)**a-Q(3,8)**a
        b=0
        while Q(1,2)**b >= delta/256: b+=1
        assert Q(1,2)**b < delta/256
        assert Q(1,2)**(b-1) >= delta/256
        thresholds.append({'a':a,'Delta':rat(delta),'sufficient_b_at_least':b})
    # Bounds used for the two-variable perturbation lemma.
    assert Q(304,27)<12
    assert Q(4224,81)<64
    out={'status':'PASS','arithmetic':'fractions.Fraction only',
         'tail_cutoff':N,'outer_order_threshold':A,'C':rat(C),'M8':rat(M),
         'B_upper':rat(B),'B_upper_decimal_interval':dec_interval(B),
         'localization_margin_lower':rat(loc),
         'localization_decimal_interval':dec_interval(loc),
         'radial_tail_upper':rat(tail),'radial_tail_decimal_interval':dec_interval(tail),
         'core_lower':'2/5','proved_Ps_over_c5_lower':'1/100',
         'Bernstein_certificates':certificates,'large_b_thresholds':thresholds}
    (ROOT/'data').mkdir(exist_ok=True)
    (ROOT/'data'/'global_certificate.json').write_text(json.dumps(out,indent=2)+'\n')
    return out

if __name__=='__main__':
    result=run()
    print('PASS: global radial theorem certificates')
    print('B8 upper:',result['B_upper_decimal_interval'])
    print('Localization margin:',result['localization_decimal_interval'])
    print('Radial tail upper:',result['radial_tail_decimal_interval'])
    print('10 positive Bernstein coefficients verified exactly.')
    print('Large-b thresholds:',[(r['a'],r['sufficient_b_at_least']) for r in result['large_b_thresholds']])
