#!/usr/bin/env python3
"""Independent finite algebra checks; no halting or consistency claim."""
from pathlib import Path
from itertools import product
from math import gcd,isqrt
import json,random
from build_primitive12 import build,evaluate,WITNESSES,FIXED

def sqrtmod(n,p):
    n%=p;r=pow(n,(p+1)//4,p)
    return r if r*r%p==n else None

def main():
    sys,prod,sos=build();rng=random.Random(121216);p=1000003
    accepted=0;attempts=0
    while accepted<50 and attempts<20000:
        attempts+=1
        values={v:rng.randrange(1,100) for v in WITNESSES+FIXED}
        vals=evaluate(sys,values,p)
        nr={k:(v if isinstance(v,int) else vals[v])%p for k,v in sys['named_registers'].items()}
        H,d=nr['H'],nr['d']
        if H*d%p==0:continue
        fa=sqrtmod(nr['D'],p);ta=sqrtmod(nr['A'],p);gg=sqrtmod(nr['G'],p)
        if None in (fa,ta,gg) or 0 in (fa,ta,gg):continue
        ys={f:sqrtmod((nr['e']-nr['B']*f)*pow(d,-1,p),p) for f in (fa,-fa)}
        if any(y is None or y==0 for y in ys.values()):continue
        expected=pow(d,8,p)*pow(H,16,p)%p
        sums=[]
        for f in (fa,-fa):
            for ty,sy,sg in product((1,-1),repeat=3):
                gamma=(sg*gg-nr['b'])*pow(H,-1,p)%p
                compressed=(gamma+ty*ta+nr['weight_y']*sy*ys[f]+nr['weight_f']*f)%p
                sums.append(compressed);expected=expected*(values['t']-compressed)%p
        actual=nr['primitive_norm']
        if actual!=expected:raise RuntimeError(('norm factorization',attempts,actual,expected))
        new=dict(values);new['t']=rng.choice(sums)
        vnew=evaluate(sys,new,p)
        if vnew[sys['named_registers']['primitive_norm']]!=0:raise RuntimeError('encoded root failed')
        pv=evaluate(prod,values,p)[prod['output']]
        sv=evaluate(sos,values,p)[sos['output']]
        if pv!=(nr['Nk']*nr['Nt']*(1+actual)-1)%p:raise RuntimeError('product')
        if sv!=((nr['Nk']-1)**2+(nr['Nt']-1)**2+actual**2)%p:raise RuntimeError('sos')
        accepted+=1
    if accepted!=50:raise RuntimeError('insufficient independent fixtures')
    guard_checks=0
    for _ in range(1000):
        values={v:rng.randrange(-20,21) for v in WITNESSES+FIXED}
        vals=evaluate(sys,values,4);norm=vals[sys['named_registers']['primitive_norm']]
        if norm not in (0,1):raise RuntimeError(('mod4',norm))
        guard_checks+=1
    rational_cases=0
    for a in range(2,251):
        den=a*a-1
        for V in range(-250,251):
            num=a*a*V*V-1
            if num<0:continue
            g=gcd(num,den);nn,dd=num//g,den//g
            if isqrt(nn)**2==nn and isqrt(dd)**2==dd:
                rational_cases+=1
                if dd!=1:raise RuntimeError(('rational Pell counterexample',a,V,nn,dd))
    report={'independent_norm_factorizations':accepted,'search_attempts':attempts,
            'prime':p,'encoded_root_fixtures':accepted,'mod4_checks':guard_checks,
            'rational_pell_cases_checked':rational_cases,
            'scope':'Finite algebraic diagnostics only; general proofs are in PRIMITIVE12_PROOF.md.'}
    out=Path(__file__).resolve().parent/'generated'/'independent_verification.json';out.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':main()
