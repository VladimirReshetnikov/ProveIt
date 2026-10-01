#!/usr/bin/env python3
"""Exact symbolic construction and finite basis-population cone diagnostics.

This is a research generator. A successful selected profile is not a theorem
for untested profiles. All arithmetic after symbolic expansion is exact.
"""
from itertools import combinations_with_replacement
from math import comb,lcm
from pathlib import Path
import argparse
import hashlib
import json
import time
import sympy as s

ROOT=Path(__file__).resolve().parent
n=s.symbols('n',positive=True)
p1,p2,m1,m2,t1,t2,q=s.symbols('p1 p2 m1 m2 t1 t2 q')
xs=s.symbols('N1:8')

def count(cols):
    out={0}
    for c in cols:
        out={a|(1<<i) for a in out for i in range(3) if c>>i&1 and not(a>>i&1)}
    return len(out)

def qcount(pop):
    total=sum(pop.values());d=[sum(v for mask,v in pop.items() if mask>>i&1) for i in range(3)]
    c2=lambda x:x*(x-1)/2;c3=lambda x:x*(x-1)*(x-2)/6
    return c3(total)-sum(c3(total-u) for u in d)+sum(c3(pop[i]) for i in (1,2,4))-sum(c2(pop[1<<i])*sum(v for mask,v in pop.items() if mask&(7^(1<<i))==7^(1<<i)) for i in range(3))

def build(J,C1,C2):
    data=json.loads((ROOT/'core_R_block_inverses.json').read_text())[str(J)]
    E=n+J.bit_count();rt=[i+1 for i in data['pivots']]
    inv=s.Matrix([[s.sympify(x,locals={'n':n}) for x in row] for row in data['inverse']])*5*E
    r=s.Matrix([n*S.bit_count()+count([J,S]) for S in rt])
    cross=[];singles=[]
    for C,p,m,t in [(C1,p1,m1,t1),(C2,p2,m2,t2)]:
        x=p+n*C.bit_count()+m*J.bit_count()-t*(C&J).bit_count()+count([J,C])
        z=s.Matrix([p*S.bit_count()+n*count([C,S])+m*count([J,S])-t*(count([J,S])+count([C,S])-count([J|C,S]))+count([J,C,S]) for S in rt])
        cross.append(4*x*r/(5*E)-z);singles.append(x)
    D1=s.cancel(4*singles[0]**2/(5*E)-(cross[0].T*inv*cross[0])[0])
    D2=s.cancel(4*singles[1]**2/(5*E)-(cross[1].T*inv*cross[1])[0])
    off=s.cancel(4*singles[0]*singles[1]/(5*E)-q-(cross[0].T*inv*cross[1])[0])
    den=s.lcm([s.denom(v) for v in (D1,D2,off)])
    den=s.Poly(den,n)
    if any(c<0 for c in den.all_coeffs()):raise RuntimeError(('denominator sign',den))
    den=den.as_expr()
    A=s.cancel(D1*den);B=s.cancel(D2*den);C=s.cancel(off*den)
    pop={i:xs[i-1] for i in range(1,8)}
    vn=sum(pop[i] for i in pop if i&1);vm1=sum(pop[i] for i in pop if i&2);vm2=sum(pop[i] for i in pop if i&4)
    vt1=pop[3]+pop[7];vt2=pop[5]+pop[7]
    allpop=pop.copy()
    for i in range(3):
        mask=((J>>i)&1)+2*((C1>>i)&1)+4*((C2>>i)&1)
        if mask:allpop[mask]+=1
    sub={n:vn,m1:vm1,m2:vm2,t1:vt1,t2:vt2,p1:vn*vm1-vt1*(vt1+1)/2,p2:vn*vm2-vt2*(vt2+1)/2,q:qcount(allpop)}
    pa=s.Poly(s.expand(A.subs(sub)),xs);pb=s.Poly(s.expand(B.subs(sub)),xs);pc=s.Poly(s.expand(C.subs(sub)),xs)
    target=pa*pb-pc*pc
    multiple=lcm(*(int(s.denom(v)) for v in target.coeffs()))
    poly={tuple(e):int(c*multiple) for e,c in target.terms() if c}
    return poly,{'clearing_denominator':str(s.factor(den)),'integer_multiplier':multiple,'degree':target.total_degree(),'base_terms':len(poly)}

def shift_one(poly,i):
    out={}
    for a,v in poly.items():
        for k in range(a[i]+1):
            e=list(a);e[i]=k;e=tuple(e)
            out[e]=out.get(e,0)+v*comb(a[i],k)
    return {e:v for e,v in out.items() if v}

def main():
    parser=argparse.ArgumentParser();parser.add_argument('J',type=int);parser.add_argument('C1',type=int);parser.add_argument('C2',type=int);args=parser.parse_args()
    start=time.time();poly,meta=build(args.J,args.C1,args.C2)
    records=[];cache={():poly};negative=None
    for basis in combinations_with_replacement(range(1,8),3):
        if count(basis)!=1:continue
        for length in range(1,4):
            prefix=basis[:length]
            if prefix not in cache:cache[prefix]=shift_one(cache[prefix[:-1]],prefix[-1]-1)
        shifted=cache[basis];bad=[(e,c) for e,c in shifted.items() if c<0]
        canonical=json.dumps([[list(e),c] for e,c in sorted(shifted.items())],separators=(',',':'))
        rec={'basis':basis,'terms':len(shifted),'negative':len(bad),'minimum':min(shifted.values()) if shifted else 0,'sha256':hashlib.sha256(canonical.encode()).hexdigest()};records.append(rec)
        if bad:
            negative={'basis':basis,'first_negative':bad[:5]};break
    out={'scope':'Exact selected-core certificate diagnostic','core_columns':[args.J,args.C1,args.C2],**meta,'basis_profiles_checked':len(records),'records':records,'negative':negative,'seconds':round(time.time()-start,3)}
    name=f'core_schur_{args.J}_{args.C1}_{args.C2}.json';(ROOT/name).write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k!='records'},indent=2))

if __name__=='__main__':main()
