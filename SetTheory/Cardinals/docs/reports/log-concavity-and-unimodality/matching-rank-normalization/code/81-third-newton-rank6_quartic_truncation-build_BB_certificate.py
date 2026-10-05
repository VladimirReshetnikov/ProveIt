#!/usr/bin/env python3
from itertools import combinations,combinations_with_replacement
from math import lcm,comb
from pathlib import Path
import sympy as s,json,hashlib,time,argparse,subprocess
from math import gcd
from functools import reduce
from sympy.polys.matrices import DomainMatrix
from sympy.polys.rings import ring
from build_BB_R import A,B,C,P,block,count
ROOT=Path(__file__).resolve().parent
xs=s.symbols('N1:8')

def match(rows):
    states={0}
    for row in rows:
        states={a|(1<<i) for a in states for i in range(4) if row>>i&1 and not a>>i&1}
    return bool(states)

def qcount(pop):
    total=sum(pop.values());d=[sum(v for mask,v in pop.items() if mask>>i&1) for i in range(3)]
    c2=lambda x:x*(x-1)/2;c3=lambda x:x*(x-1)*(x-2)/6
    return c3(total)-sum(c3(total-u) for u in d)+sum(c3(pop[i]) for i in (1,2,4))-sum(c2(pop[1<<i])*sum(v for mask,v in pop.items() if mask&(7^(1<<i))==7^(1<<i)) for i in range(3))

def counts(J,K,H,n4=None):
    core=[((J>>i)&1)+2*((K>>i)&1)+4*((H>>i)&1) for i in range(3)]
    pop={i:xs[i-1] for i in range(1,8)}
    if n4 is not None:pop[4]=s.Integer(n4)
    full=pop.copy()
    for row in core:
        if row:full[row]+=1
    q=s.Poly(qcount(pop),xs);x=s.Poly(qcount(full),xs)
    v=[]
    for S in range(1,8):
        rows=[row+(((S>>i)&1)<<3) for i,row in enumerate(core)]
        z=q*S.bit_count()
        for U,V in combinations_with_replacement(range(1,8),2):
            c=sum(match([rows[i] for i in I]+[U,V]) for I in combinations(range(3),2))
            if c:z+=s.Poly((pop[U]*(pop[U]-1)/2 if U==V else pop[U]*pop[V])*c,xs)
        for U in range(1,8):
            if match(rows+[U]):z+=s.Poly(pop[U],xs)
        v.append(z)
    return x,v

def fast_product(J,K,H,n4,piv,entries,den):
    x,vs=counts(J,K,H,n4)
    vec=[x]+[vs[i]-x*(i+1).bit_count() for i in piv]
    cm=lcm(*(int(s.denom(v)) for _,_,z in entries for v in z.coeffs()))
    cv=lcm(*(int(s.denom(v)) for z in vec for v in z.coeffs()))
    maxp=max(e[3] for _,_,z in entries for e,v in z.terms())
    if max(2*e[3]+sum(e[:3])+6 for _,_,z in entries for e,v in z.terms())>=64:raise RuntimeError('Exponent packing bound')
    tag=f'{J}_{K}_{H}_{n4}'
    ip=ROOT/f'input_{tag}.txt';op=ROOT/f'raw_{tag}.txt';log=ROOT/f'multiply_{tag}.log'
    with ip.open('w') as f:
        f.write(f'{len(vec)} {len(entries)}\n')
        for z in vec:
            f.write(str(len(z.terms()))+'\n')
            for e,v in z.terms():f.write(str(sum(e[k]<<(6*k) for k in range(7)))+' '+str(int(v*cv))+'\n')
        for i,j,z in entries:
            f.write(f'{i} {j} {len(z.terms())}\n')
            for e,v in z.terms():f.write(' '.join(map(str,e))+' '+str(int(v*cm)*2**(maxp-e[3]))+'\n')
    with ip.open() as f,op.open('w') as g,log.open('w') as h:
        subprocess.run([str(ROOT/'multiply_sparse')],stdin=f,stdout=g,stderr=h,check=True)
    poly={}
    with op.open() as f:
        length=int(f.readline())
        for line in f:
            key,value=map(int,line.split());poly[tuple((key>>(6*k))&63 for k in range(7))]=value
    if len(poly)!=length:raise RuntimeError('Packed output length mismatch')
    content=reduce(gcd,map(abs,poly.values()),0) or 1
    poly={e:v//content for e,v in poly.items()}
    multiplier=s.Rational(cv*cv*cm*2**maxp,content)
    return poly,{'denominator':str(den),'rational_multiplier':str(multiplier),'base_terms':len(poly),'degree':max(map(sum,poly),default=0),'engine':'GMP sparse integer multiplication','input_vector_scale':cv,'input_coefficient_scale':cm,'p_power_scale':maxp,'removed_content':str(content)}

def build(J,K,H,n4=None,fast=False):
    cachepath=ROOT/f'BB_M_centered_{J}_{K}.json'
    if fast and cachepath.exists():
        cache=json.loads(cachepath.read_text())
        entries=[(i,j,s.Poly.from_dict({tuple(e):s.Rational(v) for e,v in terms},(A,B,C,P))) for i,j,terms in cache['entries']]
        den=s.sympify(cache['denominator'],locals={'a':A,'b':B,'c':C,'p':P})
        return fast_product(J,K,H,n4,cache['pivots'],entries,den)
    data=json.loads((ROOT/f'BB_R_{J}_{K}.json').read_text());piv=data['pivots']
    inv=s.Matrix([[s.sympify(z,locals={'a':A,'b':B,'c':C,'p':P}) for z in row] for row in data['inverse']])
    E,r,mat=block(J,K);r=r.extract(piv,[0]);print('loaded inverse',flush=True)
    im=DomainMatrix.from_Matrix(inv).to_field();rm=DomainMatrix.from_Matrix(r).convert_to(im.domain)
    ir=im.matmul(rm).to_Matrix()
    print('formed inverse*r',flush=True)
    M=s.zeros(1+len(piv));M[0,0]=s.cancel((3-9*(r.T*ir)[0])/(4*E))
    for i in range(len(piv)):
        M[0,i+1]=M[i+1,0]=s.cancel(3*ir[i])
        for j in range(len(piv)):M[i+1,j+1]=s.cancel(-4*E*inv[i,j])
    if fast:
        T=s.eye(M.rows)
        for i,k in enumerate(piv):T[i+1,0]=(k+1).bit_count()
        dm=DomainMatrix.from_Matrix(M).to_field();dt=DomainMatrix.from_Matrix(T).convert_to(dm.domain)
        M=dt.transpose().matmul(dm).matmul(dt).to_Matrix()
    print('formed coefficient matrix',flush=True)
    denpoly=s.Poly(1,A,B,C,P)
    for v in M:denpoly=s.lcm(denpoly,s.Poly(s.denom(v),A,B,C,P))
    den=s.factor(denpoly.as_expr())
    print('denominator',den,flush=True)
    x,vs=counts(J,K,H,n4)
    if fast:
        entries=[]
        for i in range(M.rows):
            for j in range(i,M.cols):
                z=s.Poly(s.cancel(M[i,j]*den),A,B,C,P)
                if not z.is_zero:entries.append((i,j,z))
        payload={'pivots':piv,'denominator':str(den),'entries':[[i,j,[[list(e),str(v)] for e,v in z.terms()]] for i,j,z in entries]}
        (ROOT/f'BB_M_centered_{J}_{K}.json').write_text(json.dumps(payload,indent=2)+'\n')
        return fast_product(J,K,H,n4,piv,entries,den)
    ringdata=ring(xs,s.QQ);R=ringdata[0];ys=ringdata[1:]
    vec=[R.from_dict(v.as_dict()) for v in [x]+[vs[i] for i in piv]]
    aa=ys[0]+ys[4];bb=ys[1]+ys[5];cc=ys[2]+ys[6];pp=aa*bb+aa*cc+bb*cc+cc*(cc-1)/2
    cache=[{0:R.one} for _ in range(4)];values=[aa,bb,cc,pp]
    def power(i,k):
        if k not in cache[i]:cache[i][k]=values[i]**k
        return cache[i][k]
    def compose(coef):
        cp=R.zero
        for e,v in s.Poly(coef,A,B,C,P).terms():
            term=R.ground_new(v)
            for k in range(4):term*=power(k,e[k])
            cp+=term
        return cp
    poly=R.zero
    for i in range(M.rows):
        print('population row',i,'terms',len(poly),flush=True)
        for j in range(i,M.cols):
            coef=s.cancel(M[i,j]*den)
            if coef:
                cp=compose(coef)
                poly+=cp*vec[i]*vec[j]*(1 if i==j else 2)
    cancelled=[]
    for factor,multiplicity in s.factor_list(den)[1]:
        divisor=compose(factor)
        for _ in range(multiplicity):
            quotient,remainder=poly.div(divisor)
            if remainder:break
            poly=quotient;den=s.cancel(den/factor);cancelled.append(str(factor))
    print('cancelled',cancelled,'remaining terms',len(poly),flush=True)
    common=lcm(*(int(v.denominator) for v in poly.values()))
    terms={tuple(e):int(c*common) for e,c in poly.items() if c}
    return terms,{'denominator':str(s.factor(den)),'cancelled_factors':cancelled,'multiple':common,'base_terms':len(terms),'degree':max(map(sum,terms),default=0)}

def shift(poly,i):
    out={}
    for e,v in poly.items():
        for k in range(e[i]+1):
            f=list(e);f[i]=k;f=tuple(f);out[f]=out.get(f,0)+v*comb(e[i],k)
    return {e:v for e,v in out.items() if v}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('J',type=int);ap.add_argument('K',type=int);ap.add_argument('H',type=int);ap.add_argument('--n4',type=int,choices=[0,1]);ap.add_argument('--fast',action='store_true');ap.add_argument('--pair-cones',action='store_true');args=ap.parse_args();start=time.time()
    if args.pair_cones:
        if args.n4 not in (None,0):raise RuntimeError('Pair cones require N4=0')
        args.n4=0
    poly,meta=build(args.J,args.K,args.H,args.n4,args.fast);records=[];cache={():poly};bad=None
    bases=(list(combinations_with_replacement([1,2,3,5,6,7],2)) if args.pair_cones else list(combinations_with_replacement(range(1,8),3)))
    for basis in bases:
        if args.pair_cones:
            u,v=basis
            if not ((u&1 and v&2) or (u&2 and v&1)):continue
        else:
            if count(basis)!=1:continue
            if args.n4 is not None and basis.count(4)!=args.n4:continue
        for length in range(1,len(basis)+1):
            pref=basis[:length]
            if pref not in cache:cache[pref]=shift(cache[pref[:-1]],pref[-1]-1)
        target=cache[basis];negative=[(e,c) for e,c in target.items() if c<0]
        canonical=json.dumps([[list(e),c] for e,c in sorted(target.items())],separators=(',',':'))
        records.append({'basis':basis,'terms':len(target),'minimum':min(target.values()) if target else 0,'negative':len(negative),'sha256':hashlib.sha256(canonical.encode()).hexdigest()})
        if negative:bad={'basis':basis,'negative':negative[:10]};break
    out={'core_columns':[args.J,args.K,args.H],'fixed_N4':args.n4,'cone_type':'projected_pair' if args.pair_cones else 'rank_three_basis',**meta,'records':records,'bad':bad,'seconds':time.time()-start}
    suffix='_pairs' if args.pair_cones else ('' if args.n4 is None else f'_n4_{args.n4}')
    (ROOT/f'BB_certificate_{args.J}_{args.K}_{args.H}{suffix}.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k!='records'},indent=2))
if __name__=='__main__':main()
