#!/usr/bin/env python3
"""Exact finite corroboration for report110; not an asymptotic proof.
Standard library only. All mathematical comparisons use integers/Fractions.
Two polynomial reversion routes use logarithmic and exponential identities.
--write-data explicitly generates fixtures; the default verifies them strictly.
"""
from collections import Counter, defaultdict
from fractions import Fraction as F
from functools import cache
from math import comb, factorial
from pathlib import Path
import argparse
import json

ROOT=Path(__file__).resolve().parent
COUNTS=Counter()

def require(ok, message, group='guard'):
    COUNTS[group]+=1
    if not ok:
        raise RuntimeError(message)

def cat(b):
    return comb(2*b,b)//(b+1)

@cache
def direct(m,u,b):
    value=m if u==0 and b==0 else 0
    if u:
        value+=direct(m+1,u-1,b)
    if b:
        value+=sum(direct(m,j,a)*direct(m,u-j,b-1-a)
                   for j in range(u+1) for a in range(b))
    return value

@cache
def by_size(s,m,n):
    if n<0:
        return 0
    value=m if n==s else 0
    if n:
        value+=by_size(s,m+1,n-1)
        value+=sum(by_size(s,m,a)*by_size(s,m,n-1-a) for a in range(n))
    return value

@cache
def shapes(u):
    trees=[('U',None)] if u==1 else [('U',t) for t in shapes(u-1)]
    for a in range(1,u):
        trees.extend(('B',left,right) for left in shapes(a) for right in shapes(u-a))
    return tuple(trees)

def depths(tree,m=0):
    if tree is None:
        return [],[m],0
    if tree[0]=='U':
        intern,leaves,q=depths(tree[1],m+1)
        return [m]+intern,leaves,q
    ia,la,qa=depths(tree[1],m)
    ib,lb,qb=depths(tree[2],m)
    return [m]+ia+ib,la+lb,1+qa+qb

def mul(a,b,degree):
    return [sum(a[j]*b[k-j] for j in range(k+1)) for k in range(degree+1)]

BMAX=9
@cache
def reduced(m,u,h):
    if u==0:
        return tuple(cat(b)*m**(b+1) if h==0 else 0 for b in range(BMAX+1))
    if h<=0 or h>u:
        return (0,)*(BMAX+1)
    numerator=list(reduced(m+1,u-1,h-1))
    for a in range(1,u):
        for hl in range(1,a+1):
            for hr in range(1,u-a+1):
                if max(hl,hr)==h:
                    left,right=reduced(m,a,hl),reduced(m,u-a,hr)
                    for b in range(1,BMAX+1):
                        numerator[b]+=sum(left[j]*right[b-1-j] for j in range(b))
    return tuple(sum(comb(2*j,j)*m**j*numerator[b-j] for j in range(b+1))
                 for b in range(BMAX+1))

# Polynomials in z are tuples of rational coefficients, low degree first.
def trim(a):
    a=list(a)
    while len(a)>1 and a[-1]==0:
        a.pop()
    return tuple(F(v) for v in a)

Z=trim([0,1]); ZERO=trim([0]); ONE=trim([1])
def pa(a,b):
    return trim([(a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0)
                 for i in range(max(len(a),len(b)))])
def ps(a,c):
    return trim([v*c for v in a])
def pm(a,b):
    out=[F(0)]*(len(a)+len(b)-1)
    for i,v in enumerate(a):
        for j,w in enumerate(b):
            out[i+j]+=v*w
    return trim(out)
def sa(a,b):
    return [pa(v,w) for v,w in zip(a,b)]
def ss(a,c):
    return [ps(v,c) for v in a]
def sm(a,b,d):
    out=[ZERO]*(d+1)
    for n in range(d+1):
        for j in range(n+1):
            out[n]=pa(out[n],pm(a[j],b[n-j]))
    return out

def slog(a,d):
    require(a[0]==ONE,'formal log constant','algebra_domain')
    w=list(a); w[0]=ZERO
    power=[ONE]+[ZERO]*d; out=[ZERO]*(d+1)
    for k in range(1,d+1):
        power=sm(power,w,d)
        out=sa(out,ss(power,F((-1)**(k+1),k)))
    return out

def sinv(a,d):
    require(a[0]==ONE,'formal reciprocal constant','algebra_domain')
    out=[ONE]+[ZERO]*d
    for n in range(1,d+1):
        value=ZERO
        for j in range(1,n+1):
            value=pa(value,pm(a[j],out[n-j]))
        out[n]=ps(value,-1)
    return out

def sexp(a,d):
    # Independent coefficient recurrence from E'=a'E, rather than log powers.
    require(a[0]==ZERO,'formal exponential constant','algebra_domain')
    out=[ONE]+[ZERO]*d
    for n in range(1,d+1):
        value=ZERO
        for j in range(1,n+1):
            value=pa(value,ps(pm(a[j],out[n-j]),F(j,n)))
        out[n]=value
    return out

def shift(a,k,d):
    return [ZERO]*k+a[:d+1-k]

def forward(order,method):
    p=[]
    for j in range(1,order+1):
        d=j
        U=[ONE,ps(Z,-1)]+[ZERO]*(d-1)
        for k,value in enumerate(p,1):
            if k+1<=d: U[k+1]=value
        if method=='log':
            coefficient=slog(U,d)[j]
        else:
            S=[ZERO]+p+[ZERO]*(d-len(p))
            coefficient=sm(U,sexp(S,d),d)[j]
        p.append(ps(coefficient,-1))
    d=order+1; U=[ONE,ps(Z,-1)]+p
    rec=sinv(U,d)
    P=[pa(p[j-1],rec[j-1]) for j in range(1,order+1)]
    S=[ZERO]+p+[ZERO]
    require(all(v==ZERO for v in sa(S,slog(U,d))[:order+1]),
            'forward residual','series')
    return p,P

def inverse(order,A,method):
    q=[]
    for j in range(1,order+1):
        d=j; U=[ONE,ps(Z,-1)]+[ZERO]*(d-1)
        for k,value in enumerate(q,1):
            if k+1<=d: U[k+1]=value
        if method=='log':
            V=sinv(U,d)
            arg=[ONE]+[ZERO]*d
            arg=sa(arg,ss(shift(V,1,d),A))
            if d>=2: arg=sa(arg,shift(sm(V,V,d),2,d))
            coefficient=sa(ss(slog(U,d),2),slog(arg,d))[j]
        else:
            core=sa(sm(U,U,d),ss(shift(U,1,d),A))
            if d>=2: core[2]=pa(core[2],ONE)
            S=[ZERO]+q+[ZERO]*(d-len(q))
            coefficient=sm(core,sexp(S,d),d)[j]
        q.append(ps(coefficient,-1))
    d=order+1; U=[ONE,ps(Z,-1)]+q
    core=sa(sm(U,U,d),ss(shift(U,1,d),A)); core[2]=pa(core[2],ONE)
    residual=sm(core,sexp([ZERO]+q+[ZERO],d),d)
    require(residual[0]==ONE and all(v==ZERO for v in residual[1:order+1]),
            'inverse residual','series')
    return q

def serial(polys):
    return [[str(v) for v in p] for p in polys]

def run_checks():
    prefix={0:[0,1,3,14,82,579,4741,43977,454283,5159441,63782411],
            1:[0,0,1,2,4,13,42,139,506,1915,7558]}
    totals={}
    for s in (0,1):
        rows=[]
        for n in range(31):
            N=n+1; r=s+1
            total=sum(direct(0,u,(N-u)//r-1) for u in range(1,N)
                      if (N-u)%r==0)
            require(total==by_size(s,0,n),'size recurrence or parity','size')
            if n<len(prefix[s]):
                require(total==prefix[s][n],'published prefix','prefix')
            rows.append([n,total])
        totals[str(s)]=rows
    D=[defaultdict(int) for _ in range(17)]; D[0][0,0]=1
    for u in range(1,17):
        for (q,h),v in D[u-1].items(): D[u][q,h+1]+=v
        for a in range(1,u):
            for (q1,h1),v1 in D[a].items():
                for (q2,h2),v2 in D[u-a].items():
                    D[u][q1+q2+1,max(h1,h2)]+=v1*v2
        for q in range(u):
            require(sum(v for (qq,h),v in D[u].items() if qq==q)
                    ==cat(q)*comb(u+q-1,2*q),'shape count','shape_dp')
        for (q,h),v in D[u].items():
            require(q<=u-h,'height deficit','shape_dp')
    for u in range(1,8):
        counts=Counter()
        for tree in shapes(u):
            intern,leaves,q=depths(tree); h=max(leaves); d=u-h
            counts[q,h]+=1
            require(q<=d and len(intern)==u+q and len(leaves)==q+1 and max(intern)<h,
                    'tree structure','trees')
            radical=F(1)
            for m in intern: radical/=1-F(m,u)
            require(radical<=F(u**(2*u-1),factorial(u)**2),'coarse radical bound','rational')
            for delta in (F(1,2),F(1,5),F(3,7)):
                rad=F(1)
                for m in intern: rad/=1-(1-delta)*F(m,h)
                bound=F(h**h,factorial(h))*delta**(-2*d)
                require(rad<=bound,'height radical bound','rational')
        require(dict(counts)==dict(D[u]),'explicit and DP shapes','trees')
    height_rows=[]
    for u in range(1,9):
        for b in range(BMAX+1):
            values=[reduced(0,u,h)[b] for h in range(1,u+1)]
            require(sum(values)==direct(0,u,b),'direct and reduced recurrence','height')
            if b==0: require(sum(values)==u,'zero application count','height')
            height_rows.append([u,b,values])
    degree=28
    for u in range(1,11):
        Q=[1]+[0]*degree
        for m in range(u):
            Q=mul(Q,[comb(2*j,j)*m**j for j in range(degree+1)],degree)
        bottom=[cat(j)*u**(j+1) for j in range(degree+1)]
        spine=mul(Q,bottom,degree)
        for b in range(degree+1):
            partial=sum(F(Q[j],(4*u)**j) for j in range(b+1))
            require(spine[b]<=direct(0,u,b),'spine subclass','spine')
            require(spine[b]>=cat(b)*u**(b+1)*partial,'Catalan convolution','spine')
            for j in range(b+1):
                require(cat(b-j)*4**j>=cat(b),'Catalan monotonic ratio','spine')
    for u in range(1,101):
        harmonic=sum(F(1,j) for j in range(1,u+1))
        mean=sum(F(m,2*(u-m)) for m in range(u))
        var=sum(F(m*u,2*(u-m)**2) for m in range(u))
        require(mean==F(u,2)*(harmonic-1),'negative binomial mean','moments')
        require(var<=u*u,'negative binomial variance','moments')
    p,P=forward(8,'log'); p2,P2=forward(8,'exp')
    require(p==p2 and P==P2,'independent forward generators','series')
    known=[(1,1),(0,0,F(1,2)),(0,0,F(-1,2),F(1,3)),
           (0,0,F(1,2),F(-5,6),F(1,4)),
           (0,0,F(-1,2),F(3,2),F(-13,12),F(1,5)),
           (0,0,F(1,2),F(-7,3),F(71,24),F(-77,60),F(1,6))]
    require(P[:6]==[trim(v) for v in known],'printed forward coefficients','series')
    inv={}
    for r in (1,2):
        A=F(r,2)-2
        q=inverse(6,A,'log'); q2=inverse(6,A,'exp')
        require(q==q2,'independent inverse generators','series')
        require(q[0]==trim([-A,2]),'first inverse polynomial','series')
        require(q[1]==trim([A*A/2+2*A-1,-A-4,1]),'second inverse polynomial','series')
        # Treat log(4r) as an independent symbol c for exact constants.
        B=trim([1-F(r,2),1]); aa=trim([A])
        require(pa(aa,B)==trim([-1,1]),'inverse denominator constant','series')
        require(pa(pa(ps(B,-2),ps(aa,-1)),ONE)==trim([1+F(r,2),-2]),
                'inverse denominator correction','series')
        inv[str(r)]=serial(q)
    require(all(len(v)<=j+1 for j,v in enumerate(p,1)),'forward degree bounds','series')
    payload={'counts':dict(sorted(COUNTS.items())), 'total_checks':sum(COUNTS.values()),
             'ranges':{'size_n':[0,30],'shape_dp_u':[1,16],'explicit_shape_u':[1,7],
                       'height_u':[1,8],'height_b':[0,BMAX],'spine_u':[1,10],
                       'spine_b':[0,degree],'moment_u':[1,100],
                       'forward_order':8,'inverse_order':6},
             'arithmetic':'integers and exact rational numbers only',
             'proof_scope':'finite corroboration, not the asymptotic proof'}
    return {'check_results.json':payload,'counts.json':totals,'height_counts.json':height_rows,
            'coefficients.json':{'p':serial(p),'P':serial(P),'q_by_r':inv}}

def unique_pairs(pairs):
    result={}
    for key,value in pairs:
        require(key not in result,'duplicate fixture key')
        result[key]=value
    return result

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write-data',action='store_true')
    args=parser.parse_args()
    data=run_checks(); checks=sum(COUNTS.values())
    directory=ROOT/'data'
    if args.write_data:
        directory.mkdir(exist_ok=True)
        for name,value in data.items():
            (directory/name).write_text(json.dumps(value,indent=2,sort_keys=True)+'\n')
        print(f'WROTE: {len(data)} exact fixtures after {checks} checks')
        return
    actual={p.name for p in directory.iterdir() if p.is_file()}
    require(actual==set(data),'fixture inventory')
    require(all(p.is_file() and not p.is_symlink() for p in directory.iterdir()),'fixture file type')
    for name,expected in data.items():
        try:
            observed=json.loads((directory/name).read_text(),object_pairs_hook=unique_pairs)
        except (ValueError,OSError) as exc:
            raise RuntimeError('invalid fixture '+name) from exc
        require(json.dumps(observed,sort_keys=True)==json.dumps(expected,sort_keys=True),
                'fixture mismatch '+name)
    print(f'PASS: {checks} exact finite checks; all four fixtures match')
    print('Independent forward orders 1-8 and inverse orders 1-6 agree exactly')
    print('No floating-point diagnostics or asymptotic claims are inferred from this run')

if __name__=='__main__':
    main()
