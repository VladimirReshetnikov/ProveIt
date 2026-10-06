#!/usr/bin/env python3
"""Independent, standard-library finite identities. Not an asymptotic proof."""
from __future__ import annotations
import argparse
from fractions import Fraction as F
from functools import lru_cache
from itertools import product
from math import comb, factorial
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
class Invalid(Exception):
    pass

def require(condition, message):
    if not condition:
        raise Invalid(message)

def eq(a, b, message):
    require(a == b, message)

# Q(sqrt(3),i), with exact coefficients in the order 1,h,i,hi.
class K:
    __slots__ = ('v',)
    def __init__(self, a=0, b=0, c=0, d=0):
        if isinstance(a, K):
            self.v = a.v
        else:
            self.v = (F(a), F(b), F(c), F(d))
    def __add__(self, other):
        other = K(other)
        return K(*(a+b for a,b in zip(self.v,other.v)))
    __radd__ = __add__
    def __neg__(self):
        return K(*(-a for a in self.v))
    def __sub__(self, other):
        return self + -K(other)
    def __rsub__(self, other):
        return K(other) + -self
    def __mul__(self, other):
        other = K(other)
        out=[F(0)]*4
        for j,a in enumerate(self.v):
            for k,b in enumerate(other.v):
                # Low bit is sqrt(3); high bit is i.
                scale=(3 if (j&k&1) else 1)*(-1 if (j&k&2) else 1)
                out[j^k] += a*b*scale
        return K(*out)
    __rmul__ = __mul__
    def inverse(self):
        a,b,c,d=self.v
        conj=K(a,b,-c,-d)
        den=self*conj
        u,v,ci,di=den.v
        require(ci==di==0 and u*u-3*v*v != 0, 'zero field denominator')
        return conj*K(u,-v)/(u*u-3*v*v) if v else conj/K(u).rational()
    def __truediv__(self, other):
        other=K(other)
        if other.v[1:]==(0,0,0):
            require(other.v[0]!=0, 'zero rational denominator')
            return K(*(a/other.v[0] for a in self.v))
        return self*other.inverse()
    def __rtruediv__(self, other):
        return K(other)/self
    def __pow__(self, n):
        if n<0:
            return self.inverse()**(-n)
        ans=K(1)
        for _ in range(n): ans=ans*self
        return ans
    def __eq__(self, other):
        try: return self.v==K(other).v
        except (TypeError,ValueError): return False
    def rational(self):
        require(self.v[1:]==(0,0,0), 'nonrational algebraic result')
        return self.v[0]
    def __repr__(self):
        return 'K'+repr(self.v)
H=K(0,1); I=K(0,0,1)

# Dense low-to-high polynomial arithmetic, also valid over K.
def trim(a):
    a=list(a)
    while len(a)>1 and a[-1]==0: a.pop()
    return a or [F(0)]
def padd(a,b):
    out=[F(0)]*max(len(a),len(b))
    for j,v in enumerate(a): out[j]+=v
    for j,v in enumerate(b): out[j]+=v
    return trim(out)
def pscale(a,b): return trim([b*v for v in a])
def psub(a,b): return padd(a,pscale(b,-1))
def pmul(a,b):
    out=[F(0)]*(len(a)+len(b)-1)
    for j,x in enumerate(a):
        for k,y in enumerate(b): out[j+k]+=x*y
    return trim(out)
def ppow(a,n):
    out=[F(1)]
    for _ in range(n): out=pmul(out,a)
    return out
def peval(a,x):
    out=F(0)
    for v in reversed(a): out=out*x+v
    return out
def pder(a): return trim([j*a[j] for j in range(1,len(a))])
def pdiv(a,b):
    a=trim(a); b=trim(b)
    require(b!=[0], 'polynomial zero denominator')
    out=[F(0)]*max(1,len(a)-len(b)+1)
    while a!=[0] and len(a)>=len(b):
        j=len(a)-len(b); v=a[-1]/b[-1]; out[j]=v
        a=psub(a,[0]*j+pscale(b,v))
    return trim(out),trim(a)
def series_div(a,b,n):
    require(b[0]!=0, 'series zero constant')
    out=[]
    for j in range(n):
        rhs=a[j] if j<len(a) else F(0)
        rhs-=sum((b[k]*out[j-k] for k in range(1,min(j,len(b)-1)+1)),F(0))
        out.append(rhs/b[0])
    return out

# Rational functions are compared by exact cross-multiplication, no sampling.
class RF:
    __slots__=('n','d')
    def __init__(self,n=0,d=None):
        if isinstance(n,RF): self.n,self.d=n.n,n.d
        else:
            self.n=trim(n if isinstance(n,list) else [n])
            self.d=trim(d if d is not None else [F(1)])
            require(self.d!=[0], 'rational function denominator is zero')
    def __add__(self,o):
        o=RF(o); return RF(padd(pmul(self.n,o.d),pmul(o.n,self.d)),pmul(self.d,o.d))
    __radd__=__add__
    def __neg__(self): return RF(pscale(self.n,-1),self.d)
    def __sub__(self,o): return self+-RF(o)
    def __rsub__(self,o): return RF(o)+-self
    def __mul__(self,o):
        o=RF(o); return RF(pmul(self.n,o.n),pmul(self.d,o.d))
    __rmul__=__mul__
    def __truediv__(self,o):
        o=RF(o); return RF(pmul(self.n,o.d),pmul(self.d,o.n))
    def __rtruediv__(self,o): return RF(o)/self
    def __pow__(self,n):
        if n<0:return RF(self.d,self.n)**(-n)
        return RF(ppow(self.n,n),ppow(self.d,n))
    def __eq__(self,o):
        o=RF(o);return trim(pmul(self.n,o.d))==trim(pmul(o.n,self.d))
    def derivative(self):
        return RF(psub(pmul(pder(self.n),self.d),pmul(self.n,pder(self.d))),pmul(self.d,self.d))
    def at(self,x): return peval(self.n,x)/peval(self.d,x)

# All finite matrix operations below use Fraction, independently of polynomial formulas.
def eye(n):return [[F(i==j) for j in range(n)] for i in range(n)]
def trans(a):return [list(x) for x in zip(*a)]
def mm(a,b):
    return [[sum((x*y for x,y in zip(row,col)),F(0)) for col in zip(*b)] for row in a]
def madd(a,b):return [[x+y for x,y in zip(ar,br)] for ar,br in zip(a,b)]
def mscale(a,c):return [[x*c for x in r] for r in a]
def mv(a,v):return [sum((x*y for x,y in zip(row,v)),F(0)) for row in a]
def vsub(a,b):return [x-y for x,y in zip(a,b)]
def det(a):
    a=[list(r) for r in a]; out=F(1)
    for j in range(len(a)):
        k=next((k for k in range(j,len(a)) if a[k][j]),None)
        if k is None:return F(0)
        if k!=j:a[j],a[k]=a[k],a[j];out=-out
        pivot=a[j][j];out*=pivot
        for k in range(j+1,len(a)):
            scale=a[k][j]/pivot
            for l in range(j+1,len(a)):a[k][l]-=scale*a[j][l]
    return out

def solve(a,b):
    n=len(a); z=[list(r)+[b[i]] for i,r in enumerate(a)]
    for j in range(n):
        k=next((k for k in range(j,n) if z[k][j]),None)
        require(k is not None,'singular finite system')
        z[j],z[k]=z[k],z[j]; c=z[j][j];z[j]=[v/c for v in z[j]]
        for k in range(n):
            if k!=j:
                c=z[k][j];z[k]=[x-c*y for x,y in zip(z[k],z[j])]
    return [r[-1] for r in z]
def inverse(a):return trans([solve(a,[F(i==j) for i in range(len(a))]) for j in range(len(a))])
def lower(series,n):return [[series[i-j] if i>=j else F(0) for j in range(n)] for i in range(n)]
def pfaffian(a):
    n=len(a);require(n%2==0,'Pfaffian size is odd')
    @lru_cache(None)
    def pf(indices):
        if not indices:return F(1)
        total=F(0)
        for j in range(1,len(indices)):
            rest=indices[1:j]+indices[j+1:]
            total+=(-1)**(j+1)*a[indices[0]][indices[j]]*pf(rest)
        return total
    return pf(tuple(range(n)))

def rising(a,n):
    out=F(1)
    for j in range(n):out*=a+j
    return out

def binomial(x,n):return rising(x-n+1,n)/factorial(n) if n>=0 else F(0)
def choose(a,b):return comb(a,b) if 0<=b<=a else 0

def kernel_entry(i,j,t):
    def q(a,b):
        if min(a,b)<0:return F(0)
        return (t if a==b==0 else 0)+sum(choose(a-da+b-db,a-da) for da,db in ((0,0),(1,0),(0,1),(1,1)) if a>=da and b>=db)
    return sum((q(i-k,j-k-1)-q(i-k-1,j-k) for k in range(min(i,j)+1)),F(0))

def z_reduced(n,t):
    indices=list(range(n)) if n%2==0 else list(range(1,n))
    return pfaffian([[kernel_entry(i,j,t) for j in indices] for i in indices])

def enumerate_dsasm(n):
    rows=[]
    for row in product((-1,0,1),repeat=n):
        s=0;good=True
        for v in row:
            s+=v
            if s not in (0,1):good=False;break
        if good and s==1:rows.append(row)
    count=[0]*(n+1)
    def recurse(matrix,col):
        k=len(matrix)
        if k==n:
            if all(x==1 for x in col):count[sum(matrix[i][i]!=0 for i in range(n))]+=1
            return
        for row in rows:
            if any(row[j]!=matrix[j][k] for j in range(k)):continue
            nxt=[x+y for x,y in zip(col,row)]
            if any(x not in (0,1) for x in nxt):continue
            if k==n-1 and any(x!=1 for x in nxt):continue
            recurse(matrix+[row],nxt)
    recurse([], [0]*n)
    return count


def check_boundary(config,fixtures):
    tested=0; table=[]
    for n in range(1,config['boundary_n_max']+1):
        for ts in config['fugacity_squared']:
            t=F(ts)
            a=[[kernel_entry(i,j,t) for j in range(n+1)] for i in range(n+1)]
            eq(a,mscale(trans(a),-1),'kernel skew symmetry')
            hn=[[a[i][j+1] for j in range(n)] for i in range(n)]
            wn=z_reduced(n,t); wn1=z_reduced(n+1,t)
            eq(det(hn),wn*wn1,'adjacent determinant/Pfaffian identity')
            b=[a[i][0] for i in range(n)]
            v=[(t if i==0 else 0)-b[i] for i in range(n)]
            target=(t if n%2 else 1)*wn/wn1
            eq(solve(hn,v)[-1],target,'all-parity cofactor boundary ratio')
            skew=[r[:n] for r in a[:n]]
            eq(det(skew),wn*wn if n%2==0 else 0,'unbordered skew determinant')
            e0=[F(i==0) for i in range(n)]
            minor=solve(hn,e0)[-1]*det(hn)
            eq(minor,F(0) if n%2==0 else wn*wn,'cofactor parity vanishing and odd border')
            # Formal power series are truncated only after algebraic division.
            b0=series_div(pmul(pmul([-2,1],[1,1]),[-1,2]),pmul([1,-1],[1,-1,1]),n)
            denom=pmul(pmul([2,-1],ppow([1,-1],2)),[1,1])
            gs=series_div([t-1,4-t,t-4],denom,n)
            ws=series_div(pmul([t,-1],[1,-1,1]),denom,n)
            l=[[F(choose(i,j)) for j in range(n)] for i in range(n)]
            e=[[F((-1)**i if i==j else 0) for j in range(n)] for i in range(n)]
            pi=[[F(comb(i+j,i)) for j in range(n)] for i in range(n)]
            jmat=madd(eye(n),mm(lower(gs,n),pi))
            factor=mm(mm(mm(mm(mm(lower(b0,n),l),e),jmat),e),trans(l))
            eq(hn,factor,'exact bordered Pascal factorization')
            eq((-1)**(n-1)*solve(jmat,ws)[-1],target,'Pascal source boundary ratio')
            invb=series_div([1],b0,n)
            pascal_source=mv(e,mv(inverse(l),mv(lower(invb,n),v)))
            eq(pascal_source,ws,'Pascal transformed source')
            qs=series_div([2,1,-1],[1,-1,1],n)
            forcing=mv(lower(qs,n),ws)
            eq(forcing,[t*(j+1)-j for j in range(n)],'forcing q/r cancellation')
            vm=[[F(comb(i+j+2,i)) for j in range(n)] for i in range(n)]
            rc=series_div([1,-1,1],[2,1,-1],n)
            eq(jmat,madd(madd(eye(n),vm),mscale(mm(lower(rc,n),vm),t-3)), 'unnormalized D-conjugate finite matrix identity')
            tested+=1
        table.append({'n':n,'reduced_at_1':str(z_reduced(n,F(1)))})
    enum=[]
    for n in range(1,config['enumeration_n_max']+1):
        counts=enumerate_dsasm(n)
        eq(counts,fixtures['diagonal_distributions'][str(n)],'independent DSASM diagonal enumeration')
        for ts in config['fugacity_squared']:
            t=F(ts)
            reduced=sum(F(v)*t**((j-n%2)//2) for j,v in enumerate(counts) if v)
            eq(reduced,z_reduced(n,t),'enumeration versus independent Pfaffian')
        enum.append({'n':n,'count':sum(counts),'diagonal_coefficients':counts})
    return {'matrix_cases':tested,'n_range':[1,config['boundary_n_max']],'t_values':config['fugacity_squared'],'enumeration':enum,'reduced_at_1':table}


def hahn(n,a,b):
    s=a+b
    out=[K(0)];term=[K(1)]
    pref=(I**n)*rising(2*a,n)*rising(s,n)/factorial(n)
    for k in range(n+1):
        fac=rising(F(-n),k)*rising(n+2*s-1,k)/(rising(2*a,k)*rising(s,k)*factorial(k))
        out=padd(out,pscale(term,pref*fac))
        term=pmul(term,[K(a+k),I])
    return [K(v).rational() for v in out]

def hahn_lead(n,a,b):return rising(n+2*(a+b)-1,n)/factorial(n)
def hv(n):return rising(F(1,3),n)*rising(F(5,3),n)/((2*n+1)*comb(2*n,n)**2)
def hw(n):
    ratio=rising(F(5,3),n)*rising(F(2),n)**2*rising(F(7,3),n)/(F(2*n+3,3)*rising(F(3),n)*factorial(n))
    return F(2,27)*ratio/comb(2*n+2,n)**2

def check_hahn(config):
    maximum=config['hahn_degree_max']
    vpol=[];wpol=[];records=[]
    for n in range(maximum+3):
        p=hahn(n,F(1,6),F(5,6));eq(p[-1],F(comb(2*n,n)),'lowered Hahn leading coefficient')
        vpol.append(pscale(p,1/p[-1]))
    # Monic recurrence generates the moments independently of the Christoffel quotient.
    moments=[];state=[F(1)]+[F(0)]*(2*maximum+3)
    for power in range(2*maximum+3):
        moments.append(state[0]);nxt=[F(0)]*len(state)
        for j,v in enumerate(state):
            if j+1<len(state):nxt[j+1]+=v
            if j:nxt[j-1]+=v*hv(j)/hv(j-1)
        state=nxt
    def inner(p,q):return sum((c*moments[j] for j,c in enumerate(pmul(p,q))),F(0))
    for n in range(maximum+1):
        p=hahn(n,F(5,6),F(7,6));ell=F(comb(2*n+2,n));eq(p[-1],ell,'original Hahn leading coefficient')
        q=pscale(p,1/ell);wpol.append(q)
        r=F((3*n+1)*(3*n+4)*(n+1)*(n+2),36*(2*n+1)*(2*n+3))
        quotient,remainder=pdiv(padd(vpol[n+2],pscale(vpol[n],r)),[F(1,36),0,1])
        eq(remainder,[0],'Christoffel divisibility')
        eq(quotient,q,'lowered-parameter Christoffel polynomial identity')
        expected=(I**n)*rising(F(1,3),n)/comb(2*n,n)
        eq(peval(vpol[n],I/6),expected,'Hahn imaginary-point evaluation')
        eq(hw(n),r*hv(n),'Christoffel norm identity')
        eq(inner(vpol[n],vpol[n]),hv(n),'lowered Hahn norm from Jacobi moments')
        eq(inner(q,pmul(q,[F(1,36),0,1])),hw(n),'Christoffel weighted norm from moments')
        for k in range(n):eq(inner(q,pmul([0]*k+[1],[F(1,36),0,1])),F(0),'Christoffel orthogonality')
        an=rising(F(1,3),n)**2/(comb(2*n,n)**2*hv(n))
        asum=sum((rising(F(1,3),k)**2/(comb(2*k,k)**2*hv(k)) for k in range(n%2,n+1,2)),F(0))
        exactmass=inner(q,q)/hw(n)
        eq(exactmass,asum/(r*an),'positive Christoffel inverse-quadratic mass sum')
        original=2*27**n*hw(n)/hw(0)
        closed=2*F(27,16)**n*factorial(n)*rising(F(3),n)*rising(F(5,3),n)*rising(F(7,3),n)/(rising(F(3,2),n)*rising(F(5,2),n))
        eq(original,closed,'original-variable Hahn norm')
        if n:
            ratio=F(3*n*(n+2)*(3*n+2)*(3*n+4),4*(2*n+1)*(2*n+3))
            eq(original/(2*27**(n-1)*hw(n-1)/hw(0)),ratio,'original Hahn norm recurrence')
        records.append({'degree':n,'r_n':str(r),'inverse_quadratic_mass':str(exactmass),'original_monic_norm':str(original)})
    eq(records[0]['inverse_quadratic_mass'],'27/2','degree-zero mass normalization')
    return {'degree_range':[0,maximum],'records':records,'claim':'Exact finite norm identities only; no weighted-tightness or large-degree limit is inferred.'}


def expand_in_basis(poly,basis):
    out=[F(0)]*len(basis);remainder=trim(poly)
    for j in range(len(basis)-1,-1,-1):
        if len(remainder)==j+1:
            out[j]=remainder[-1]/basis[j][-1]
            remainder=psub(remainder,pscale(basis[j],out[j]))
    eq(remainder,[0],"finite polynomial basis expansion")
    return out

def translation_action(poly):
    def shifted(shift):
        out=[K(0)]
        for k,v in enumerate(poly):out=padd(out,pscale(ppow([shift,1],k),v))
        return out
    ep=(1+I*H)/2;em=(1-I*H)/2
    return [K(v).rational() for v in padd(poly,padd(pscale(shifted(I*H),ep),pscale(shifted(-I*H),em)))]

def check_hahn_resolvent(config):
    maximum=config['boundary_n_max']
    mp=[[F(1)],[F(3,2),F(-1)]]
    for j in range(1,maximum-1):mp.append(psub(pmul([j+F(3,2),-1],mp[-1]),pscale(mp[-2],j*(j+2))))
    monic=[[F(1)],[F(0),F(-1)]];norms=[F(2)]
    for j in range(1,maximum):
        beta=F(3*j*(j+2)*(3*j+2)*(3*j+4),4*(2*j+1)*(2*j+3))
        norms.append(norms[-1]*beta)
        if j<maximum-1:monic.append(psub(pmul([0,-1],monic[-1]),pscale(monic[-2],beta)))
    cases=0
    for n in range(1,maximum+1):
        uu=mp[:n];vv=monic[:n];hn=norms[:n]
        change=[expand_in_basis(p,uu) for p in vv]
        gu=[[F(factorial(i))*rising(F(3),i) if i==j else F(0) for j in range(n)] for i in range(n)]
        gm=[[rising(F(3),i+j) for j in range(n)] for i in range(n)]
        gv=mm(mm(change,madd(gu,gm)),trans(change))
        diag=[[hn[i] if i==j else F(0) for j in range(n)] for i in range(n)]
        eq(gv,diag,'MP Gram to monic Hahn Gram conversion')
        mminus=mm(mm(change,gm),trans(change))
        ku=[expand_in_basis(translation_action(p),uu) for p in uu]
        kv=[expand_in_basis(translation_action(p),vv) for p in vv]
        eq(mm(mm(change,ku),inverse(change)),kv,'exact finite-difference basis conjugacy')
        eq([kv[j][j] for j in range(n)],[F(2)]*n,'finite K diagonal')
        lowering=[[F(i) if i==j+1 else F(0) for j in range(n)] for i in range(n)]
        lsq=mm(lowering,lowering)
        qr=mm(madd(madd(mscale(eye(n),2),lowering),mscale(lsq,-1)),inverse(madd(madd(eye(n),mscale(lowering,-1)),lsq)))
        eq(ku,qr,'imaginary translation versus q/r lowering functional calculus')
        tr=inverse(kv)
        weighted=[[mminus[i][j]/hn[j] for j in range(n)] for i in range(n)]
        adjoint_compression=mm(tr,weighted)
        calibration_source=None
        for ts in config['fugacity_squared']:
            t=F(ts);ellbar=mv(change,[F(factorial(j))*(t*(j+1)-j) for j in range(n)])
            qbar=mv(tr,ellbar)
            finite=madd(mm(kv,diag),mscale(mminus,t-3))
            vector=solve(madd(eye(n),mscale(adjoint_compression,t-3)),qbar)
            x=solve(finite,ellbar)
            eq(vector,[hn[j]*x[j] for j in range(n)],'finite Hahn adjoint resolvent ordering')
            target=(t if n%2 else 1)*z_reduced(n,t)/z_reduced(n+1,t)
            pref=F((-1)**(n-1)*factorial(n-1)*n*(n+1),2)
            eq(pref*x[-1],target,'Hahn boundary-resolvent Pfaffian ratio')
            determinant_ratio=det(finite)/(2**n*product_fractions(hn))
            exact_ratio=z_reduced(n,t)*z_reduced(n+1,t)/(z_reduced(n,F(3))*z_reduced(n+1,F(3)))
            eq(determinant_ratio,exact_ratio,'finite Hahn compression determinant normalization')
            calell=mv(change,[F(factorial(j))*(3*(j+1)-j) for j in range(n)])
            calq=mv(tr,calell)
            eq(vector[-1]/calq[-1],target/(F(3 if n%2 else 1)*z_reduced(n,F(3))/z_reduced(n+1,F(3))),'calibrated Hahn moving-coefficient ratio')
            cases+=1
    return {'n_range':[1,maximum],'t_values':config['fugacity_squared'],'cases':cases,'normalization':'Unnormalized real monic bases; all square-root norms cancel exactly','claim':'Only finite compressed adjoint inverses are used.'}

def product_fractions(values):
    result=F(1)
    for value in values:result*=value
    return result


def jacobi(n,alpha,beta):
    total=[F(0)]
    for k in range(n+1):
        term=pmul(ppow([-1,1],n-k),ppow([1,1],k))
        total=padd(total,pscale(term,binomial(n+alpha,k)*binomial(n+beta,n-k)/2**n))
    return total

def apply_iL(p):
    return pscale(psub(pscale(pmul([1,0,-1],pder(p)),F(1,2)),pmul([F(1,6),1],p)),I)

def check_basis(config):
    for n in range(config['basis_degree_max']+1):
        hp=hahn(n,F(5,6),F(7,6)); transformed=[K(0)];power=[K(1)]
        for coefficient in hp:
            transformed=padd(transformed,pscale(power,coefficient));power=apply_iL(power)
        jp=jacobi(n,F(4,3),F(2,3))
        expected=pscale(jp,(-I)**n*factorial(n+1))
        eq(transformed,expected,'exact continuous-Hahn/Jacobi phase transform')
        eq(pscale(transformed,(-1)**n),pscale(jp,I**n*factorial(n+1)),'negative-leading basis phase i^n')
        eq(jp[-1],F(comb(2*n+2,n),2**n),'Jacobi leading normalization')
        jnorm=F(3,2*n+3)*rising(F(7,3),n)*rising(F(5,3),n)/(factorial(n)*rising(F(3),n))
        hnorm=(hw(n)/hw(0))*comb(2*n+2,n)**2
        eq(hnorm,factorial(n+1)**2*jnorm,'Jacobi/Hahn squared-norm factor')
    # Shift of angular coordinate: conjugating by i^j gives exp(-ir*pi/2).
    for j in range(config['basis_degree_max']+1):
        for k in range(config['basis_degree_max']+1):
            eq((-I)**j*I**k,(-I)**(j-k),'Toeplitz phase factor')
    b0=1-H/2; tau=-b0/2
    eq(tau,H/4-F(1,2),'half-symbol opposite-point constant')
    eq(F(1,4)-F(1,12)+tau,H/4-F(1,3),'first Galerkin correction normalization')
    return {'degree_range':[0,config['basis_degree_max']],'phase':'i^j for negative-leading Hahn basis','b0_coefficients':[str(x) for x in b0.v],'tau_coefficients':[str(x) for x in tau.v],'claim':'Exact phase and constant algebra; the Fourier integral and symbol decay estimates are not numerical tests.'}


def check_source():
    # Affine in t: equality for t=0,1 establishes both exact coefficient identities.
    poles=0
    for m in (-3,-1,1,3):
        y=I*H*m/2
        e=I if m==3 else -I if m==-3 else (H+I)/2 if m==1 else (H-I)/2
        for t in (0,1):
            numerator=H*F(t+1,4)*e**2+(-y-t+F(3,2))*e+H*(t-2)+((1-t)*y/2-t+F(3,2))/e
            eq(numerator,K(0),'source density removable pole numerator')
        poles+=1
    u=RF([0,1]);cos=(1-u*u)/(1+u*u);sin=2*u/(1+u*u)
    def shifted(k):
        values={-1:(H/2,K(-F(1,2))),0:(K(1),K(0)),1:(H/2,K(F(1,2))),2:(K(F(1,2)),H/2)}
        c,s=values[k]
        return cos*c-sin*s,sin*c+cos*s
    def sech(k):
        c,s=shifted(k)
        return RF(H/2)/c, RF(F(3,4))*s/(c*c)
    checks=0
    for t in (0,1):
        ap,dp=sech(1);am,dm=sech(-1);a0,d0=sech(0);a2,d2=sech(2)
        nu=dp+(t-F(3,2))*ap+(1-t)*dm+F(3-t,2)*am
        claimed=3*(3*t*cos+(2-t)*sin*H)/(1+2*(cos*cos-sin*sin))**2
        eq(nu,claimed,'nu transform exact rational-trigonometric identity')
        rho=a2*(H*F(t+1,4))-dp+(-t+F(3,2))*ap+a0*(H*(t-2))+F(1-t,2)*dm+(-t+F(3,2))*am
        divisor=1+(cos*cos-sin*sin)-2*sin*cos*H
        eq(rho,nu/divisor,'rho convolution transform exact rational-trigonometric identity')
        z=-2*sin/(cos*H-sin);rz=1-z+z*z
        eq(rz,3/(cos*H-sin)**2,'inverse eta rational map')
        # r^(-3/2) uses the analytic branch near u=0: (h cos-sin)^3/(3h).
        eq(nu*(cos*H-sin)**3/(3*H),(t-z)/(1-z)**2,'functional source normalization')
        eq(nu.at(F(0)),K(t),'nu mass sqrt(2) normalization')
        checks+=5
    # y is kept formal; exponential r=e^(ay) is a separate indeterminate.
    # Verify calibration simplification separately for coefficients 1 and y.
    r=RF([0,1]);ch=(r+1/r)/2
    for y in (0,1):
        num=r*r*H+(-y-F(3,2))*r+H+(-y-F(3,2))/r
        eq(num,2*(r*H-y-F(3,2))*ch,'calibrated source simplification')
        nudot=r-F(y+F(1,2))/r
        rho3=r*r*H+(-y-F(3,2))*r+H+(-y-F(3,2))/r
        eq(nudot-rho3/(1+r*r),2*ch-H,'source derivative subtraction nu-dot minus m-rho')
    return {'removable_poles':poles,'affine_t_basis':[0,1],'rational_function_equalities':checks+4,'claim':'Identities are exact polynomial cross-products over Q(sqrt(3),i); no quadrature or contour limit is tested.'}


def check_defects(config):
    cases=0;edge_records=[]
    for dimension in config['synthetic_dimensions']:
        # Deliberately nonsymmetric and non-Toeplitz, to expose adjoint/order errors.
        b=[[F((i+2)*(j+3)%7-3,(i+j+2)*5)+F(i==j,3) for j in range(dimension)] for i in range(dimension)]
        bt=trans(b)
        for n in range(1,dimension):
            a=[r[:n] for r in bt[:n]]
            source=[F((-1)**j,j+1) for j in range(dimension)]
            full=source[:];finite=source[:n];defect=[F(0)]*n
            for power in range(config['synthetic_power_max']+1):
                eq(defect,vsub(finite,full[:n]),'finite-section defect definition')
                if power==config['synthetic_power_max']:break
                tail=[F(0)]*n+full[n:]
                rhs=vsub(mv([r[:n] for r in bt[:n]],defect),mv(bt,tail)[:n])
                full=mv(bt,full);finite=mv(a,finite)
                eq(rhs,vsub(finite,full[:n]),'finite-section exact defect recurrence with adjoint')
                defect=rhs;cases+=1
            edge_records.append({'dimension':dimension,'cut':n,'power':config['synthetic_power_max'],'edge_defect':str(defect[-1])})
    # Finite-band, alternating-tail profile arithmetic: evaluate both index forms.
    bands={-2:F(1,15),-1:F(1,10),0:F(1,3),1:F(1,10),2:F(1,15)}
    profiles=[F(0)]*(config['synthetic_power_max']*2+5)
    for power in range(config['synthetic_power_max']):
        kappa=F(power+1,power+2);out=[]
        for r in range(len(profiles)-2):
            toeplitz=sum((bands.get(s-r,F(0))*profiles[s] for s in range(len(profiles))),F(0))
            forcing=sum((bands.get(-r-1-m,F(0))*(-1)**(m+1) for m in range(3)),F(0))
            reindexed=sum((coeff*profiles[r+d] for d,coeff in bands.items() if 0<=r+d<len(profiles)),F(0))
            exterior=sum((coeff*(-1)**(-r-d) for d,coeff in bands.items() if d<=-r-1),F(0))
            eq(toeplitz-kappa*forcing,reindexed-kappa*exterior,'finite-band edge profile reindexing')
            out.append(toeplitz-kappa*forcing)
        profiles=out
    return {'exact_recurrence_steps':cases,'dimensions':config['synthetic_dimensions'],'powers':[0,config['synthetic_power_max']],'edge_records':edge_records,'claim':'Synthetic finite matrices and finite-band reindexing verify algebra only; they establish no DSASM column rate or edge limit.'}


def log_series_of_moments(moments):
    # Coefficients of log(sum m_k u^k/k!), constant normalized to zero.
    p=[moments[k]/factorial(k) for k in range(len(moments))]
    derivative=pder(p);quot=series_div(derivative,p,len(p)-1)
    return [F(0)]+[quot[k-1]/k for k in range(1,len(p))]

def euler(r):return RF([0,1])*r.derivative()
def check_normalization(config,fixtures):
    s=RF([0,1]);p=(s+1)**2/(2*(s+2))
    eq(p.at(H),K(1),'P(sqrt(3)) calibration')
    eq(p.at(F(1)),F(2,3),'P(1) count specialization')
    amplitude4=s*s/(3*p)
    eq(amplitude4.at(F(1)),F(1,2),'fourth-power amplitude factor at s=1')
    eq(amplitude4.at(H),K(1),'fourth-power amplitude calibration')
    # Boundary F(t): logarithmic derivative at t=3.
    dlogp=2*s/(s+1)-s/(s+2)
    eq(dlogp.at(H)/6,1-H/2,'b0 pressure-derivative normalization')
    boundary_log_derivative=(1-dlogp.at(H)/2)/6
    eq(boundary_log_derivative,H/4-F(1,3),'boundary t-derivative calibration')
    cumulants=[];dr=dlogp
    for k in range(1,config['cumulant_order_max']+1):
        leading=dr.at(F(1))/2
        eq(str(leading),fixtures['pressure_cumulants'][str(k)],'pressure cumulant fixture')
        # Test chain-rule normalization on general monomials E(t)=t^m.
        for m in range(0,5):
            left=(2*m)**k/F(2)
            right=2**(k-1)*m**k
            eq(left,right,'Euler chain factor in amplitude cumulants')
        correction=F(k==1,2)-dr.at(F(1))/4
        cumulants.append({'order':k,'n_coefficient':str(leading),'constant_besides_2^(r-1)_EulerE':str(correction)})
        dr=euler(dr)
    for n in range(1,config['enumeration_n_max']):
        dist=fixtures['diagonal_distributions'][str(n)];dist1=fixtures['diagonal_distributions'][str(n+1)]
        order=config['cumulant_order_max']
        def moments(distribution):
            mass=sum(distribution)
            return [sum(F(c)*j**k for j,c in enumerate(distribution))/mass for k in range(order+1)]
        cz=log_series_of_moments(moments(dist));cz1=log_series_of_moments(moments(dist1))
        # D(t) polynomial comes from convolution of independently enumerated Z's.
        ds=[F(0)]*(n+1)
        for i,a in enumerate(dist):
            for j,b in enumerate(dist1):
                if a*b:
                    require((i+j-1)%2==0,'companion parity')
                    ds[(i+j-1)//2]+=a*b
        cd=log_series_of_moments(moments(ds))
        for k in range(1,order+1):
            eq(cz[k]+cz1[k]-F(k==1),2**k*cd[k],'finite companion cumulant normalization')
    # Exact coefficient cancellation in the amplitude-aware inverse ansatz.
    # Here u is a formal stand-in for log r; no finite test evaluates an o-term.
    u=RF([0,1]);inverse_cases=0
    for alpha,beta,kappa,ell in [(F(2,3),F(1,4),F(5,72),F(7,5)),(F(1,7),F(-2,5),F(3,8),F(-4,3)),(F(5,2),F(0),F(1,3),F(0))]:
        shift=-beta/(2*alpha)
        v=(kappa*u+beta*beta/(4*alpha)-ell)/(2*alpha)
        eq(2*alpha*shift+beta,F(0),'inverse coefficient at r')
        eq(alpha*shift*shift+beta*shift+2*alpha*v-kappa*u+ell,RF(0),'inverse constant including log-amplitude sign')
        eq(2*alpha*shift*v+beta*v-kappa*shift,-kappa*shift,'inverse first residual coefficient')
        inverse_cases+=1
    # Schur complement algebra at finite real rational matrices.
    schur_cases=0
    for delta in (F(-1),F(0),F(2,3),F(3)):
        x=[[F(1,5),F(1,7),F(0)],[F(0),F(1,6),F(1,8)]]
        y=[[F(1,9),F(0),F(1,10)],[F(1,11),F(1,12),F(0)]]
        aa=mm(trans(x),x);bb=mm(trans(y),y)
        rx=inverse(madd(eye(2),mscale(mm(x,trans(x)),delta)))
        ry=inverse(madd(eye(2),mscale(mm(y,trans(y)),delta)))
        overlap=mm(x,trans(y))
        rhs=det(madd(eye(2),mscale(mm(mm(mm(ry,trans(overlap)),rx),overlap),-delta*delta)))
        lhs=det(madd(eye(3),mscale(madd(aa,bb),delta)))/(det(madd(eye(3),mscale(aa,delta)))*det(madd(eye(3),mscale(bb,delta))))
        eq(lhs,rhs,'finite mixed-determinant Schur factor order')
        schur_cases+=1
    # Exact single-edge Jacobi variance, checked in a nonsymmetric monic basis.
    jacobi_variances=[]
    for n in range(1,config['basis_degree_max']+1):
        def beta(j):
            return 4*F(j)*(j+F(4,3))*(j+F(2,3))*(j+2)/((2*j+2)**2*(2*j+3)*(2*j+1))
        jac=[[F(0)]*(n+1) for _ in range(n+1)]
        for j in range(n+1):
            jac[j][j]=-F(1,3*(j+1)*(j+2))
            if j<n:jac[j+1][j]=F(1)
            if j:jac[j-1][j]=beta(j)
        squared=mm(jac,jac);compressed=[row[:n] for row in jac[:n]];csquared=mm(compressed,compressed)
        variance=sum(squared[j][j]-csquared[j][j] for j in range(n))
        eq(variance,beta(n),'single-edge Jacobi variance normalization')
        jacobi_variances.append(str(variance))
    leading_ratio=F(4,16)
    eq(leading_ratio,F(1,4),'Jacobi variance leading-coefficient ratio')
    eq(leading_ratio/2,F(1,8),'scalar centered log-determinant factor one-half')
    return {'pressure_cumulants':cumulants,'finite_cumulant_n_range':[1,config['enumeration_n_max']-1],'inverse_coefficient_cases':inverse_cases,'finite_schur_cases':schur_cases,'jacobi_single_edge_variances':jacobi_variances,'claim':'Exact amplitude, inverse-ansatz, cumulant and Schur algebra only; no numerical value of the analytic amplitude is claimed.'}


def reject_duplicates(pairs):
    out={}
    for k,v in pairs:
        require(k not in out,'duplicate JSON key: '+k);out[k]=v
    return out

def read_json(path):
    require(path.is_file() and not path.is_symlink(),'missing or symlinked data file: '+path.name)
    try:
        return json.loads(path.read_text(encoding='utf-8'),object_pairs_hook=reject_duplicates,parse_float=lambda _: (_ for _ in ()).throw(Invalid('JSON floats forbidden')))
    except (json.JSONDecodeError,UnicodeError) as exc:raise Invalid('invalid JSON: '+str(exc)) from exc

def exact_keys(obj,keys,label):
    require(type(obj) is dict and set(obj)==set(keys),label+' has wrong key inventory')

def load_inputs():
    directory=ROOT/'data'
    require(directory.is_dir() and not directory.is_symlink(),'data directory missing or symlinked')
    eq(sorted(p.name for p in directory.iterdir()),['cases.json','expected.json'],'closed data inventory')
    config=read_json(directory/'cases.json');fixtures=read_json(directory/'expected.json')
    required={'schema':'dsasm-report128-exact-cases-v1','boundary_n_max':8,'fugacity_squared':['1/4','1','3','7/2','9'],'enumeration_n_max':5,'hahn_degree_max':12,'basis_degree_max':12,'synthetic_dimensions':[3,5,8],'synthetic_power_max':6,'cumulant_order_max':6}
    exact_keys(config,required,'cases')
    # Canonical range declarations are part of the reproducibility contract.
    for key,value in required.items():
        require(type(config[key]) is type(value) and config[key]==value,'invalid or altered case declaration: '+key)
    exact_keys(fixtures,['schema','diagonal_distributions','pressure_cumulants'],'expected')
    eq(fixtures['schema'],'dsasm-report128-exact-expected-v1','expected schema')
    exact_keys(fixtures['diagonal_distributions'],[str(n) for n in range(1,6)],'diagonal distributions')
    for key,dist in fixtures['diagonal_distributions'].items():
        n=int(key);require(type(dist) is list and len(dist)==n+1,'distribution shape')
        require(all(type(v) is int and v>=0 for v in dist),'distribution entries must be nonnegative integers')
        require(all(v==0 or j%2==n%2 for j,v in enumerate(dist)),'distribution parity')
    exact_keys(fixtures['pressure_cumulants'],[str(n) for n in range(1,7)],'pressure cumulants')
    for value in fixtures['pressure_cumulants'].values():
        require(type(value) is str,'cumulant fraction must be a string')
        try:canonical=str(F(value))
        except (ValueError,ZeroDivisionError) as exc:raise Invalid('invalid rational fixture') from exc
        eq(canonical,value,'noncanonical rational fixture')
    return config,fixtures

def run():
    config,fixtures=load_inputs()
    result={'schema':'dsasm-report128-finite-result-v1','status':'PASS','arithmetic':'Python standard library, exact fractions and Q(sqrt(3),i)','infinite_limits_certified':False}
    result['boundary']=check_boundary(config,fixtures)
    result['hahn_christoffel']=check_hahn(config)
    result['hahn_resolvent']=check_hahn_resolvent(config)
    result['basis_phase']=check_basis(config)
    result['source_algebra']=check_source()
    result['finite_section']=check_defects(config)
    result['normalizations']=check_normalization(config,fixtures)
    result['input_sha256']={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted((ROOT/'data').iterdir())}
    return (json.dumps(result,sort_keys=True,indent=2,ensure_ascii=True)+'\n').encode('ascii')

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,help='Write a new result outside the source package; existing targets are refused')
    args=parser.parse_args()
    try:
        if args.output is not None:
            target=args.output.absolute()
            require(not target.exists() and not target.is_symlink(),'refusing existing output target')
            require(target.parent.is_dir(),'output parent must already exist')
            resolved=target.resolve()
            require(not resolved.is_relative_to(ROOT),'refusing output inside source package')
            require(target==resolved,'refusing noncanonical or symlinked output path')
        payload=run()
        if args.output is None:sys.stdout.buffer.write(payload)
        else:
            with args.output.open('xb') as stream:stream.write(payload)
            print('PASS: exact finite identities; result SHA256 '+hashlib.sha256(payload).hexdigest())
        return 0
    except (Invalid,OSError,ValueError,ZeroDivisionError) as exc:
        print('FAIL: '+str(exc),file=sys.stderr)
        return 1
if __name__=='__main__':
    raise SystemExit(main())
