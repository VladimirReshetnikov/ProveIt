#!/usr/bin/env python3
"""Exact corroboration of the all-but-main-projection theorem; no upstream execution.
The analytic shrinking-target theorem is proved in the note, not by these checks.
"""
import argparse
import hashlib
import json
import sys
from pathlib import Path
ROOT=Path(__file__).resolve().parent


def require(test,message):
    if not test:
        raise RuntimeError(message)


class Poly:
    """Small exact multivariate integer polynomial ring, independently written."""
    def __init__(self,value=0):
        self.d=value if isinstance(value,dict) else ({():int(value)} if value else {})
        self.d={m:c for m,c in self.d.items() if c}
    @staticmethod
    def var(name):return Poly({(name,):1})
    @staticmethod
    def cast(x):return x if isinstance(x,Poly) else Poly(x)
    def __add__(self,other):
        other=Poly.cast(other);d=dict(self.d)
        for m,c in other.d.items():d[m]=d.get(m,0)+c
        return Poly(d)
    __radd__=__add__
    def __neg__(self):return Poly({m:-c for m,c in self.d.items()})
    def __sub__(self,other):return self+-Poly.cast(other)
    def __rsub__(self,other):return Poly.cast(other)+-self
    def __mul__(self,other):
        other=Poly.cast(other);d={}
        for m,c in self.d.items():
            for n,e in other.d.items():
                key=tuple(sorted(m+n));d[key]=d.get(key,0)+c*e
        return Poly(d)
    __rmul__=__mul__
    def __pow__(self,n):
        require(type(n) is int and n>=0,'invalid polynomial exponent')
        z=Poly(1)
        for _ in range(n):z=z*self
        return z


def pell(A,n,mod=None):
    require(A>=2 and n>=0,'invalid Pell arguments')
    D=A*A-1
    def mul(x,y):
        z=(x[0]*y[0]+D*x[1]*y[1],x[0]*y[1]+x[1]*y[0])
        return tuple(a%mod for a in z) if mod else z
    z=(1,0);base=(A,1)
    while n:
        if n&1:z=mul(z,base)
        n//=2
        if n:base=mul(base,base)
    return z


def formal_identities():
    q,K,W,r,ell,M=[Poly.var(n) for n in ('q','K','W','r','ell','M')]
    C=W+1;Q=q*q-1;L=q*(q-1)*Q;X=q**3*(1+(q-1)*r)
    P0=Q*((1+q*(K+q**3))*C-q*q-W)-M
    p=P0+L*ell;F=(K+q**3)*C+(q-1)*ell;z=q**3*C*r-ell
    identities={
      'affine_transport':(K+X)*C-F-z*(q-1),
      'affine_negative_packing':-p-((q*q-1-q*F)*Q+M),
      'lattice_progression':Q*((1+q*(K+X))*C-q*q-W)-M-P0-L*q**3*C*r}
    D,h=[Poly.var(n) for n in ('D','h')]
    identities['positive21_single_norm_residual']=(D-h)**2-D**2+h*(2*D-h)
    Y,z,v,a,ea,eb,ek,delta=[Poly.var(n) for n in ('Y','z','v','a','ea','eb','ek','delta')]
    ed=2*ea+eb
    numerator=(Y+z)*(1+2*a*v+3*eb*v)+6*delta*v*z-6*ek*v*z
    reconstructed=(Y+2*Y*a*v+z)*(1+v*ed)+v*(2*Y*(eb-ea)+2*z*(a+eb-ea)+6*delta*z-6*ek*z-2*Y*a*v*ed)
    identities['exact_analytic_G_rearrangement']=numerator-reconstructed
    for name,value in identities.items():require(not value.d,'formal identity failed: '+name)
    return sorted(identities)


def compiler_scale_bounds():
    count=0
    for b in (1,5,25):
        for L in (5,25):
            d=b*L;B=2**d
            for x in range(1,7):
                u=2*d*x+b;W=2**u;q=B**(2*x+2)
                require(q%2==0 and q%3!=0 and (q-1)%(B-1)==0,'q congruence')
                require(q>=W+u-b+2 and q>W>B*B,'loading bound')
                require((B*B-1)*(q*q-1)<q**3,'sharpened K0 bound')
                count+=1
    return {'cases':count,'scope':'structural exponent/bound fixtures, not actual materialized compiler exports'}


def lattice_fixtures():
    count=positive=0
    for q in (8,10,16,32):
        for W in (2,4):
            for K in (1,3,17):
                for M in (2,8,100):
                    C=W+1;Q=q*q-1;L=q*(q-1)*Q
                    P0=Q*((1+q*(K+q**3))*C-q*q-W)-M
                    require(P0%2==1 and L%2==0,'lattice parity')
                    for r in (1,2,7):
                        X=q**3*(1+(q-1)*r)
                        for ell in (-1,0,1,100):
                            p=P0+L*ell;F=(K+q**3)*C+(q-1)*ell;z=q**3*C*r-ell
                            require((p+M)%Q==0,'Q divisibility')
                            N=(p+M)//Q
                            require(N%q==1 and (N-1+q*q)//q==F,'Z=1 recovery')
                            require(-p==(q*q-1-q*F)*Q+M,'packing')
                            require((K+X)*C==F+z*(q-1),'transport')
                            count+=1
                            positive+=int(min(p,F,z)>0)
    return {'cases':count,'positive_outer_arithmetic_cases':positive,
      'scope':'algebra/parity fixtures only; no Pell-ratio claim, compiler counterexample or full zero'}


def residual_fixtures():
    count=zero=nonzero=0
    for q in (2,4,8):
        Y=q**3
        for w in (1,2,3,4):
            X=w*q**3;a=Y*(X+1);A=a+2;Delta=A*A-1;H=4*a+3
            for p in (13,15,17,19):
                D,c=pell(A,p);ga,res=divmod(D-a*c-X,H)
                require(ga>0 and 0<=res<H,'floor quotient positivity')
                require(res==(pow(2,p,H)-X)%H,'main projection remainder')
                Dprime=X+a*c+ga*H
                require(Dprime==D-res and Dprime>0,'triangular positive root')
                require(D*D-Delta*c*c==1,'raw exact Pell norm')
                require(Dprime*Dprime-Delta*c*c-1==-res*(2*D-res),'positive21 residual')
                count+=1;zero+=int(res==0);nonzero+=int(res!=0)
    return {'cases':count,'zero_projection_residues':zero,'nonzero_projection_residues':nonzero,
      'scope':'exact main-block residual fixtures only; no full source or ratio tuple'}


def source_authentication():
    expected={'Report37.snapshot.tex':'57d6598d60389b2fc283f89f47b29ef5905af259ebe0ea69433a8838f9749001',
      'projection.snapshot.json':'ea982f9585eb4e16d756dfc33c73041e73e5e18a38ea37c2302d57c1fe104c92',
      'compiler.snapshot.md':'68edf3bc40238ccf47b023d7358e4be62664a2d78a60b6fae19de14b67208117',
      'complete77.snapshot.py':'9222a13dc180bd2361877674c4bd957d18f2d9aef827852cf5d320a3d7ac7d7a'}
    for name,h in expected.items():require(hashlib.sha256((ROOT/'context'/name).read_bytes()).hexdigest()==h,'source pin mismatch: '+name)
    doc=json.loads((ROOT/'context/projection.snapshot.json').read_bytes())
    modes=[]
    for f in doc['forms']:
        p=f['packet'];mode=p['mode']
        if mode not in ('raw30','positive22'):continue
        rows={r[0]:r[1:] for r in p['source']}
        require(rows['gam']==['*','ga','a4m5'],'ga product')
        require(rows['R14']==['+','D1','gam'],'main projection root')
        require(['L15','R15'] in p['comparisons'],'main norm retained')
        if mode=='raw30':require(['d','R14'] in p['comparisons'],'raw main projection comparison')
        else:require(rows['L15']==['*','R14','R14'],'positive21 triangular norm root')
        modes.append(mode)
    return {'pinned_inputs':expected,'static_modes':modes,'scope':'static data only; no schedule evaluated'}


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--expect',type=Path)
    ap.add_argument('--output',type=Path)
    args=ap.parse_args()
    if args.output:
        target=args.output.resolve()
        require(not target.is_relative_to(ROOT),'--output must be outside packet')
        require(args.expect is None or target!=args.expect.resolve(),'--output must not overwrite --expect')
    result={'scope':'Exact algebraic corroboration, not a proof by sampling or a full-zero search',
      'source_authentication':source_authentication(),'formal_polynomial_identities':formal_identities(),
      'compiler_scale_bounds':compiler_scale_bounds(),'lattice_fixtures':lattice_fixtures(),
      'residual_fixtures':residual_fixtures(),'analytic_distribution_claim':'Proved in manuscript using stated standard estimates, not experimentally certified'}
    data=(json.dumps(result,sort_keys=True,indent=2)+'\n').encode()
    if args.expect:require(data==args.expect.read_bytes(),'frozen receipt mismatch')
    if args.output:args.output.write_bytes(data)
    sys.stdout.buffer.write(data)


if __name__=='__main__':main()
