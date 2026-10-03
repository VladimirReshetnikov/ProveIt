"""Exact polynomial and finite-word checks of the scalar spectral restriction."""
import argparse
from itertools import product
import json
from math import gcd,lcm
from pathlib import Path
import sympy as sp

Z=sp.Symbol('Z')
POLYNOMIALS=((0,),(1,),(2,),(0,1),(1,1),(1,-1),(1,1,1),(1,0,-1,1),(0,2,-1))


def spectrum(coefficients):
    K=sum(c*Z**j for j,c in enumerate(coefficients));A=1-K
    G=sp.expand(Z**(len(coefficients)-1)*(A*A.subs(Z,1/Z)-1))
    if G==0:
        terms=sp.Poly(A,Z).terms()
        assert len(terms)==1 and abs(terms[0][1])==1
        return dict(K=str(K),exceptional=True,epsilon=int(terms[0][1]),exponent=terms[0][0][0])
    g=sp.Poly(G,Z);D=g.degree();orders=[]
    for n in range(1,2*D*D+1):
        phi=sp.Poly(sp.cyclotomic_poly(n,Z),Z)
        assert n<=2*int(sp.totient(n))**2
        if sp.rem(g,phi).is_zero:orders.append(n)
    return dict(K=str(K),exceptional=False,g=str(g.as_expr()),degree=D,order_bound=2*D*D,orders=orders)


def shift(word,j):
    return tuple(word[(i-j)%len(word)] for i in range(len(word)))


def checks():
    R=32;rows=[];total=admitted=0
    for coefficients in POLYNOMIALS:
        spec=spectrum(coefficients)
        K=sum(c*R**j for j,c in enumerate(coefficients));count=found=0;examples=[]
        for T in range(1,9):
            q=R**T
            for L in (1,2):
                if T%L:continue
                N=T//L;B=R**L;J=(q-1)//(B-1)
                P=lcm(L,*spec.get('orders',[]))
                for u in product((0,1,2),repeat=T):
                    U=sum(d*R**j for j,d in enumerate(u))
                    Ku=tuple(sum(c*u[(i-j)%T] for j,c in enumerate(coefficients)) for i in range(T))
                    for h in range(N):
                        shifted=shift(u,L*h)
                        v=tuple(Ku[i]+shifted[i]-u[i] for i in range(T))
                        lam=v[:L];residual=[v[i]-lam[i%L] for i in range(T)]
                        assert max(abs(c) for c in residual)<=R-2
                        lamword=sum(c*R**i for i,c in enumerate(lam))
                        arithmetic=((K+R**(L*h)-1)*U-lamword*J)%(q-1)==0
                        semantic=all(c==0 for c in residual)
                        assert arithmetic==semantic
                        if arithmetic:
                            found+=1
                            if spec['exceptional']:
                                a=spec['exponent'];eps=spec['epsilon'];forcing=tuple(lam[i%L] for i in range(T))
                                rhs=tuple(eps*u[i]+shift(forcing,-a)[i] for i in range(T))
                                assert shift(u,L*h-a)==rhs
                            else:
                                assert P%L==0 and shift(u,gcd(P,T))==u
                                if len(set(u))>1 and len(examples)<2:
                                    examples.append(dict(T=T,L=L,h=h,u=list(u),lambda_digits=list(lam),period_bound=P))
                        count+=1
        rows.append(dict(coefficients=list(coefficients),spectrum=spec,candidates=count,admitted=found,examples=examples))
        total+=count;admitted+=found
    return dict(radix=R,alphabet=[0,1,2],maximum_digit_length=8,candidates=total,admitted=admitted,domains=rows)


def verify():
    return dict(status='PASS_SINGLE_FIELD_SPECTRAL_PERIOD',audit=checks(),
                scope='Coefficientwise scalar convolution and fixed periodic forcing; variable carry streams excluded',
                established_complete_universal_bound=76)


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=verify();path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(json.dumps(dict(status=result['status'],candidates=result['audit']['candidates'],admitted=result['audit']['admitted']),indent=2))
