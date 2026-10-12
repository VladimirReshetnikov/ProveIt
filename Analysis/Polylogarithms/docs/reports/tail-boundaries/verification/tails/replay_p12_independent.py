#!/usr/bin/env python3
"""Independent, complete order-twelve certificate replay, standard library only.

Bernoulli input: exact integer polynomial multiplication and series inversion.
Newton coefficients: polynomial conversion in the global parameter b.
Matrix entries: factorial-cancelled Bernoulli coefficient formula.
Determinants: division-free subset Laplace expansion, not Gaussian elimination.
"""
from math import comb,prod,isqrt
from pathlib import Path
from functools import lru_cache
import json,time
from coefficient_norm_bound import newton_coefficients
P=65537
A_ORDER=6
LIMIT=11520
WORD=8


def multiply(left,right,stop):
    """Truncated polynomial product modulo P via exact Kronecker substitution."""
    if not left or not right:return []
    # The unreduced convolution coefficients fit in one 64-bit word.
    assert min(len(left),len(right))*(P-1)**2 < 2**(8*WORD)
    x=int.from_bytes(b''.join(int(c).to_bytes(WORD,'little') for c in left),'little')
    y=int.from_bytes(b''.join(int(c).to_bytes(WORD,'little') for c in right),'little')
    count=len(left)+len(right)-1
    raw=memoryview((x*y).to_bytes(WORD*count,'little'))
    return [int.from_bytes(raw[WORD*j:WORD*(j+1)],'little')%P
            for j in range(min(stop,count))]


def inverse_series(f):
    assert f[0]==1
    g=[1]
    while len(g)<len(f):
        size=min(2*len(g),len(f))
        product=multiply(f[:size],g,size)
        correction=[(-c)%P for c in product]
        correction[0]=(2-product[0])%P
        g=multiply(g,correction,size)
    assert multiply(f,g,len(f))==[1]+[0]*(len(f)-1)
    return g


def bernoulli_coefficients(factorial_inverse):
    # t/(exp(t)-1) is the inverse of sum t^n/(n+1)!.
    return inverse_series(factorial_inverse[1:2*LIMIT+1])


@lru_cache(None)
def laplace_plan(n):
    plan=[]
    for mask in range(1,1<<n):
        cols=[j for j in range(n) if mask&(1<<j)]
        k=len(cols)
        plan.append((k-1,[(j,mask^(1<<j),(-1)**(k-1+pos))
                          for pos,j in enumerate(cols)]))
    return plan


def determinant(matrix):
    dp=[1]+[0]*((1<<len(matrix))-1)
    for mask,(row,terms) in enumerate(laplace_plan(len(matrix)),1):
        dp[mask]=sum(sign*matrix[row][j]*dp[child]
                     for j,child,sign in terms)%P
    return dp[-1]


def evaluate(coeff,b):
    value=0
    for c in reversed(coeff):value=(value*b+c)%P
    return value


def retained(b,mu,fac,fi,inverse,polynomial_d):
    rows=[]
    for i in range(A_ORDER):
        n=b-A_ORDER+i
        ds=[evaluate(polynomial_d[i][h],b) for h in range(1,2*i+2,2)]
        row=[]
        for ell in range(A_ORDER):
            R=2*b-2*A_ORDER+2+2*ell
            F=(fac[2*n]*fi[2*n-2*ell]*fac[2*n+2*ell+2]
               *fi[2*n+2]*fi[2*ell+1])%P
            scale=fac[R]*inverse[2*n+1]*inverse[2*n+2]*fi[2*ell+2]%P
            correction=sum(2*d*mu[2*b-2*(A_ORDER-i+ell+k)]
                           for k,d in enumerate(ds))%P
            row.append((2*F+scale*correction)%P)
        rows.append(row)
    return rows


def original(b,mu,fac,inverse):
    rows=[]
    for i in range(b):
        row=[]
        for k in range(b):
            e=2*(i+k-A_ORDER+1)
            if e<0:row.append(0);continue
            terms=0
            for upper,lower in [(2*i+2,2*A_ORDER-2*k),
                    (2*b+2*i-2*A_ORDER+2,2*b-2*k)]:
                if 2<=lower<=upper:terms+=comb(upper,lower)*inverse[upper]
            row.append(terms*mu[e]*fac[e]%P)
        rows.append(row)
    return rows


def main():
    start=time.perf_counter()
    assert all(P%j for j in range(2,isqrt(P)+1))
    assert 4*LIMIT+5<P
    fac=[1]
    for j in range(1,4*LIMIT+5):fac.append(fac[-1]*j%P)
    fi=[0]*len(fac);fi[-1]=pow(fac[-1],-1,P)
    for j in range(len(fac)-1,0,-1):fi[j-1]=fi[j]*j%P
    inverse=[0]+[fac[j-1]*fi[j]%P for j in range(1,len(fac))]
    mu=bernoulli_coefficients(fi)
    assert all(mu[j]==0 for j in range(3,len(mu),2))
    polynomial_d=[newton_coefficients(A_ORDER,i) for i in range(A_ORDER)]
    residues=[]
    for b in range(A_ORDER+1,LIMIT):
        matrix=(original(b,mu,fac,inverse) if b<2*A_ORDER else
                retained(b,mu,fac,fi,inverse,polynomial_d))
        value=determinant(matrix)
        assert value,(b,value)
        residues.append(value)
    expected=json.loads(Path(__file__).with_name('complete_p12.json').read_text())
    assert residues==expected['determinant_residues']
    result={'a':A_ORDER,'p':2*A_ORDER,'prime':P,'first_b':A_ORDER+1,
      'last_b':LIMIT-1,'case_count':len(residues),
      'all_determinant_residues_nonzero':True,
      'all_residues_match_separate_cpp_verifier':True,
      'bernoulli_method':'exact Kronecker multiplication and Newton series inversion',
      'matrix_method':'factorial-cancelled Bernoulli coefficients with global polynomial Newton coefficients',
      'determinant_method':'division-free subset Laplace expansion',
      'series_inverse_checked_through_degree':len(mu)-1,
      'elapsed_seconds_diagnostic':round(time.perf_counter()-start,3),
      'all_checks_passed':True}
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':main()
