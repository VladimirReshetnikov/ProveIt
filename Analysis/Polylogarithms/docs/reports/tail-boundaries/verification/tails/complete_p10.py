#!/usr/bin/env python3
"""Exact finite-field certificate for the sole missing p=10 prefix case."""
from math import factorial, comb, isqrt
from pathlib import Path
import json
P = 65537
assert all(P % d for d in range(2,isqrt(P)+1))

def falling(x, m):
    result=1
    for j in range(m): result *= x-j
    return result

def bernoulli_mod(max_n):
    B = [0]*(max_n+1)
    B[0]=1
    if max_n: B[1]=(-pow(2,-1,P))%P
    inv=[0]+[pow(k,-1,P) for k in range(1,max_n+2)]
    for n in range(2,max_n+1,2):
        c=1; s=1
        for k in range(1,n):
            c=c*(n+2-k)*inv[k]%P
            if k==1 or k%2==0: s=(s+c*B[k])%P
        B[n]=(-s*inv[n+1])%P
    return B

def matrix_mod(a,b,B):
    f=[1]
    for j in range(1,2*b+2*a+1): f.append(f[-1]*j%P)
    rows=[]
    for i in range(a):
        n=b-a+i
        W=lambda y:(2*n+2-y)*falling(4*n+2-y,2*i)
        d={h:sum((-1)**(h-j)*comb(h,j)*W(j) for j in range(h+1))//factorial(h)
           for h in range(1,2*i+2,2)}
        row=[]
        for l in range(a):
            N=2*(n-l)+1; R=2*b-2*a+2+2*l
            F=falling(2*n,2*l)*falling(2*n+2*l+2,2*l)*pow(f[2*l+1],-1,P)%P
            fac=f[R]*pow((2*n+1)*(2*n+2)*f[2*l+2]*f[N]%P,-1,P)%P
            corr=sum(d[2*k+1]*falling(N,2*k+1)*2*B[2*b-2*(a-i+l+k)] for k in range(i+1))%P
            row.append((2*F+fac*corr)%P)
        rows.append(row)
    return rows

def det_mod(A):
    A=[row[:] for row in A]; answer=1; pivots=[]
    for k in range(len(A)):
        r=next((r for r in range(k,len(A)) if A[r][k]),None)
        if r is None: return 0,pivots
        if r!=k: A[k],A[r]=A[r],A[k];answer=-answer
        q=A[k][k]; answer=answer*q%P;pivots.append(q)
        qi=pow(q,-1,P)
        for r in range(k+1,len(A)):
            u=A[r][k]*qi%P
            for c in range(k,len(A)): A[r][c]=(A[r][c]-u*A[k][c])%P
    return answer%P,pivots

if __name__=='__main__':
    a,b=5,962
    B=bernoulli_mod(2*b-2)
    A=matrix_mod(a,b,B)
    det,pivots=det_mod(A)
    assert det
    result={'prime':P,'a':a,'b':b,'p':2*a,'q':2*b,
      'bernoulli_values':{str(2*b-2*j):B[2*b-2*j] for j in range(1,2*a)},
      'A_mod_prime':A,'elimination_pivots':pivots,'det_A_mod_prime':det,
      'all_denominator_factors_below_prime':2*b+2*a<P,
      'result':'nonzero, hence the entire p=10 family is proved by the two cited source theorems'}
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
