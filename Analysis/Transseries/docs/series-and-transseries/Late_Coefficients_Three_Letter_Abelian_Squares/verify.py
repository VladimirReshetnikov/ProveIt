#!/usr/bin/env python3
"""Exact arithmetic checks for the A274600 proof; no network required."""
# ed. (2026-10-02): both output files are written with LF line endings on every
# platform (as delivered, the platform's, so CRLF on Windows, where the cmp of
# replay.sh then failed). They are written beside this script; run it on a copy.
from fractions import Fraction as Q
from math import factorial,comb
from pathlib import Path
import json
import mpmath as mp
D=Path(__file__).resolve().parent

def mul(a,b,n):
    c=[Q(0)]*(n+1)
    for i,x in enumerate(a):
        if x:
            for j,y in enumerate(b[:n+1-i]):
                if y:c[i+j]+=x*y
    return c

def compose_F(z,n):
    p=[Q(1)]+[Q(0)]*n; out=p.copy(); h=Q(1)
    mindeg=next(i for i,x in enumerate(z) if x)
    for k in range(1,n//mindeg+1):
        p=mul(p,z,n); h*=Q((2*k-1)**2,4*k*k)
        for j in range(n+1):out[j]+=h*p[j]
    return out

def germ_coefficients(n):
    m=[(-27*Q(-3,2)**j+18*Q(-1,2)**j+8*(j==0)+Q(1,2)**j)/(16*factorial(j)) for j in range(n+1)]
    e=[Q(-3,4)**j/factorial(j) for j in range(n+1)]
    return [x*4**j*factorial(j) for j,x in enumerate(mul(e,compose_F(m,n),n))]

def gb(n,k):
    if k<0:return 0
    if n>=0:return comb(n,k) if k<=n else 0
    return (-1)**k*comb(k-n-1,k)

def recurrence(n):
    a=[1]
    for j in range(1,n+1):
        z=sum(4**(j-k)*(9*gb(1-k,j+1-k)+comb(j+1,k))*a[k] for k in range(j))-12*a[j-1]
        assert z%(8*j)==0,(j,z)
        a.append(z//(8*j))
    return a

def log_multiplier(n):
    w=[(Q(3,2)**j-6*Q(1,2)**j+8*(j==0)-3*Q(-1,2)**j)/(16*factorial(j)) for j in range(n+1)]
    e=[Q(3,4)**j/factorial(j) for j in range(n+1)]
    return mul(e,compose_F(w,n),n)

def fall(n,j):
    p=1
    for k in range(j):p*=n-k
    return p

def main():
    a=recurrence(500)
    first=[1,-1,1,2,7,59,616,6992,90847,1352549,22591681,417527582,8465505412,186906393764,4463901355096,114672825810272,3153127461349327,92405864554182329,2875362251645606611,94680648376734042062,3289274269898822961967,120235993277078434540619]
    assert a[:len(first)]==first
    assert germ_coefficients(30)==a[:31]
    d=log_multiplier(15)
    assert d[:4]==[Q(1),Q(3,4),Q(9,32),Q(5,64)]
    mp.mp.dps=100; L=mp.log(9); C=1/(mp.pi*mp.sqrt(3))
    stats=[]
    for n in [20,40,80,160,320,500]:
        exact=mp.mpf(a[n])/(C*(4/L)**n*mp.factorial(n-1))
        row={'n':n,'ratio_to_leading':mp.nstr(exact,30),'errors':{}}
        for r in [1,2,4,8]:
            est=sum((-1)**j*mp.mpf(d[j].numerator)/d[j].denominator*mp.factorial(j)*L**j/fall(n-1,j) for j in range(r))
            row['errors'][str(r)]=mp.nstr(exact-est,18)
        stats.append(row)
    report={'first_terms_verified':len(first),'independent_germ_terms_verified':31,'largest_index_generated':500,'d_coefficients':[str(x) for x in d],'asymptotic_checks':stats}
    # ed. (2026-10-02): newline='\n' in both writes.
    (D/'verification.json').write_text(json.dumps(report,indent=2)+'\n',newline='\n')
    (D/'coefficients_0_500.txt').write_text('\n'.join(f'{n} {v}' for n,v in enumerate(a))+'\n',newline='\n')
    print(json.dumps(report,indent=2))
if __name__=='__main__':main()
