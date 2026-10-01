#!/usr/bin/env python3
"""Exact finite closure of central strips; two independent coefficient formulas."""
from math import comb
import json
from pathlib import Path

def require(condition, message):
    if not condition: raise ArithmeticError(message)

def shifted_product(d,q):
    a=[1]+[0]*d
    for j in range(2*d+q+1):
        c=2*d-j
        for r in range(d,0,-1):a[r]=c*a[r]+a[r-1]
        a[0]*=c
    return a[d]

signed=[[1]]
for n in range(1,91):
    prev=signed[-1]
    row=[0]*(n+1)
    for j in range(n+1):
        row[j]=(prev[j-1] if j else 0)-(n-1)*(prev[j] if j<n else 0)
    signed.append(row)

def stirling_evaluation(d,q):
    n=2*d+q+1
    return sum(signed[n][j]*comb(j,d)*(2*d)**(j-d) for j in range(d,n+1))

certificate=[]
for d in list(range(1,15,2))+list(range(2,22,2)):
    width=5 if d%2 else 9
    for q in range(max(0,2*d-width),2*d+width+1):
        left=shifted_product(d,q)
        right=stirling_evaluation(d,q)
        require(left==right,f'Independent formulas disagree: {(d,q)}')
        require((left==0)==(d%2==0 and q==2*d),f'Unexpected zero status: {(d,q)}')
        certificate.append({'d':d,'q':q,'H':str(left)})
require(len(certificate)==258,'Wrong finite-strip case count')
Path(__file__).with_name('central_strip_certificate.json').write_text(json.dumps(certificate,indent=2)+'\n')
print('PASS: 258 central-strip cases, both exact formulas; only 10 prescribed holes')

count=0
for p in [3,5,7,11,13,17,19]:
    for d in range(1,45):
        for r in range((2*d)%p+1):
            q=(p-2)*d+r-1
            expected=(-1)**d
            for j in range(r):expected=expected*(2*d-j)%p
            got=shifted_product(d,q)%p
            require(got==expected%p and got!=0,f'Prime-block failure: {(p,d,r)}')
            count+=1
print(f'PASS: {count} prime-block cases, seven primes through 19, depths through 44')

# Verify polynomial inequalities used to close the analytic ranges.
for h in range(7,1000):require(4*h*h-28*h+8>0,'Odd threshold failed')
for h in range(10,1000):require(16*h*h-168*h+96>0,'Even threshold failed')
print('PASS: threshold checks; the displayed quadratic arguments prove all higher h')
