#!/usr/bin/env python3
"""Exact finite diagnostics, with acceptance gates active under python -O."""
import argparse
import ast
from fractions import Fraction as F
from math import factorial
from pathlib import Path
import sys
import sympy as S

MAX_N=30
class VerificationError(RuntimeError):
    pass

def require(condition,label):
    if not condition:
        raise VerificationError(label)

def symbolic_checks(corrupt=None):
    n,k=S.symbols('n k')
    a=(n-k+1)/(n+k);b=(n-k-1)/((n+k)*(n+k-1))
    p=(n-k)/(n+k);q=(n-k-2)/((n+k)*(n+k-1))
    L=(n-k+1)**2/((n+k)*(n+k-1));D=(2*n-2*k+1)/(n+k)
    P=(n-k-1)*(2*n-2*k+1)/((n+k)*(n+k-1)*(n+k-2))
    Q=(2*n-2*k-3)/((n+k)*(n+k-1))
    W=(n-k-1)*(n-k-2)/((n+k)*(n+k-1)*(n+k-2)*(n+k-3))
    equations=[('L',L-a*p.subs(k,k-1)),('D',D-a-p),
      ('P',P-a*q.subs(k,k-1)-b*p.subs({n:n-1,k:k-1},simultaneous=True)),
      ('Q',Q-q-b),('W',W-b*q.subs({n:n-1,k:k-1},simultaneous=True)),
      ('boundary p',p.subs(k,0)-1),('boundary q',q.subs(k,0)-(n-2)/(n*(n-1)))]
    j2=(n-k+1)**2/((n+k)*(n+k-1))
    canceledP2=((n-k-1)/(n-k+1))**2*(2*n-2*k+1)**2/((n+k-2)**2*(n+k)*(n+k-1))
    canceledW2=((n-k-1)*(n-k-2)/(n-k+1))**2/((n+k-2)**2*(n+k-3)**2*(n+k)*(n+k-1))
    if corrupt=='canceled gauge':canceledP2+=1
    equations.extend([('canceled P gauge',P**2/j2-canceledP2),('canceled W gauge',W**2/j2-canceledW2)])
    for label,expr in equations:
        require(S.cancel(expr)==0,'symbolic identity: '+label)
    require(len(equations)==9,'symbolic coverage')
    print('PASS 9 exact rational identities: odd-time elimination, boundary, and canceled gauge bands',flush=True)

def s2(n,k):
    require(type(n) is int and type(k) is int and 1<=n and 0<=k<=n,'squared gauge input domain')
    return F(factorial(n)**3*factorial(n-1),factorial(n-k)**2*factorial(n+k-1)*factorial(n+k))

def r2(n,k):
    require(type(n) is int and type(k) is int and n>=2 and 0<=k<n,'gauge drift input domain')
    return F((n-k)**2*(n+k-1)*(n+k),n**3*(n-1))

def exact_checks(max_n=MAX_N,corrupt=None):
    require(type(max_n) is int and max_n==MAX_N,'coverage must be exactly n=4..30')
    C={};R={}
    for row in range(2*max_n+1):
        C[row,0]=R[row,0]=1
        for col in range(1,row+1):
            C[row,col]=(col+1)*C.get((row-1,col),0)+C[row,col-1]-(col-1)*C.get((row-2,col-1),0)
            R[row,col]=(col+1)*R.get((row-1,col),0)+R[row,col-1]
    require([C[n,n] for n in range(10)]==[1,1,3,15,111,1119,14487,230943,4395855,97608831],'initial diagonal')
    def u(n,k):
        if n<0 or k<0 or k>n:return F(0)
        return F(C[n+k,n-k],factorial(n+k))
    states=diags=lowers=thirds=0
    for n in range(4,max_n+1):
        for k in range(n+1):
            require(0<=C[n+k,n-k]<=R[n+k,n-k],'counting comparison')
            if k==0:
                coeff=F(n-2,n*(n-1))
                if corrupt=='boundary':coeff+=F(1,n)
                value=u(n-1,0)+u(n-1,1)-coeff*u(n-2,0)
            else:
                L=F((n-k+1)**2,(n+k)*(n+k-1));D=F(2*n-2*k+1,n+k)
                P=F((n-k-1)*(2*n-2*k+1),(n+k)*(n+k-1)*(n+k-2))
                Q=F(2*n-2*k-3,(n+k)*(n+k-1))
                W=F((n-k-1)*(n-k-2),(n+k)*(n+k-1)*(n+k-2)*(n+k-3))
                if corrupt=='memory':P+=F(1,n)
                value=L*u(n-1,k-1)+D*u(n-1,k)+u(n-1,k+1)-P*u(n-2,k-1)-Q*u(n-2,k)+W*u(n-3,k-1)
            require(u(n,k)==value,f'exact memory recurrence at n={n},k={k}')
            states+=1
        for k in range(n-1):
            ratio=s2(n-2,k)/s2(n,k)
            require(ratio==r2(n,k)*r2(n-1,k),'diagonal gauge ratio')
            Q=F(n-2,n*(n-1)) if k==0 else F(2*n-2*k-3,(n+k)*(n+k-1))
            require(Q>=0 and Q*Q*ratio<=F(8,n)**2,'diagonal global band check')
            diags+=1
        for k in range(1,n):
            ratio=s2(n-2,k-1)/s2(n,k)
            j2=F((n-k+1)**2,(n+k)*(n+k-1))
            predicted=r2(n,k-1)*r2(n-1,k-1)/j2
            if corrupt=='gauge ratio':predicted+=1
            require(ratio==predicted,'lower gauge ratio')
            P=F((n-k-1)*(2*n-2*k+1),(n+k)*(n+k-1)*(n+k-2))
            require(P>=0 and P*P*ratio<=F(8,n)**2,'lower global band check')
            if k==n-1:require(P==0,'upper B boundary')
            lowers+=1
        for k in range(1,n-1):
            ratio=s2(n-3,k-1)/s2(n,k)
            j2=F((n-k+1)**2,(n+k)*(n+k-1))
            require(ratio==r2(n,k-1)*r2(n-1,k-1)*r2(n-2,k-1)/j2,'third-lag gauge ratio')
            W=F((n-k-1)*(n-k-2),(n+k)*(n+k-1)*(n+k-2)*(n+k-3))
            require(W>=0 and W*W*ratio<=F(8,n*n)**2,'third-lag global band check')
            if k==n-2:require(W==0,'upper F boundary')
            thirds+=1
    require((states,diags,lowers,thirds)==(486,432,432,405),'exact state coverage')
    print(f'PASS exact n=4..30: {states} recurrence states, {diags} diagonal, {lowers} lower, {thirds} third-lag gauge checks',flush=True)

def negative_tests():
    passed=[]
    def rejected(label,operation,fragment):
        try:operation()
        except VerificationError as exc:
            require(fragment in str(exc),f'{label}: wrong rejection reason {exc}')
            passed.append(label);print('PASS rejection: '+label,flush=True);return
        raise VerificationError(label+': corruption accepted')
    rejected('explicit gate',lambda:require(False,'active gate'),'active gate')
    for value in (0,29,31,True):
        rejected('invalid coverage '+repr(value),lambda value=value:exact_checks(value),'coverage')
    for bad in ('boundary','memory','gauge ratio'):
        rejected('altered '+bad,lambda bad=bad:exact_checks(corrupt=bad),'recurrence' if bad!='gauge ratio' else 'lower gauge ratio')
    rejected('altered canceled gauge',lambda:symbolic_checks('canceled gauge'),'canceled P gauge')
    rejected('out of domain gauge',lambda:s2(2,3),'input domain')
    require(len(passed)==10,'negative coverage')
    require(not any(isinstance(x,ast.Assert) for x in ast.walk(ast.parse(Path(__file__).read_text()))),'assert-free acceptance gates')
    print('PASS 10 compacted negative regressions; no optimized-away acceptance gates',flush=True)

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--negative',action='store_true')
    parser.add_argument('--max-n',type=int,choices=(30,),default=30)
    args=parser.parse_args()
    print('Compacted certificate: optimization='+str(sys.flags.optimize),flush=True)
    if args.negative:negative_tests()
    else:symbolic_checks();exact_checks(args.max_n)
    print('COMPLETE: finite algebra diagnostics only; analytic asymptotics are proved in the article',flush=True)

if __name__=='__main__':
    try:main()
    except VerificationError as exc:
        print('FAIL: '+str(exc),file=sys.stderr,flush=True);sys.exit(1)
