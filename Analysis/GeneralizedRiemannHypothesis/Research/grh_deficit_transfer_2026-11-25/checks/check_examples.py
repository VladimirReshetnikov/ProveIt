#!/usr/bin/env python3
"""Exact finite group and kernel checks; numerical prime-sum illustrations only."""
from itertools import permutations
from collections import Counter, defaultdict
from fractions import Fraction as Q
import csv, math, pathlib
OUT = pathlib.Path(__file__).resolve().parent

def mul(a,b): return tuple(a[b[i]] for i in range(len(a)))
def inv(a): return tuple(a.index(i) for i in range(len(a)))
def typ(a):
    seen=set(); lengths=[]
    for i in range(len(a)):
        if i not in seen:
            j=i; n=0
            while j not in seen:
                seen.add(j); j=a[j]; n+=1
            lengths.append(n)
    return tuple(sorted(lengths))
def fixed(a): return sum(i==j for i,j in enumerate(a))
def sign(a): return (-1)**(len(a)-len(typ(a)))

def check_s4():
    G=list(permutations(range(4))); e=tuple(range(4)); r=(1,2,3,0)
    C={e,r,mul(r,r),mul(mul(r,r),r)}
    cosets={frozenset(mul(g,h) for h in C) for g in G}; assert len(cosets)==6
    def chi6(g): return sum(frozenset(mul(g,h) for h in A)==A for A in cosets)
    table={}
    for g in G:
        t=typ(g); v=(sign(g),fixed(g),chi6(g)); assert table.setdefault(t,v)==v
    expected={(1,1,1,1):(1,4,6),(1,1,2):(-1,2,0),(2,2):(1,0,2),(1,3):(1,1,0),(4,):(-1,0,2)}
    assert table==expected
    sizes=Counter(map(typ,G)); m={s:max(v[1]+v[2] for v in table.values() if v[0]==s) for s in (-1,1)}
    weights={t:m[v[0]]-v[1]-v[2] for t,v in table.items()}
    assert weights=={(1,1,1,1):0,(1,1,2):0,(2,2):8,(1,3):9,(4,):0}
    assert sum(sizes[t]*w for t,w in weights.items())==96
    # Class order: 1, transposition, double transposition, 3-cycle, 4-cycle.
    ts=[(1,1,1,1),(1,1,2),(2,2),(1,3),(4,)]
    chars=[[1,1,1,1,1],[1,-1,1,1,-1],[2,0,2,-1,0],[3,1,-1,0,-1],[3,-1,-1,0,1]]
    def ip(a,b): return Q(sum(sizes[t]*u*v for t,u,v in zip(ts,a,b)),24)
    assert all(ip(a,b)==int(i==j) for i,a in enumerate(chars) for j,b in enumerate(chars))
    assert [ip([table[t][1] for t in ts],a) for a in chars]==[1,0,0,1,0]
    assert [ip([table[t][2] for t in ts],a) for a in chars]==[1,0,1,0,1]
    assert [ip([weights[t] for t in ts],a) for a in chars[2:]]==[-1,-1,-1]
    unweighted=[int(t in ((2,2),(1,3))) for t in ts]
    assert [ip(unweighted,a) for a in chars[2:]]==[Q(-1,12),Q(-1,8),Q(-1,8)]
    # Necessity of the two classes in any nonnegative vector with all three
    # nonabelian inner products strictly negative: sum of last two requires
    # double transpositions; degree-2 then requires 3-cycles.
    for t in ts:
        assert not all(a[ts.index(t)]<0 for a in chars[2:])
    assert [chars[3][i]+chars[4][i] for i in range(5)]==[6,0,-2,0,0]
    print('S4: coset characters, orthogonality, weight support, negative projections verified')
    for t in ts: print(' ',t,'class size',sizes[t],'chi4,chi6',table[t][1:],'weight',weights[t])
    return weights

def check_affine():
    for ell in [3,5,7,11,13]:
        G=[(b,a) for b in range(ell) for a in range(1,ell)]
        w=lambda g:int(g[1]==1 and g[0]!=0)
        chi=lambda g:sum((g[1]*x+g[0])%ell==x for x in range(ell))-1
        assert sum(w(g) for g in G)==ell-1
        assert Q(sum(w(g) for g in G),len(G))==Q(1,ell)
        assert Q(sum(w(g)*chi(g) for g in G),len(G))==Q(-1,ell)
        assert Q(sum(chi(g)**2 for g in G),len(G))==1
    print('Affine Kummer groups: exact density and character coefficients for ell=3,5,7,11,13')

def kernel(c,y): return max(Q(0),min(1-1/c,1/y-1/c))
def check_kernel():
    for x in range(1,30):
        for c in [Q(3,2),Q(2),Q(5,2),Q(7)]:
            A=math.ceil(c*x)
            for n in range(1,A+4):
                diff=max(Q(0),Q(1,n)-1/(c*x))-max(Q(0),Q(1,n)-Q(1,x))
                assert diff==kernel(c,Q(n,x))/x
                assert A*diff==max(Q(0),Q(A,n)-A/(c*x))-max(Q(0),Q(A,n)-Q(A,x))
    print('Finite-difference kernel: exact rational identity verified')

def primes(n):
    s=bytearray(b'\1')*(n+1); s[:2]=b'\0\0'
    for p in range(2,math.isqrt(n)+1):
        if s[p]: s[p*p:n+1:p]=b'\0'*((n-p*p)//p+1)
    return [p for p in range(2,n+1) if s[p]]

def factor_type(p):
    # Exact squarefree factorization pattern via gcd degrees, independently
    # of factor selection.  SymPy's finite-field polynomial arithmetic.
    import sympy as sp
    x=sp.Symbol('x'); f=sp.Poly(x**4-x-1,x,modulus=p)
    # Compute x^(p^j) mod f by repeated squaring.
    def power(a,n):
        b=sp.Poly(1,x,modulus=p)
        while n:
            if n&1: b=(b*a).rem(f)
            n//=2
            if n: a=(a*a).rem(f)
        return b
    X=sp.Poly(x,x,modulus=p); r=X; counts={}; t=[]
    for j in range(1,5):
        r=power(r,p)
        d=f.gcd(r-X).degree()
        rest=d-sum(k*counts[k] for k in counts if j%k==0)
        assert rest>=0 and rest%j==0
        counts[j]=rest//j; t += [j]*counts[j]
    assert sum(t)==4
    return tuple(t)

def check_polynomials(weights):
    import sympy as sp
    X=sp.Symbol('X'); assert sp.discriminant(X**4-X-1,X)==-283
    ps=primes(2000); rows=[]; witness={}; count=Counter()
    for p in ps:
        if p==283: continue
        t=factor_type(p); witness.setdefault(t,p); count[t]+=1
        roots=sum((a**4-a-1)%p==0 for a in range(p)); assert roots==t.count(1)
        # parity of factorization checked by discriminant character for odd p
        if p!=2: assert (-1)**(4-len(t))==(1 if pow((-283)%p,(p-1)//2,p)==1 else -1)
        rows.append((p,'+'.join(map(str,t)),weights[t],roots))
    assert witness[(4,)]==2 and (1,3) in witness
    print('S4 polynomial: discriminant -283; first cycle witnesses',witness)
    print('Exact factor types checked for',len(rows),'unramified primes <= 2000')
    with (OUT/'quartic_types.csv').open('w',newline='') as f:
        wr=csv.writer(f); wr.writerow(['p','factor_degrees','weight_8_9','roots']); wr.writerows(rows)
    return rows

def diagnostic(rows):
    def D(x,weighted,delta):
        return sum(w*math.log(p)*max(0.0,min(.5, x/p-.5))/x for p,w in weighted if p<=2*x)-delta*math.log(2)
    ps=primes(200000)
    print('Illustration only: x, cubic D, prime-5 Kummer D, quartic D (latter x<=1000)')
    ws={l:[(p,int(p%l==1 and pow(2,(p-1)//l,p)!=1)) for p in ps if p not in (2,l)] for l in [3,5]}
    out=[]
    for x in [10,30,100,300,1000,3000,10000,30000,100000]:
        a=D(x,ws[3],1/3); b=D(x,ws[5],1/5); q=D(x,[(p,w) for p,t,w,r in rows],4) if x<=1000 else None
        out.append((x,a,b,q)); print(x,format(a,'.8g'),format(b,'.8g'),'-' if q is None else format(q,'.8g'))
    with (OUT/'diagnostics.csv').open('w',newline='') as f:
        wr=csv.writer(f);wr.writerow(['x','Kummer_3_D','Kummer_5_D','S4_8_9_D']);wr.writerows(out)

if __name__=='__main__':
    weights=check_s4(); check_affine(); check_kernel(); rows=check_polynomials(weights); diagnostic(rows)
    print('All exact assertions passed. Numerical diagnostics do not prove asymptotic bounds.')
