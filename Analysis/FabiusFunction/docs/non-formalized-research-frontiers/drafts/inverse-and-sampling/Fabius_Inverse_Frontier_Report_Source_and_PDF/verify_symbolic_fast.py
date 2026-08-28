from fractions import Fraction
from math import comb, factorial
import sympy as sp

RMAX=12
M=12

def bernoulli_frac(n):
    q=sp.Rational(sp.bernoulli(n))
    return Fraction(int(q.p),int(q.q))

# d recurrence
d=[Fraction(1)]
for n in range(1,RMAX+1):
    num=sum(Fraction(comb(n+1,k))*d[k] for k in range(n))
    d.append(num/Fraction((n+1)*(2**n-1)))

# b recurrence
gamma=[Fraction(0)]
b=[Fraction(1)]
for k in range(1,RMAX//2+1):
    g=Fraction(((-1)**(k+1))*2**(2*k-1), k*factorial(2*k)*(4**k-1))*bernoulli_frac(2*k)
    gamma.append(g)
    b.append(sum(Fraction(j)*gamma[j]*b[k-j] for j in range(1,k+1))/Fraction(k))

# polynomial array utilities, length M+1
def mul(a,bv):
    out=[Fraction(0) for _ in range(M+1)]
    for i,x in enumerate(a):
        if not x: continue
        for j,y in enumerate(bv[:M+1-i]):
            if y: out[i+j]+=x*y
    return out

def powpoly(a,p):
    out=[Fraction(0)]*(M+1); out[0]=Fraction(1)
    for _ in range(p): out=mul(out,a)
    return out

def compose_coeff(terms, Delta, target):
    # terms list (p,q,c) for c*z^p*Q^q
    powers={0:[Fraction(1)]+[Fraction(0)]*M}
    maxp=max(p for p,q,c in terms)
    for p in range(1,maxp+1): powers[p]=mul(powers[p-1],Delta)
    s=Fraction(0)
    for p,q,c in terms:
        idx=target-q
        if 0<=idx<=M:
            s += c*powers[p][idx]
    return s

print('b first:', b[:5])
for r in range(1,RMAX+1):
    # J coefficient alpha[k]
    alpha={}
    for k in range(1,r+1):
        exp=comb(k+1,2)-comb(r-k,2)
        pow2=Fraction(2**exp) if exp>=0 else Fraction(1,2**(-exp))
        alpha[k]=pow2*d[r-k]/Fraction(factorial(k)*factorial(r-k))
    # A terms
    terms=[]
    for k,c in alpha.items(): terms.append((k,0,c))
    for j in range(1,r//2+1):
        sign=Fraction((-1)**j)*b[j]
        for k,c in alpha.items():
            if k>=2*j:
                deriv_factor=Fraction(factorial(k),factorial(k-2*j))
                terms.append((k-2*j,j,sign*c*deriv_factor))
    # combine
    dic={}
    for p,q,c in terms: dic[(p,q)]=dic.get((p,q),Fraction(0))+c
    terms=[(p,q,c) for (p,q),c in dic.items() if c]
    lin=dic[(1,0)]
    Delta=[Fraction(0)]*(M+1)
    coeffs=[]
    for m in range(1,M+1):
        res=compose_coeff(terms,Delta,m)
        dm=-res/lin
        Delta[m]=dm
        coeffs.append(dm)
    ok=all(compose_coeff(terms,Delta,m)==0 for m in range(1,M+1))
    print(f'r={r:2d} degz={max(p for p,q,c in terms):2d} degQ={max(q for p,q,c in terms):2d} lin={lin} delta1={coeffs[0]} ok={ok}')
    if r<=4:
        print('  alpha=',alpha)
        print('  terms=',sorted(terms,key=lambda t:(t[1],t[0])))
        print('  first3=',coeffs[:3])
    assert ok
