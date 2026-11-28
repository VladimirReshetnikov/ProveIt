"""Exact finite regression checks; standard library only. Not a Lean proof."""
from fractions import Fraction as Q
from math import prod


def endpoint(word, m, start=(0, None)):
    a, b = start
    if b is None: b = m
    for c in word:
        a += c == 'R'
        b -= c == 'D'
        assert 0 <= a <= m and 0 <= b <= m
    return a, b


def sweep(m):
    paths = ['D'*m]*2
    seen = []
    for j in range(m):
        assert paths == ['R'*j+'D'*(m-j)]*2
        assert all(endpoint(w, m) == (j,j) for w in paths)
        # Source diagonal constructor: both prefixes end at (j,j+1).
        assert all(w[-1]=='D' and endpoint(w[:-1], m)==(j,j+1) for w in paths)
        paths = [w[:-1]+'R' for w in paths]
        seen.append((j,j))
        for half in range(2):
            for b in range(j+1,m):
                q='R'*j+'D'*(m-b-1)
                r='D'*(b-j-1)
                assert paths[half]==q+'DR'+r
                assert endpoint(q,m)==(j,b+1)
                assert endpoint(r,m,(j+1,b))==(j+1,j+1)
                paths[half]=q+'RD'+r
                seen.append((j,b) if half==0 else (b,j))
                assert all(endpoint(w,m)==(j+1,j+1) for w in paths)
        assert paths==['R'*(j+1)+'D'*(m-j-1)]*2
    assert paths==['R'*m]*2
    assert len(seen)==m*m and set(seen)=={(i,j) for i in range(m) for j in range(m)}
    assert sum(i==j for i,j in seen)==m
    assert prod(3 if i==j else 1 for i,j in seen)==3**m<=3**(m*m)
    assert prod(2**(j+1) if i==j else 1 for i,j in seen)==2**(m*(m+1)//2)
    return len(seen)

# 2 x 2 rational matrices; no external numerical libraries.
I=((Q(1),Q(0)),(Q(0),Q(1)))
def mul(a,b): return tuple(tuple(sum(a[i][k]*b[k][j] for k in range(2)) for j in range(2)) for i in range(2))
def scale(c,a): return tuple(tuple(c*x for x in row) for row in a)
def tr(a): return tuple(zip(*a))
def mprod(ms):
    result=I
    for a in ms: result=mul(result,a)
    return result


def triangle(m, shift):
    # H's are commuting, invertible symmetric rational matrices; weights and
    # scales vary with both indices. This is a nonconstant-weight model of
    # the two source square laws, not a model of the arithmetic geometry.
    w=lambda n: Q(2+n+shift,1)
    H=lambda k: ((Q(3+k+shift),Q(1)),(Q(1),Q(3+k+shift)))
    aa=lambda i,n: Q(i+2*n+2+shift,n+1)
    dd=lambda i,n: aa(i,0) if n==0 else Q(2*i+n+3+shift,i+1)
    a=lambda i,n: scale(aa(i,n),H(i+n))
    d=lambda i,n: scale(dd(i,n),H(i))
    A=lambda i,n: scale(w(n),a(i,n))
    D=lambda i,n: scale(w(n+1),d(i,n))
    beta=lambda i,n: w(n+2)*dd(i,n+1)*aa(i,n+1)/(w(n)*aa(i+1,n)*dd(i,n))
    kap=lambda i,n: dd(i,n)*aa(i,n+1)/(dd(i,n+1)*aa(i+1,n))
    X=lambda i,n: mprod(A(i,k) for k in reversed(range(n)))
    P=lambda i: mul(D(i,0),A(i,0))
    B=lambda i,n: prod((beta(i,k) for k in range(n)),start=Q(1))
    K=lambda i,n: prod((kap(i,k) for k in range(n)),start=Q(1))
    G=lambda i,n: scale(w(n)/w(0),mul(tr(X(i,n)),X(i,n)))
    S=lambda i: scale(w(0),mul(tr(a(i,0)),a(i,0)))
    count=0
    for i in range(m):
        assert P(i)==G(i,1)==scale(w(1),S(i))
        for n in range(m-i-1):
            assert scale(w(n),mul(a(i+1,n),d(i,n)))==scale(w(n+2)/beta(i,n),mul(d(i,n+1),a(i,n+1)))
            assert mul(d(i,n),tr(a(i,n+1)))==scale(kap(i,n),mul(tr(a(i+1,n)),d(i,n+1)))
            assert mul(A(i+1,n),D(i,n))==scale(1/beta(i,n),mul(D(i,n+1),A(i,n+1)))
            xt=scale(w(n+2),tr(a(i,n+1)))
            assert scale(w(n)/w(0),tr(mul(D(i,n),xt)))==scale(kap(i,n)*w(n+1)/w(0),mul(tr(D(i,n+1)),A(i+1,n)))
            count+=1
        for n in range(m-i):
            assert mul(X(i+1,n),P(i))==scale(1/B(i,n),mul(D(i,n),X(i,n+1)))
            assert scale(w(n+1)/w(0),X(i,n+1))==scale(K(i,n)*w(n)/w(0),mul(tr(D(i,n)),X(i+1,n)))
            assert G(i,n+1)==scale(B(i,n)*K(i,n),mul(tr(P(i)),G(i+1,n)))
    for i in range(m+1):
        for n in range(m-i+1):
            c=prod((beta(p,q-p-1)*kap(p,q-p-1) for p in range(i,i+n) for q in range(p+1,i+n)),start=Q(1))
            expected=scale(w(0)*w(1)**n/w(n)*c,mprod(S(p) for p in range(i,i+n)))
            assert mul(tr(X(i,n)),X(i,n))==expected
    return count

if __name__=='__main__':
    total=sum(sweep(m) for m in range(61))
    print(f'PASS: canonical sweeps m=0..60, {total} total exchanges, exact coverage and costs')
    total=sum(triangle(m,s) for m in range(9) for s in range(4))
    print(f'PASS: 36 rational-matrix triangle models, {total} local squares, chain and Gram identities')
    print('Scope: exact finite checks only; not a verification of the universal theorems or the Lean project.')
