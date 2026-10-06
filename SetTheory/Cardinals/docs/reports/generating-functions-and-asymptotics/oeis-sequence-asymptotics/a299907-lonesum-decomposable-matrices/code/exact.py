"""Exact integer enumeration of lonesum-decomposable binary matrices."""
from math import factorial, comb
from fractions import Fraction


def require_nonnegative(n):
    if isinstance(n, bool) or not isinstance(n, int) or n < 0:
        raise ValueError('dimension must be a nonnegative integer')


def list_sets(N):
    require_nonnegative(N)
    B = [1] if N == 0 else [1, 1]
    for k in range(1, N):
        B.append((2*k+1)*B[k] - k*(k-1)*B[k-1])
    return B


def stirling_row(N):
    require_nonnegative(N)
    row = [1]
    for n in range(N):
        row = [0]+[k*(row[k] if k<len(row) else 0)+row[k-1] for k in range(1,n+2)]
    return row


def exact_selected(N, selected):
    require_nonnegative(N)
    incoming=list(selected)
    if any(isinstance(n,bool) or not isinstance(n,int) or not 0<=n<=N for n in incoming):
        raise ValueError('selected dimensions must be integers between zero and N')
    chosen=set(incoming)
    B = list_sets(N)
    facts = [factorial(k) for k in range(N+1)]
    row = [1]
    values={}
    for m in range(1,N+2):
        row=[0]+[k*(row[k] if k<len(row) else 0)+row[k-1] for k in range(1,m+1)]
        n=m-1
        if n in chosen:
            values[n]=sum(facts[k]*B[k]*row[k+1]**2 for k in range(n+1))
    return values


def exact_values(N):
    require_nonnegative(N)
    values=exact_selected(N, range(N+1))
    return [values[n] for n in range(N+1)]


def independent_exact(n):
    """Composition sum for B and finite differences for Stirling numbers."""
    require_nonnegative(n)
    total=0
    for k in range(n+1):
        bk=1 if k==0 else sum(Fraction(factorial(k)*comb(k-1,j-1),factorial(j)) for j in range(1,k+1))
        sk=sum((-1)**(k+1-j)*comb(k+1,j)*j**(n+1) for j in range(k+2))//factorial(k+1)
        total+=factorial(k)*bk*sk**2
    if getattr(total,'denominator',1)!=1:
        raise ArithmeticError('nonintegral exact count')
    return int(total)
