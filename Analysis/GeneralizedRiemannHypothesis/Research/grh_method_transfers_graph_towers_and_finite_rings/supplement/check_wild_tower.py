"""Exact monic approximants at conductors 9, 27, 81, 243, and 729.
The norm to the cyclotomic base is A^3+3B^3+9C^3-9ABC when
P(alpha)=A+B*pi+C*pi^2 and pi^3=3. Uses only integer arithmetic.
"""
from math import comb


def add(a,b,scale=1):
    c = [0]*max(len(a),len(b))
    for i,x in enumerate(a):
        c[i] += x
    for i,x in enumerate(b):
        c[i] += scale*x
    return c


def product(a,b):
    c = [0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        if x:
            for j,y in enumerate(b):
                c[i+j] += x*y
    return c


def ord_three(n):
    assert n
    s=0
    while n%3==0:
        n//=3
        s+=1
    return s


def value(parts,phi):
    a,b,c=parts
    f=add(add(product(a,product(a,a)),product(b,product(b,b)),3),
          product(c,product(c,c)),9)
    f=add(f,product(a,product(b,c)),-9)
    N=len(phi)-1
    for t in reversed(range(N,len(f))):
        lead=f[t]
        if lead:
            for j,coeff in enumerate(phi):
                f[t-N+j] -= coeff*lead
    return min(i+N*ord_three(x) for i,x in enumerate(f[:N]) if x)


def main():
    for h in range(2,7):
        N=2*3**(h-1)
        n=N//3
        phi=[sum(comb(k,j) for k in (0,N//2,N) if k>=j) for j in range(N+1)]
        parts=[[0]*(n+1) for _ in range(3)]
        parts[0][n]=1
        steps=0
        while (r:=value(parts,phi))%3==0:
            k,j=divmod(r//3,n)
            exp,idx=divmod(k,3)
            d=3**exp
            parts[idx][j]+=d
            if value(parts,phi)==r:
                parts[idx][j]-=2*d
            assert value(parts,phi)>r
            steps+=1
        # r/(3N) is the exact valuation of this monic degree-n test;
        # the residues of valuations of all monomials of lower degree
        # lie in (1/N)Z, so none can increase the last value.
        assert 2*r==5*N-10
        print(f'h={h}, N={N}, highest scaled valuation={r}, corrections={steps}')


if __name__=='__main__':
    main()
