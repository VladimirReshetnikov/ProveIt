"""Exact Fraction checks; no external dependencies."""
from fractions import Fraction as F
from math import factorial, prod
from collections import namedtuple

class Z(namedtuple('Zbase','r i',defaults=(0,0))):
    def __add__(self,b):
        b = b if isinstance(b,Z) else Z(b)
        return Z(self.r+b.r,self.i+b.i)
    __radd__=__add__
    def __neg__(self): return Z(-self.r,-self.i)
    def __sub__(self,b): return self+-b
    def __mul__(self,b):
        b=b if isinstance(b,Z) else Z(b)
        return Z(self.r*b.r-self.i*b.i,self.r*b.i+self.i*b.r)
    __rmul__=__mul__
    def __truediv__(self,b): return self*F(1,b)
    def __pow__(self,k): return prod([self]*k,start=Z(1))
    def norm1(self): return abs(self.r)+abs(self.i)

def coeff(z):
    A=z*(z+1)/2
    D=-z*(z+1)*(z*2+1)/12
    C=A*A/3
    return A,D,C

def S(z,n):
    A,D,C=coeff(z)
    return A/n+D/n**2+C/n**3

def check():
    num=0
    for R in range(1,17):
        M=R+1
        for z in range(1,R+1):
            A,D,C=coeff(F(z))
            for n in (2*M*M,2*M*M+1,4*M*M,2**42,2**64):
                P=1+A/n+(D+A*A/2)/n**2+(C+A*D+A**3/6)/n**3
                E=factorial(z-1)/prod(1+F(j,n) for j in range(1,z+1))
                assert abs(factorial(z-1)-E*P)<=3*(2+factorial(R-1))*F(M**8,n**4)
                assert abs(P)<=F(3,2)
                if z<=3:
                    assert E*P==factorial(z-1)
                num+=1
    print(num,'exact integer-input checks')
    num=0
    for R in range(1,9):
        M=R+1
        for a in range(1,2*R):
            for b in range(1,2*R-a+1):
                for sg in (-1,1):
                    z=Z(F(a,2),F(sg*b,2))
                    w=z+1
                    for n in (2*M, 2*M+1, 4*M):
                        L=sum((w-w**k)*F((-1)**(k-1),k*n**k) for k in range(2,11))
                        tail=(F(M,n**11)+F(M,n)**11)/(11*(1-F(M,n)))
                        assert (L-S(z,n)+S(z,n+1)).norm1()+tail<=2*F(M**5,n**5)
                        num+=1
    print(num,'nonreal rational local defect enclosures (even in the l1 norm)')
    assert F(3*5040*9**8,2**168)+F(3,2**131)<F(1,2**128)
    print('Exact 128-bit budget: N = 2^42, input absolute error at most 2^-130.')

if __name__=='__main__': check()
