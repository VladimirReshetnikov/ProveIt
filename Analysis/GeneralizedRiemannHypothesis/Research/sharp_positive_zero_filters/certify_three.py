#!/usr/bin/env python3
"""Pure-integer outward interval certificate for a three-frequency optimum.
Proves a uniform result for the explicit rational frequency boxes below.
Does not itself compute or certify the zeta zeros (see the paper for source).
No third-party libraries needed. Run: python certify_three.py.
"""
from fractions import Fraction
from math import factorial
S=10**30
class I:
    __slots__=('lo','hi')
    def __init__(self,lo,hi):
        assert lo<=hi
        self.lo,self.hi=lo,hi
    @staticmethod
    def q(x):
        if isinstance(x,I):return x
        f=Fraction(x)*S
        return I(f.numerator//f.denominator,-((-f.numerator)//f.denominator))
    @staticmethod
    def box(a,b):return I(I.q(a).lo,I.q(b).hi)
    def __add__(a,b):
        b=I.q(b);return I(a.lo+b.lo,a.hi+b.hi)
    __radd__=__add__
    def __neg__(a):return I(-a.hi,-a.lo)
    def __sub__(a,b):return a+-I.q(b)
    def __rsub__(a,b):return I.q(b)+-a
    def __mul__(a,b):
        b=I.q(b);v=[a.lo*b.lo,a.lo*b.hi,a.hi*b.lo,a.hi*b.hi]
        return I(min(v)//S,-((-max(v))//S))
    __rmul__=__mul__
    def divint(a,b):
        assert isinstance(b,int) and b>0
        return I(a.lo//b,-((-a.hi)//b))
    def mag(a):return max(abs(a.lo),abs(a.hi))
    def mid(a):return Fraction(a.lo+a.hi,2*S)
    def __repr__(a):return '[%.12g, %.12g]'%(a.lo/S,a.hi/S) # display only

def trig(x,sine):
    # Taylor at the exact dyadic/decimal-grid midpoint, with rigorous remainder
    # and a Lipschitz extension to the whole interval.
    assert max(abs(x.lo),abs(x.hi))<=7*S
    m=(x.lo+x.hi)//2;v=I(m,m);v2=v*v
    term=v if sine else I.q(1);ans=term
    for k in range(1,41):
        den=(2*k)*(2*k+1) if sine else (2*k-1)*(2*k)
        term=(-(term*v2)).divint(den);ans=ans+term
    assert 7**81*S<factorial(81) and 7**82*S<factorial(82)
    e=max(m-x.lo,x.hi-m)+1
    return I(ans.lo-e,ans.hi+e)
def sin(x):return trig(x,True)
def cos(x):return trig(x,False)
def dot(a,b):return sum(x*y for x,y in zip(a,b))
def cross(a,b):return [a[(i+1)%3]*b[(i+2)%3]-a[(i+2)%3]*b[(i+1)%3] for i in range(3)]
def invert(A):
    # Exact rational Gaussian elimination; result enclosed on the grid later.
    M=[list(row)+[Fraction(i==j) for j in range(3)] for i,row in enumerate(A)]
    for j in range(3):
        k=next(i for i in range(j,3) if M[i][j]);M[j],M[k]=M[k],M[j]
        d=M[j][j];M[j]=[x/d for x in M[j]]
        for i in range(3):
            if i!=j:
                d=M[i][j];M[i]=[x-d*y for x,y in zip(M[i],M[j])]
    return [row[3:] for row in M]

lam=[I.box('14.1347251417','14.1347251418'),I.box('21.0220396387','21.0220396388'),I.box('25.0108575801','25.0108575802')]
x0=[I.q(x) for x in ('0.0794453460700645','0.2349726063584985','0.6943858328459642')]
r=I.q('0.00000001').lo
X=[I(x.lo-r,x.hi+r) for x in x0]

def f(X):
    t,T,w=X
    return [w*cos(l*t)+(1-w)*cos(l*T) for l in lam]
def jac(X):
    t,T,w=X
    return [[-w*l*sin(l*t),-(1-w)*l*sin(l*T),cos(l*t)-cos(l*T)] for l in lam]
Aq=invert([[x.mid() for x in row] for row in jac(x0)])
A=[[I.q(x) for x in row] for row in Aq]
J=jac(X)
err=[[I.q(i==j)-dot(A[i],[J[k][j] for k in range(3)]) for j in range(3)] for i in range(3)]
q=max(sum(x.mag() for x in row) for row in err) # scaled by S
res=max(dot(row,f(x0)).mag() for row in A)
assert q<I.q("0.000004").lo and res<I.q("0.0000000000058").lo
assert q<S//2 and res*S+q*r<r*S
print('Frequency boxes:',lam)
print('Solution box:',X)
print('Contraction infinity norm upper bound:',q/S)
print('Center displacement infinity norm upper bound:',res/S)
print('PASS: uniform contraction maps box strictly into itself.')

t,T,w=X
assert 0<t.lo<t.hi<T.lo<T.hi and 0<w.lo<w.hi<S
c=cross([cos(l*t) for l in lam],[-l*sin(l*t) for l in lam])
if sum(c).hi<0:c=[-v for v in c]
assert sum(c).lo>0

def g(u,order=0):
    if order==0:return sum(a*cos(l*u) for a,l in zip(c,lam))
    if order==1:return -sum(a*l*sin(l*u) for a,l in zip(c,lam))
    if order==2:return -sum(a*l*l*cos(l*u) for a,l in zip(c,lam))
    raise ValueError
# Choose exact rational neighborhoods around the variable inner/outer nodes.
left=I.q('0.075').lo;right=I.q('0.084').lo;tail=I.q('0.230').lo
assert left<t.lo<t.hi<right<tail<T.lo
def range_sub(lo,hi,k):
    vs=[g(I(lo+(hi-lo)*j//32,lo+(hi-lo)*(j+1)//32),k) for j in range(32)]
    return I(min(v.lo for v in vs),max(v.hi for v in vs))
curv=range_sub(left,right,2);slope=range_sub(tail,T.hi,1)
assert curv.lo>0 and slope.hi<0
print('Unnormalized dual coefficient boxes:',c)
print('g\'\' on inner neighborhood:',curv)
print('g\' on endpoint neighborhood:',slope)
# Certify the remaining compact pieces by exact interval bisection.
stack=[(0,left),(right,tail)];n=0;mind=None
while stack:
    lo,hi=stack.pop();v=g(I(lo,hi));
    if v.lo>0:
        n+=1;mind=v.lo if mind is None else min(mind,v.lo)
    else:
        assert hi-lo>10**15, 'failed to prove strict positivity'
        m=(lo+hi)//2;stack.extend([(lo,m),(m,hi)])
print('PASS: positive dual on remaining intervals; certified cells:',n,'minimum lower bound:',mind/S)
# At actual solution cos first frequency has opposite signs on the two pairs.
assert cos(lam[0]*t).lo>0 and cos(lam[0]*T).hi<0
# Check sine moments independently fix the two pair differences.
det=sin(lam[0]*t)*sin(lam[1]*T)-sin(lam[0]*T)*sin(lam[1]*t)
assert det.lo>0 or det.hi<0
print('Sine determinant interval:',det)
print('PASS: all probability measures are forced to the four nodes with unique weights.')
# Exact endpoints written with integer arithmetic; displayed decimal bounds padded.
assert I.q('0.46994519').lo<2*T.lo<2*T.hi<I.q('0.46994524').hi
print('CERTIFIED width in (0.46994519, 0.46994524) for every triple in frequency boxes.')
