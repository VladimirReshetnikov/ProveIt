"""Exact sparse-polynomial verification of the symmetric four-root norm."""
from itertools import product

N=5
def const(k): return {(0,)*N:k} if k else {}
def var(i):
    e=[0]*N;e[i]=1;return {tuple(e):1}
def add(a,b):
    c=a.copy()
    for e,k in b.items():
        c[e]=c.get(e,0)+k
        if not c[e]: del c[e]
    return c
def neg(a):return {e:-k for e,k in a.items()}
def sub(a,b):return add(a,neg(b))
def mul(a,b):
    c={}
    for e,k in a.items():
        for f,l in b.items():
            h=tuple(i+j for i,j in zip(e,f));c[h]=c.get(h,0)+k*l
    return {e:k for e,k in c.items() if k}
def scale(a,k):return {e:k*v for e,v in a.items() if k*v}
def square(a):return mul(a,a)

def symmetric_norm(z,a,b,c,d):
    p=add(a,b);q=add(c,d);ab=mul(a,b);cd=mul(c,d)
    e1=add(p,q);e2=add(add(ab,cd),mul(p,q))
    e3=add(mul(ab,q),mul(cd,p));e4=mul(ab,cd)
    s=sub(z,e1);t=sub(square(s),scale(e2,4))
    C=add(square(t),scale(sub(e4,mul(z,e3)),64))
    L=sub(t,scale(mul(z,s),4))
    return sub(square(C),scale(mul(e4,square(L)),256))

def main():
    x,*r=[var(i) for i in range(N)]
    literal=const(1)
    for signs in product((-1,1),repeat=4):
        factor=x
        for sign,root in zip(signs,r):factor=sub(factor,scale(root,sign))
        literal=mul(literal,factor)
    if any(any(k%2 for k in e[1:]) for e in literal):
        raise AssertionError('radical did not cancel')
    expected={(e[0],*(k//2 for k in e[1:])):v for e,v in literal.items()}
    actual=symmetric_norm(square(x),*r)
    if actual!=expected:raise AssertionError('incorrect norm')
    print({'norm_identity':True,'terms':len(expected),'degree_in_x':max(e[0] for e in expected)})

if __name__=='__main__':main()
