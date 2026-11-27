"""Independent class-polynomial replay using mpmath interval arithmetic.

All displayed coefficient comparisons are interval comparisons against
exact integers. Analytic truncation tails are enclosed explicitly.
"""
from mpmath import iv
from verify import DATA,forms

iv.dps=220
N=112
r=iv.mpf(1)/200
assert iv.exp(-iv.pi*iv.sqrt(3)).b < r.a
e=(240*(N+1)**4*r**(N+1)/(1-16*r)).b
d=(100*r**(N+1)).b

def box(e):
    return iv.mpc(iv.mpf([-e,e]),iv.mpf([-e,e]))

def j_value(D,a,b):
    theta=-(iv.pi*b/a)
    q=iv.exp(-iv.pi*iv.sqrt(D)/a)*iv.mpc(iv.cos(theta),iv.sin(theta))
    qn=iv.mpc(1)
    E=iv.mpc(1)
    delta=iv.mpc(1)
    sigma=[0]*(N+1)
    for k in range(1,N+1):
        for j in range(k,N+1,k):
            sigma[j]+=k**3
    for n in range(1,N+1):
        qn*=q
        E+=240*sigma[n]*qn
        delta*=1-qn
    E+=box(e)
    return E**3/(q*delta**24)*(1+box(d))

def check():
    count=0
    for k,a in DATA.items():
        D=int(k)
        product=[iv.mpc(1)]
        for x,y,_ in forms(D):
            j=j_value(D,x,y)
            product=[(product[i-1] if i>0 else 0) -
                     (product[i]*j if i<len(product) else 0)
                     for i in range(len(product)+1)]
        assert len(product)==len(a)
        for coeff,expected in zip(product,a):
            assert coeff.real.a <= expected <= coeff.real.b, (D,expected)
            assert coeff.real.a > expected-1 and coeff.real.b < expected+1
            assert coeff.imag.a <= 0 <= coeff.imag.b
            count+=1
    print('Independent interval regeneration isolated',count,'integer coefficients.')

if __name__=='__main__': check()
