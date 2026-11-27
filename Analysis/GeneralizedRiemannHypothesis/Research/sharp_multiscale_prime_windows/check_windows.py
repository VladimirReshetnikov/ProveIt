#!/usr/bin/env python3
"""Numerical illustration only; no zeros or GRH numerical tests are needed.
Requires mpmath. Run: python check_windows.py
"""
import math
import mpmath as mp
mp.mp.dps = 40
q = 5
h = mp.mpf('0.4')
G = mp.expm1(h)
B = h*G

def g(u):
    u = abs(u)
    return mp.exp(u/2)*mp.expm1(h-u) if u < h else mp.mpf(0)

def b(u, parity):
    return mp.exp(-(mp.mpf('0.5')+parity)*u)/(-mp.expm1(-2*u))

def J(parity):
    # At zero, 2*(g(0)-g(u))*b(u) has limit (exp(h)+1)/2.
    def integrand(u):
        if abs(u) < mp.mpf('1e-35'):
            return (mp.exp(h)+1)/2
        # stable evaluation of G-g(u) inside support
        diff = -mp.exp(h)*mp.expm1(-u/2)+mp.expm1(u/2)
        return 2*diff*b(u, parity)
    return mp.quad(integrand, [0,h])+2*G*mp.quad(lambda u:b(u,parity), [h,1,mp.inf])

D0 = G*(-mp.log(mp.pi)+mp.digamma(mp.mpf(1)/4))+J(0)+2*B
De = G*(mp.log(q/mp.pi)+mp.digamma(mp.mpf(1)/4))+J(0)
Do = G*(mp.log(q/mp.pi)+mp.digamma(mp.mpf(3)/4))+J(1)
M = (D0+(q-3)//2*De+(q-1)//2*Do)/(q-1)

N=30000
sieve=bytearray(b'\x01')*(N+1)
sieve[0:2]=b'\x00\x00'
for p in range(2,math.isqrt(N)+1):
    if sieve[p]: sieve[p*p:N+1:p]=b'\x00'*((N-p*p)//p+1)
pp=[]
for p in range(2,N+1):
    if sieve[p]:
        n=p
        while n<=N:
            pp.append((n,mp.log(p),mp.log(n)))
            n*=p

def K(a,t):
    a %= q
    if t < 0: return K(pow(a,-1,q),-t)
    if t == 0 and a==1: return M
    if t <= h: raise ValueError('example uses positive separated windows only')
    if mp.exp(t+h)>N: raise ValueError('increase sieve cutoff')
    C=B*(mp.exp(t/2)+mp.exp(-t/2))/(q-1)
    P=mp.fsum(lpn/mp.sqrt(n)*g(ln-t)*(1 if n%q==a else mp.mpf(1)/(q-1) if n%q==0 else 0)
              for n,lpn,ln in pp if abs(ln-t)<h)
    A=mp.quad(lambda u:g(u-t)*((b(u,0)+b(u,1))/2*(a==1)+(b(u,0)-b(u,1))/2*(a==q-1)), [t-h,t,t+h])
    return C-P-A

def out(k,v): print(f'{k:27s} {mp.nstr(v,16)}')

if __name__=='__main__':
    print('q=5, h=0.4; all values are numerical illustrations, not certified intervals.')
    out('diagonal M',M)
    a=2; u=mp.log(10); t=mp.log(1000)
    k=K(a,u); bound=2*(M-k)
    contrast=2*K(1,t)-K(a,t+u)-K(pow(a,-1,q),t-u)
    out('K(2,log 10)',k)
    out('K(1,log 1000)',K(1,t))
    out('K(2,log 10000)',K(a,t+u))
    out('K(3,log 100)',K(pow(a,-1,q),t-u))
    out('contrast',contrast)
    out('sharp contrast bound',bound)
    assert abs(contrast)<=bound
    # Three-window Gram matrix for (1,0), (2,log 10), (1,log 1000).
    pts=[(1,mp.mpf(0)),(2,u),(1,t)]
    mat=mp.matrix([[K(ai*pow(aj,-1,q),ti-tj) for aj,tj in pts] for ai,ti in pts])
    out('three-point determinant',mp.det(mat))
    assert min(mp.eigsy(mat,eigvals_only=True))>0
