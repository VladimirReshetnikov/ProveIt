#!/usr/bin/env python3
"""Exact Kerr-Newman checker using Python's standard library only.

The coefficient ring is Z[r,x,a,m,q,1/2,1/S,1/D,1/s].  A value is an
integer sparse polynomial divided by 2^e S^i D^j s^k.  Normalization uses
only exact polynomial division by S, D and s; there is no polynomial gcd,
sampling, floating point, symbolic CAS, or unbounded mathematical search.

All loops have elementary finite bounds in the sizes/degrees of their inputs.
The source is a reproducible finite algebra computation, not a Lean proof.
"""
import json
import time
from itertools import permutations
from pathlib import Path

START = time.monotonic()
N = 5
ZERO_EXP = (0,)*N
COUNTS = {'add':0,'mul':0,'differentiate':0,'exact_division':0,'max_terms':0,'max_total_degree':0}

def clean(p):
    return {e:c for e,c in p.items() if c}

def padd(p,q):
    z = p.copy()
    for e,c in q.items():
        z[e] = z.get(e,0)+c
        if not z[e]: del z[e]
    return z

def pscale(p,c):
    return {e:v*c for e,v in p.items() if v*c}

def pmul(p,q):
    z = {}
    for e,c in p.items():
        for f,d in q.items():
            k = tuple(u+v for u,v in zip(e,f))
            z[k] = z.get(k,0)+c*d
    return clean(z)

def ppow(p,n):
    z = {ZERO_EXP:1}
    for _ in range(n): z = pmul(z,p)
    return z

def pder(p,i):
    z = {}
    for e,c in p.items():
        if e[i]:
            f = list(e); f[i] -= 1
            z[tuple(f)] = c*e[i]
    return z

def deriv_poly(p,i):
    """Coordinate derivative; replaceable by a finite formal-jet derivation."""
    return pder(p,i-1)

def pdiv_exact(p,q):
    """Return p/q if exact, else None (q monic up to sign).

    Graded lexicographic order is used. Each subtraction strictly decreases
    the leading monomial. No total degree increases. For input total degree
    d, there are at most binomial(d+N,N) monomials, a primitive-recursive bound.
    """
    COUNTS['exact_division'] += 1
    if not p: return {}
    order = lambda e:(sum(e),e)
    qe = max(q,key=order); qc = q[qe]
    if qc not in (-1,1):
        raise ValueError('Exact-division divisor must be monic up to sign')
    w = p.copy(); z = {}
    while w:
        e = max(w,key=order)
        if any(u<v for u,v in zip(e,qe)): return None
        shift = tuple(u-v for u,v in zip(e,qe))
        c = w[e]//qc
        z[shift] = z.get(shift,0)+c
        for f,d in q.items():
            h = tuple(u+v for u,v in zip(f,shift))
            w[h] = w.get(h,0)-c*d
            if not w[h]: del w[h]
    return z

def variable(i):
    e = [0]*N; e[i] = 1
    return {tuple(e):1}

P_R,P_X,P_A,P_M,P_Q = [variable(i) for i in range(N)]
P_S = padd(pmul(P_R,P_R),pmul(pmul(P_A,P_A),pmul(P_X,P_X)))
P_D = padd(padd(pmul(P_R,P_R),pscale(pmul(P_M,P_R),-2)),padd(pmul(P_A,P_A),pmul(P_Q,P_Q)))
P_s = padd({ZERO_EXP:1},pscale(pmul(P_X,P_X),-1))
FACTORS = [{ZERO_EXP:2},P_S,P_D,P_s]
POWER_CACHE = {}
def factor_pow(i,n):
    if (i,n) not in POWER_CACHE: POWER_CACHE[i,n] = ppow(FACTORS[i],n)
    return POWER_CACHE[i,n]

class Rat:
    __slots__ = ('p','d')
    def __init__(self,p=0,d=(0,0,0,0)):
        if isinstance(p,int): p = {ZERO_EXP:p} if p else {}
        p = clean(p); d = list(d)
        if len(d)!=4 or any(not isinstance(v,int) or v<0 for v in d):
            raise ValueError('Denominator exponents must be four natural numbers')
        if not p:
            self.p = {}; self.d = (0,0,0,0); return
        while d[0] and all(c%2==0 for c in p.values()):
            p = {e:c//2 for e,c in p.items()}; d[0] -= 1
        for i in (1,2,3):
            while d[i]:
                v = pdiv_exact(p,FACTORS[i])
                if v is None: break
                p = v; d[i] -= 1
        self.p = p; self.d = tuple(d)
        COUNTS['max_terms'] = max(COUNTS['max_terms'],len(p))
        COUNTS['max_total_degree'] = max(COUNTS['max_total_degree'],max(map(sum,p)))
    @staticmethod
    def coerce(z): return z if isinstance(z,Rat) else Rat(z)
    def __add__(self,z):
        COUNTS['add'] += 1
        z = Rat.coerce(z)
        if not self.p: return z
        if not z.p: return self
        d = tuple(max(i,j) for i,j in zip(self.d,z.d))
        p,q = self.p,z.p
        for i in range(4):
            if d[i]>self.d[i]: p = pmul(p,factor_pow(i,d[i]-self.d[i]))
            if d[i]>z.d[i]: q = pmul(q,factor_pow(i,d[i]-z.d[i]))
        return Rat(padd(p,q),d)
    __radd__ = __add__
    def __neg__(self):
        z = object.__new__(Rat); z.p = pscale(self.p,-1); z.d = self.d; return z
    def __sub__(self,z): return self+-Rat.coerce(z)
    def __rsub__(self,z): return Rat.coerce(z)+-self
    def __mul__(self,z):
        COUNTS['mul'] += 1
        z = Rat.coerce(z)
        return Rat(pmul(self.p,z.p),tuple(i+j for i,j in zip(self.d,z.d)))
    __rmul__ = __mul__
    def __pow__(self,n):
        if not isinstance(n,int) or n<0:
            raise ValueError('Exponent must be a natural number')
        z = Rat(1)
        for _ in range(n): z = z*self
        return z
    def diff(self,i):
        COUNTS['differentiate'] += 1
        if i not in (1,2): return Rat(0)
        z = Rat(deriv_poly(self.p,i),self.d)
        for k in (1,2,3):
            if self.d[k]:
                den = [0]*4; den[k] = 1
                z = z-self*Rat(pscale(deriv_poly(FACTORS[k],i),self.d[k]),tuple(den))
        return z
    def iszero(self): return not self.p
    def serialize(self):
        return {'numerator':[[list(e),c] for e,c in sorted(self.p.items())],
                'denominator_powers_2_S_D_s':list(self.d)}

def announce(msg): print(f'{time.monotonic()-START:8.2f}s {msg}',flush=True)
def matrix(): return [[Rat(0) for _ in range(4)] for _ in range(4)]
def mmul(U,V): return [[sum(U[i][k]*V[k][j] for k in range(4)) for j in range(4)] for i in range(4)]
def transpose(U): return [[U[j][i] for j in range(4)] for i in range(4)]
def flatten(U): return [x for row in U for x in row]
CHECKS = {}
def check(name,values):
    values = list(values)
    bad = [i for i,z in enumerate(values) if not Rat.coerce(z).iszero()]
    CHECKS[name] = {'count':len(values),'nonzero_residuals':bad}
    if bad:
        raise ValueError((name,bad,[values[i].serialize() for i in bad]))
    announce(f'{name}: {len(values)} exact zero residuals')

def main():
    r,x,a,m,q = [Rat(p) for p in (P_R,P_X,P_A,P_M,P_Q)]
    S,D,s = Rat(P_S),Rat(P_D),Rat(P_s)
    iS,iD,is_ = Rat(1,(0,1,0,0)),Rat(1,(0,0,1,0)),Rat(1,(0,0,0,1))
    half = Rat(1,(1,0,0,0)); quarter = half*half
    B = r*r+a*a
    g,gi = matrix(),matrix()
    g[0][0] = (-D+a*a*s)*iS
    g[0][3] = g[3][0] = a*s*(D-B)*iS
    g[1][1] = S*iD
    g[2][2] = S*is_
    g[3][3] = s*(B*B-a*a*D*s)*iS
    gi[0][0] = -(B*B-a*a*D*s)*iS*iD
    gi[0][3] = gi[3][0] = a*(D-B)*iS*iD
    gi[1][1] = D*iS
    gi[2][2] = s*iS
    gi[3][3] = (D-a*a*s)*iS*iD*is_
    check('metric_symmetry',(g[i][j]-g[j][i] for i in range(4) for j in range(4)))
    check('inverse',(sum(g[i][k]*gi[k][j] for k in range(4))-int(i==j) for i in range(4) for j in range(4)))
    det = Rat(0)
    for p in permutations(range(4)):
        sign = (-1)**sum(p[i]>p[j] for i in range(4) for j in range(i+1,4))
        v = Rat(sign)
        for i in range(4): v = v*g[i][p[i]]
        det = det+v
    check('determinant',[det+S*S])
    dg = [[[g[i][j].diff(k) for j in range(4)] for i in range(4)] for k in range(4)]
    Gamma = [[[Rat(0) for _ in range(4)] for _ in range(4)] for _ in range(4)]
    for i in range(4):
        for j in range(4):
            for k in range(j,4):
                Gamma[i][j][k] = Gamma[i][k][j] = half*sum(gi[i][l]*(dg[j][l][k]+dg[k][l][j]-dg[l][j][k]) for l in range(4))
    announce('Christoffel symbols computed')
    trace = [sum(Gamma[k][i][k] for k in range(4)) for i in range(4)]
    check('connection_trace',(trace[i]-S.diff(i)*iS for i in range(4)))
    Ric = matrix()
    # All sixteen are computed independently, so symmetry is also tested.
    for i in range(4):
        for j in range(4):
            Ric[i][j] = sum(Gamma[k][i][j].diff(k)+Gamma[k][i][j]*trace[k] for k in range(4))-trace[i].diff(j)-sum(Gamma[k][i][l]*Gamma[l][j][k] for k in range(4) for l in range(4))
        announce(f'Ricci row {i} computed')
    C = [[Rat(1),Rat(0),Rat(0),-a*s],[Rat(0),Rat(1),Rat(0),Rat(0)],[Rat(0),Rat(0),Rat(1),Rat(0)],[-a,Rat(0),Rat(0),B]]
    RC = matrix()
    for i,z in enumerate((q*q*D*iS**3,-q*q*iS*iD,q*q*iS*is_,q*q*s*iS**3)): RC[i][i] = z
    expected = mmul(mmul(transpose(C),RC),C)
    check('ricci_formula',(Ric[i][j]-expected[i][j] for i in range(4) for j in range(4)))
    check('ricci_symmetry',(Ric[i][j]-Ric[j][i] for i in range(4) for j in range(4)))
    check('scalar_curvature',[sum(gi[i][j]*Ric[i][j] for i in range(4) for j in range(4))])
    A = [-q*r*iS,Rat(0),Rat(0),q*r*a*s*iS]
    F = [[A[j].diff(i)-A[i].diff(j) for j in range(4)] for i in range(4)]
    Fu = mmul(mmul(gi,F),gi)
    density = [[S*Fu[i][j] for j in range(4)] for i in range(4)]
    check('field_antisymmetry',(F[i][j]+F[j][i] for i in range(4) for j in range(4)))
    check('maxwell_divergence',(sum(density[i][j].diff(i) for i in range(4)) for j in range(4)))
    check('bianchi_dF',(F[j][k].diff(i)+F[k][i].diff(j)+F[i][j].diff(k) for i in range(4) for j in range(i+1,4) for k in range(j+1,4)))
    F2 = sum(F[i][j]*Fu[i][j] for i in range(4) for j in range(4))
    T0 = mmul(mmul(F,gi),transpose(F))
    EM = [[2*(T0[i][j]-quarter*g[i][j]*F2) for j in range(4)] for i in range(4)]
    check('einstein_maxwell',(Ric[i][j]-EM[i][j] for i in range(4) for j in range(4)))
    out = {
      'status':'PASS', 'engine':'Python standard library only',
      'variables':['r','x','a','m','q'],
      'denominator_factors':['2','r^2+a^2*x^2','r^2-2*m*r+a^2+q^2','1-x^2'],
      'domain':'S != 0 and D != 0 and s != 0; geometric Lorentz domain S>0, s>0',
      'checks':CHECKS,'arithmetic_counters':COUNTS,
      'ricci':[[z.serialize() for z in row] for row in Ric],
      'field':[[z.serialize() for z in row] for row in F],
      'maxwell_density':[[z.serialize() for z in row] for row in density],
      'seconds':round(time.monotonic()-START,3)
    }
    dest = Path(__file__).resolve().parents[1]/'certificates'/'stdlib_results.json'
    dest.write_text(json.dumps(out,indent=2)+'\n')
    announce(f'PASS: wrote {dest.name}')

if __name__ == '__main__': main()
