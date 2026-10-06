"""Independent finite implementation for report122 (stdlib, integer/rational only).
Range-difference tree propagation, rank-pattern avoidance, sparse polynomial
identities, and generic formal-series composition were written for this companion.
Finite checks are evidence about stated ranges, not substitutes for the proof.
"""
from collections import defaultdict
from fractions import Fraction as F
from math import comb
import hashlib
import json


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(value):
    return hashlib.sha256(json.dumps(value, separators=(',', ':'), sort_keys=True).encode()).hexdigest()


def tree(limit):
    states = {(0, 0, 'S'): 1}
    totals, levels, hs = [], [], []
    for n in range(limit + 1):
        totals.append(sum(states.values()))
        if n <= 40:
            levels.append(dict(states))
        h = [0] * (n + 1)
        for (a, b, kind), v in states.items():
            h[a] += v
        hs.append(h)
        if n == limit:
            break
        nxt, row_total, ranges = defaultdict(int), defaultdict(int), defaultdict(lambda: defaultdict(int))
        for (a, b, kind), v in states.items():
            nxt[a + 1, b, 'S'] += v
            row_total[a] += v
            upper = b - (kind == 'S')
            if upper >= 1:
                ranges[a + 1][1] += v
                ranges[a + 1][upper + 1] -= v
        for a, v in row_total.items():
            for d in range(1, a + 1):
                nxt[a + 1 - d, d, 'S'] += v
        for a, changes in ranges.items():
            active = 0
            for b in range(1, max(changes)):
                active += changes[b]
                if active:
                    nxt[a, b, 'T'] += active
        states = dict(nxt)
    return totals, levels, hs


def direct_avoidance(limit):
    forbidden = {(0, 1, 0), (1, 2, 0), (2, 1, 0)}
    seqs, levels, totals = [()], [], []
    examined = 0
    for n in range(limit + 1):
        level = defaultdict(int)
        for seq in seqs:
            maximum = max(seq, default=0)
            premaximum = max((v for v in seq if v < maximum), default=0)
            kind = 'T' if seq and seq[-1] != maximum else 'S'
            require(not seq or seq[-1] in (maximum, premaximum), 'avoidance: invalid S/T classification')
            level[n - maximum, maximum - premaximum, kind] += 1
        levels.append(dict(level)); totals.append(len(seqs))
        if n == limit:
            break
        new = []
        for seq in seqs:
            for v in range(n + 1):
                examined += 1
                bad = False
                for j in range(1, n):
                    for i in range(j):
                        triple = (seq[i], seq[j], v)
                        rank = {x: k for k, x in enumerate(sorted(set(triple)))}
                        if tuple(rank[x] for x in triple) in forbidden:
                            bad = True; break
                    if bad:
                        break
                if not bad:
                    new.append(seq + (v,))
        seqs = new
    return totals, levels, examined


def padd(*items):
    out = defaultdict(int)
    for sign, poly in items:
        for monomial, value in poly.items():
            out[monomial] += sign * value
    return {m: v for m, v in out.items() if v}


def pmul(a, b, limit):
    out = defaultdict(int)
    for u, v in a.items():
        for w, x in b.items():
            monomial = tuple(i + j for i, j in zip(u, w))
            if monomial[0] <= limit:
                out[monomial] += v * x
    return {m: v for m, v in out.items() if v}


def functional_checks(levels, hs, limit, correction):
    one = {(0, 0, 0): 1}; zx = {(1, 1, 0): 1}
    x = {(0, 1, 0): 1}; y = {(0, 0, 1): 1}
    S, T, Hx, Hy = {}, {}, {}, {}
    for n, level in enumerate(levels[:limit + 1]):
        for (a, b, kind), v in level.items():
            (S if kind == 'S' else T)[n, a, b] = v
        for a, v in enumerate(hs[n]):
            if v:
                Hx[n, a, 0] = v; Hy[n, 0, a] = v
    B = padd((1, S), (1, T))
    xy = padd((1, x), (-1, y)); oy = padd((1, one), (-1, y)); oz = padd((1, one), (-1, zx))
    resS = padd((1, pmul(xy, padd((1, S), (-1, one), (-1, pmul(zx, B, limit))), limit)),
                 (-1, pmul({(1, 1, 1): 1}, padd((1, Hx), (-1, Hy)), limit)))
    require(not resS, 'functional: source S equation residual')
    resT = padd((1, pmul(pmul(oy, pmul(oz, oz, limit), limit), T, limit)),
                 (-1, pmul(pmul(zx, oz, limit), padd((1, pmul(y, Hx, limit)), (-1, B)), limit)),
                 (-correction, pmul(zx, oy, limit)))
    require(not resT, 'functional: source T all-zero correction residual')
    phi = [1] + list(range(1, limit + 1))
    powers = [[1] + [0] * limit]
    for a in range(1, limit + 1):
        powers.append([sum(powers[-1][j] * phi[m-j] for j in range(m+1)) for m in range(limit+1)])
    H, HP = {}, defaultdict(int)
    for n, h in enumerate(hs[:limit+1]):
        for a, v in enumerate(h):
            if v:
                H[n, a] = v
                for m in range(limit-n+1):
                    HP[n+m, m] += v * powers[a][m]
    A = {(0,0):1,(1,1):-2,(2,2):1}; u = {(1,1):1}; omu = {(0,0):1,(1,1):-1}
    B2 = padd((1,pmul({(0,1):1,(0,0):-1},A,limit)),(-1,u))
    uA = pmul(u,A,limit)
    res = padd((1,pmul(uA,HP,limit)),(-1,pmul(padd((1,uA),(-1,pmul(omu,B2,limit))),H,limit)),(-1,B2))
    require(not res, 'scalar: cleared kernel identity residual')
    return {'source_S_monomials':len(S), 'source_T_monomials':len(T), 'scalar_H_monomials':len(H),
            'source_equations_residual_monomials':0, 'scalar_residual_monomials':0}


class Series:
    def __init__(self, values, degree):
        self.n = degree
        if isinstance(values, (int, F)):
            values = [values]
        self.a = tuple(values[:degree+1]) + (0,) * max(0, degree+1-len(values))
    def coerce(self, other):
        return other if isinstance(other, Series) else Series(other, self.n)
    def __add__(self, other):
        other = self.coerce(other)
        return Series([a+b for a,b in zip(self.a,other.a)],self.n)
    __radd__ = __add__
    def __neg__(self): return Series([-a for a in self.a],self.n)
    def __sub__(self,other): return self+-self.coerce(other)
    def __rsub__(self,other): return self.coerce(other)+-self
    def __mul__(self,other):
        other=self.coerce(other); out=[0]*(self.n+1)
        for i,a in enumerate(self.a):
            if a:
                for j,b in enumerate(other.a[:self.n+1-i]):
                    if b: out[i+j]+=a*b
        return Series(out,self.n)
    __rmul__=__mul__
    def inv(self):
        require(self.a[0]!=0,'series: zero constant denominator')
        out=[1/self.a[0] if isinstance(self.a[0],F) else F(1,self.a[0])]
        for n in range(1,self.n+1):
            out.append(-sum(self.a[k]*out[n-k] for k in range(1,n+1))/self.a[0])
        return Series(out,self.n)
    def __truediv__(self,other): return self*self.coerce(other).inv()
    def __rtruediv__(self,other): return self.coerce(other)*self.inv()
    def times_z(self): return Series([0]+list(self.a[:-1]),self.n)
    def over_z(self):
        require(self.a[0]==0,'series: nondivisible by z')
        return Series(list(self.a[1:])+[0],self.n)


def formal_checks(totals,hs,degree,iterations,claimed_next):
    K=degree+1
    one=Series(1,K)
    R=Series([F(comb(3*n,n),2*n+1) for n in range(K+1)],K)
    require(R.a==(1+(R*R*R).times_z()).a,'anchor: ternary root equation')
    def phi(x): return 1+x.times_z()/(1-x.times_z())/(1-x.times_z())
    def step(x):
        nx=phi(x); d=(x-nx).over_z()/x; c=1-(1-x.times_z())*d
        return nx,c,d
    X=R*R; Y=phi(X); _,c,d=step(X)
    require(Y.a==(X-R+1).a,'anchor: argument identity')
    require(all(v==0 for v in c.a[:degree+1]),'anchor: c does not vanish')
    require(d.a[:degree+1]==R.a[:degree+1],'anchor: d differs from R')
    out=Series(0,K); powers=[one]
    for a in range(1,K+1): powers.append(powers[-1]*Y)
    for n,h in enumerate(hs[:K+1]):
        for a,v in enumerate(h):
            if v: out=out+Series([0]*n+[v*w for w in powers[a].a[:K+1-n]],K)
    require(out.a[:degree+1]==R.a[:degree+1],'anchor: H(Y) differs from R')
    x,y,p,q,v=one,Y,one,Series(0,K),R
    outcomes=[]
    for m in range(iterations+1):
        quotient=(v-q)/p
        require(quotient.a[:m+2]==tuple(totals[:m+2]),'orbit: finite quotient coefficient mismatch')
        delta=quotient.a[m+2]-totals[m+2]
        require(delta==claimed_next[m],'orbit: next coefficient discrepancy mismatch')
        outcomes.append({'iterations':m,'matched_through_n':m+1,'next_difference':str(delta)})
        x,c,d=step(x); p=c*p; q=c*q+d
        y,c,d=step(y); v=c*v+d
    return outcomes


def finite_checks(data):
    totals,levels,hs=tree(data['tree_max_n'])
    brute,bl,examined=direct_avoidance(data['direct_max_n'])
    require(bl==levels[:len(bl)],'avoidance: full transformed state distributions differ')
    require(totals[:26]==data['published_prefix'],'prefix: published 26-term sequence mismatch')
    require(totals==[int(x) for x in data['generated_terms']],'sequence: generated n=0..150 mismatch')
    ident=functional_checks(levels,hs,data['identity_max_n'],F(data['source_T_correction']))
    orbits=formal_checks(totals,hs,data['anchor_max_n'],data['orbit_max_m'],[F(x) for x in data['orbit_next_differences']])
    serialized=[[[a,b,k,v] for (a,b,k),v in sorted(level.items())] for level in bl]
    return {'direct_max_n':data['direct_max_n'],'direct_totals':brute,'direct_candidates_tested':examined,
            'direct_state_counts':[len(x) for x in bl],'direct_state_distribution_sha256':digest(serialized),
            'published_prefix_terms_matched':26,'tree_max_n':data['tree_max_n'],'generated_terms':len(totals),
            'generated_sequence_sha256':digest([str(x) for x in totals]),'a150':str(totals[-1]),
            'functional_identity_through_z':data['identity_max_n'],'anchor_through_z':data['anchor_max_n'],
            'finite_orbit_checks':orbits,**ident}


def inversion_algebra_check():
    # Sparse polynomials in (q, lambda, d1, d2), with q=p log L-A.
    # Substitution in log a_n through L^-2 must cancel coefficientwise.
    q={(1,0,0,0):F(1)}; lam={(0,1,0,0):F(1)}
    d1={(0,0,1,0):F(1)}; d2={(0,0,0,1):F(1)}; p=F(3,2)
    def mul(a,b): return pmul(a,b,20)
    P1=padd((p,q),(-1,mul(lam,d1)))
    P2=padd((p,P1),(-p/2,mul(q,q)),(1,mul(mul(lam,d1),q)),
             (-1,mul(mul(lam,lam),padd((1,d2),(-F(1,2),mul(d1,d1))))))
    order1=padd((1,P1),(-p,q),(1,mul(lam,d1)))
    order2=padd((1,P2),(-p,P1),(p/2,mul(q,q)),(-1,mul(mul(lam,d1),q)),
                 (1,mul(mul(lam,lam),padd((1,d2),(-F(1,2),mul(d1,d1))))))
    require(not order1 and not order2,'inversion: symbolic residual through L^-2')
    g1=lambda a:a*(a+1)/2
    g2=lambda a:a*(a+1)*(a+2)*(3*a+1)/24
    require(g1(F(1,2))==F(3,8) and g2(F(1,2))==F(25,128),'transfer: half-power gamma ratio factors')
    require(-F(3,2)*g1(F(3,2))==-F(45,16),'transfer: cubic-root mixed factor')
    return {'inverse_log_residual_powers':[1,2],'inverse_residual_monomials':0,
            'P1_monomials':len(P1),'P2_monomials':len(P2),
            'transfer_factors':['3/8','25/128','-3/2','-45/16','15/4']}
