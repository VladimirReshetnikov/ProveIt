#!/usr/bin/env python3
"""Exact finite checks for Sharp Cubical Correlation and Characteristic Barriers.

Python 3.10+; standard library only.  No floating-point tests and no external CAS.
Run: python3 verify.py --output validation.json
These finite checks are supplementary, not a proof of the general theorems.
"""
from __future__ import annotations
import argparse
import itertools as it
import json
import math
import random
from collections import Counter
from fractions import Fraction
from pathlib import Path


def digits(x: int, p: int, n: int) -> list[int]:
    out = []
    for _ in range(n):
        out.append(x % p)
        x //= p
    return out


def encode(xs: list[int], p: int) -> int:
    return sum(x * p**i for i, x in enumerate(xs))


def remainder(a: list[int], b: list[int], p: int) -> list[int]:
    a = a[:]
    while a and a[-1] == 0:
        a.pop()
    while len(a) >= len(b):
        c = a[-1] * pow(b[-1], -1, p) % p
        j = len(a) - len(b)
        for i, v in enumerate(b):
            a[i+j] = (a[i+j] - c*v) % p
        while a and a[-1] == 0:
            a.pop()
    return a


def irreducible(p: int, n: int) -> list[int]:
    """Trial division by all monic factors of degree <= n/2; small n only."""
    if n == 1:
        return [0, 1]
    for c in range(1, p**n):
        f = digits(c, p, n) + [1]
        if f[0] == 0:
            continue
        good = True
        for k in range(1, n//2 + 1):
            for b in range(p**k):
                if not remainder(f, digits(b, p, k) + [1], p):
                    good = False
                    break
            if not good:
                break
        if good:
            return f
    raise AssertionError('No irreducible polynomial found')


class Field:
    """F_p[t]/(modulus); field elements are base-p encoded coefficient vectors."""
    def __init__(self, p: int, n: int):
        self.p, self.n, self.q = p, n, p**n
        self.modulus = irreducible(p, n)
        self.vec = [digits(x, p, n) for x in range(self.q)]
        self.add_table = [[self._add(a,b) for b in range(self.q)]
                          for a in range(self.q)]
        self.mul_table = [[self._mul(a,b) for b in range(self.q)]
                          for a in range(self.q)]
        self.trace_table = [self._trace(a) for a in range(self.q)]
        for a in range(1, self.q):
            assert self.power(a, self.q-1) == 1

    def _add(self, a: int, b: int) -> int:
        return encode([(x+y)%self.p for x,y in zip(self.vec[a],self.vec[b])],self.p)

    def _mul(self, a: int, b: int) -> int:
        coeff = [0]*(2*self.n-1)
        for i,x in enumerate(self.vec[a]):
            for j,y in enumerate(self.vec[b]):
                coeff[i+j] = (coeff[i+j]+x*y)%self.p
        for k in range(2*self.n-2, self.n-1, -1):
            for j in range(self.n):
                coeff[k-self.n+j] = (coeff[k-self.n+j]-coeff[k]*self.modulus[j])%self.p
        return encode(coeff[:self.n],self.p)

    def add(self, a: int, b: int) -> int:
        return self.add_table[a][b]

    def mul(self, a: int, b: int) -> int:
        return self.mul_table[a][b]

    def power(self, a: int, k: int) -> int:
        out = 1
        while k:
            if k&1: out = self.mul(out,a)
            a = self.mul(a,a)
            k >>= 1
        return out

    def _trace(self, a: int) -> int:
        z, out = a, 0
        for _ in range(self.n):
            out = self.add(out,z)
            z = self.power(z,self.p)
        assert out < self.p
        return out

    def trace(self, a: int) -> int:
        return self.trace_table[a]

    def tensor(self, c: int, hs: tuple[int,...]) -> int:
        for h in hs: c = self.mul(c,h)
        return self.trace(c)

    def obstruction(self, c: int, a: int, b: int) -> int:
        x = self.trace(self.mul(c,self.mul(self.power(a,self.p),b)))
        y = self.trace(self.mul(c,self.mul(a,self.power(b,self.p))))
        return (x-y)%self.p


def rank(A: list[list[int]], p: int) -> int:
    if not A: return 0
    A = [[v%p for v in row] for row in A]
    r = 0
    for j in range(len(A[0])):
        k = next((i for i in range(r,len(A)) if A[i][j]),None)
        if k is None: continue
        A[r],A[k] = A[k],A[r]
        inv = pow(A[r][j],-1,p)
        A[r] = [v*inv%p for v in A[r]]
        for i in range(len(A)):
            if i != r:
                t = A[i][j]
                A[i] = [(u-t*v)%p for u,v in zip(A[i],A[r])]
        r += 1
        if r == len(A): break
    return r


def addv(a: list[int], b: list[int], p: int) -> list[int]:
    return [(x+y)%p for x,y in zip(a,b)]


def scale(a: list[int], t: int, p: int) -> list[int]:
    return [t*x%p for x in a]


def pairing(A: list[list[int]], a: list[int], b: list[int], p: int) -> int:
    return sum(x*A[i][j]*y for i,x in enumerate(a) for j,y in enumerate(b))%p


def symplectic(A: list[list[int]], p: int):
    """Return hyperbolic pairs and radical basis in original coordinates."""
    n = len(A)
    pool = [[int(i==j) for i in range(n)] for j in range(n)]
    pairs = []
    while True:
        ij = next(((i,j) for i in range(len(pool)) for j in range(i+1,len(pool))
                   if pairing(A,pool[i],pool[j],p)),None)
        if ij is None: break
        i,j = ij
        u = pool[i]
        v = scale(pool[j],pow(pairing(A,u,pool[j],p),-1,p),p)
        rest = [w for k,w in enumerate(pool) if k not in (i,j)]
        pool = []
        for w in rest:
            w0 = addv(w,scale(u,-pairing(A,w,v,p),p),p)
            w0 = addv(w0,scale(v,pairing(A,w,u,p),p),p)
            pool.append(w0)
        pairs.append((u,v))
    assert rank([v for pair in pairs for v in pair]+pool,p)==n
    for u,v in pairs:
        assert pairing(A,u,v,p)==1
    W = [u for u,v in pairs]+pool
    assert all(pairing(A,u,v,p)==0 for u in W for v in W)
    return pairs,pool,W


def scalar_phase(p: int, d: int) -> tuple[int,list[int]]:
    if d<1: raise ValueError('Positive degree required')
    r = (d-1)//(p-1)
    a = d-r*(p-1)
    M = p**(r+1)
    u = pow(((-1)**r*math.factorial(a))%p,-1,p)
    return M,[u*x**a%M for x in range(p)]


def diff(vals: list[int], h: int, F: Field, M: int) -> list[int]:
    return [(vals[F.add(x,h)]-vals[x])%M for x in range(F.q)]


def multiindices(n: int, d: int):
    if n == 1:
        yield (d,)
    else:
        for a in range(d+1):
            for rest in multiindices(n-1,d-a):
                yield (a,)+rest


def integrator(F: Field, c: int, d: int) -> tuple[int,list[int]]:
    """Construct the article's explicit integrator in admissible d<=p+1 cases."""
    p,n = F.p,F.n
    if not 1<=d<=p+1: raise ValueError('This constructor covers d<=p+1')
    if d==p+1:
        assert all(F.obstruction(c,p**i,p**j)==0 for i in range(n) for j in range(n))
    # Safe common denominator; the F_4 exceptional case is reduced afterward.
    R = max(1,(d+p-2)//(p-1))
    M = p**R
    out = [0]*F.q
    basis = [p**i for i in range(n)]
    for alpha in multiindices(n,d):
        hs = tuple(b for b,a in zip(basis,alpha) for _ in range(a))
        b = F.tensor(c,hs)
        if not b: continue
        if max(alpha)<p:
            inv = pow(math.prod(math.factorial(a) for a in alpha)%p,-1,p)
            for x,v in enumerate(F.vec):
                out[x] += (b*inv%p)*(M//p)*math.prod(t**a for t,a in zip(v,alpha))
        elif max(alpha)==d:
            i = alpha.index(d)
            M0,phase = scalar_phase(p,d)
            for x,v in enumerate(F.vec): out[x] += b*(M//M0)*phase[v[i]]
        elif d==p+1:
            i,j = alpha.index(p),alpha.index(1)
            if i>j: continue  # The paired coefficient is inserted exactly once.
            for x,v in enumerate(F.vec): out[x] -= b*(M//p**2)*v[i]*v[j]
        else: raise AssertionError('Unexpected multiindex')
    out = [z%M for z in out]
    while M>p and all(z%p==0 for z in out):
        M//=p
        out = [z//p for z in out]
    return M,out


def verify_phase(F: Field,c: int,d: int,M: int,vals: list[int]) -> int:
    count = 0
    # Full enumeration of all derivative tuples and all basepoints.
    for hs in it.product(range(F.q),repeat=d):
        v = vals
        for h in hs: v = diff(v,h,F,M)
        expected = F.tensor(c,hs)*(M//F.p)%M
        assert all(z==expected for z in v),(F.p,F.n,c,d,hs,v,expected)
        count += F.q
    return count


def expected_radical(F: Field,c: int) -> int:
    if F.n%2: return 1
    return 2 if F.power(c,(F.q-1)//(F.p+1))==1 else 0


def gaussian_mul(a: tuple[int,int],b: tuple[int,int]) -> tuple[int,int]:
    return a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0]


def gaussian_conj(a: tuple[int,int]) -> tuple[int,int]: return a[0],-a[1]


def spectral_moment(F: Field,c: int,f: list[tuple[int,int]]) -> Fraction:
    assert F.p==2
    total = 0
    for a,b in it.product(range(F.q),repeat=2):
        ab = F.mul(a,b)
        s = (0,0)
        for x in range(F.q):
            g = gaussian_mul(f[x],gaussian_conj(f[F.add(x,a)]))
            g = gaussian_mul(g,gaussian_conj(f[F.add(x,b)]))
            g = gaussian_mul(g,f[F.add(F.add(x,a),b)])
            sign = (-1)**F.trace(F.mul(c,F.mul(ab,x)))
            s = s[0]+sign*g[0],s[1]+sign*g[1]
        if F.obstruction(c,a,b): assert s==(0,0)
        total += s[0]**2+s[1]**2
    return Fraction(total,F.q**4)



def binary_tensor_checks(rng: random.Random) -> list[dict]:
    """Verify sharp extremizers, mixed cube bounds, seven-function bounds, and Gauss spectra."""
    out=[]
    roots=[(1,0),(0,1),(-1,0),(0,-1)]
    for n in (2,3,4):
        q=2**n
        F=Field(2,n)
        for case in range(3):
            coeff={alpha:rng.randrange(2) for alpha in it.combinations_with_replacement(range(n),3)}
            def T(a,b,c):
                return sum(coeff[tuple(sorted((i,j,k)))] for i in range(n) for j in range(n)
                           for k in range(n) if a>>i&1 and b>>j&1 and c>>k&1)%2
            table=[[[T(a,b,c) for c in range(q)] for b in range(q)] for a in range(q)]
            A=[[T(1<<i,1<<i,1<<j)^T(1<<i,1<<j,1<<j)
                for j in range(n)] for i in range(n)]
            rr=rank(A,2)
            pairs,rad,W=symplectic(A,2)
            ell=[[pairing(A,F.vec[x],u,2) for x in range(q)] for u,v in pairs]
            emm=[[pairing(A,F.vec[x],v,2) for x in range(q)] for u,v in pairs]
            def S(a,b,c):
                return sum(l[a]*m[b]*m[c]+m[a]*l[b]*m[c]+m[a]*m[b]*l[c]
                           for l,m in zip(ell,emm))%2
            def R(a,b,c): return T(a,b,c)^S(a,b,c)
            phase=[]
            for x in range(q):
                z=sum(R(1<<i,1<<i,1<<i)*(x>>i&1) for i in range(n))
                for i,j in it.combinations(range(n),2):
                    assert R(1<<i,1<<i,1<<j)==R(1<<i,1<<j,1<<j)
                    z-=2*R(1<<i,1<<i,1<<j)*(x>>i&1)*(x>>j&1)
                z+=4*sum(R(1<<i,1<<j,1<<k)*(x>>i&1)*(x>>j&1)*(x>>k&1)
                         for i,j,k in it.combinations(range(n),3))
                phase.append(z%8)
            cube_count=0; extremal_sum=0
            for a,b,c in it.product(range(q),repeat=3):
                vals=phase
                for h in (a,b,c): vals=diff(vals,h,F,8)
                assert vals==[4*R(a,b,c)]*q
                extremal_sum+=q*((-1)**S(a,b,c))
                cube_count+=q
            assert Fraction(extremal_sum,q**4)==Fraction(1,2**(rr//2))
            # Every Walsh coefficient of the diagonal quadratic is 0 or +/-2^{-r/2}.
            Q=[T(x,x,x) for x in range(q)]
            walsh=[]
            for xi in range(q):
                w=sum((-1)**(Q[x]^((xi&x).bit_count()%2)) for x in range(q))
                assert w*w in (0,q*q//2**rr)
                walsh.append(w)
            mixed_tests=0; seven_tests=0
            for _ in range(4):
                fs=[[rng.choice(roots) for _ in range(q)] for j in range(8)]
                total=(0,0)
                for x,a,b,c in it.product(range(q),repeat=4):
                    z=(1,0)
                    for mask in range(8):
                        y=x ^ (a if mask&1 else 0) ^ (b if mask&2 else 0) ^ (c if mask&4 else 0)
                        v=fs[mask][y]
                        if mask.bit_count()%2: v=gaussian_conj(v)
                        z=gaussian_mul(z,v)
                    sign=(-1)**table[a][b][c]
                    total=total[0]+sign*z[0],total[1]+sign*z[1]
                assert (total[0]**2+total[1]**2)*2**rr<=q**8
                mixed_tests+=1
                seven=(0,0)
                for a,b,c in it.product(range(q),repeat=3):
                    z=(1,0)
                    for mask in range(1,8):
                        y=(a if mask&1 else 0) ^ (b if mask&2 else 0) ^ (c if mask&4 else 0)
                        z=gaussian_mul(z,fs[mask][y])
                    sign=(-1)**table[a][b][c]
                    seven=seven[0]+sign*z[0],seven[1]+sign*z[1]
                assert (seven[0]**2+seven[1]**2)**2*2**rr<=q**12
                seven_tests+=1
            out.append({'n':n,'case':case,'rank':rr,
                        'symmetric_coefficients':{','.join(map(str,k)):v for k,v in coeff.items()},
                        'extremizing_phase_numerators_mod_8':phase,
                        'exact_extremal_moment':str(Fraction(extremal_sum,q**4)),
                        'cube_basepoint_checks':cube_count,'walsh_numerators':walsh,
                        'mixed_cube_tests':mixed_tests,'seven_function_tests':seven_tests})
    return out


def main(output: Path) -> None:
    result = {'description':'Exact supplementary finite checks; not a formal proof',
              'seed':172917,'arithmetic':'integers and fractions only'}
    scalar=[]
    for p in (2,3,5,7):
        F=Field(p,1)
        for d in range(1,21):
            M,v=scalar_phase(p,d)
            for _ in range(d): v=diff(v,1,F,M)
            assert v==[M//p]*p
            assert diff(v,1,F,M)==[0]*p
            scalar.append({'p':p,'d':d,'root_order':M})
    result['scalar_checks']=scalar
    phase_cases=[]
    for p,n,c,d in [(2,2,1,3),(2,3,1,2),(3,2,1,3),(3,2,1,4),
                    (3,2,2,4),(3,2,3,2),(5,2,1,2)]:
        F=Field(p,n)
        M,vals=integrator(F,c,d)
        count=verify_phase(F,c,d,M,vals)
        phase_cases.append({'p':p,'n':n,'c':c,'d':d,'modulus':F.modulus,
                            'root_order':M,'phase_numerators':vals,
                            'basepoint_tuple_checks':count})
    result['integrators']=phase_cases
    rank_cases=[]
    for p,ns in [(2,range(1,9)),(3,range(1,5)),(5,range(1,4))]:
        for n in ns:
            F=Field(p,n)
            counts=Counter()
            for c in range(1,F.q):
                A=[[F.obstruction(c,p**i,p**j) for j in range(n)] for i in range(n)]
                rr=rank(A,p)
                t=expected_radical(F,c)
                assert rr==n-t,(p,n,c,rr,t)
                pairs,rad,W=symplectic(A,p)
                assert len(rad)==t and len(W)==(n+t)//2
                # Verify the wedge decomposition giving the exact correction count.
                basis=[[int(i==j) for i in range(n)] for j in range(n)]
                for e in basis:
                    for f in basis:
                        wedges=sum(pairing(A,e,u,p)*pairing(A,f,v,p)
                                   -pairing(A,e,v,p)*pairing(A,f,u,p) for u,v in pairs)%p
                        assert wedges==pairing(A,e,f,p)
                counts[(rr,len(W))]+=1
            rank_cases.append({'p':p,'n':n,'modulus':F.modulus,'nonzero_c_checked':F.q-1,
              'classes':[{'rank':r,'max_integrable_dimension':w,'count':cnt}
                         for (r,w),cnt in sorted(counts.items())]})
    result['radical_and_isotropic_checks']=rank_cases
    witnesses=[]
    for p,n,c,d in [(2,2,2,3),(2,3,1,3),(3,2,3,4),(3,3,1,4),(2,2,1,4)]:
        F=Field(p,n)
        found=None
        for a,b,z in it.product(range(F.q),range(F.q),range(1,F.q)):
            if d==p+1 and z!=1: continue
            cz=F.mul(c,z)
            if F.obstruction(cz,a,b):
                found={'p':p,'n':n,'c':c,'d':d,'a':a,'b':b,'extra_product':z,
                       'defect':F.obstruction(cz,a,b),'modulus':F.modulus}
                break
        assert found
        witnesses.append(found)
    result['nonintegrability_witnesses']=witnesses
    roots=[(1,0),(0,1),(-1,0),(0,-1)]
    rng=random.Random(172917)
    spectral=[]
    for n,c,exhaustive,count in [(2,1,True,0),(2,2,True,0),(3,1,False,100),(4,1,False,40),(4,2,False,40)]:
        F=Field(2,n)
        tables=(it.product(roots,repeat=F.q) if exhaustive else
                ([rng.choice(roots) for _ in range(F.q)] for _ in range(count)))
        rr=n-expected_radical(F,c)
        bound=Fraction(1,2**(rr//2))
        mmax=Fraction(0); tests=0
        for table in tables:
            moment=spectral_moment(F,c,list(table))
            assert moment<=bound
            mmax=max(mmax,moment);tests+=1
        spectral.append({'n':n,'c':c,'tables_checked':tests,'all_fourth_root_tables':exhaustive,
                         'rank':rr,'proved_bound':str(bound),'largest_tested_moment':str(mmax)})
    result['binary_spectral_checks']=spectral
    result['sharp_binary_tensor_checks']=binary_tensor_checks(rng)
    result['status']='PASS'
    output.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print('PASS: scalar lifts:',len(scalar))
    print('PASS: integrator cube/basepoint checks:',sum(x['basepoint_tuple_checks'] for x in phase_cases))
    print('PASS: trace coefficients/ranks:',sum(x['nonzero_c_checked'] for x in rank_cases))
    print('PASS: nonintegrability witnesses:',len(witnesses))
    print('PASS: exact spectral tables:',sum(x['tables_checked'] for x in spectral))
    print('PASS: sharp tensor/extremizer cases:',len(result['sharp_binary_tensor_checks']))
    print('Wrote',output)

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=Path('validation.json'))
    args=parser.parse_args()
    main(args.output)
