#!/usr/bin/env python3
"""Exact, dependency-free certificates for the accompanying research report.

This verifies finite algebra and q-expansion calculations. It is not a Lean
verification of the new arguments and does not prove any new L-function RH.
Run from any directory; results are written beside this file.
"""
from fractions import Fraction as F
from itertools import combinations, permutations, product
from math import comb, gcd, isqrt
from pathlib import Path
import json


def matmul(a, b):
    return [[sum(a[i][k] * b[k][j] for k in range(len(b)))
             for j in range(len(b[0]))] for i in range(len(a))]


def matsub(a, b):
    return [[x-y for x,y in zip(ar,br)] for ar,br in zip(a,b)]


def determinant(a):
    n = len(a)
    total = 0
    for perm in permutations(range(n)):
        inv = sum(perm[i] > perm[j] for i in range(n) for j in range(i+1,n))
        term = (-1)**inv
        for i,j in enumerate(perm):
            term *= a[i][j]
        total += term
    return total


def smith_invariants_by_minors(a):
    """Use determinantal divisors, independent of a Smith-reduction algorithm."""
    previous = 1
    diagonal = []
    for size in range(1, min(len(a),len(a[0]))+1):
        div = 0
        for rows in combinations(range(len(a)),size):
            for cols in combinations(range(len(a[0])),size):
                minor = [[a[i][j] for j in cols] for i in rows]
                div = gcd(div,abs(determinant(minor)))
        if div == 0:
            diagonal.extend([0]*(min(len(a),len(a[0]))-len(diagonal)))
            break
        assert div % previous == 0
        diagonal.append(div//previous)
        previous = div
    return diagonal


def commutator_relations(m):
    generators = [[[1,m],[0,1]], [[1,0],[m,1]]]
    columns = []
    for pos in range(4):
        e = [[int(2*i+j == pos) for j in range(2)] for i in range(2)]
        col = []
        for g in generators:
            col.extend(x for row in matsub(matmul(e,g),matmul(g,e)) for x in row)
        columns.append(col)
    return [list(row) for row in zip(*columns)]


def hom_certificates():
    smith = []
    for m in [1,2,3,4,5,7,9,25]:
        matrix = commutator_relations(m)
        diagonal = smith_invariants_by_minors(matrix)
        assert diagonal == [m,m,m,0]
        smith.append({'m':m, 'smith_diagonal':diagonal})
    cases = []
    for ell,max_n,max_r in [(2,4,3),(3,2,2),(5,2,1)]:
        for n in range(1,max_n+1):
            modulus = ell**n
            for r in range(max_r+1):
                matrix = commutator_relations(ell**r)
                count = 0
                for x in product(range(modulus),repeat=4):
                    if all(sum(a*b for a,b in zip(row,x)) % modulus == 0 for row in matrix):
                        count += 1
                predicted_length = n+3*min(n,r)
                assert count == ell**predicted_length
                cases.append({'ell':ell,'n':n,'r':r,'count':count,
                              'length':predicted_length,
                              'reduced_length':3*min(n,r)})
    symmetric = []
    for ell in [2,3,5]:
        for n in range(1,4):
            modulus = ell**n
            for r in range(3):
                m = ell**r
                generators = [[[1,m],[0,1]],[[1,0],[m,1]]]
                count = 0
                for u,v,w in product(range(modulus),repeat=3):
                    form = [[u,v],[v,w]]
                    if all(all(x % modulus == 0 for row in matsub(
                        matmul(matmul([list(t) for t in zip(*g)],form),g),form)
                        for x in row) for g in generators):
                        count += 1
                length = 2*min(n,r)+min(n,r+(ell==2))
                assert count == ell**length
                symmetric.append({'ell':ell,'n':n,'r':r,'count':count,'length':length})
    return {'smith_checks':smith, 'exhaustive_modular_checks':cases,
            'symmetric_pairing_checks':symmetric}


def conv(a,b,n):
    out = [0]*(n+1)
    for i,x in enumerate(a):
        if x:
            for j,y in enumerate(b[:n+1-i]):
                if y:
                    out[i+j] += x*y
    return out


def add(a,b,scale=1):
    return [x+scale*y for x,y in zip(a,b)]


def expansions(n):
    e4 = [1]+[240*sum(d**3 for d in range(1,k+1) if k % d == 0)
              for k in range(1,n+1)]
    delta = [1]+[0]*n
    for j in range(1,n+1):
        factor = [0]*(n+1)
        for k in range(min(24,n//j)+1):
            factor[k*j] = (-1)**k*comb(24,k)
        delta = conv(delta,factor,n)
    delta = [0]+delta[:n]
    delta2 = conv(delta,delta,n)
    de43 = conv(delta,conv(conv(e4,e4,n),e4,n),n)
    g1 = add(de43,delta2,-696)
    assert (g1[1],g1[2],delta2[1],delta2[2]) == (1,0,0,1)
    return delta,e4,g1,delta2


def hecke_p(series,p,n,weight=24):
    return series[p*n]+(p**(weight-1)*series[n//p] if n % p == 0 else 0)


def prime_factors(n):
    factors = {}
    d = 2
    while d*d <= n:
        while n % d == 0:
            factors[d] = factors.get(d,0)+1
            n //= d
        d += 1
    if n > 1:
        factors[n] = factors.get(n,0)+1
    return factors


D = 144169


class Q:
    """Element u+v*sqrt(D) with exact rational coordinates."""
    def __init__(self,u=0,v=0):
        self.u,self.v = F(u),F(v)
    @staticmethod
    def cast(x):
        return x if isinstance(x,Q) else Q(x)
    def __add__(self,other):
        other = self.cast(other)
        return Q(self.u+other.u,self.v+other.v)
    __radd__ = __add__
    def __neg__(self):
        return Q(-self.u,-self.v)
    def __sub__(self,other):
        return self+-self.cast(other)
    def __rsub__(self,other):
        return self.cast(other)+-self
    def __mul__(self,other):
        other = self.cast(other)
        return Q(self.u*other.u+D*self.v*other.v,
                 self.u*other.v+self.v*other.u)
    __rmul__ = __mul__
    def __truediv__(self,other):
        other = self.cast(other)
        norm = other.u**2-D*other.v**2
        assert norm != 0
        return self*Q(other.u/norm,-other.v/norm)
    def __rtruediv__(self,other):
        return self.cast(other)/self
    def __eq__(self,other):
        other = self.cast(other)
        return self.u == other.u and self.v == other.v
    def integral(self):
        # O_K = Z[(1+sqrt(D))/2], coordinates u-v and 2v.
        return (self.u-self.v).denominator == 1 and (2*self.v).denominator == 1
    def json(self):
        return {'rational':str(self.u),'sqrt_coefficient':str(self.v)}


def hecke_certificates():
    nmax = 64
    delta,e4,g1,g2 = expansions(nmax)
    t2 = [[hecke_p(g,2,i) for g in (g1,g2)] for i in (1,2)]
    assert t2 == [[0,1],[20468736,1080]]
    trace = sum(t2[i][i] for i in range(2))
    det = determinant(t2)
    discr = trace**2-4*det
    assert (trace,det,discr) == (1080,-20468736,576*D)
    assert prime_factors(D) == {D:1} and D % 4 == 1
    lambdap,lambdam = Q(540,12),Q(540,-12)
    pplus = [[(t2[i][j]-(lambdam if i==j else 0))/(lambdap-lambdam)
              for j in range(2)] for i in range(2)]
    identity = [[Q(int(i==j)) for j in range(2)] for i in range(2)]
    pminus = matsub(identity,pplus)
    assert matmul(pplus,pplus) == pplus
    assert matmul(pminus,pminus) == pminus
    assert all(x==0 for row in matmul(pplus,pminus) for x in row)
    assert matmul(t2,pplus) == [[lambdap*x for x in row] for row in pplus]
    clearing = 24*D
    assert all((clearing*x).integral() for row in pplus for x in row)
    for prime in prime_factors(clearing):
        assert not (F(clearing,prime)*pplus[0][1]).integral()
    hecke = []
    for p in [2,3,5,7,11,13,17,19,23,29,31]:
        t = [[hecke_p(g,p,i) for g in (g1,g2)] for i in (1,2)]
        a,b = t[0]
        assert t == [[a,b],[20468736*b,a+1080*b]]
        # Extra coefficient check. Equality as modular forms already follows
        # from dimension two and the first two coefficient coordinates.
        for j,g in enumerate((g1,g2)):
            for k in range(1,nmax//p+1):
                assert hecke_p(g,p,k) == t[0][j]*g1[k]+t[1][j]*g2[k]
        hecke.append({'p':p, 'matrix':t,'I_coefficient':a,'T2_coefficient':b})
    return {'basis':'g1=Delta*E4^3-696*Delta^2; g2=Delta^2',
            'g1_coefficients_1_to_8':g1[1:9], 'g2_coefficients_1_to_8':g2[1:9],
            'T2':t2, 'characteristic_polynomial':[1,-trace,det],
            'discriminant':discr,'discriminant_factorization':prime_factors(discr),
            'quadratic_field_discriminant':D,
            'eigenvalues':[lambdap.json(),lambdam.json()],
            'P_plus':[[x.json() for x in row] for row in pplus],
            'projector_denominator_ideal':'(24*sqrt(144169))',
            'denominator_ideal_norm':576*D,
            'least_positive_rational_integer_clearing_projector':clearing,
            'hecke_operators_checked':hecke}


def main():
    result = {'scope':'Exact finite calculations; not a Lean build or a proof of a new RH.',
              'hom':hom_certificates(), 'hecke':hecke_certificates()}
    out = Path(__file__).with_name('exact_results.json')
    out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'status':'all exact assertions passed',
                      'hom_enumerations':len(result['hom']['exhaustive_modular_checks']),
                      'smith_cases':len(result['hom']['smith_checks']),
                      'symmetric_pairing_cases':len(result['hom']['symmetric_pairing_checks']),
                      'hecke_primes':len(result['hecke']['hecke_operators_checked']),
                      'T2':result['hecke']['T2'],
                      'integer_projector_denominator':result['hecke']['least_positive_rational_integer_clearing_projector'],
                      'output':str(out)},indent=2))


if __name__ == '__main__':
    main()
