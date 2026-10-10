#!/usr/bin/env python3
"""Integral polynomial normal forms for finite weighted distributions.

Every computation uses exact arithmetic.  Local coordinates encode
sum(a_p/p**e_p) in Q/Z; none of the methods use Dirichlet characters.
"""
from __future__ import annotations
from functools import lru_cache
from itertools import product
from math import gcd
import sympy as sp

class Distribution:
    def __init__(self, q):
        self.q = q
        self.factors = tuple((int(p),int(e)) for p,e in sp.factorint(q).items())
        self.primes = tuple(p for p,e in self.factors)
        self.moduli = tuple(p**e for p,e in self.factors)
        self.weights = sp.symbols(' '.join(f't{p}' for p in self.primes), seq=True)
        self.basis = tuple(x for x in product(*(range(m) for m in self.moduli))
                           if all(not self.is_pivot(i,a) for i,a in enumerate(x)))
        self.basis_index = {x:i for i,x in enumerate(self.basis)}

    def is_pivot(self, i, a):
        if a == 0:
            return False
        p,e = self.factors[i]
        j=e
        while a % p == 0:
            a //= p
            j -= 1
        return a == 1 if j == 1 else a < p**(j-1)

    def to_residue(self, x):
        return sum(a*(self.q//m) for a,m in zip(x,self.moduli)) % self.q

    def from_residue(self, r):
        return tuple(r * pow(self.q//m, -1, m) % m for m in self.moduli)

    @lru_cache(None)
    def normal(self, x):
        """Return tuple of integer-polynomial coordinates in the fixed basis."""
        index=next((i for i,a in enumerate(x) if self.is_pivot(i,a)), None)
        if index is None:
            v=[sp.Integer(0)]*len(self.basis)
            v[self.basis_index[x]]=sp.Integer(1)
            return tuple(v)
        p,e=self.factors[index]
        m=self.moduli[index]
        parent=p*x[index] % m
        lower=tuple(p*a % n for a,n in zip(x,self.moduli))
        result=[self.weights[index]*c for c in self.normal(lower)]
        for k in range(p):
            sibling=(x[index]+k*(m//p)) % m
            if sibling == x[index]:
                continue
            y=list(x)
            y[index]=sibling
            for j,c in enumerate(self.normal(tuple(y))):
                result[j] -= c
        return tuple(sp.expand(c) for c in result)

    def relation_matrix(self):
        rows=[]
        for p,t in zip(self.primes,self.weights):
            for r in range(0,self.q,p):
                row=[sp.Integer(int((p*j-r)%self.q == 0)) for j in range(self.q)]
                row[r] -= t
                rows.append(row)
        return sp.Matrix(rows)

    def normal_matrix(self):
        return sp.Matrix.hstack(*(sp.Matrix(self.normal(self.from_residue(r)))
                                  for r in range(self.q)))

    def primitive_matrix(self):
        return sp.Matrix.hstack(*(sp.Matrix(self.normal(self.from_residue(r)))
                                  for r in range(self.q) if gcd(r,self.q)==1))

    def determinant_formula(self):
        ans=sp.Integer(1)
        for (p,e),t in zip(self.factors,self.weights):
            M=self.q//p**e
            h=int(sp.n_order(p,M)) if M > 1 else 1
            ans *= t**(int(sp.totient(M))*(p**(e-1)-1)) * (t**h-1)**(int(sp.totient(M))//h)
        return ans

if __name__=='__main__':
    for q in (2,3,4,5,6,8,9,10,12,15,16,18,20,21,24,25,27,30):
        D=Distribution(q)
        C=D.normal_matrix()
        residual=C*D.relation_matrix().T
        assert all(sp.expand(x)==0 for x in residual)
        A=D.primitive_matrix()
        det=sp.factor(A.det(method='domain-ge'))
        ratio=sp.cancel(det/D.determinant_formula())
        print(q, 'basis',tuple(D.to_residue(x) for x in D.basis), 'primitive determinant ratio',ratio,flush=True)
        assert ratio in (-1,1)
