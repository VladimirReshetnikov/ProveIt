#!/usr/bin/env python3
"""Exact finite checks for Affine Matrix Inputs and Diophantine Universality.

Python 3.10+, standard library only.  These are implementation tests, not a
proof of the unbounded classification or of the external universality theorem.
Run: python3 verify.py --output verification.json
"""
from __future__ import annotations
import argparse
from dataclasses import dataclass
from fractions import Fraction as F
from itertools import combinations, product
from math import factorial, gcd, lcm
from pathlib import Path
import json
import random


def integer(x: int) -> int:
    if type(x) is not int:
        raise TypeError("Exact built-in integers are required; bool and float are rejected")
    return x


def choose(n: int, j: int) -> int:
    integer(n); integer(j)
    if j < 0:
        raise ValueError("j must be nonnegative")
    z = 1
    for i in range(j):
        z = z * (n - i) // (i + 1)
    return z


def coordinates(k: int, n: int) -> tuple[int, ...]:
    if type(k) is not int or k < 1:
        raise ValueError("k must be a positive integer")
    integer(n)
    return tuple(choose(n, i) * choose(k - n, k - i) for i in range(1, k + 1))


def mul(a: tuple[int, ...], b: tuple[int, ...]) -> tuple[int, ...]:
    if len(a) != len(b):
        raise ValueError("truncation degrees differ")
    return tuple(sum(a[j] * b[i-j] for j in range(i+1)) for i in range(len(a)))


def unipotent_power(k: int, slope: int, exponent: int) -> tuple[int, ...]:
    return tuple(choose(exponent, j) * slope**j for j in range(k + 1))


def period(k: int, e: int) -> int:
    integer(k); integer(e)
    if k < 1 or e < 1:
        raise ValueError("k,e must be positive")
    ans, n, p = e, e, 2
    while p * p <= n:
        if n % p == 0:
            while n % p == 0:
                n //= p
            power = p
            while power <= k:
                ans *= p
                power *= p
        p += 1
    if n > 1:
        power = n
        while power <= k:
            ans *= n
            power *= n
    return ans


def inverse(a: list[list[int | F]]) -> list[list[F]]:
    n = len(a)
    if n == 0:
        return []
    if any(len(row) != n for row in a):
        raise ValueError("matrix must be square")
    b = [[F(x) for x in row] + [F(i == j) for j in range(n)] for i, row in enumerate(a)]
    for j in range(n):
        piv = next((i for i in range(j, n) if b[i][j]), None)
        if piv is None:
            raise ValueError("singular matrix")
        b[j], b[piv] = b[piv], b[j]
        d = b[j][j]
        b[j] = [x/d for x in b[j]]
        for i in range(n):
            if i != j:
                d = b[i][j]
                b[i] = [x-d*y for x,y in zip(b[i], b[j])]
    return [row[n:] for row in b]


def matvec(a, v):
    return [sum(x*y for x,y in zip(row, v)) for row in a]


def lattice_membership(b: list[list[int]], v: tuple[int, ...]) -> bool:
    """Membership in an independent-column integer lattice, including rank zero."""
    k = len(v)
    r = len(b[0]) if b else 0
    if r == 0:
        return all(x == 0 for x in v)
    for rows in combinations(range(k), r):
        try:
            inv = inverse([b[j] for j in rows])
        except ValueError:
            continue
        sol = matvec(inv, [v[j] for j in rows])
        return all(q.denominator == 1 for q in sol) and matvec(b, sol) == list(v)
    raise ValueError("lattice columns are not independent")


def triangular(t: int) -> int:
    integer(t)
    return t*(t-1)//2


def T(t: int, s: int) -> tuple[tuple[int, ...], ...]:
    integer(t); integer(s)
    return ((1,t,s),(0,1,t),(0,0,1))


def cyclic_member(t: int, s: int) -> bool:
    """Compare the affine block with the exact power of the fixed generator."""
    return T(t,s) == ((1,t,choose(t,2)),(0,1,t),(0,0,1))


def multiplication_member(x: int,y: int,z: int,u: int) -> bool:
    for a in (x,y,z,u): integer(a)
    return cyclic_member(x+y,u) and cyclic_member(x-y,u-2*z+y)


def multiplication_residuals(x: int,y: int,z: int,u: int) -> tuple[int,int]:
    for a in (x,y,z,u): integer(a)
    return (2*u-(x+y)*(x+y-1), 2*(u-2*z+y)-(x-y)*(x-y-1))


@dataclass(frozen=True)
class Affine:
    constant: int = 0
    terms: tuple[tuple[str,int], ...] = ()
    def evaluate(self, values: dict[str,int]) -> int:
        integer(self.constant)
        total = self.constant
        for name, coeff in self.terms:
            integer(coeff)
            total += coeff*integer(values[name])
        return total


@dataclass(frozen=True)
class Gate:
    name: str
    left: Affine
    right: Affine


@dataclass(frozen=True)
class Circuit:
    variables: tuple[str,...]
    gates: tuple[Gate,...]
    output: Affine
    def validate(self) -> None:
        if len(set(self.variables)) != len(self.variables):
            raise ValueError("duplicate input variables")
        known = set(self.variables)
        for gate in self.gates:
            if gate.name in known:
                raise ValueError("duplicate register")
            for form in (gate.left,gate.right):
                integer(form.constant)
                for name,coefficient in form.terms:
                    integer(coefficient)
                    if name not in known:
                        raise ValueError("noncausal gate")
            known.add(gate.name)
        integer(self.output.constant)
        for name,coefficient in self.output.terms:
            integer(coefficient)
            if name not in known: raise ValueError("undefined output register")
    def witness(self, source: dict[str,int]):
        self.validate()
        values = {v:integer(source[v]) for v in self.variables}
        aux = []
        for gate in self.gates:
            a,b = gate.left.evaluate(values),gate.right.evaluate(values)
            values[gate.name] = a*b
            aux.append(triangular(a+b))
        return tuple(values[g.name] for g in self.gates), tuple(aux)
    def blocks(self, source, registers, aux):
        self.validate()
        if len(registers) != len(self.gates) or len(aux) != len(self.gates):
            raise ValueError("wrong witness arity")
        values = {v:integer(source[v]) for v in self.variables}
        values.update({g.name:integer(z) for g,z in zip(self.gates,registers)})
        blocks=[]
        for gate,u in zip(self.gates,aux):
            integer(u)
            a,b,z=gate.left.evaluate(values),gate.right.evaluate(values),values[gate.name]
            blocks.extend(((a+b,u),(a-b,u-2*z+b)))
        return blocks,self.output.evaluate(values)
    def accepts(self, source, registers, aux):
        blocks,final = self.blocks(source,registers,aux)
        return final == 0 and all(cyclic_member(t,s) for t,s in blocks)
    def quartic_value(self, source, registers, aux):
        blocks,final = self.blocks(source,registers,aux)
        return final*final + sum((2*s-t*(t-1))**2 for t,s in blocks)


def run_tests() -> dict:
    counts={}
    count=0
    for k in range(1,10):
        for n in range(-20,25):
            c=coordinates(k,n)
            z=(1,)+(0,)*k
            for i,exponent in enumerate(c,1):
                z=mul(z,unipotent_power(k,i,exponent))
            assert z == (1,n)+(0,)*(k-1)
            # Independent rational logarithm / moment calculation.
            for j in range(1,k+1):
                assert sum(c[i-1]*i**j for i in range(1,k+1)) == n**j
            count+=1
    counts['truncated_ring_and_moment_identities']=count
    count=0
    for k in range(1,9):
        for e in range(1,25):
            p=period(k,e)
            for n in range(-p,2*p+1):
                cn=coordinates(k,n)
                assert all(x % e == 0 for x in cn) == (n % p == 0)
                assert all((a-b)%e==0 for a,b in zip(coordinates(k,n+p),cn))
                count+=1
            assert all(not all(x%e==0 for x in coordinates(k,q)) for q in range(1,p))
    counts['exact_period_and_kernel_cases']=count
    count=0
    for k in range(1,5):
        for size in range(1,k+1):
            for subset in combinations(range(-2,4),size):
                n0=subset[0]; c0=coordinates(k,n0)
                cols=[tuple(a-b for a,b in zip(coordinates(k,f),c0)) for f in subset[1:]]
                b=[[col[i] for col in cols] for i in range(k)]
                for n in range(-8,10):
                    v=tuple(a-bb for a,bb in zip(coordinates(k,n),c0))
                    assert lattice_membership(b,v) == (n in subset)
                    count+=1
    counts['arbitrary_finite_hit_sets']=count
    count=0
    rng=random.Random(20261002)
    for k in range(1,6):
        for trial in range(12):
            # Unimodular row operations on a diagonal lattice.
            b=[[rng.randint(1,4) if i==j else 0 for j in range(k)] for i in range(k)]
            for _ in range(6):
                if k>1:
                    i,j=rng.sample(range(k),2); q=rng.choice((-2,-1,1,2))
                    b[i]=[x+q*y for x,y in zip(b[i],b[j])]
            inv=inverse(b)
            e=lcm(*(q.denominator for row in inv for q in row))
            p=period(k,e); n0=rng.randint(-5,5); c0=coordinates(k,n0)
            def mem(n):
                v=tuple(a-b for a,b in zip(coordinates(k,n),c0))
                return all(q.denominator==1 for q in matvec(inv,v))
            for n in range(-2*p,2*p+1):
                assert mem(n)==mem(n+p)
                count+=1
    counts['full_rank_lattice_period_cases']=count
    count=0
    for n in range(-100,101):
        assert lattice_membership([[1,0],[0,2]],coordinates(2,n)) == (n%4 in (0,1))
        assert lattice_membership([[1],[0]],coordinates(2,n)) == (n in (0,1))
        c2,c5=coordinates(3,2),coordinates(3,5)
        assert lattice_membership([[c2[i],c5[i]] for i in range(3)],coordinates(3,n)) == (n in (0,2,5))
        count+=3
    counts['printed_example_membership_cases']=count
    count=0
    for x,y in product(range(-12,13),repeat=2):
        u0=triangular(x+y)
        for dz,du in product(range(-3,4),repeat=2):
            z,u=x*y+dz,u0+du
            a,b=multiplication_residuals(x,y,z,u)
            assert a-b==4*(z-x*y)
            assert multiplication_member(x,y,z,u)==(dz==0 and du==0)
            assert (a*a+b*b==0)==multiplication_member(x,y,z,u)
            count+=1
    counts['multiplication_gadget_assignments']=count
    circuit=Circuit(('a','b','c'),(
        Gate('r0',Affine(0,(('a',1),)),Affine(0,(('b',1),))),
        Gate('r1',Affine(0,(('r0',1),('c',1))),Affine(0,(('r0',1),('c',1)))),
        Gate('r2',Affine(0,(('a',1),('c',1))),Affine(0,(('b',1),)))),
        Affine(-7,(('r1',1),('r2',-1))))
    count=0; accepted=[]; corruptions=0
    for a,b,c in product(range(-5,6),repeat=3):
        source={'a':a,'b':b,'c':c}
        registers,aux=circuit.witness(source)
        val=(a*b+c)**2-(a+c)*b-7
        assert circuit.accepts(source,registers,aux)==(val==0)
        assert circuit.quartic_value(source,registers,aux)==val*val
        if val==0:
            accepted.append([a,b,c])
            for j in range(6):
                for delta in (-1,1):
                    w=list(registers+aux);w[j]+=delta
                    assert not circuit.accepts(source,tuple(w[:3]),tuple(w[3:]))
                    assert circuit.quartic_value(source,tuple(w[:3]),tuple(w[3:]))>0
                    corruptions+=1
        count+=1
    counts['compiled_circuit_source_assignments']=count
    counts['compiled_circuit_corruptions_rejected']=corruptions
    # Symbolically universal quadratic curve: pointwise unipotent, but not
    # commuting after normalization. Exact identities here, not hardness tests.
    count=0
    for n in range(-1000,1001):
        a,b,c,d=1+12*n,1,-144*n*n,1-12*n
        assert a*d-b*c==1
        assert (a-1)**2+b*c==0 and c*(a+d-2)==0 and (d-1)**2+b*c==0
        count+=1
    counts['quadratic_loader_algebra_cases']=count
    rejected=0
    for bad in (True,False,1.0,F(1),"1"):
        try: coordinates(2,bad)
        except TypeError: rejected+=1
        else: raise AssertionError('inexact type accepted')
    counts['type_guard_rejections']=rejected
    return {
        'title':'Exact finite verification of affine-matrix input results',
        'seed':20261002,
        'status':'PASS',
        'arithmetic':'Python integers and fractions.Fraction; no floating point',
        'counts':counts,
        'total_cases':sum(counts.values()),
        'example_circuit':{'polynomial':'(a*b+c)^2-(a+c)*b-7','multiplication_gates':3,
                           'matrix_dimension':20,'additional_integer_coordinates':6,
                           'accepted_inputs_in_box':accepted},
        'scope':'Finite tests do not prove the unbounded theorems or instantiate a universal subgroup.',
    }


def main():
    if not __debug__:
        raise RuntimeError("Run without -O: this verifier uses assertions")
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=Path('verification.json'))
    args=parser.parse_args()
    result=run_tests()
    args.output.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(result,indent=2))

if __name__=='__main__': main()
