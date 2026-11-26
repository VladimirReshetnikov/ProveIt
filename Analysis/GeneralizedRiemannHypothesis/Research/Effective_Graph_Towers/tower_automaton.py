#!/usr/bin/env python3
"""Compile digit automata for p-adic valuations of Laurent polynomial torsion products.

Input is a JSON array [[coefficient, [exponents...]], ...] with integer entries.
For a spanning-tree determinant, --trees BASE_COUNT adds v_p(BASE_COUNT)-d*n.
Alternatively pass --graph and an object with vertex count vertices and an edges
list [[tail, head, voltage_vector], ...], one orientation per undirected edge.
Vertex labels are 0 through vertices-1. Loops and parallel edges are allowed.
Default output gives a provably exact generating function for the level sequence.
Use --levels for direct finite-layer evaluation with no closure enumeration.
Requires Python 3.10+ and SymPy.  Run with --help for the command-line interface.
"""
from __future__ import annotations

import argparse
import json
from collections import defaultdict, deque
from functools import lru_cache
from itertools import product
from math import comb, gcd
from pathlib import Path

import sympy as sp


def valuation(a, p):
    if not a:
        raise ValueError("zero has no finite valuation")
    a = abs(a)
    v = 0
    while a % p == 0:
        a //= p
        v += 1
    return v


def greedy_rows(candidates, p):
    """Yield the original independent rows and their parent/digit index recipes."""
    pivots = {}
    for row, parent, digit in candidates:
        reduced = list(row)
        for j in sorted(pivots):
            if reduced[j]:
                factor = reduced[j]
                reduced = [(x-factor*y) % p for x,y in zip(reduced,pivots[j])]
        j = next((i for i,x in enumerate(reduced) if x), None)
        if j is not None:
            factor = pow(reduced[j], -1, p)
            pivots[j] = tuple(x*factor % p for x in reduced)
            yield row, parent, digit


# A state is (pivot coordinate, first-digit flag, exponent carries, ordered Lucas rows).
# Empty carries and empty rows denote a stable nonzero coefficient at an index j.
# Its two aggregate registers are Q=p^k and that j. An ordinary state has Q followed
# by the indices of its rows. All registers are summed across paths into that state.
class Compiler:
    def __init__(self, p, terms, omit_zeros=False):
        if not sp.isprime(p):
            raise ValueError("p must be prime")
        if not terms:
            raise ValueError("supply at least one coefficient-exponent pair")
        self.p = int(p)
        self.d = len(terms[0][1])
        if not self.d:
            raise ValueError("at least one variable is required")
        merged = defaultdict(int)
        for c,a in terms:
            if len(a) != self.d or type(c) is not int or any(type(x) is not int for x in a):
                raise ValueError("expected integral coefficients and exponent tuples of common dimension")
            merged[tuple(a)] += c
        exps = sorted(a for a,c in merged.items() if c)
        if not exps:
            raise ValueError("zero polynomial")
        self.g = min(valuation(merged[a],p) for a in exps)
        self.coeffs = tuple(merged[a] // p**self.g for a in exps)
        self.exps = exps
        self.m = len(exps)
        self.omit = omit_zeros
        self.choose = [[comb(i,j) % p if j <= i else 0 for j in range(p)] for i in range(p)]

    def starts(self):
        return [(i, True, (0,)*self.m, ((1,)*self.m,)) for i in range(self.d)]

    @staticmethod
    def size(s):
        return 1 + (len(s[3]) or 1)

    @lru_cache(maxsize=None)
    def choices(self, pivot, first):
        ds = [([int(first)] if i == pivot else ([0] if first and i < pivot else range(self.p)))
              for i in range(self.d)]
        return tuple(product(*ds))

    @lru_cache(maxsize=None)
    def low_groups(self, rows):
        group = {}
        for i,col in enumerate(zip(*rows)):
            group.setdefault(col,[]).append(i)
        return tuple((col,tuple(indices)) for col,indices in group.items())

    def stop(self, rows, digits):
        """Return (coefficient of Q, earlier row index), or None for an exact zero."""
        p = self.p
        grouped = []
        content = 0
        for col,indices in self.low_groups(rows):
            sums = [0]*p
            for i in indices:
                sums[digits[i]] += self.coeffs[i]
            values = [x-sums[-1] for x in sums[:-1]]
            for x in values:
                content = gcd(content,x)
            grouped.append((col,values))
        if not content:
            return None
        mu = valuation(content,p)
        for t in range(p-1):
            weights = [sum((x//(p**mu))*self.choose[a][t] for a,x in enumerate(vals)) % p
                       for col,vals in grouped]
            for j in range(len(rows)):
                if sum(w*col[j] for w,(col,vals) in zip(weights,grouped)) % p:
                    return (p-1)*(self.g+mu)+t, j
        raise ArithmeticError("nonzero reduced cyclotomic remainder lost its first unit coefficient")

    @lru_cache(maxsize=None)
    def transitions(self, state):
        pivot,first,carries,rows = state
        p = self.p
        size = self.size(state)
        final = [0]*size
        blocks = {}
        has_zero = False

        def add(target, recipes, mult=1):
            if target not in blocks:
                blocks[target] = [[0]*size for _ in range(1+len(recipes))]
            mat = blocks[target]
            mat[0][0] += p*mult
            for i,(parent,digit) in enumerate(recipes,1):
                mat[i][0] += digit*mult
                mat[i][parent+1] += mult

        choices = self.choices(pivot,first)
        stable = (pivot,False,(),())
        if not rows:
            m = len(choices)
            final = [m*(p-1)*self.g, m]
            add(stable,[(0,0)],m)
        else:
            for u in choices:
                raw = [c+sum(x*y for x,y in zip(a,u)) for c,a in zip(carries,self.exps)]
                digits = tuple(x % p for x in raw)
                stop = self.stop(rows,digits)
                if stop is None:
                    has_zero = True
                else:
                    factor,j = stop
                    final[0] += factor
                    final[1+j] += 1
                cand = ((tuple(self.choose[v][t]*b % p for v,b in zip(digits,row)),j,t)
                        for t in range(p) for j,row in enumerate(rows))
                kept = list(greedy_rows(cand,p))
                first_unit = next(((j,t) for r,j,t in kept
                                  if sum(a*b for a,b in zip(r,self.coeffs)) % p), None)
                if first_unit is not None:
                    add(stable,[first_unit])
                else:
                    nxt = (pivot,False,tuple(x//p for x in raw),tuple(r for r,j,t in kept))
                    add(nxt,[(j,t) for r,j,t in kept])
        return final,blocks,has_zero

    def initial_registers(self):
        return {s:[1,0] for s in self.starts()}

    def advance(self, registers):
        total = 0
        result = {}
        for s,reg in registers.items():
            final,blocks,has_zero = self.transitions(s)
            if has_zero and not self.omit:
                raise ValueError("p-power torsion zero found on a nontrivial shell; use --omit-zeros to skip zero values")
            total += sum(x*y for x,y in zip(final,reg))
            for target,mat in blocks.items():
                if target not in result:
                    result[target] = [0]*len(mat)
                for i,row in enumerate(mat):
                    result[target][i] += sum(x*y for x,y in zip(row,reg))
        return total,result

    def reachable_matrix(self):
        """Build the block transition matrix on aggregate registers of reachable states."""
        starts = self.starts()
        seen = set(starts)
        queue = deque(starts)
        ordered = []
        while queue:
            state = queue.popleft()
            ordered.append(state)
            _,blocks,has_zero = self.transitions(state)
            if has_zero and not self.omit:
                raise ValueError("nontrivial p-power torsion zero; use --omit-zeros to skip zero values")
            for target in blocks:
                if target not in seen:
                    seen.add(target)
                    queue.append(target)
        offsets = {}
        size = 0
        for state in ordered:
            offsets[state] = size
            size += self.size(state)
        entries = {}
        for state in ordered:
            _,blocks,_ = self.transitions(state)
            for target,block in blocks.items():
                for i,row in enumerate(block):
                    for j,x in enumerate(row):
                        if x:
                            entries[offsets[target]+i,offsets[state]+j] = x
        return len(ordered),sp.SparseMatrix(size,size,entries)

    def levels(self, last, trees=None):
        reg = self.initial_registers()
        value = 0 if trees is None else valuation(trees,self.p)
        values = [value]
        for _ in range(last):
            shell,reg = self.advance(reg)
            value += shell - (0 if trees is None else self.d)
            values.append(value)
        return values


def exact_law(compiler, trees=None):
    """Use the exact characteristic polynomial to certify all levels at once."""
    t = sp.Symbol('t')
    states,matrix = compiler.reachable_matrix()
    L = matrix.rows
    d,p = compiler.d,compiler.p
    # If char_M(x)=x^L+c1*x^(L-1)+...+cL, det(I-tM)=1+c1*t+...+cL*t^L.
    coeff = matrix.charpoly().all_coeffs()
    denominator = sum(c*t**i for i,c in enumerate(coeff) if c)
    # Shell generating function f(I-tM)^(-1)u has numerator of degree at most
    # L-1 even when M is singular. The first L shell sums determine it.
    vals = compiler.levels(L,trees)
    correction = d if trees is not None else 0
    shells = [vals[i+1]-vals[i]+correction for i in range(L)]
    conv = [sum(coeff[k]*shells[i-k] for k in range(i+1) if coeff[k]) for i in range(L)]
    numerator = sum(a*t**i for i,a in enumerate(conv) if a)
    gf = sp.cancel(vals[0]/(1-t) - correction*t/(1-t)**2 + t*numerator/((1-t)*denominator))
    allowed = sp.Poly((1-p**d*t)*sp.prod((1-p**i*t)**2 for i in range(d)),t)
    num,den = sp.fraction(gf)
    poly,proper = sp.div(num,den,t,domain=sp.QQ)
    result = {"states":states,"register_dimension":L,"generating_function":str(gf)}
    if sp.rem(allowed.as_expr(),den,t,domain=sp.QQ)==0:
        n,X = sp.symbols('n X')
        tail = 0
        # Write partial fractions as A_i/(1-qt) + B_i/(1-qt)^2.
        for i in range(d+1):
            q = p**i
            regular = sp.cancel((1-q*t)**2 * proper/den)
            point = sp.Rational(1,q)
            B = regular.subs(t,point)
            A = -sp.diff(regular,t).subs(t,point)/q
            tail += (A+(n+1)*B)*X**i
        onset = 0 if poly == 0 else int(sp.degree(poly,t))+1
        result.update({"P(X,n)":str(sp.expand(tail)),"least_onset":onset,
                       "finite_correction":str(poly),"prefix":vals[:max(1,onset)]})
    return result


def graph_terms(graph):
    """Compute the determinant of the Laurent Laplacian and a base cofactor."""
    num = graph["vertices"]
    edges = graph["edges"]
    if type(num) is not int or num < 1 or not edges:
        raise ValueError("expected a positive vertex count and nonempty edge list")
    dim = len(edges[0][2])
    if dim < 1:
        raise ValueError("voltage vectors must have positive dimension")
    variables = sp.symbols(f"x0:{dim}")
    lap = sp.zeros(num)
    base = sp.zeros(num)
    for a,b,voltage in edges:
        if (type(a) is not int or type(b) is not int or not (0<=a<num and 0<=b<num)
                or len(voltage)!=dim or any(type(v) is not int for v in voltage)):
            raise ValueError("invalid edge or voltage")
        char = sp.prod(x**v for x,v in zip(variables,voltage))
        lap[a,a] += 1
        lap[b,b] += 1
        lap[a,b] -= char
        lap[b,a] -= 1/char
        if a != b:
            base[a,a] += 1
            base[b,b] += 1
            base[a,b] -= 1
            base[b,a] -= 1
    count = int(base[1:,1:].det())
    if not count:
        raise ValueError("base graph is disconnected")
    # Division-free determinant avoids symbolic fractional pivots.
    symbol = sp.expand(lap.det(method="berkowitz"))
    terms = []
    for monomial in sp.Add.make_args(symbol):
        c,term = monomial.as_coeff_Mul()
        powers = term.as_powers_dict()
        terms.append((int(c),[int(powers.get(x,0)) for x in variables]))
    return terms,count


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("p",type=int)
    parser.add_argument("terms",help="JSON string or path to JSON file")
    parser.add_argument("--graph",action="store_true",help="read a voltage graph instead of a Laurent polynomial")
    parser.add_argument("--trees",type=int,metavar="BASE_COUNT",help="apply the graph complexity correction")
    parser.add_argument("--levels",type=int,metavar="N",help="compute only levels 0 through N")
    parser.add_argument("--omit-zeros",action="store_true",help="sum only nonzero specializations")
    args = parser.parse_args()
    raw = args.terms.strip()
    terms = json.loads(raw if raw.startswith(('[','{')) else Path(raw).read_text())
    if args.graph:
        if args.trees is not None or args.omit_zeros:
            parser.error("--graph computes its own base count and requires connected levels")
        terms,args.trees = graph_terms(terms)
    if args.trees is not None and args.trees < 1:
        parser.error("the base tree count must be positive")
    c = Compiler(args.p,terms,args.omit_zeros)
    value = exact_law(c,args.trees) if args.levels is None else c.levels(args.levels,args.trees)
    print(json.dumps(value,indent=2))

if __name__ == "__main__":
    main()
