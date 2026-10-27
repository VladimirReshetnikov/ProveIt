"""Exact geometry and rational enclosure helpers for the r18 certificate."""


from fractions import Fraction as F

from itertools import combinations

from math import isqrt

from pathlib import Path

import json

def require(condition, message):
    if not condition:
        raise RuntimeError(message)

def affine_plans(r=18):
    require(9 <= r <= 18, "The explicit construction here uses 9..18 groups")
    plans = [[[3*x+y for y in range(3)] for x in range(3)]]
    for slope in range(3):
        plans.append([[3*x+(slope*x+b)%3 for x in range(3)] for b in range(3)])
    for plan in plans:
        for point in range(9, r):
            next(block for block in plan if point-9 in block).append(point)
    return plans

def operation_supports(plan, discounted=3, full=8):
    """Return (integer support vector, operation cardinalities) pairs."""
    r = sum(map(len, plan))
    require(sorted(x for block in plan for x in block) == list(range(r)), "Bad partition")
    edges = list(combinations(range(r), 2))
    all_vertices = set(range(r))
    result = []
    def operation(A, B, O):
        parts = [set(A), set(B), set(O)]
        require(all(parts), "Empty part")
        require(set.union(*parts) == all_vertices, "Incomplete operation")
        require(sum(map(len, parts)) == r, "Overlapping operation")
        category = {}
        for c, (j, k) in enumerate(((0,1),(0,2),(1,2))):
            for x in parts[j]:
                for y in parts[k]:
                    category[tuple(sorted((x,y)))] = c
        kind = tuple(sorted(map(len, parts)))
        for discount in range(3):
            vector = tuple(0 if edge not in category else
                           discounted if category[edge] == discount else full
                           for edge in edges)
            result.append((vector, kind))
    def recurse(block):
        if len(block) == 1:
            return
        split = len(block)//2
        left, right = block[:split], block[split:]
        recurse(left); recurse(right)
        operation(left, right, all_vertices-set(block))
    for block in plan:
        recurse(block)
    operation(*plan)
    require(len(result) == 3*(r-2), "Incorrect number of operation supports")
    return result

def dot(a, b):
    return sum(x*y for x,y in zip(a,b))

def sqrt_bounds(value, digits=50):
    value=F(value); scale=10**digits
    lower=isqrt(value.numerator*scale*scale//value.denominator)
    return F(lower,scale),F(lower+1,scale)

def atan_bounds(inverse, terms=80):
    partial=sum((F(1 if j%2==0 else -1,(2*j+1)*inverse**(2*j+1))
                 for j in range(terms)), F(0))
    following=F(1 if terms%2==0 else -1,(2*terms+1)*inverse**(2*terms+1))
    return min(partial,partial+following),max(partial,partial+following)

def pi_ln2_bounds():
    a,b=atan_bounds(5); c,d=atan_bounds(239)
    pi=(16*a-4*d,16*b-4*c)
    N=100
    lo=sum((F(2,(2*j+1)*3**(2*j+1)) for j in range(N)),F(0))
    remainder=F(2,(2*N+1)*3**(2*N+1))*F(9,8)
    return pi,(lo,lo+remainder)

def coefficient_bounds(squared_factors):
    pi,ln2=pi_ln2_bounds()
    roots=[sqrt_bounds(x) for x in squared_factors]
    return (pi[0]/ln2[1]*sum((x[0] for x in roots),F(0)),
            pi[1]/ln2[0]*sum((x[1] for x in roots),F(0)))

def decimal_enclosure(bounds, digits=12):
    scale=10**digits; lo,hi=bounds
    low=lo.numerator*scale//lo.denominator
    high=(hi.numerator*scale+hi.denominator-1)//hi.denominator
    def fmt(v): return str(v//scale)+'.'+str(v%scale).zfill(digits)
    return [fmt(low),fmt(high)]
