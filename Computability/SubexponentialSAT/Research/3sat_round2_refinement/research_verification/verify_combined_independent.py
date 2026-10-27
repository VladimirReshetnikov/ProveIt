#!/usr/bin/env python3
"""Independent finite checks; no imported proposal code or end-to-end SAT solver.

Every guard remains active under Python -O. Only Python standard library is used.
"""
from fractions import Fraction as F
from itertools import product, combinations_with_replacement
from math import factorial, comb, log, pi, sqrt
import json


def check(condition, message):
    if not condition:
        raise RuntimeError(message)


def v2(x):
    x = F(x)
    if not x:
        return float("inf")
    def vi(n):
        n = abs(n)
        return (n & -n).bit_length() - 1
    return vi(x.numerator) - vi(x.denominator)


def ceil_fraction(x):
    return -((-x.numerator) // x.denominator)


def greedy_matchings(edges):
    colors = []
    vertices = []
    for e in edges:
        for j, used in enumerate(vertices):
            if e[0] not in used and e[1] not in used:
                colors[j].append(e)
                used.update(e)
                break
        else:
            colors.append([e])
            vertices.append(set(e))
    return colors


def conditional_potential(colors, labels, q, lam):
    z = F(lam + 1, lam)
    total = F(0)
    for matching in colors:
        threshold = ceil_fraction(z * F(len(matching), q*q) + 10*lam*lam)
        for gamma in product(range(q), repeat=2):
            term = z ** (-threshold)
            for e in matching:
                probability = F(1)
                for endpoint, desired in zip(e, gamma):
                    if endpoint in labels:
                        probability *= int(labels[endpoint] == desired)
                    else:
                        probability /= q
                term *= 1 + probability / lam
            total += term
    return total


def test_potential():
    fixtures = [
        (4, [(0,2),(0,2),(0,3),(1,2),(1,3)], 2),
        (6, [(0,3),(1,4),(2,5),(0,4),(1,5),(2,3),(0,3)], 2),
        (4, [(0,2),(1,3),(0,3),(1,2)], 3),
    ]
    checked = 0
    exhaustive_assignments = 0
    for nv, edges, q in fixtures:
        colors = greedy_matchings(edges)
        degree = max(sum(v in e for e in edges) for v in range(nv))
        check(len(colors) <= 2*degree-1, "greedy edge-color bound")
        labels = {}
        lam = 2
        previous = conditional_potential(colors, labels, q, lam)
        check(previous < 1, "initial potential")
        for next_vertex in range(nv+1):
            free = [v for v in range(nv) if v not in labels]
            brute = F(0)
            for assignment in product(range(q), repeat=len(free)):
                full = dict(labels)
                full.update(zip(free, assignment))
                brute += conditional_potential(colors, full, q, lam)
                exhaustive_assignments += 1
            brute /= q**len(free)
            check(brute == previous, "conditional factorization mismatch")
            checked += 1
            if next_vertex == nv:
                break
            candidates = []
            for label in range(q):
                trial = dict(labels)
                trial[next_vertex] = label
                candidates.append(conditional_potential(colors, trial, q, lam))
            check(sum(candidates, F(0))/q == previous, "conditional average")
            chosen = min(range(q), key=lambda k: candidates[k])
            labels[next_vertex] = chosen
            check(candidates[chosen] <= previous, "potential increased")
            previous = candidates[chosen]
        check(previous < 1, "final potential")
        for gamma in product(range(q), repeat=2):
            total_load = 0
            for matching in colors:
                load = sum((labels[x], labels[y]) == gamma for x,y in matching)
                threshold = ceil_fraction(F(lam+1, lam)*F(len(matching),q*q)+10*lam*lam)
                check(load < threshold, "matching threshold")
                total_load += load
            bound = F(lam+1,lam)*F(len(edges),q*q)+20*degree*lam*lam
            check(total_load < bound, "summed cell bound")
    return {"fixtures":len(fixtures), "exact_conditional_expectations":checked,
            "exhaustive_completions":exhaustive_assignments}


def test_packets():
    tested = 0
    slots = 0
    for r in (2,3):
        for a in (1,2,3):
            L = 2**a
            for multiple in (1,2):
                H = multiple*L
                B = H*r**(2*a)
                packets = 0
                crossing = [0]*a
                row_ports = [[0]*r for _ in range(a)]
                col_ports = [[0]*r for _ in range(a)]
                for pairs in product(list(combinations_with_replacement(range(r),2)),repeat=a):
                    unequal = sum(x != y for x,y in pairs)
                    copies = H*2**unequal//L
                    packets += copies
                    for i, (x,y) in enumerate(pairs):
                        if x != y:
                            crossing[i] += copies
                    for slot in range(L):
                        slots += copies
                        for i,(x,y) in enumerate(pairs):
                            row,col = (y,x) if (slot>>i)&1 else (x,y)
                            row_ports[i][row] += copies
                            col_ports[i][col] += copies
                check(packets*L == B, "total padded packets")
                for i in range(a):
                    check(crossing[i]*r == packets*(r-1), "crossing fraction")
                    check(all(n*r == B for n in row_ports[i]), "row group balance")
                    check(all(n*r == B for n in col_ports[i]), "column group balance")
                tested += 1
    return {"fixtures":tested,"padded_slots_counted":slots}


class Q4:
    """Exact Q[U]/(U^2+U+1), unramified at 2."""
    def __init__(self,a=0,b=0):
        if isinstance(a,Q4):
            self.a,self.b = a.a,a.b
        else:
            self.a,self.b = F(a),F(b)
    def __add__(self,other):
        other=Q4(other)
        return Q4(self.a+other.a,self.b+other.b)
    __radd__=__add__
    def __neg__(self):
        return Q4(-self.a,-self.b)
    def __sub__(self,other):
        return self+-Q4(other)
    def __rsub__(self,other):
        return Q4(other)+-self
    def __mul__(self,other):
        other=Q4(other)
        return Q4(self.a*other.a-self.b*other.b,
                  self.a*other.b+self.b*other.a-self.b*other.b)
    __rmul__=__mul__
    def inv(self):
        norm=self.a*self.a-self.a*self.b+self.b*self.b
        check(norm != 0,"zero inverse")
        return Q4((self.a-self.b)/norm,-self.b/norm)
    def __truediv__(self,other):
        return self*Q4(other).inv()
    def __rtruediv__(self,other):
        return Q4(other)*self.inv()
    def __eq__(self,other):
        other=Q4(other)
        return self.a == other.a and self.b == other.b
    def valuation(self):
        return min(v2(self.a),v2(self.b))


def test_factorial_modes():
    rows=0
    identities=0
    coefficients=0
    for a in (1,2,3):
        L=2**a
        alpha=2*L
        grid=range(-L,L)
        derivative=1
        for t in grid:
            if t:
                derivative *= -t
        for t in grid:
            if not t or v2(t)>=a:
                continue
            i=v2(t)
            J=L//2**(i+1)
            for shift in (Q4(0),Q4(1),Q4(0,1),Q4(1,1)):
                T=t+alpha*shift
                numerator=Q4(1)
                for node in grid:
                    numerator *= T-node
                for x in range(L):
                    for y0 in range(2**(i+1)):
                        d0=t-y0+x
                        if not d0 or v2(d0)>i:
                            continue
                        d=T-y0+x
                        z=2**(i+1)/d
                        c=numerator/(derivative*d)
                        check(z.valuation()>=1,"z not even")
                        check(c.valuation()>=a+1-v2(d0),"kernel valuation")
                        w=z/2
                        w0=F(2**i,d0)
                        check((w-w0).valuation()>=a+1-i,"prime-subring congruence")
                        A=Q4(1)
                        target=[]
                        for b in range(J):
                            rb=c*factorial(b)*A/(1-b*z)
                            weight=1+b+2*v2(factorial(b))
                            check(rb.valuation()>=weight,"factorial target valuation")
                            target.append(rb)
                            A *= (z-2*b)/(1-b*z)
                            coefficients += 1
                        for j in range(J):
                            total=Q4(0)
                            for b in range(J):
                                numerator_b=(1-2*b*b)*(comb(j,b) if b<=j else 0)
                                denominator=1
                                for h in range(b+1):
                                    denominator *= 1-2*h*j
                                check(denominator%2 != 0,"source denominator not unit")
                                total += target[b]*F(numerator_b,denominator)
                            check(total == c/(1-z*j),"factorial separation identity")
                            identities += 1
                        rows += 1
    return {"extension_row_fixtures":rows,"exact_separation_identities":identities,
            "target_coefficient_valuation_checks":coefficients}


def test_hermite():
    schedules=0
    nodes=0
    for a in (1,2,3,4):
        L=2**a
        for u in range(1,a+1):
            for M in (1,3,17):
                A=L*(2*u-2)+2**(a+1-u)
                degree=M*(2*L-1)
                h=(degree+1+A-1)//A
                q=lambda i: h*max(0,u-i)
                retained=[t for t in range(-L,L) if t and v2(t)<u]
                check(sum(q(v2(t)) for t in retained) == h*A,"jet count")
                check(h*A>degree,"insufficient interpolation conditions")
                check((h-1)*A<=degree,"nonminimal integer slope")
                for t in retained:
                    i=v2(t)
                    B=sum(j*2**(a-i-j)*(q(i)-q(i+j)) for j in range(1,a-i+1))
                    E=F(1)
                    for t2 in retained:
                        if t2 != t:
                            E *= F(-t2,t-t2)**q(v2(t2))
                    check(v2(E)==-B,"Hermite rational multiplier valuation")
                    loss=B+(q(i)-1)*(a+1-i)
                    check(loss>0,"creation precision must increase")
                    check(B<=6*h*2**(a-i),"six-bit upper bound")
                    for j in range(q(i)):
                        check(loss+v2(E*F(-t,2*L)**j)>=0,"precision insufficiency")
                    nodes += 1
                schedules += 1
    return {"exact_schedules":schedules,"rational_Hermite_node_checks":nodes}


def test_constants():
    check(37**200 < 2**1043,"root packing exponent")
    A=F(10,1043)+F(5,708)
    check(6*A < F(1,10),"tail packing exponent")
    check(F(8226,1000)**2 > F(12516,185),"root radical upper bound")
    check(F(11734,1000)**2 > F(413,3),"tail radical upper bound")
    check(F(1582,1000)**2 > F(5,2),"geometric radical upper bound")
    ln2_lower=2*sum((F(1,(2*k+1)*3**(2*k+1)) for k in range(4)),F(0))
    check(ln2_lower>F(693,1000),"log lower bound via positive series")
    upper=2*F(22,7)/F(693,1000)*(F(8226,1000)+F(2,37)*F(11734,1000)/(1-F(1582,1000)/4))
    check(upper<85,"safe85 constant")
    C=2*pi/log(2)*(sqrt(F(12516,185))+F(2,37)*sqrt(F(413,3))/(1-sqrt(2.5)/4))
    return {"root_integer_inequality":True,"tail_exponent_exact":str(F(9,10)+6*A),
            "coefficient_decimal_noncertifying":C,"safe85_exact_upper":str(upper),
            "safe85_upper_decimal_noncertifying":float(upper)}


def main():
    output={"purpose":"Independent finite algebraic regression checks, not an end-to-end SAT solver or formal proof",
            "guards":"Explicit exceptions, active under Python -O",
            "matching_potential":test_potential(),"packet_counts":test_packets(),
            "factorial_modes":test_factorial_modes(),"Hermite_precision":test_hermite(),
            "schedule_and_constant":test_constants(),"status":"PASS"}
    print(json.dumps(output,indent=2,sort_keys=True))


if __name__ == "__main__":
    main()
