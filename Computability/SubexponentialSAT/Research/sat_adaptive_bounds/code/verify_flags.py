#!/usr/bin/env python3
"""Exact finite checks for adaptive linear-flag separator certificates.

Python standard library only. All verification gates use explicit exceptions
and remain active under python -O. This checks finite combinatorics, exact sum
reassociation over a ring with zero divisors, and the rational schedule.
It is not a verification of the imported SAT reduction or contraction engine.
"""

from collections import Counter
from fractions import Fraction
from functools import lru_cache
from itertools import product
import json
import math
import random
import time


def require(condition, message):
    """A correctness gate that cannot be disabled by optimized Python."""
    if not condition:
        raise RuntimeError(message)


def elements(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


@lru_cache(None)
def hyperplanes(space):
    """All codimension-one linear subspaces, as point-membership bitmasks."""
    points = list(elements(space))
    coordinates = [0]
    for x in points:
        if x not in coordinates:
            coordinates += [v ^ x for v in coordinates]
    require(set(coordinates) == set(points), "coordinate basis does not span the space")
    dimension = (len(points)).bit_length() - 1
    require(1 << dimension == len(points), "subspace size is not a power of two")
    result = []
    for functional in range(1, 1 << dimension):
        mask = 0
        for coord, point in enumerate(coordinates):
            if (coord & functional).bit_count() % 2 == 0:
                mask |= 1 << point
        result.append(mask)
    require(len(set(result)) == (1 << dimension) - 1, "hyperplane count failed")
    return tuple(sorted(result))


@lru_cache(None)
def flags_below(space):
    if space == 1:
        return ((1,),)
    return tuple((space,) + tail
                 for plane in hyperplanes(space)
                 for tail in flags_below(plane))


def flags(j):
    return flags_below((1 << (1 << j)) - 1)


def path_masks(flag):
    """For each d!=0, allowed a for the zero-path edge (a,a xor d)."""
    r = flag[0].bit_count()
    answer = []
    for d in range(1, r):
        for k in range(1, len(flag)):
            if not (flag[k] >> d) & 1:
                answer.append(flag[k-1])
                break
        else:
            raise AssertionError("Difference never leaves the flag")
    return tuple(answer)


@lru_cache(None)
def translate(mask, x):
    return sum(1 << (a ^ x) for a in elements(mask))


def intersection(first, second, delta):
    """Translation symmetry reduces arbitrary leaf pairs to (0,delta)."""
    return sum((a & translate(b, delta)).bit_count()
               for a, b in zip(first, second))


def check_flags(j, exhaustive_intersections):
    r = 1 << j
    family = flags(j)
    expected = math.prod((1 << i) - 1 for i in range(1, j+1))
    require(len(family) == expected, "complete flag count failed")
    paths = [path_masks(flag) for flag in family]
    path_size = 2 * (r*r-1) // 3
    counts = Counter()
    for p in paths:
        require(sum(mask.bit_count() for mask in p) == path_size, "balanced path size failed")
        for d, mask in enumerate(p, 1):
            for a in elements(mask):
                counts[(a, a ^ d)] += 1
    require(len(counts) == r*(r-1), "flag average omits a directed pair")
    for (a, b), count in counts.items():
        require(count == (expected if a == 0 or b == 0 else 2*expected//3),
                "flag-average incidence count failed")
    norm_squared = sum(Fraction(c, expected)**2 for c in counts.values())
    require(norm_squared == Fraction((r-1)*(4*r+10), 9), "flag-average norm failed")

    checked = 0
    if exhaustive_intersections:
        selected = ((i, k) for i in range(len(paths))
                    for k in range(i, len(paths)))
    else:
        rng = random.Random(378_2026 + j)
        selected = [(rng.randrange(len(paths)), rng.randrange(len(paths)))
                    for _ in range(2000)]
    for i, k in selected:
        homogeneous = intersection(paths[i], paths[k], 0)
        for delta in range(r):
            require(intersection(paths[i], paths[k], delta) <= homogeneous,
                    "common-origin intersection bound failed")
            checked += 1
    return {
        "r": r, "flags": expected, "path_pairs": path_size,
        "average_squared_norm": str(norm_squared),
        "intersection_cases": checked,
        "intersection_scope": "exhaustive" if exhaustive_intersections
                              else "2000 seeded flag pairs, all relative leaves",
    }


def check_exact_streaming():
    """Compare direct and streamed contractions of random tensors modulo 8."""
    r = 4
    edges = [(a, b) for a in range(r) for b in range(r) if a != b]
    incident = {g: [e for e in edges if g in e] for g in range(r)}
    rng = random.Random(47_165_982)
    rows = []
    for fixture in range(5):
        sizes = {e: (1 if fixture and rng.randrange(5) == 0 else 2)
                 for e in edges}
        factors = {g: {key: rng.randrange(8)
                       for key in product(*(range(sizes[e]) for e in incident[g]))}
                   for g in range(r)}

        def factor(g, assignment):
            return factors[g][tuple(assignment[e] for e in incident[g])]

        brute = 0
        for values in product(*(range(sizes[e]) for e in edges)):
            assignment = dict(zip(edges, values))
            term = 1
            for g in range(r):
                term = term * factor(g, assignment) % 8
            brute = (brute + term) % 8

        for flag in flags(2):
            calls = Counter()
            assignment = {}

            def stream(group, depth):
                if len(group) == 1:
                    g = next(iter(group))
                    calls[g] += 1
                    return factor(g, assignment)
                representative = min(group)
                left = {representative ^ v for v in elements(flag[depth+1])}
                right = group - left
                require(left and right and left | right == group,
                        "separator does not partition its current group")
                cut = [(a, b) for a, b in edges
                       if (a in left and b in right) or
                          (b in left and a in right)]
                total = 0
                for values in product(*(range(sizes[e]) for e in cut)):
                    assignment.update(zip(cut, values))
                    total = (total + stream(left, depth+1)*stream(right, depth+1)) % 8
                for e in cut:
                    assignment.pop(e)
                return total

            result = stream(set(range(r)), 0)
            require(result == brute, "streamed sum differs from direct contraction")
            zero_path = path_masks(flag)
            for g in range(r):
                expected_calls = 1
                for d, mask in enumerate(zero_path, 1):
                    for a in elements(translate(mask, g)):
                        expected_calls *= sizes[(a, a ^ d)]
                require(calls[g] == expected_calls, "paid leaf-call count failed")
            rows.append({"fixture": fixture, "flag": list(flag),
                         "residue_mod_8": result, "paid_leaf_calls": sum(calls.values())})
    return rows


def check_adaptive_selection():
    """Exact integer tests, including the equality profile for balanced trees."""
    rng = random.Random(2026_47_46)
    rows = []
    for j in (2,3,4):
        r = 1 << j
        family = [path_masks(f) for f in flags(j)]
        pairs = [(a,b) for a in range(r) for b in range(r) if a != b]
        profiles = [
            ("uniform", {(a,b): 1 for a,b in pairs}),
            ("sharp_star", {(a,b): 3 if a == 0 or b == 0 else 2 for a,b in pairs}),
            ("seeded_nonuniform", {(a,b): rng.randrange(17) for a,b in pairs}),
        ]
        for name, h in profiles:
            costs = []
            for f in family:
                leaf_costs = [sum(h[(a,a^d)]
                                 for d,mask in enumerate(f,1)
                                 for a in elements(translate(mask,x)))
                              for x in range(r)]
                costs.append(max(leaf_costs))
            chosen = min(costs)
            norm = sum(value*value for value in h.values())
            right = Fraction((r-1)*(4*r+10),9)*norm
            require(chosen*chosen <= right, "adaptive integer-profile bound failed")
            if name == "sharp_star":
                require(chosen*chosen == right, "extremal star profile is not sharp")
            rows.append({"r":r, "profile":name, "selected_maximum_path_cost":chosen,
                         "squared_norm_bound":str(right), "equality":chosen*chosen==right})
    return rows


def log_interval(x, n=64):
    """Rational enclosure from log(x)=2*atanh((x-1)/(x+1))."""
    require(x > 1, "log enclosure requires x>1")
    t = (x-1)/(x+1)
    lower = sum((2*t**(2*k+1)/Fraction(2*k+1) for k in range(n)), Fraction(0))
    tail = 2*t**(2*n+1)/(Fraction(2*n+1)*(1-t*t))
    return lower, lower+tail


def atan_interval(x, n=40):
    """Alternating-series rational enclosure, for 0<x<1."""
    require(0 < x < 1, "arctangent enclosure requires 0<x<1")
    partial = sum(((-1)**k*x**(2*k+1)/Fraction(2*k+1) for k in range(n)), Fraction(0))
    next_term = (-1)**n*x**(2*n+1)/Fraction(2*n+1)
    return min(partial,partial+next_term), max(partial,partial+next_term)


def sqrt_interval(x, decimal_places=40):
    """Rational square-root enclosure verified by integer squaring."""
    require(x >= 0, "square-root enclosure requires nonnegative input")
    scale = 10**decimal_places
    integer = math.isqrt((x.numerator*scale*scale)//x.denominator)
    lower, upper = Fraction(integer,scale), Fraction(integer+1,scale)
    require(lower*lower <= x < upper*upper, "square-root enclosure failed")
    return lower, upper


def coefficient_certificate():
    """Certify C_flag < 46.19 and strict improvement with rational arithmetic.

    The log and arctangent series match the exact interval method in the
    accompanying cached verifier. Every subsequent operation uses positive
    rational interval endpoints; floating point is used only for summaries.
    """
    def scalar(x):
        return Fraction(x), Fraction(x)

    def add(a,b):
        return a[0]+b[0], a[1]+b[1]

    def mul(a,b):
        require(a[0] >= 0 and b[0] >= 0, "positive interval multiplication")
        return a[0]*b[0], a[1]*b[1]

    def div(a,b):
        require(a[0] >= 0 and b[0] > 0, "positive interval division")
        return a[0]/b[1], a[1]/b[0]

    a,b = atan_interval(Fraction(1,5))
    c,d = atan_interval(Fraction(1,239))
    pi_interval = 16*a-4*d, 16*b-4*c  # Machin's identity.
    ln2_interval = log_interval(Fraction(2))
    multiplier = div(mul(pi_interval,sqrt_interval(Fraction(2))),ln2_interval)

    def beta(r):
        return sqrt_interval(Fraction((r-1)*(4*r+10),9*r*r))

    root = mul(scalar(Fraction(9,8)),mul(sqrt_interval(Fraction(80)),beta(16)))
    middle = mul(scalar(Fraction(1,64)),mul(sqrt_interval(Fraction(120)),beta(8)))
    q = Fraction(63,100)
    q_root = sqrt_interval(q)
    inverse = div(scalar(Fraction(1,2)),q_root)
    geometric = 1-inverse[1], 1-inverse[0]
    require(geometric[0] > 0, "tail geometric series does not converge")
    denominator = mul(scalar(256),mul(sqrt_interval(1-q),geometric))
    tail = div(mul(sqrt_interval(Fraction(60)),beta(4)),denominator)
    lower,upper = mul(multiplier,add(add(root,middle),tail))
    require(upper < Fraction(4619,100), "exact safe eventual coefficient failed")

    old_factor = div(mul(scalar(Fraction(5,2)),mul(pi_interval,sqrt_interval(Fraction(17)))),
                     ln2_interval)
    old_extra = add(scalar(1),div(scalar(Fraction(1,3)),sqrt_interval(Fraction(3))))
    old_lower,old_upper = mul(old_factor,old_extra)
    require(upper < old_lower, "exact strict improvement over incumbent failed")

    def decimal_enclosure(lo,hi,places=12):
        scale = 10**places
        lo_integer = (lo.numerator*scale)//lo.denominator
        hi_integer = -((-hi.numerator*scale)//hi.denominator)
        wide_lo,wide_hi = Fraction(lo_integer,scale), Fraction(hi_integer,scale)
        require(wide_lo <= lo <= hi <= wide_hi, "decimal enclosure rounding failed")
        return [f"{lo_integer}/{scale}",f"{hi_integer}/{scale}"]

    return {"certified_interval":decimal_enclosure(lower,upper),
            "incumbent_certified_interval":decimal_enclosure(old_lower,old_upper),
            "safe_eventual":"4619/100",
            "strict_improvement_certified":True,
            "arithmetic":"Rational intervals, Machin arctangent identity, atanh log series, integer square roots."}


def check_schedule():
    q = Fraction(63,100)
    require(Fraction(1,80)*2 + Fraction(1,120) == Fraction(1,30), "prefix taper sum")
    require(Fraction(37,6000)/(1-q) == Fraction(1,60), "geometric tail taper sum")
    require(Fraction(1,30)+Fraction(1,60) == Fraction(1,20), "total taper sum")
    require(Fraction(1,80)*8 + Fraction(9,10) == 1, "root symmetric degree gate")
    require(Fraction(1,40)*4 + Fraction(9,10) == 1, "depth-one degree gate")
    require(Fraction(1,30)*3 + Fraction(9,10) == 1, "depth-two degree gate")
    require(Fraction(1,20)*2 + Fraction(9,10) == 1, "tail degree gate")
    require(Fraction(9,40) < 1 and Fraction(7,30) < 1 and Fraction(1,4) < 1,
            "fresh-side or packet-rounding gate")
    require(q > Fraction(11,20), "least taper must grow at the stopping depth")
    cases = []
    for lam in [10**36, 10**48, 10**60]:
        g = math.isqrt(lam)
        if g*g < lam:
            g += 1
        inward = lam-g
        buffer = 6*lam.bit_length()  # Conservative integer rounding of 6log2(lambda).
        maxdepth = 0
        numerator = denominator = 1
        while numerator < lam*denominator:
            numerator *= 20
            denominator *= 11
            maxdepth += 1
        maxdepth += 2
        ranges = [inward//80, inward//80, inward//120]
        ranges += [(37*inward*63**(d-3))//(6000*100**(d-3))
                   for d in range(3,maxdepth+1)]
        require(min(ranges) > 0, "finite schedule has a zero taper")
        accumulated = 0
        margins = []
        for d, taper in enumerate(ranges):
            accumulated += taper + buffer
            multiplier = 8 if d == 0 else 4 if d == 1 else 3 if d == 2 else 2
            margin = lam - (multiplier*accumulated + 9*lam//10)
            require(margin > 100*lam.bit_length(), "finite degree gate lacks logarithmic slack")
            fresh_multiplier = 9 if d <= 1 else 7 if d == 2 else 5
            require(3*fresh_multiplier*accumulated < lam, "finite fresh-side gate failed")
            margins.append(margin)
        cases.append({"lambda": str(lam), "checked_depth": maxdepth,
                      "smallest_taper": str(min(ranges)),
                      "smallest_degree_gate_margin_bits": str(min(margins))})

    beta = lambda r: math.sqrt((r-1)*(4*r+10)/9)/r
    q_float = float(q)
    coefficient = math.pi*math.sqrt(2)/math.log(2)*(
        9*math.sqrt(80)/8*beta(16) + math.sqrt(120)/64*beta(8)
        + math.sqrt(60)*beta(4)/(256*math.sqrt(1-q_float)*(1-.5/math.sqrt(q_float))))
    old = 5*math.pi*math.sqrt(17)/(2*math.log(2))*(1+1/(3*math.sqrt(3)))
    require(coefficient < 46.19 < old, "approximate coefficient sanity check failed")
    return {"coefficient": coefficient, "incumbent_polynomial_space": old,
            "relative_coefficient_reduction": 1-coefficient/old,
            "alphabet_schedule": [16,16,8,"4 thereafter"],
            "tail_taper_ratio": str(q),
            "finite_integer_gate_checks": cases,
            "exact_coefficient_certificate":coefficient_certificate(),
            "scope": "Exact identities and finite checks; asymptotic proof remains in report."}


def main():
    started = time.monotonic()
    report = {
        "status": "all_checks_passed",
        "flags": [check_flags(j, j <= 4) for j in (2,3,4,5)],
        "adaptive_integer_selection": check_adaptive_selection(),
        "exact_streaming_over_zero_divisor_ring": check_exact_streaming(),
        "schedule": check_schedule(),
        "limitations": ["No end-to-end SAT implementation or benchmark.",
                        "No re-verification of imported deformation, recovery or SAT reductions.",
                        "Displayed coefficient approximations use binary floating point; safe bound and strict improvement also have an exact rational certificate."],
    }
    report["elapsed_seconds"] = time.monotonic()-started
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
