#!/usr/bin/env python3
"""Verify two lower bounds by exact rational subdivision of three scalar intervals."""
from fractions import Fraction as F
from math import isqrt

b, w = F(43892, 100000), F(25607, 100000)
scale = 10**12


def sqrt_lower(x):
    return F(isqrt((scale**2 * x.numerator) // x.denominator), scale)


def exclusion(box, r, A0):
    (d, D), (h, H), (f, Fmax) = box
    if d*h > 2*A0:
        return 'area'
    H = min(H, 2*A0/d)
    D = min(D, 2*A0/h)
    # The sum of the two reflected paths decreases as the smaller height
    # fraction increases to 1/2. Substitute the largest fraction in both terms.
    p = (sqrt_lower(d*d + 4*(h*Fmax)**2) +
         sqrt_lower(d*d + 4*(h*(1-Fmax))**2))
    if r*r * ((p/2)**2 + (d*h)**2) > A0*A0:
        return 'surface'
    # Bound the horizontal offset of each farthest point using its confocal
    # perimeter ellipse. Reject contradictory upper bounds on the two path lengths.
    def sqrt_upper(value):
        return sqrt_lower(value) + F(1, scale)
    pmax = 2 * sqrt_upper((A0/r)**2 - (d*h)**2)
    low_u, low_b = h*f, h*(1-Fmax)
    def offset(low_height, other_height):
        length = pmax - sqrt_lower(d*d + 4*other_height**2)
        if length <= 0 or length*length < d*d+4*low_height**2:
            return None
        if low_height == 0:
            return D/2
        ell = 1-4*low_height**2/(length*length-d*d)
        return min(D/2, length*sqrt_upper(ell)/2)
    upper_x, upper_y = offset(low_u,low_b), offset(low_b,low_u)
    if upper_x is None or upper_y is None:
        return 'surface'
    ratio = Fmax/(1-Fmax)
    extra = min(D*ratio, max(0, -d*(1-ratio)/2 + upper_x + ratio*upper_y))
    total = D + extra
    slack = 2*A0 - d*w + (H-w)*extra
    if w*w*(total*total + 4*low_u**2) > (w*total+slack)**2:
        return 'width'
    return None


def certify(r, bound):
    A0 = 3 * bound
    original = ((b, 2*A0/w), (w, 2*A0/b), (F(0), F(1, 2)))
    todo = [original]
    counts = dict(area=0, surface=0, width=0)
    splits = 0
    while todo:
        box = todo.pop()
        result = exclusion(box, r, A0)
        if result:
            counts[result] += 1
            continue
        widths = [hi-lo for lo, hi in box]
        # All three coordinates are dimensionless here; these weights reflect
        # their different numerical scales. They only pick a bisection order.
        k = max(range(3), key=lambda j: widths[j] * (1, 1, F(1, 4))[j])
        lo, hi = box[k]
        mid = (lo+hi)/2
        if hi-lo < F(1, 10**12):
            raise ArithmeticError('unresolved interval')
        for pair in [(lo, mid), (mid, hi)]:
            todo.append(box[:k] + (pair,) + box[k+1:])
        splits += 1
    print('bisections:', splits)
    print('excluded leaves:', counts)
    print('proved V >', bound, '=', float(bound))


if __name__ == '__main__':
    certify(F(1000, 9577), F(".018975"))
    certify(F(".1043499"), F(".01897"))
