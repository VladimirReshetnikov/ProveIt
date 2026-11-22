"""Verify the finite-side intersections for every straight-side reflection formula."""
import csv
from fractions import Fraction
from pathlib import Path
from geometry import I, iv, SCALE, UNIT, W, K, H, ROOT3, point_box, gate_box

def convert(box):
    return [I(a*(UNIT//SCALE),b*(UNIT//SCALE)) for a,b in box]

def quotient(a,b):
    if b.hi < 0:
        return (-a)/(-b)
    assert b.lo > 0
    return a/b

def main():
    count = 0
    filename = Path(__file__).resolve().parents[1]/'data'/'distances.csv'
    for row in csv.DictReader(filename.open()):
        word = row['upper_route']
        if word=='direct':
            word=''
        if any(g not in 'LR' for g in word):
            continue
        p = convert(point_box(row['from']))
        q = convert(point_box(row['to']))
        sign, shift, lines = 1, iv(0), []
        for g in word:
            k = iv(0) if g=='L' else W
            lines.append((sign*k+shift,g))
            shift += 2*sign*k
            sign = -sign
        delta = sign*q[0]+shift-p[0]
        previous = iv(0)
        for x,g in lines:
            lam=quotient(x-p[0],delta)
            assert previous.hi < lam.lo and lam.hi < UNIT
            y = p[1]+lam*(q[1]-p[1])
            a,b = (iv(0),ROOT3) if g=='L' else (K,H)
            assert a.hi<y.lo and y.hi<b.lo
            previous = lam
        dy = q[1]-p[1]
        exact = (delta*delta+dy*dy).sqrt()
        # The published enclosure must intersect this independent one.
        lo, hi = iv(Fraction(row['lower'])), iv(Fraction(row['upper']))
        assert exact.lo<=hi.hi and exact.hi>=lo.lo
        count += 1
    # Explicit competitor through the shared endpoint B(1) for the close P6-P9 pair.
    p, q = (convert(point_box(k)) for k in ('P6','P9'))
    b = convert(gate_box('B', Fraction(1)))
    def distance(x,y):
        dx, dy = (a-c for a,c in zip(x,y))
        return (dx*dx+dy*dy).sqrt()
    feasible = distance(p,b)+distance(b,q)
    assert feasible.hi < iv(Fraction('0.711456882267')).lo
    assert count==25
    print('25 exact reflected-chord formulas verified, including all finite-side intersections.')

if __name__=='__main__':
    main()
