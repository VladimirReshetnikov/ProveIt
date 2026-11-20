"""Rational producer and independent segment-by-segment clearance check."""
from dataclasses import dataclass
from fractions import Fraction as Q
from itertools import combinations
from math import ceil, floor, lcm

# A complex vector is a pair (real coordinates, imaginary coordinates).
@dataclass(frozen=True)
class Form:
    coefficients: tuple
    offset: Q
    forbidden: str     # "integers", "nonpositive", or "zero"

    def value(self, p):
        return self.offset + dot(self.coefficients, p[0]), dot(self.coefficients, p[1])

def dot(a, b):
    return sum((x*y for x,y in zip(a,b, strict=True)), Q(0))

def integer_gap(x):
    return min(x - floor(x), ceil(x) - x)

def distance(form, p):
    real, imag = form.value(p)
    if form.forbidden == "zero":
        gap = abs(real)
    elif form.forbidden == "nonpositive" and real > 0:
        gap = real
    else:
        gap = integer_gap(real)
    return max(gap, abs(imag))

def produce(forms, x, y):
    if len(x) != 2 or len(y) != 2:
        raise ValueError("an endpoint requires real and imaginary coordinate arrays")
    d = len(x[0])
    if any(len(a) != d for a in (*x, *y)):
        raise ValueError("inconsistent endpoint dimensions")
    if not forms:
        radius = Q(1, 4)
        length = max((abs(a - b) for aa, bb in zip(x, y)
                      for a, b in zip(aa, bb)), default=Q(0))
        return (x, y), Q(1), radius, (max(1, ceil(length / radius)),)
    integer_rows = []
    for f in forms:
        if (len(f.coefficients) != d or not any(f.coefficients)
                or f.forbidden not in {"zero","integers","nonpositive"}):
            raise ValueError("invalid form")
        common = lcm(*(c.denominator for c in f.coefficients))
        integer_rows.append([int(c * common) for c in f.coefficients])
    cap = 2 + max(sum(map(abs,row)) for row in integer_rows)
    for t in range(1, cap + 1):
        v = tuple(t**j for j in range(d))
        slopes = [abs(dot(f.coefficients, v)) for f in forms]
        if all(slopes):
            break
    else:
        raise ArithmeticError("no transverse direction within the proved cap")
    amplitude = max([1,*slopes])
    slope_min = min(slopes)

    def shift(p):
        clearances = [distance(f,p) for f in forms]
        if not all(clearances):
            raise ValueError("endpoint belongs to a forbidden family")
        real_gaps = [integer_gap(f.value(p)[0]) for f in forms]
        eta = min([1,*clearances,*(g for g in real_gaps if g)])
        delta = Q(eta,4) / amplitude
        shifted = tuple(a + delta*b for a,b in zip(p[0],v))
        return shifted, min(3*Q(eta,4),delta*slope_min)

    left, m1 = shift(x)
    right, m2 = shift(y)
    nodes = (x,(left,x[1]),(left,v),(right,v),(right,y[1]),y)
    gamma = min(m1,m2,slope_min)
    row_bound = max([1,*(sum(map(abs,f.coefficients)) for f in forms)])
    radius = gamma/(4*row_bound)
    counts = tuple(max(1,ceil(max(abs(a-b) for aa,bb in zip(p,q)
                                   for a,b in zip(aa,bb))/radius))
                   for p,q in zip(nodes,nodes[1:]))
    return nodes,gamma,radius,counts

def segment_min(a,b,n):
    # The maximum of four affine functions is affine between their intersections.
    lines = []
    for start,stop in ((a[0]-n,b[0]-n),(a[1],b[1])):
        lines.extend([(start,stop-start),(-start,start-stop)])
    candidates = [Q(0),Q(1)]
    for (s,u),(t,v) in combinations(lines,2):
        if u != v:
            h = Q(t-s,u-v)
            if 0<h<1:
                candidates.append(h)
    return min(max(s+h*u for s,u in lines) for h in candidates)

def verify(forms, nodes, gamma):
    if not 0 < gamma <= 1:
        return False
    for p,q in zip(nodes,nodes[1:]):
        for f in forms:
            a,b = f.value(p), f.value(q)
            low, high = floor(min(a[0],b[0]))-1, ceil(max(a[0],b[0]))+1
            if f.forbidden == "zero":
                levels = [0]
            else:
                if f.forbidden == "nonpositive":
                    high = min(0,high)
                levels = range(low,high+1)
            if any(segment_min(a,b,n) < gamma for n in levels):
                return False
    return True

def point(real, imag=None):
    return tuple(map(Q,real)), tuple(map(Q,imag or [0]*len(real)))

def form(row, offset=0, family="nonpositive"):
    return Form(tuple(map(Q,row)),Q(offset),family)

def main():
    for p, q in [(point([]), point([])), (point([-8]), point([8], [3]))]:
        nodes, clearance, radius, counts = produce([], p, q)
        length = max((abs(a - b) for aa, bb in zip(p, q)
                      for a, b in zip(aa, bb)), default=Q(0))
        assert nodes == (p, q) and verify([], nodes, clearance)
        assert counts[0] >= 1 and length / counts[0] <= radius
    forms = [form([1]),form([1],Q(-1,4)),form([1],Q(-1,3)),
             form([1],Q(-7,12),"integers")]
    x,y = point(["5/4"]),point(["1/2"])
    nodes,gamma,radius,counts = produce(forms,x,y)
    assert verify(forms,nodes,gamma)
    assert not verify(forms,(x,y),gamma)
    assert (gamma,radius) == (Q(1,48),Q(1,192))
    print("one-dimensional Gauss detour")
    print("centers:", [(str(p[0][0]),str(p[1][0])) for p in nodes])
    print("clearance:",gamma,"subdivision scale:",radius,"interval counts:",counts)
    rows = [form(row) for row in [(0,0,1),(-1,0,1),(0,-1,1),(1,0,0),(0,1,0)]]
    rows.append(form((-1,-1,1),family="integers"))
    samples = [point(["1/4","1/3","5/4"]),point(["1/2","2/3",1]),
               point([-1,0,1], [1,2,4]),point(["1/5","3/4","-5/3"],[0,0,0])]
    for p in samples:
        for q in samples:
            path,g,r,c = produce(rows,p,q)
            assert verify(rows,path,g)
            assert all(v>=1 for v in c)
    try:
        produce(rows,point([1,1,2]),samples[0])
    except ValueError:
        pass
    else:
        raise AssertionError("resonant endpoint admitted")
    print("16 ordered three-dimensional cases verified, resonant endpoint rejected")

if __name__ == "__main__":
    main()
