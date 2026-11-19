"""Independent high-precision evaluator for all 45 certified winning words.

Prerequisites: run verify.py, straight_routes.py and verify_roots.py on the
same distances.csv. They establish route optimality, finite-side feasibility,
and the I/32 Hessian bound on the stated contact rectangles. This program
uses its own dyadic interval arithmetic and an alternative chart evaluation.
It needs only the Python standard library. contacts.json is untrusted input.
"""
import argparse
import csv
import json
from fractions import Fraction as Q
from functools import lru_cache
from itertools import combinations
from math import isqrt
from pathlib import Path

from geometry import POINTS

BASE = 1 << 272


def require(value, message):
    if not value:
        raise ValueError(message)


def ceil(n, d):
    return -(-n // d)


class Interval:
    """Closed interval [lo/BASE,hi/BASE] with outward rounding."""
    __slots__ = ('lo', 'hi')

    def __init__(self, lo, hi):
        require(lo <= hi, 'reversed bounds')
        self.lo, self.hi = lo, hi

    def __neg__(self):
        return Interval(-self.hi, -self.lo)

    def __add__(self, other):
        other = interval(other)
        return Interval(self.lo+other.lo, self.hi+other.hi)

    __radd__ = __add__

    def __sub__(self, other):
        return self + (-interval(other))

    def __rsub__(self, other):
        return interval(other) + (-self)

    def __mul__(self, other):
        other = interval(other)
        ab = [x*y for x in (self.lo,self.hi) for y in (other.lo,other.hi)]
        return Interval(min(ab)//BASE, ceil(max(ab),BASE))

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = interval(other)
        require(other.lo > 0, 'nonpositive denominator')
        return self * Interval(BASE**2//other.hi, ceil(BASE**2,other.lo))

    def __rtruediv__(self, other):
        return interval(other)/self

    def square(self):
        n = 0 if self.lo <= 0 <= self.hi else min(self.lo**2,self.hi**2)
        return Interval(n//BASE, ceil(max(self.lo**2,self.hi**2),BASE))

    def sqrt(self):
        require(self.lo >= 0, 'unproved radicand')
        return Interval(isqrt(self.lo*BASE), isqrt(self.hi*BASE)+1)

    def error(self, units):
        return Interval(self.lo-units,self.hi+units)


def interval(q):
    if isinstance(q, Interval):
        return q
    q = Q(q)
    n = q.numerator*BASE
    d = q.denominator
    return Interval(n//d,ceil(n,d))


ZERO, ONE, R3 = interval(0), interval(1), interval(3).sqrt()


def atan_small(x):
    require(0 <= x.lo and 2*x.hi <= BASE, 'atan series domain')
    # After 92 terms, the alternating tail is at most x^185/185.
    s, power, x2 = ZERO, x, x.square()
    for k in range(92):
        s += power/(2*k+1) if k%2==0 else -power/(2*k+1)
        power *= x2
    return s.error(ceil(power.hi,185))


PI = 16*atan_small(interval(Q(1,5))) - 4*atan_small(interval(Q(1,239)))
T = 2*PI/3
W = 2*R3*PI/9


def atan(x):
    require(x.lo >= 0,'negative angle argument')
    complement = x.lo >= BASE
    if complement:
        x = ONE/x
    # Two half-angle reductions give a fast alternating series.
    for _ in range(2):
        x = x/(1+(1+x.square()).sqrt())
    value = 4*atan_small(x)
    return PI/2-value if complement else value


def log_positive(x):
    y = (x-1)/(x+1)
    require(0 <= y.lo and 10*y.hi <= 7*BASE, 'log series domain')
    s, power, y2 = ZERO, y, y.square()
    for k in range(182):
        s += power/(2*k+1)
        power *= y2
    tail = 2*power/(365*(1-y2))
    return 2*s + Interval(0,tail.hi)


K = R3*(6+log_positive(interval(4)))/9
H = K+R3


def tan_small(x):
    # Sine and cosine alternating sums; the first omitted terms dominate.
    require(0 <= x.lo and 3*x.hi <= 4*BASE, 'angle outside range')
    sine, cosine = ZERO, ZERO
    si, co = x, ONE
    x2 = x.square()
    for k in range(53):
        sine += si if k%2==0 else -si
        cosine += co if k%2==0 else -co
        si = si*x2/((2*k+2)*(2*k+3))
        co = co*x2/((2*k+1)*(2*k+2))
    return sine.error(si.hi)/cosine.error(co.hi)


def frame(h):
    v = h/R3
    v2 = v.square()
    w = (1-v2).sqrt()
    d = 1+3*v2
    a = (2*R3/9*(atan(v/w)+atan(2*v/w)+6*v*w/d),
         R3/9*(log_positive(d)+8*(1-1/d)))
    ruling = (-2*v*(1+v2)*w/d,(1+v2+2*v2.square())/d)
    tangent = (w*w*w/d,v*(3+v2)/d)
    return a,ruling,tangent


@lru_cache(maxsize=None)
def point(p):
    h,s,*_ = POINTS[p]
    a,e,_ = frame(interval(h))
    return tuple(x+interval(s)*R3*y for x,y in zip(a,e))


def gate(g,f):
    if g in 'LR':
        return ((ZERO,R3*f) if g=='L' else (W,K+R3*f)), (ZERO,R3)
    a,_,v = frame(tan_small(T*interval(f)/2))
    return (a,tuple(T*x for x in v)) if g=='A' else ((W-a[0],H-a[1]),tuple(-T*x for x in v))


def value_gradient(p,q,word,ts):
    gates = [gate(g,f) for g,f in zip(word,ts)]
    stops = [p, *[a for a,_ in gates], q]
    total, units = ZERO, []
    for a,b in zip(stops,stops[1:]):
        dx,dy = (y-x for x,y in zip(a,b))
        length = (dx.square()+dy.square()).sqrt()
        total += length
        units.append((dx/length,dy/length))
    gradient = [sum((l-r)*v for l,r,v in zip(left,right,tangent))
                for left,right,(_,tangent) in zip(units,units[1:],gates)]
    return total,gradient


def reflect_chord(p,q,word):
    x,y = q
    for g in reversed(word):
        require(g in 'LR','invalid reflected word')
        x = -x if g=='L' else 2*W-x
    return ((x-p[0]).square()+(y-p[1]).square()).sqrt()


def fmt(integer, digits):
    sign = '-' if integer < 0 else ''
    n,d = divmod(abs(integer),10**digits)
    return f'{sign}{n}.{d:0{digits}d}'


def outward(x,digits):
    scale = 10**digits
    return fmt(x.lo*scale//BASE,digits),fmt(ceil(x.hi*scale,BASE),digits)


def nearest_endpoints(x,digits):
    scale = 10**digits
    return tuple((2*z*scale+BASE)//(2*BASE) for z in (x.lo,x.hi))


def main():
    data = Path(__file__).resolve().parents[1]/'data'
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=data/'refined_distances.csv')
    args = parser.parse_args()
    contacts = json.loads((data/'contacts.json').read_text())
    seen,used = set(),set()
    max_gradient,max_error = 0,0
    with (data/'distances.csv').open(newline='') as source, args.output.open('w',newline='') as out:
        writer = csv.writer(out,lineterminator='\n')
        writer.writerow(['from','to','word','lower','upper','rounded_40','gradient_norm_upper','contact_radius_upper'])
        for row in csv.DictReader(source):
            a,b = row['from'],row['to']
            key = a+'-'+b
            require((a,b) not in seen,'duplicate pair')
            seen.add((a,b))
            word = row['upper_route']
            p,q = point(a),point(b)
            if any(g in 'AB' for g in word):
                ts = tuple(map(Q,contacts[key]))
                old = tuple(map(Q,row['upper_gate_parameters'].split()))
                require(len(ts)==len(old)==len(word),'wrong number of contacts')
                for t,s in zip(ts,old):
                    j = (4096*s).__floor__()
                    require(Q(j-1,4096)<t<Q(j+2,4096),'guess outside strong-convexity box')
                sample,grad = value_gradient(p,q,word,ts)
                residual2 = sum(x.square() for x in grad)
                residual = residual2.sqrt()
                # F(t*) >= F(t)-|grad F(t)|²/(2*mu), mu=1/32.
                bounds = Interval((sample-16*residual2).lo,sample.hi)
                # Strong monotonicity gives |t-t*| <= |grad F(t)|/mu.
                contact_error = 32*residual
                # A projected-gradient fixed point with this residual bound
                # lies strictly inside every face of the localization box.
                radius_exact = Q(contact_error.hi,BASE)
                for t,s in zip(ts,old):
                    j = (4096*s).__floor__()
                    require(Q(j-1,4096) < t-radius_exact and
                            t+radius_exact < Q(j+2,4096), 'contact ball touches a box face')
                max_gradient = max(max_gradient,residual.hi)
                max_error = max(max_error,contact_error.hi)
                radius = outward(contact_error,40)[1]
                norm = outward(residual,40)[1]
                used.add(key)
            else:
                bounds = reflect_chord(p,q,'' if word=='direct' else word)
                radius,norm = '',''
            old_lo,old_hi = Q(row['lower']),Q(row['upper'])
            require(old_lo < Q(bounds.lo,BASE) <= Q(bounds.hi,BASE) < old_hi,'original bounds failed '+key)
            rounded_lo,rounded_hi = nearest_endpoints(bounds,40)
            require(rounded_lo==rounded_hi,'ambiguous rounding '+key)
            lo,hi = outward(bounds,50)
            writer.writerow([a,b,word,lo,hi,fmt(rounded_lo,40),norm,radius])
    require(seen==set(combinations(POINTS,2)),'incomplete pair list')
    require(used==set(contacts) and len(used)==20,'incorrect contact list')
    print(f'{len(seen)} original enclosures strictly contain the refined intervals; 40-place rounding verified.')
    print('Maximum gradient norm <=',outward(Interval(0,max_gradient),40)[1])
    print('Maximum contact error <=',outward(Interval(0,max_error),40)[1])

if __name__=='__main__':
    main()
