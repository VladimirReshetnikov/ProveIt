"""Independent double-precision comparison for every allowable crossing order.

Requires SciPy. Accepts --output PATH and locates the exact point specifications
in the companion geometry.py. Candidate lengths are numerical diagnostics.
"""
from __future__ import annotations

import argparse
import csv
from functools import lru_cache
from itertools import combinations, product
from math import asin, atan2, hypot, log, pi, sqrt, tan
from pathlib import Path
import sys

from scipy.optimize import minimize, minimize_scalar

here = Path(__file__).resolve().parent
for directory in (here, here.parent / 'code', here.parent / 'bundle' / 'code'):
    if (directory / 'geometry.py').is_file():
        sys.path.insert(0, str(directory))
        break
from geometry import POINTS

R3 = sqrt(3)
angle = 2*pi/3
W = 2*R3*pi/9
H = R3 + R3*(6+log(4))/9


def ruling(h):
    # Integrate the tangent angles of the first unit circle in its flat chart.
    g = min(1., max(0., h/R3))
    w = sqrt((1-g)*(1+g))
    d = 1+3*g*g
    a = (2*R3/9*(asin(g) + atan2(2*g,w) + 6*g*w/d),
         R3/9*(log(d)+8*(1-1/d)))
    e = (-2*g*(1+g*g)*w/d, (1+g*g+2*g**4)/d)
    tangent = (w**3/d, g*(3+g*g)/d)
    return a,e,tangent


def fixed(label):
    h,s,*_ = POINTS[label]
    a,e,_ = ruling(float(h))
    return tuple(x+R3*float(s)*y for x,y in zip(a,e))


@lru_cache(maxsize=65536)
def gate(code, f):
    if code == 'L': return (0., R3*f),(0.,R3)
    if code == 'R': return (W, H-R3+R3*f),(0.,R3)
    a,_,v = ruling(tan(pi*f/3))
    if code == 'A': return a,(v[0]*angle,v[1]*angle)
    return (W-a[0], H-a[1]),(-v[0]*angle,-v[1]*angle)


def words(a,b):
    dy,dz = (i!=j for i,j in zip(POINTS[a][2:],POINTS[b][2:]))
    if dy and dz:
        return [j for p in product('BL','AR') for j in (p,p[::-1])]
    return [(l,) for l in 'BL'] if dy else [(l,) for l in 'AR'] if dz else [()]


def objective(p,q,word,parameters):
    gates = [gate(k,float(t)) for k,t in zip(word,parameters)]
    pts = [p] + [a for a,_ in gates] + [q]
    value, dirs = 0.,[]
    for a,b in zip(pts,pts[1:]):
        x,y = b[0]-a[0],b[1]-a[1]
        d = hypot(x,y)
        value += d
        dirs.append((x/d,y/d) if d else (0.,0.))
    gradient = [sum((x-y)*z for x,y,z in zip(e1,e2,v))
                for e1,e2,(_,v) in zip(dirs,dirs[1:],gates)]
    return value,gradient


def minimize_route(a,b,word):
    p,q = fixed(a), fixed(b)
    f = lambda z: objective(p,q,word,z)
    if not word:
        return f(())[0],()
    candidates = []
    def trial(z): candidates.append((f(z)[0],tuple(z)))
    # 1D search in every edge interval, including each boundary of the square.
    for variable in range(len(word)):
        for side in ((0.,1.) if len(word)==2 else (0.,)):
            def params(t):
                v = [side]*len(word)
                v[variable] = t
                return v
            for i in range(8):
                left,right = i/8,(i+1)/8
                trial(params(left))
                val = minimize_scalar(lambda t:f(params(t))[0], bounds=(left,right),
                                      method='bounded',options={'xatol':8e-15})
                trial(params(val.x))
            trial(params(1.))
    if len(word)==2:
        for start in product((.04,.27,.5,.73,.96),repeat=2):
            val = minimize(f,start,jac=True,method='L-BFGS-B',bounds=[(0.,1.)]*2,
                           options={'ftol':1e-15,'gtol':1e-12,'maxiter':250})
            trial(val.x)
    return min(candidates)


def main():
    cmd = argparse.ArgumentParser(description=__doc__)
    cmd.add_argument('--output',type=Path,default=Path('route_comparison.csv'))
    cmd.add_argument('--certificates',type=Path,help='compare all minimizing words against a certificate CSV')
    args = cmd.parse_args()
    with args.output.open('w',newline='') as output:
        writer = csv.writer(output,lineterminator='\n')
        writer.writerow(['from','to','rank','word','length_float','gate_1_fraction','gate_2_fraction'])
        for a,b in combinations(POINTS,2):
            results = [(minimize_route(a,b,w),w) for w in words(a,b)]
            for rank,((v,ts),w) in enumerate(sorted(results),1):
                writer.writerow([a,b,rank,''.join(w) or 'direct',f'{v:.15f}',
                                 *[f'{t:.10f}' for t in ts], *['']*(2-len(ts))])
            output.flush()
    if args.certificates:
        with args.output.open(newline='') as source:
            winners = {(r['from'],r['to']):r for r in csv.DictReader(source) if r['rank']=='1'}
        with args.certificates.open(newline='') as source:
            bounds = {(r['from'],r['to']):r for r in csv.DictReader(source)}
        assert winners.keys()==bounds.keys(), 'different pair sets'
        largest_delta=0.
        for key, row in winners.items():
            bound=bounds[key]
            assert row['word']==bound['upper_route'], key
            lo,hi=float(bound['lower']),float(bound['upper'])
            value=float(row['length_float'])
            assert lo-5e-14<=value<=hi+5e-14, (key,lo,value,hi)
            largest_delta=max(largest_delta,abs(value-(lo+hi)/2))
        print(f'{len(winners)} matching words and enclosures; maximum displacement '
              f'from an interval midpoint {largest_delta:.3g}.')


if __name__=='__main__':
    main()
