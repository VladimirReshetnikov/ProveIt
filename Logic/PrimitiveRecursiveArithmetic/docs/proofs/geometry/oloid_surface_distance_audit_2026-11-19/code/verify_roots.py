"""Isolate all 20 nonlinear winning contact tuples and certify strong convexity.

Put this file beside geometry.py and verify.py, with distances.csv and
root_trees.json in ../data.  --build regenerates the localization trees.
All comparisons use outward rational intervals or exact integers.
"""
import argparse
import csv
import json
from fractions import Fraction as Q
from pathlib import Path

import geometry as g
import verify as cert


def hull(a, b):
    return g.I(min(a.lo, b.lo), max(a.hi, b.hi))


def square(x):
    lo = 0 if x.lo <= 0 <= x.hi else min(x.lo*x.lo, x.hi*x.hi)
    hi = max(x.lo*x.lo, x.hi*x.hi)
    return g.I(lo // g.UNIT, g.ceildiv(hi, g.UNIT))


def dot(x, y):
    return x[0]*y[0] + x[1]*y[1]


def cross(x, y):
    return x[0]*y[1] - x[1]*y[0]


def mul(c, p):
    return tuple(c*t for t in p)


def minus(a,b):
    return tuple(x-y for x,y in zip(a,b))


def fixed_point(name):
    return tuple(g.I(g.UNIT*a//g.SCALE, g.ceildiv(g.UNIT*b,g.SCALE))
                 for a,b in g.point_box(name))


def derivatives(gate, interval):
    l,r = interval
    # Each gate coordinate is monotone in its parameter.
    position = tuple(hull(x,y) for x,y in zip(g.gate(gate,l),g.gate(gate,r)))
    zero = (g.iv(0), g.iv(0))
    if gate in 'LR':
        return position, (g.iv(0),g.ROOT3), zero
    # Natural circular arclength is t = ANGLE*f; cosine is decreasing here.
    c = hull(g.cosine(g.ANGLE*g.iv(l)), g.cosine(g.ANGLE*g.iv(r)))
    v2 = (1-c)/(3*(1+c))
    v, w = v2.sqrt(), (1-v2).sqrt()
    d = 1+3*v2
    tau = (w*w*w/d, v*(3+v2)/d)
    kappa = g.ROOT3*w/2
    sign = 1 if gate == 'A' else -1
    return (position, mul(sign*g.ANGLE,tau),
            mul(sign*g.ANGLE*g.ANGLE*kappa,(-tau[1],tau[0])))


def hessian(p,q,word,rectangle):
    n = len(word)
    zero = (g.iv(0),g.iv(0))
    nodes = [(p,zero,zero)]
    nodes.extend(derivatives(a,r) for a,r in zip(word,rectangle))
    nodes.append((q,zero,zero))
    H = [[g.iv(0) for _ in range(n)] for _ in range(n)]
    length_lower = g.iv(4).lo
    for j,(a,b) in enumerate(zip(nodes,nodes[1:])):
        r = minus(b[0],a[0])
        length = (square(r[0])+square(r[1])).sqrt()
        cert.require(length.lo > 0, 'possible collapsed link')
        length_lower = min(length_lower,length.lo)
        cube = length*length*length
        tangents = []
        if j > 0:
            tangents.append((j-1,mul(-1,a[1]),mul(-1,a[2])))
        if j < n:
            tangents.append((j,b[1],b[2]))
        for i,t,acceleration in tangents:
            H[i][i] += square(cross(r,t))/cube + dot(r,acceleration)/length
            for k,u,_ in tangents:
                if k != i:
                    H[i][k] += cross(r,t)*cross(r,u)/cube
    return H,length_lower


def verify_curvature(p,q,word,rect):
    p,q = fixed_point(p),fixed_point(q)
    H, ell = hessian(p,q,word,rect)
    # Sylvester's criterion for H-I/32.
    target = g.iv(Q(1,32))
    a = H[0][0]-target
    cert.require(a.lo>0,'leading minor not positive')
    if len(word) == 2:
        c = H[1][1]-target
        determinant = a*c - square(H[0][1])
        cert.require(determinant.lo>0,'determinant not positive')
    # In the mixed cases unfold the one straight side. This proves strict
    # convexity for the one-variable expression over the entire curved interval,
    # even where the reflected segment meets the infinite straight line outside
    # its recorded contact box.
    if len(word)==2 and any(w in 'LR' for w in word):
        j = next(j for j,w in enumerate(word) if w in 'LR')
        u = g.W if word[j]=='R' else g.iv(0)
        if j==0:
            p = (2*u-p[0],p[1])
        else:
            q = (2*u-q[0],q[1])
        scalar, unfolded_ell = hessian(p,q,word[1-j],(rect[1-j],))
        cert.require((scalar[0][0]-target).lo>0,'scalar Hessian too small')
        ell = min(ell,unfolded_ell)
    return ell


def contact_rectangle(guess):
    boxes=[]
    for t in guess:
        k = (4096*t).__floor__()
        bounds = (Q(k-1,4096),Q(k+2,4096))
        cert.require(0 < bounds[0] < bounds[1] < 1,'noninterior box')
        boxes.append(bounds)
    return tuple(boxes)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    data = Path(__file__).resolve().parents[1]/'data'
    parser.add_argument('--csv', type=Path, default=data/'distances.csv')
    parser.add_argument('--trees',type=Path,default=data/'root_trees.json')
    parser.add_argument('--build',action='store_true')
    args=parser.parse_args()
    trees = {} if args.build else json.loads(args.trees.read_text())
    processed = set()
    total,min_length = 0,g.UNIT*4
    with args.csv.open(newline='') as stream:
        for row in csv.DictReader(stream):
            word = row['upper_route']
            if not any(c in word for c in 'AB'):
                continue
            p,q = row['from'],row['to']
            key = p+'-'+q
            guess = tuple(map(Q,row['upper_gate_parameters'].split()))
            rectangle = contact_rectangle(guess)
            st,en = cert.center(g.point_box(p)),cert.center(g.point_box(q))
            hi = cert.int_value(row['upper'])
            cert.require(cert.upper(cert.witness(st,en,word,guess))<=hi,
                         'infeasible upper bound')
            tree = cert.inspect_word(st,en,word,hi+1,guess,
                                     None if args.build else trees[key],rectangle)
            if args.build:
                trees[key] = tree
            total += sum(trees[key].count(marker) for marker in 'mwi')
            min_length = min(min_length,verify_curvature(p,q,word,rectangle))
            cert.require(key not in processed,'duplicate row')
            processed.add(key)
            print(p,q,word,[int(l*4096) for l,_ in rectangle])
    cert.require(len(processed)==20 and processed==set(trees),'incomplete root set')
    if args.build:
        args.trees.write_text(json.dumps(trees,indent=1,sort_keys=True)+'\n')
    print(f'{len(processed)} isolated contact tuples, {total} localization leaves.')
    print(f'All Hessians exceed I/32; all links exceed {1000*min_length//g.UNIT}/1000.')


if __name__ == '__main__':
    main()
