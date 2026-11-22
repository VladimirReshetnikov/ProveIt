"""Replay a dyadic subdivision proof. Uses geometry.py, independent of certify.py.

Each word has a preorder tree. '/' splits the longest interval (earliest
on a tie), 'm' uses support directions at the cell midpoint, and 'w' uses
the published path parameters clamped to the cell. Every leaf proves its
whole cell exceeds the published lower bound. No numerical optimizer runs.
"""
import argparse
import csv
import json
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations, product
from math import isqrt
from pathlib import Path

from geometry import POINTS, SCALE, gate_box, point_box


def require(condition, message):
    if not condition:
        raise ValueError(message)


def normhi(x, y):
    square = x*x + y*y
    n = isqrt(square)
    return n if n*n == square else n+1


def center(box):
    (xmin,xmax),(ymin,ymax) = box
    require(xmin<=xmax and ymin<=ymax, 'empty coordinate box')
    x,y = (xmin+xmax)//2,(ymin+ymax)//2
    return (x,y,normhi(max(x-xmin,xmax-x),max(y-ymin,ymax-y)))


@lru_cache(maxsize=None)
def boundary(g, t):
    return center(gate_box(g,t))


def int_value(s):
    result = F(s)*SCALE
    require(result.denominator == 1, 'decimal incompatible with SCALE')
    return result.numerator


def gate_words(p,q):
    ychange = POINTS[p][2] != POINTS[q][2]
    zchange = POINTS[p][3] != POINTS[q][3]
    if ychange and zchange:
        return {a+b for a,b in product('BL','AR')} | {b+a for a,b in product('BL','AR')}
    return set('BL' if ychange else 'AR') if ychange or zchange else {'direct'}


def witness(st, en, gates, ts):
    return [st, *(boundary(g,t) for g,t in zip(gates,ts)), en]


def upper(stops):
    return sum(normhi(a[0]-b[0],a[1]-b[1]) + a[2] + b[2]
               for a,b in zip(stops,stops[1:]))


def directions(stops):
    vectors = []
    for a,b in zip(stops,stops[1:]):
        x,y = b[0]-a[0],b[1]-a[1]
        d = normhi(x,y)
        v = (0,0) if d == 0 else tuple((1 if z>=0 else -1)*(abs(z)*SCALE//d) for z in (x,y))
        require(v[0]**2+v[1]**2 <= SCALE**2, 'invalid support direction')
        vectors.append(v)
    return [(0,0), *vectors, (0,0)]


def leaf(st, en, gates, spans, ts, threshold):
    v = directions(witness(st,en,gates,ts))
    acc = 0
    nodes = [(st,st,st[2])]
    for g,(l,r) in zip(gates,spans):
        a,b = boundary(g,l), boundary(g,r)
        defect = F(5,8)*SCALE*(r-l)**2 if g in 'AB' else F(0)
        radius = max(a[2],b[2]) - ((-defect.numerator)//defect.denominator)
        nodes.append((a,b,radius))
    nodes.append((en,en,en[2]))
    for i,(a,b,e) in enumerate(nodes):
        x,y = v[i][0]-v[i+1][0],v[i][1]-v[i+1][1]
        acc += min(x*a[0]+y*a[1],x*b[0]+y*b[1]) - e*normhi(x,y)
    return acc >= SCALE*threshold


def inspect_word(st, en, word, threshold, guess, tree, contact=None):
    """With tree=None create a proof; otherwise validate exactly the supplied tree."""
    gates = '' if word == 'direct' else word
    cursor = 0
    built = []
    def visit(spans, level):
        nonlocal cursor
        require(level < 120, 'subdivision depth exceeds the checker limit')
        mid = tuple((a+b)/2 for a,b in spans)
        choices = {'m':mid}
        if guess is not None:
            choices['w'] = tuple(min(b,max(a,t)) for (a,b),t in zip(spans,guess))
        inside = contact is not None and all(c <= l and r <= d
                                             for (l,r),(c,d) in zip(spans,contact))
        if tree is None:
            marker = 'i' if inside else next((k for k,t in choices.items() if leaf(st,en,gates,spans,t,threshold)), '/')
            built.append(marker)
        else:
            require(cursor < len(tree), 'premature end of tree')
            marker = tree[cursor]
            cursor += 1
            if marker == 'i':
                require(inside, 'cell outside claimed contact rectangle')
            elif marker != '/':
                require(marker in choices, 'invalid leaf tag')
                require(leaf(st,en,gates,spans,choices[marker],threshold), 'leaf lower bound failed')
        if marker == '/':
            require(len(spans)>0, 'cannot split a direct path')
            i = max(range(len(spans)), key=lambda j: spans[j][1]-spans[j][0])
            a,b = spans[i]
            for half in ((a,mid[i]),(mid[i],b)):
                visit(spans[:i]+(half,)+spans[i+1:], level+1)
    visit(((F(0),F(1)),)*len(gates), 0)
    require(tree is None or cursor == len(tree), 'trailing tree data')
    return ''.join(built)


def main():
    base = Path(__file__).resolve().parents[1]/'data'
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--csv',type=Path,default=base/'distances.csv')
    ap.add_argument('--trees',type=Path,default=base/'trees.json')
    ap.add_argument('--build',action='store_true',help='regenerate the subtree proofs')
    args = ap.parse_args()
    trees = {} if args.build else json.loads(args.trees.read_text())
    seen = set()
    # This additional tree encloses every minimizing pair of contact parameters
    # for the highlighted path through the interiors of both curved creases.
    contact_pair = ('P4','P10')
    contact_rect = ((F('0.7365'),F('0.7366')),(F('0.8600'),F('0.8601')))
    contact_key = 'P4-P10.contact'
    with args.csv.open(newline='') as f:
        for row in csv.DictReader(f):
            p,q = row['from'],row['to']
            require(p in POINTS and q in POINTS and (p,q) not in seen, 'invalid pair')
            seen.add((p,q))
            key = p+'-'+q
            words = gate_words(p,q)
            st,en = center(point_box(p)),center(point_box(q))
            win = row['upper_route']
            require(win in words, 'invalid upper-bound route')
            gates = '' if win=='direct' else win
            guess = tuple(map(F,row['upper_gate_parameters'].split()))
            require(len(guess)==len(gates) and all(0<=t<=1 for t in guess), 'invalid witness')
            hi,lo = int_value(row['upper']),int_value(row['lower'])
            require(upper(witness(st,en,gates,guess))<=hi and 0<=lo<=hi, 'upper bound failed')
            alternate = int_value(row['other_routes_lower']) if len(words)>1 else None
            if alternate is not None:
                gap = int_value(row['route_gap_lower'])
                require(alternate > hi and 0 < gap <= alternate-hi, 'invalid route separation')
            if args.build:
                trees[key] = {}
            else:
                require(set(trees[key])==words, 'incomplete set of gate words')
            for word in sorted(words):
                threshold = lo if word==win else alternate
                own_guess = guess if word==win else None
                tree = None if args.build else trees[key][word]
                trace = inspect_word(st,en,word,threshold,own_guess,tree)
                if args.build:
                    trees[key][word] = trace
            if (p,q)==contact_pair:
                require(win=='AB', 'unexpected highlighted path')
                subtree = None if args.build else trees[contact_key]['AB']
                trace = inspect_word(st,en,'AB',hi+1,guess,subtree,contact_rect)
                if args.build:
                    trees[contact_key] = {'AB':trace}
    require(seen==set(combinations(POINTS,2)), 'incomplete set of point pairs')
    require(set(trees)==({p+'-'+q for p,q in seen} | {contact_key}), 'unexpected tree keys')
    if args.build:
        args.trees.write_text(json.dumps(trees,indent=1,sort_keys=True)+'\n')
    nwords = sum(len(s) for key,s in trees.items() if key!=contact_key)
    nleaves = sum(s.count('m')+s.count('w')+s.count('i') for group in trees.values() for s in group.values())
    print(f'{len(seen)} pairs, {nwords} gate words, {nleaves} leaf bounds/containments verified.')


if __name__ == '__main__':
    main()
