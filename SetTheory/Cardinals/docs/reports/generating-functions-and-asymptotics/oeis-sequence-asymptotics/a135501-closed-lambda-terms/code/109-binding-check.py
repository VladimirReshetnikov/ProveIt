#!/usr/bin/env python3
"""Exact, standard-library validation for report109. No assert statements.

Run python3 check.py (also python3 -O check.py).
To reconstruct snapshots, use --generate. Finite tests are not asymptotic proofs.
"""
import argparse
from collections import Counter
from fractions import Fraction
from functools import cache
from math import comb, factorial, prod
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parent
COUNTS = Counter()
PUBLISHED = {
    1: [0,0,1,2,4,13,42,139,506,1915,7558,31092,132170,580466,2624545,12190623],
    0: [0,1,3,14,82,579,4741,43977,454283,5159441,63782411,851368766,12188927818,186132043831,3017325884473,51712139570022],
}

def require(condition, message, category="consistency"):
    COUNTS[category] += 1
    if not condition:
        raise RuntimeError(message)

def total_and_moment(max_n, s):
    """Independent size recurrence and first derivative in a unary marker."""
    T = [[0]*(max_n-n+1) for n in range(max_n+1)]
    D = [[0]*(max_n-n+1) for n in range(max_n+1)]
    if s == 0:
        T[0] = list(range(max_n+1))
    for n in range(1, max_n+1):
        for m in range(max_n-n+1):
            value = m if n == s else 0
            value += T[n-1][m+1]
            moment = T[n-1][m+1] + D[n-1][m+1]
            for i in range(n):
                j = n-1-i
                value += T[i][m]*T[j][m]
                moment += D[i][m]*T[j][m] + T[i][m]*D[j][m]
            T[n][m], D[n][m] = value, moment
    return [v[0] for v in T], [v[0] for v in D]

@cache
def direct(m, u, b):
    """Bivariate decomposition: last two arguments count unary/binary nodes."""
    if u == 0 and b == 0:
        return m
    value = direct(m+1, u-1, b) if u else 0
    if b:
        value += sum(direct(m,j,a)*direct(m,u-j,b-1-a)
                     for j in range(u+1) for a in range(b))
    return value

@cache
def radical(m, u, b):
    """Coefficient recurrence after solving the zero-unary Catalan equation."""
    if u == 0:
        return comb(2*b,b)//(b+1) * m**(b+1)
    value = 0
    for h in range(b+1):
        inner = radical(m+1,u-1,b-h)
        if b-h:
            inner += sum(radical(m,j,a)*radical(m,u-j,b-h-1-a)
                         for j in range(1,u) for a in range(b-h))
        value += comb(2*h,h)*m**h*inner
    return value

def admissible(n,s):
    for u in range(1,n-s+1):
        if (n-u-s) % (s+1) == 0:
            yield u, (n-u-s)//(s+1)

def total_bounds(n,s):
    lower = upper = 0
    for u,b in admissible(n,s):
        root = comb(2*b,b)//(b+1)*u**(b+1)
        lower += root
        upper += root*comb(u+2*b,u)
    return lower,upper

@cache
def binary_trees(b):
    if b == 0:
        return (None,)
    return tuple((a,c) for i in range(b)
                 for a in binary_trees(i) for c in binary_trees(b-1-i))

def leaf_paths(tree):
    next_id, paths = 0, []
    def visit(t,path):
        nonlocal next_id
        node = next_id
        next_id += 1
        path += (node,)
        if t is None:
            paths.append(path)
        else:
            visit(t[0],path)
            visit(t[1],path)
    visit(tree,())
    return paths,next_id

def compositions(n,k):
    if k == 1:
        yield (n,)
    else:
        for a in range(n+1):
            for tail in compositions(n-a,k-1):
                yield (a,)+tail

def text_table(values):
    return ''.join(f'{n} {value}\n' for n,value in enumerate(values))

def compare_file(path, expected):
    require(path.read_text(encoding='utf-8') == expected,
            f'snapshot mismatch: {path.name}', 'snapshot')

def check_fixtures():
    """Fast mathematical corruption check of published and computed prefixes."""
    for s in (0,1):
        values,_ = total_and_moment(20,s)
        require(values[:16] == PUBLISHED[s], f'published prefix s={s}', 'published_prefix')
        path = ROOT/'data'/f'A{135501 if s else 220894}_computed.txt'
        entries = [line.split() for line in path.read_text().splitlines()]
        require(len(entries)==201, f'table length: {path}', 'fixture')
        for n,value in enumerate(values):
            require(entries[n] == [str(n),str(value)], f'prefix entry s={s}, n={n}', 'fixture')

def run_all():
    outputs = {}
    for s in (0,1):
        A,D = total_and_moment(200,s)
        require(A[:16] == PUBLISHED[s], f'published prefix s={s}', 'published_prefix')
        for n in range(201):
            lo,hi = total_bounds(n,s)
            require(lo <= A[n] <= hi, f'total bounds s={s}, n={n}', 'total_sandwich')
            if n:
                require(A[n-1] <= A[n], f'monotonicity s={s}, n={n}', 'monotonicity')
            require(0 <= D[n] <= n*A[n], f'moment range s={s}, n={n}', 'moment_range')
        for n in range(21):
            terms = [(u,direct(0,u,b)) for u,b in admissible(n,s)]
            require(sum(a for u,a in terms) == A[n], f'refined total s={s}, n={n}', 'refined_total')
            require(sum(u*a for u,a in terms) == D[n], f'refined moment s={s}, n={n}', 'refined_moment')
        outputs[f'A{135501 if s else 220894}_computed.txt'] = text_table(A)
        outputs[f'A{135501 if s else 220894}_unary_moment.txt'] = text_table(D)
    for u in range(1,10):
        for m in range(u+1):
            for k in range(u-m+1):
                for b in range(15):
                    require(direct(m,k,b)==radical(m,k,b),
                            f'direct/radical {m,k,b}', 'radical_recurrence')
        for b in range(31):
            a = direct(0,u,b)
            lower = comb(2*b,b)//(b+1)*u**(b+1)
            require(lower <= a <= 2*u*12**u*(4*u)**b,
                    f'rational majorant {u,b}', 'uniform_majorant')
    heights=[]
    for b in range(5):
        for u in range(1,7):
            counts = [0]*(u+1)
            for tree in binary_trees(b):
                paths,slots = leaf_paths(tree)
                require(slots == 2*b+1, f'slot count b={b}', 'skeleton_slots')
                for alpha in compositions(u,slots):
                    depths = [sum(alpha[i] for i in path) for path in paths]
                    counts[max(depths)] += prod(depths)
            require(sum(counts)==direct(0,u,b), f'height total {b,u}', 'height_total')
            cat=comb(2*b,b)//(b+1)
            for h in range(1,u+1):
                require(counts[h]<=cat*comb(u+2*b,u)*h**(b+1),
                        f'height upper {b,u,h}', 'height_upper')
                if h>=2 and 1<=u-h+1<=b+1:
                    require(counts[h]>=cat*(h-1)**(b+1),
                            f'height lower {b,u,h}', 'height_lower')
            heights.append({'b':b,'u':u,'counts_by_height':counts})
    for u in range(1,76):
        @cache
        def max_denominator_squared(m,k):
            if k == 0:
                return Fraction(1)
            candidates = [max_denominator_squared(m+1,k-1)]
            candidates += [max_denominator_squared(m,j)*max_denominator_squared(m,k-j)
                           for j in range(1,k)]
            return Fraction(u,u-m)*max(candidates)
        bound=Fraction(u**(2*u-1),factorial(u)**2)
        require(max_denominator_squared(0,u)<=bound, f'deficit majorant u={u}', 'deficit_product')
    weighted=[Fraction(0)]
    for u in range(1,101):
        direct_shapes=sum(Fraction(comb(2*q,q),q+1)*comb(u+q-1,2*q)/2**q for q in range(u))
        recursive=(Fraction(1) if u==1 else weighted[u-1])
        recursive += sum(weighted[j]*weighted[u-j]/2 for j in range(1,u))
        require(direct_shapes==recursive, f'shape recurrence u={u}', 'weighted_shapes')
        require(direct_shapes<=Fraction(4**u,2), f'shape radius u={u}', 'shape_radius')
        weighted.append(direct_shapes)
    # This summary counts only mathematical guards, not output-file comparisons.
    result={'status':'PASS','arithmetic':'integer and Fraction only',
            'scope':'Finite consistency tests, not asymptotic proofs or global novelty certification.',
            'published_prefix_length_per_model':16,'computed_terms_n_range':[0,200],
            'complete_remote_bfiles_compared':False,'checks':dict(sorted(COUNTS.items())),
            'total_mathematical_checks':sum(COUNTS.values()),'height_records':heights}
    outputs['check_results.json']=json.dumps(result,indent=2,sort_keys=True)+'\n'
    return outputs,result

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--generate',action='store_true',help='write reconstructed deterministic snapshots')
    parser.add_argument('--fixtures-only',action='store_true',help='fast prefix check, not the complete suite')
    args=parser.parse_args()
    if args.fixtures_only:
        check_fixtures()
        print('PASS: exact prefix fixtures')
        return
    outputs,result=run_all()
    if not args.generate:
        actual = {p.name for p in (ROOT/'data').iterdir()}
        require(actual == set(outputs), f'data inventory mismatch: {sorted(actual ^ set(outputs))}', 'snapshot')
    for name,content in outputs.items():
        path=ROOT/'data'/name
        if args.generate:
            path.write_text(content,encoding='utf-8')
        else:
            compare_file(path,content)
    print(f"PASS: {result['total_mathematical_checks']} exact mathematical checks; snapshots {'generated' if args.generate else 'matched'}")

if __name__=='__main__':
    main()
