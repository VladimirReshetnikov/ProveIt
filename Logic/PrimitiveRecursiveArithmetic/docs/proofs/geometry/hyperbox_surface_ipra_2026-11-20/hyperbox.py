"""Exact intrinsic point distances and fixed-vertex farthest points of rectangular boxes.

Only the Python standard library is required. All geometric tests use Fraction.
Face i is encoded by 2*i (lower) and 2*i+1 (upper), with zero-based axes.
"""
import argparse
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations, product
import json


def rational_box(sides):
    a = tuple(map(F, sides))
    if len(a) < 2 or min(a) <= 0:
        raise ValueError("Use at least two strictly positive side lengths.")
    return a


def tags(a, p):
    if len(a) != len(p) or any(not 0 <= x <= b for b, x in zip(a, p)):
        raise ValueError("Point outside box.")
    out = tuple(2*i+b for i in range(len(a)) for b in (0, 1) if p[i] == b*a[i])
    if not out:
        raise ValueError("Point must be on the boundary.")
    return out


def dot(v, w):
    return sum(x*y for x, y in zip(v,w))


def squared(v,w):
    return sum((x-y)**2 for x,y in zip(v,w))


def develop(a, start, end_faces, block):
    """Develop away from the query facet, stopping at the first source facet.

    frame triples (physical axis, orientation, intercept) give each chart slot.
    A gate is the closed box in chart coordinates at a transition.
    """
    n = len(a)
    frame = tuple((i, 1, 0) for i in range(n) if i != start//2)

    def grow(face, frame, used, gates):
        if face in end_faces:
            yield frame, gates
            return
        old_axis, old_side = divmod(face,2)
        for slot,(axis,sign,offset) in enumerate(frame):
            for side in (0,1):
                nxt = 2*axis + side
                if nxt in used or nxt in block:
                    continue
                boundary = offset+sign*side*a[axis]
                gate = []
                for k,(j,s,o) in enumerate(frame):
                    if slot == k:
                        gate.append((boundary,boundary))
                    else:
                        other = o+s*a[j]
                        gate.append((min(o,other),max(o,other)))
                new_sign = sign*(2*side-1)*(1-2*old_side)
                replacement = (old_axis,new_sign,boundary-new_sign*old_side*a[old_axis])
                new_frame = frame[:slot]+(replacement,)+frame[slot+1:]
                yield from grow(nxt,new_frame,used | {nxt},gates+(tuple(gate),))
    return grow(start, frame, {start}, ())


@lru_cache(maxsize=512)
def charts(a, src, start, blocked):
    images = {}
    for frame, gates in develop(a, start, set(tags(a,src)), set(blocked)):
        site = tuple(o+s*src[j] for j,s,o in frame)
        images.setdefault(site, []).append(gates)
    return tuple((site,tuple(paths)) for site,paths in images.items())


def visible(z, site, gates):
    """Interval clipping, including segments that run along a gate."""
    earliest = F(0)
    for gate in gates:
        first, last = earliest, F(1)
        for x,y,(lo,hi) in zip(z,site,gate):
            delta = y-x
            if delta == 0:
                if not lo <= x <= hi:
                    return False
            else:
                u, v = (lo-x)/delta, (hi-x)/delta
                if u > v:
                    u, v = v, u
                first, last = max(first,u), min(last,v)
                if first > last:
                    return False
        earliest = first
    return True


def surface_squared(sides, p, q):
    """Exact squared distance, including arbitrarily many incident endpoint facets."""
    a, p, q = rational_box(sides), tuple(map(F,p)), tuple(map(F,q))
    fp, fq = tags(a,p), tags(a,q)
    if set(fp).intersection(fq):
        return squared(p,q)
    if len(fp) < len(fq):
        p,q,fp,fq = q,p,fq,fp
    best = None
    for face in fq:
        z = q[:face//2] + q[face//2+1:]
        for site, paths in charts(a,p,face,fq):
            value = squared(z,site)
            if (best is None or value < best) and any(visible(z,site,w) for w in paths):
                best = value
    if best is None:
        raise ArithmeticError("No admissible development.")
    return best


def solve_linear(rows):
    """Exact square Gaussian elimination. Return None on rank deficiency."""
    m = len(rows)
    rows = [list(map(F,r)) for r in rows]
    for j in range(m):
        pivot = next((i for i in range(j,m) if rows[i][j]),None)
        if pivot is None:
            return None
        rows[j],rows[pivot] = rows[pivot],rows[j]
        d = rows[j][j]
        rows[j] = [x/d for x in rows[j]]
        for i in range(m):
            if i != j and rows[i][j]:
                v = rows[i][j]
                rows[i] = [x-v*y for x,y in zip(rows[i],rows[j])]
    return tuple(r[-1] for r in rows)


def fixed_candidates(a, axis):
    # Coordinates in this chart range from zero to h. Lower target facets have
    # maxima at vertices already covered by positive charts (and the origin).
    n = len(a)
    h = a[:axis]+a[axis+1:]
    origin = (F(0),)*n
    sites = [s for s,_ in charts(a,origin,2*axis+1,())]
    # A direct two-facet route yields this upper bound throughout the chart.
    upper = dot(a,a)+2*a[axis]*min(h)
    sites = [s for s in sites if sum((x-min(b,max(0,x)))**2 for x,b in zip(s,h)) <= upper]
    # Direct sites are legal throughout this chart. If one is strictly closer
    # everywhere than a site s, that site can never realize the true distance.
    direct = [tuple(-a[axis] if i==j else F(0) for i in range(n-1)) for j in range(n-1)]
    def dominated(s):
        return any(dot(s,s)-dot(t,t)+sum(min(0,2*b*(v-u)) for b,u,v in zip(h,s,t))>0
                   for t in direct)
    sites = [s for s in sites if not dominated(s)]
    seen = set()
    for mode in product((-1,0,1), repeat=n-1):  # -1 means free, 0/1 a wall
        free = [i for i,b in enumerate(mode) if b < 0]
        base = [F(0) if b < 0 else b*h[i] for i,b in enumerate(mode)]
        for group in combinations(sites,len(free)+1):
            s = group[0]
            rows = []
            for t in group[1:]:
                normal = tuple(2*(v-u) for u,v in zip(s,t))
                rows.append([normal[i] for i in free]+[dot(t,t)-dot(s,s)-dot(normal,base)])
            u = solve_linear(rows)
            if u is None or any(not 0 < x < h[i] for i,x in zip(free,u)):
                continue
            z = base.copy()
            for i,x in zip(free,u):
                z[i] = x
            z = tuple(z)
            if z not in seen:
                seen.add(z)
                yield z[:axis]+(a[axis],)+z[axis:]


def vertex_maximum(sides, vertex_bits=None, arrangement=False):
    a = rational_box(sides)
    n = len(a)
    bits = tuple(vertex_bits) if vertex_bits is not None else (0,)*n
    if len(bits) != n or any(b not in (0,1) for b in bits):
        raise ValueError("Supply one vertex bit per side.")
    origin = (F(0),)*n
    order = sorted(a)
    best = dot(a,a) + 2*order[0]*order[1]
    winner = a
    if not arrangement:
        family = None
        if n == 2 or order[1] == order[-1]:
            family = 'rectangle or one short side'
        elif order[0] == order[-2]:
            family = 'cubical-base prism'
            base, long_side = order[0], order[-1]
            t = (long_side+base)/(2*long_side)
            raised = long_side**2 + (n-1)*(base*t)**2 + 2*long_side*base*t
            if raised > best:
                winner = tuple(b if b == long_side else base*t for b in a)
                best = raised
        if family:
            return {'squared':best,'point':tuple(b-x if v else x for b,x,v in zip(a,winner,bits)),
                    'method':family}
    count = 0
    # Equal-length axes may be permuted while fixing the origin.
    for axis in range(n):
        if a[axis] in a[:axis]:
            continue
        zaxes = [i for i in range(n) if i != axis]
        for p in fixed_candidates(a,axis):
            if any(a[i]==a[j] and p[i]>p[j] for i,j in combinations(zaxes,2)):
                continue
            count += 1
            value = surface_squared(a,origin,p)
            if value > best:
                best, winner = value, p
    return {'squared':best, 'point':tuple(b-x if v else x for b,x,v in zip(a,winner,bits)),
            'tested_candidates':count}


def csv(s):
    return tuple(map(F,s.split(',')))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode',choices=['point','vertex'])
    parser.add_argument('sides',type=csv)
    parser.add_argument('--p',type=csv)
    parser.add_argument('--q',type=csv)
    parser.add_argument('--arrangement',action='store_true',help='use full bisector enumeration even on closed-form families')
    parser.add_argument('--vertex-bits',type=lambda s:tuple(map(int,s.split(','))))
    args = parser.parse_args()
    if args.mode=='point':
        if args.p is None or args.q is None:
            parser.error('point requires --p and --q')
        result = {'squared':surface_squared(args.sides,args.p,args.q)}
    else:
        result = vertex_maximum(args.sides,args.vertex_bits,args.arrangement)
    print(json.dumps(result,default=str,indent=2))
