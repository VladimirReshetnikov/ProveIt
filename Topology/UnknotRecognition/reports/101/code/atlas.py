"""Exact convex face atlases, dimension <= 3, with binary half-open ranks.

All local face OCCURRENCES are explicit.  Validity establishes a polytopal
CW quotient; it does not certify that that quotient is a 3-manifold, or
that an arbitrary external source is homeomorphic to it.

Standard library only. Integer validation deliberately rejects bool.
"""
from __future__ import annotations
from dataclasses import dataclass, asdict
from functools import lru_cache
from itertools import combinations
from fractions import Fraction
from typing import Callable, Iterable
import hashlib
import json

Check = Callable[[], None]
def noop() -> None: pass

def integers(*xs: int) -> None:
    if any(type(x) is not int for x in xs):
        raise ValueError('expected integers, not bool, float, or numeric strings')

def rank(rows: Iterable[Iterable[int]]) -> int:
    a = [list(map(Fraction, r)) for r in rows]
    if not a: return 0
    n = len(a[0]); k = 0
    for j in range(n):
        pivot = next((i for i in range(k, len(a)) if a[i][j]), None)
        if pivot is None: continue
        a[k], a[pivot] = a[pivot], a[k]
        x = a[k][j]; a[k] = [y / x for y in a[k]]
        for i in range(k + 1, len(a)):
            x = a[i][j]
            if x: a[i] = [u - x*v for u,v in zip(a[i], a[k])]
        k += 1
        if k == len(a): break
    return k

def bits(mask: int) -> tuple[int, ...]:
    return tuple(i for i in range(mask.bit_length()) if mask >> i & 1)

def mask_image(mask: int, domain: int, vertex_map: tuple[int, ...]) -> int:
    """Map a face inside domain; vertex_map is in sorted domain-vertex order."""
    if mask & ~domain: raise ValueError('face is outside chart domain')
    return sum(1 << vertex_map[j] for j,v in enumerate(bits(domain)) if mask >> v & 1)

@dataclass(frozen=True)
class Polytope:
    name: str
    vertices: tuple[tuple[int, ...], ...]

    @property
    def dim(self) -> int: return len(self.vertices[0]) if self.vertices else -1
    @property
    def full(self) -> int: return (1 << len(self.vertices)) - 1

    @lru_cache(maxsize=None)
    def faces(self) -> tuple[int, ...]:
        """Recover the COMPLETE convex face lattice using exact support planes."""
        if not isinstance(self.name, str) or not self.name or not self.vertices:
            raise ValueError('empty or unnamed polytope')
        d = self.dim
        if not 0 <= d <= 3 or any(len(p) != d for p in self.vertices):
            raise ValueError('dimension or coordinate length')
        for p in self.vertices: integers(*p)
        if len(set(self.vertices)) != len(self.vertices):
            raise ValueError('repeated polytope vertex')
        p0 = self.vertices[0]
        if rank(tuple(tuple(x-y for x,y in zip(p,p0)) for p in self.vertices[1:])) != d:
            raise ValueError('polytope is not full dimensional')
        if d == 0:
            if len(self.vertices) != 1: raise ValueError('invalid point')
            return (1,)
        facets: set[int] = set()
        for ids in combinations(range(len(self.vertices)), d):
            base = self.vertices[ids[0]]
            dif = [tuple(x-y for x,y in zip(self.vertices[i],base)) for i in ids[1:]]
            if d == 1: normal = (1,)
            elif d == 2:
                u, = dif; normal = (-u[1], u[0])
            else:
                u,v = dif
                normal = (u[1]*v[2]-u[2]*v[1], u[2]*v[0]-u[0]*v[2], u[0]*v[1]-u[1]*v[0])
            if not any(normal): continue
            vals = [sum(n*(x-y) for n,x,y in zip(normal,p,base)) for p in self.vertices]
            if not (all(x >= 0 for x in vals) or all(x <= 0 for x in vals)): continue
            face = sum(1 << i for i,x in enumerate(vals) if x == 0)
            if face != self.full: facets.add(face)
        faces = {self.full}
        # In dimension d every face is the intersection of <= d suitably
        # independent supporting facets. No powerset of facets is enumerated.
        for k in range(1, d+1):
            for fs in combinations(sorted(facets), k):
                f = self.full
                for g in fs: f &= g
                if f: faces.add(f)
        if any((1 << v) not in faces for v in range(len(self.vertices))):
            raise ValueError('coordinate list contains a non-extreme point')
        return tuple(sorted(faces, key=lambda f: (self.face_dim(f), f)))

    @lru_cache(maxsize=None)
    def face_dim(self, face: int) -> int:
        ids = bits(face)
        if not ids or face & ~self.full: raise ValueError('invalid face mask')
        p = self.vertices[ids[0]]
        return rank(tuple(tuple(x-y for x,y in zip(self.vertices[i], p)) for i in ids[1:]))

@dataclass(frozen=True)
class Family:
    name: str
    poly: str
    lo: int
    hi: int

@dataclass(frozen=True)
class Chart:
    """upper(i)'s local face maps isomorphically to lower(slope*i+shift)."""
    upper: str
    face: int
    lo: int
    hi: int
    lower: str
    slope: int
    shift: int
    vertex_map: tuple[int, ...]

@dataclass(frozen=True)
class Mark:
    label: str
    family: str
    lo: int
    hi: int

@dataclass(frozen=True)
class Atlas:
    polytopes: tuple[Polytope, ...]
    families: tuple[Family, ...]
    charts: tuple[Chart, ...]
    marks: tuple[Mark, ...] = ()

@dataclass
class Index:
    polys: dict[str, Polytope]
    families: dict[str, Family]
    charts: dict[tuple[str,int], list[Chart]]
    marks: dict[tuple[str,str], list[tuple[int,int]]]


def image(lo: int, hi: int, s: int, b: int) -> tuple[int,int]:
    if s == 1: return lo+b, hi+b
    if s == -1: return b-hi+1, b-lo+1
    raise ValueError('chart slope must be +1 or -1')

def pullback(lo: int, hi: int, s: int, b: int) -> tuple[int,int]:
    return image(lo, hi, s, -s*b)

def equal_affine(s: int,b: int,t: int,c: int,lo: int,hi: int) -> bool:
    return s*lo+b == t*lo+c and s*(hi-1)+b == t*(hi-1)+c

def covered(intervals: Iterable[tuple[int,int]], lo: int,hi: int) -> bool:
    cursor=lo
    for a,b in sorted(intervals):
        if b <= cursor: continue
        if a > cursor: return False
        cursor=max(cursor,b)
        if cursor>=hi: return True
    return cursor>=hi


def validate(atlas: Atlas, check: Check = noop) -> Index:
    """Check convex templates, total charts, face coherence, and marked subcomplexes.

    No represented rank is enumerated. Runtime polynomial in record size;
    this simple implementation is not optimized to the best possible exponent.
    """
    polys: dict[str,Polytope] = {}
    for p in atlas.polytopes:
        check(); p.faces()
        if p.name in polys: raise ValueError('duplicate polytope name')
        polys[p.name]=p
    fam: dict[str,Family] = {}
    for f in atlas.families:
        check(); integers(f.lo,f.hi)
        if not isinstance(f.name,str) or not f.name or f.name in fam or f.poly not in polys or f.lo>=f.hi:
            raise ValueError('invalid or duplicate family')
        fam[f.name]=f
    if not fam: raise ValueError('empty atlas')
    grouped: dict[tuple[str,int],list[Chart]] = {}
    iso_cache=set()
    for c in atlas.charts:
        check(); integers(c.face,c.lo,c.hi,c.slope,c.shift,*c.vertex_map)
        if c.upper not in fam or c.lower not in fam or c.slope not in (-1,1):
            raise ValueError('unknown family or invalid slope')
        u,v=fam[c.upper],fam[c.lower]; p,q=polys[u.poly],polys[v.poly]
        if c.face not in p.faces() or c.face==p.full or not u.lo<=c.lo<c.hi<=u.hi:
            raise ValueError('invalid chart face or source domain')
        if p.face_dim(c.face)!=q.dim or sorted(c.vertex_map)!=list(range(len(q.vertices))) or len(bits(c.face))!=len(c.vertex_map):
            raise ValueError('chart is not a vertex bijection of the required dimension')
        a,b=image(c.lo,c.hi,c.slope,c.shift)
        if not v.lo<=a<b<=v.hi: raise ValueError('chart leaves target domain')
        iso_key=(p,c.face,q,c.vertex_map)
        if iso_key not in iso_cache:
            mapped={mask_image(g,c.face,c.vertex_map) for g in p.faces() if g & ~c.face==0}
            if mapped!=set(q.faces()): raise ValueError('chart is not a face-lattice isomorphism')
            iso_cache.add(iso_key)
        grouped.setdefault((c.upper,c.face),[]).append(c)
    for f in fam.values():
        p=polys[f.poly]
        for g in p.faces():
            if g==p.full: continue
            entries=sorted(grouped.get((f.name,g),[]),key=lambda c:c.lo)
            x=f.lo
            for c in entries:
                if c.lo!=x: raise ValueError('missing or overlapping chart domain')
                x=c.hi
            if x!=f.hi: raise ValueError('incomplete local face occurrence')
            grouped[f.name,g]=entries
    # Commutative nested-face squares. Direct charts are compared to every
    # actual intersection of two successive chart domains, not to a global
    # iterated refinement. Family dimension strictly decreases.
    for c in atlas.charts:
        check(); p=polys[fam[c.upper].poly]
        for g in p.faces():
            if g==c.face or g & ~c.face: continue
            target_face=mask_image(g,c.face,c.vertex_map)
            for d in grouped[c.lower,target_face]:
                a,b=pullback(d.lo,d.hi,c.slope,c.shift)
                lo,hi=max(c.lo,a),min(c.hi,b)
                if lo>=hi: continue
                cdict=dict(zip(bits(c.face),c.vertex_map)); ddict=dict(zip(bits(target_face),d.vertex_map))
                composed=tuple(ddict[cdict[v]] for v in bits(g))
                for e in grouped[c.upper,g]:
                    l,h=max(lo,e.lo),min(hi,e.hi)
                    if l>=h: continue
                    if (e.lower!=d.lower or e.vertex_map!=composed or not equal_affine(
                        e.slope,e.shift,d.slope*c.slope,d.slope*c.shift+d.shift,l,h)):
                        raise ValueError('incoherent nested-face charts')
    marks: dict[tuple[str,str],list[tuple[int,int]]] = {}
    for m in atlas.marks:
        check(); integers(m.lo,m.hi)
        if not isinstance(m.label,str) or not m.label or m.family not in fam or not fam[m.family].lo<=m.lo<m.hi<=fam[m.family].hi:
            raise ValueError('invalid marked interval')
        marks.setdefault((m.label,m.family),[]).append((m.lo,m.hi))
    for key, intervals in marks.items():
        intervals.sort()
        if any(b>c for (a,b),(c,d) in zip(intervals,intervals[1:])):
            raise ValueError('overlapping marked intervals')
    for m in atlas.marks:
        p=polys[fam[m.family].poly]
        for g in p.faces():
            if g==p.full: continue
            for c in grouped[m.family,g]:
                lo,hi=max(m.lo,c.lo),min(m.hi,c.hi)
                if lo<hi:
                    a,b=image(lo,hi,c.slope,c.shift)
                    if not covered(marks.get((m.label,c.lower),[]),a,b):
                        raise ValueError('marked set is not a subcomplex')
    return Index(polys,fam,grouped,marks)


def canonical_data(atlas: Atlas) -> dict:
    return asdict(atlas)

def _encode(x):
    # Avoid Python decimal digit conversion limits; do not change process limits.
    if type(x) is int and x.bit_length()>256: return {'$hex': ('-' if x<0 else '')+format(abs(x),'x')}
    if isinstance(x,dict): return {k:_encode(v) for k,v in x.items()}
    if isinstance(x,(list,tuple)): return [_encode(y) for y in x]
    return x

def _decode(x):
    if isinstance(x,dict):
        if set(x)=={'$hex'}:
            s=x['$hex']
            if not isinstance(s,str) or not s: raise ValueError('bad hex integer')
            return int(s,16)
        return {k:_decode(v) for k,v in x.items()}
    if isinstance(x,list): return [_decode(y) for y in x]
    return x

def dumps(data) -> str: return json.dumps(_encode(data),sort_keys=True,separators=(',',':'))
def loads(text: str): return _decode(json.loads(text))
def digest(atlas: Atlas) -> str: return hashlib.sha256(dumps(canonical_data(atlas)).encode()).hexdigest()

def from_data(data: dict) -> Atlas:
    if set(data)!={'polytopes','families','charts','marks'}: raise ValueError('wrong atlas keys')
    return Atlas(tuple(Polytope(p['name'],tuple(tuple(v) for v in p['vertices'])) for p in data['polytopes']),
                 tuple(Family(**f) for f in data['families']),
                 tuple(Chart(**{**c,'vertex_map':tuple(c['vertex_map'])}) for c in data['charts']),
                 tuple(Mark(**m) for m in data['marks']))


def simplex(d: int) -> Polytope:
    integers(d)
    if not 0<=d<=3: raise ValueError('simplex dimension')
    return Polytope(f'D{d}',(tuple(0 for _ in range(d)),)+tuple(tuple(int(i==j) for j in range(d)) for i in range(d)))


def submasks(mask: int) -> tuple[int,...]:
    """For <=4 flag vertices only; not used on unrestricted prototype vertices."""
    result=[]; s=mask
    while s:
        result.append(s); s=(s-1)&mask
    return tuple(sorted(result))
