"""Exact rank certificates for interval-encoded regular-cell Morse matchings.

This module verifies combinatorial matching/rank data, NOT source geometry.
No boolean supplied by a caller is accepted as proof that a packet is a manifold.
Python 3.10+, standard library only.  Integers are arbitrary precision.
"""
from __future__ import annotations
from dataclasses import dataclass, asdict
from collections import defaultdict, deque
from typing import Mapping, Iterable
import json


@dataclass(frozen=True)
class Family:
    name: str
    dim: int
    lo: int
    hi: int

@dataclass(frozen=True)
class Cover:
    """upper(i) has lower(slope*i+shift) as a codimension-one face."""
    upper: str
    lower: str
    lo: int
    hi: int
    slope: int = 1
    shift: int = 0

@dataclass(frozen=True)
class Match:
    cover: int
    lo: int
    hi: int

@dataclass(frozen=True)
class Arc:
    src: str
    dst: str
    lo: int
    hi: int
    slope: int = 1
    shift: int = 0

@dataclass(frozen=True)
class Packet:
    families: tuple[Family, ...]
    covers: tuple[Cover, ...]
    matching: tuple[Match, ...]

@dataclass(frozen=True)
class Prepared:
    packet: Packet
    arcs: tuple[Arc, ...]
    critical: tuple[tuple[str, int, int], ...]
    counts: tuple[int, ...]

@dataclass(frozen=True)
class AffineProof:
    slopes: dict[str, int]
    offsets: dict[str, int]

@dataclass(frozen=True)
class ModularProof:
    modulus: int
    scale: int
    multipliers: dict[str, int]
    phases: dict[str, int]
    offsets: dict[str, int]


def _integer(*values: int) -> None:
    if any(type(x) is not int for x in values):
        raise ValueError('integer fields must be integers, not bools/floats')


def _image(lo: int, hi: int, s: int, b: int) -> tuple[int, int]:
    x, y = s*lo+b, s*hi+b
    return min(x,y), max(x,y)


def _complement(lo: int, hi: int, intervals: Iterable[tuple[int,int]]) -> list[tuple[int,int]]:
    result = []
    cursor = lo
    for a,b in sorted(intervals):
        if a < cursor or b < a or b > hi:
            raise ValueError('overlapping or out-of-range occupied intervals')
        if cursor < a:
            result.append((cursor,a-1))
        cursor = b+1
    if cursor <= hi:
        result.append((cursor,hi))
    return result


def prepare(packet: Packet) -> Prepared:
    """Check all interval matching data and orient every cover, without expansion.

    Complete, regular, geometric incidence is an external source obligation.
    Duplicate cover pairs are rejected rather than treated as matrix cancellation.
    """
    fam = {}
    for f in packet.families:
        _integer(f.dim,f.lo,f.hi)
        if not isinstance(f.name,str) or not f.name or f.name in fam or not 0 <= f.dim <= 3 or f.lo > f.hi:
            raise ValueError('invalid or duplicate family')
        fam[f.name] = f
    if not fam:
        raise ValueError('empty cell inventory')
    grouped = defaultdict(list)
    for c in packet.covers:
        _integer(c.lo,c.hi,c.slope,c.shift)
        if c.upper not in fam or c.lower not in fam or c.slope not in (-1,1):
            raise ValueError('invalid cover reference or slope')
        u,v = fam[c.upper],fam[c.lower]
        if u.dim != v.dim+1 or not u.lo <= c.lo <= c.hi <= u.hi:
            raise ValueError('cover dimension or source domain')
        a,b = _image(c.lo,c.hi,c.slope,c.shift)
        if not v.lo <= a <= b <= v.hi:
            raise ValueError('cover target domain')
        # Detect equal cell pairs, including isolated agreement of opposite slopes.
        for d in grouped[(c.upper,c.lower)]:
            lo,hi = max(c.lo,d.lo),min(c.hi,d.hi)
            if lo > hi:
                continue
            k = c.slope-d.slope
            z = d.shift-c.shift
            if (k == 0 and z == 0) or (k and z % k == 0 and lo <= z//k <= hi):
                raise ValueError('duplicate codimension-one cell incidence')
        grouped[(c.upper,c.lower)].append(c)
    by_cover = defaultdict(list)
    occupied = defaultdict(list)
    for m in packet.matching:
        _integer(m.cover,m.lo,m.hi)
        if not 0 <= m.cover < len(packet.covers):
            raise ValueError('invalid matching cover')
        c = packet.covers[m.cover]
        if not c.lo <= m.lo <= m.hi <= c.hi:
            raise ValueError('matching outside cover domain')
        by_cover[m.cover].append((m.lo,m.hi))
        occupied[c.upper].append((m.lo,m.hi))
        occupied[c.lower].append(_image(m.lo,m.hi,c.slope,c.shift))
    critical = []
    counts = [0]*(1+max(f.dim for f in fam.values()))
    for f in fam.values():
        for lo,hi in _complement(f.lo,f.hi,occupied[f.name]):
            critical.append((f.name,lo,hi))
            counts[f.dim] += hi-lo+1
    arcs = []
    for k,c in enumerate(packet.covers):
        for lo,hi in _complement(c.lo,c.hi,by_cover[k]):
            arcs.append(Arc(c.upper,c.lower,lo,hi,c.slope,c.shift))
        for lo,hi in by_cover[k]:
            a,b = _image(lo,hi,c.slope,c.shift)
            arcs.append(Arc(c.lower,c.upper,a,b,c.slope,-c.slope*c.shift))
    return Prepared(packet,tuple(arcs),tuple(critical),tuple(counts))


def floor_sum(n: int, modulus: int, a: int, b: int) -> int:
    """sum(floor((a*i+b)/modulus), i=0..n-1), signed a,b, O(log modulus)."""
    _integer(n,modulus,a,b)
    if n < 0 or modulus <= 0:
        raise ValueError('floor_sum needs n>=0 and modulus>0')
    answer = 0
    while True:
        qa,a = divmod(a,modulus)
        qb,b = divmod(b,modulus)
        answer += qa*n*(n-1)//2 + qb*n
        y = a*n+b
        if y < modulus:
            return answer
        n,b = divmod(y,modulus)
        modulus,a = a,modulus


def residue_ge(lo: int, hi: int, modulus: int, a: int, b: int, threshold: int) -> int:
    """Number of i in [lo,hi] with (a*i+b) mod modulus >= threshold."""
    _integer(lo,hi,modulus,a,b,threshold)
    if lo > hi or modulus <= 0 or not 0 <= threshold <= modulus:
        raise ValueError('invalid residue-count parameters')
    n = hi-lo+1
    start = a*lo+b
    return floor_sum(n,modulus,a,start+modulus-threshold)-floor_sum(n,modulus,a,start)


def solve_offsets(names: Iterable[str], constraints: Iterable[tuple[str,str,int]]) -> dict[str,int] | None:
    """Solve h[u]>=h[v]+c exactly; None means positive cycle IN THIS TEMPLATE.

    None never means noncollapsible or nonball.  All names get an implicit
    zero lower bound, which is harmless because a common shift is free.
    """
    names = tuple(names)
    edges = tuple(constraints)
    if len(set(names)) != len(names):
        raise ValueError('duplicate variable name')
    h = dict.fromkeys(names,0)
    for u,v,c in edges:
        if u not in h or v not in h:
            raise ValueError('unknown constraint variable')
        _integer(c)
    for _ in range(len(names)):
        updated = h.copy()
        for u,v,c in edges:
            updated[u] = max(updated[u],h[v]+c)
        if updated == h:
            return h
        h = updated
    return None


def _check_keys(prepared: Prepared, *maps: Mapping[str,int]) -> None:
    names = {f.name for f in prepared.packet.families}
    for mapping in maps:
        if set(mapping) != names:
            raise ValueError('rank map does not name exactly all families')
        _integer(*mapping.values())


def affine_constraints(prepared: Prepared, slopes: Mapping[str,int]) -> tuple[tuple[str,str,int], ...]:
    _check_keys(prepared,slopes)
    result = []
    for e in prepared.arcs:
        c = max(1+slopes[e.dst]*(e.slope*i+e.shift)-slopes[e.src]*i for i in (e.lo,e.hi))
        result.append((e.src,e.dst,c))
    return tuple(result)


def synthesize_affine(prepared: Prepared, slopes: Mapping[str,int]) -> AffineProof | None:
    constraints = affine_constraints(prepared,slopes)
    h = solve_offsets((f.name for f in prepared.packet.families),constraints)
    return None if h is None else AffineProof(dict(slopes),h)


def verify_affine(prepared: Prepared, proof: AffineProof) -> bool:
    """Independent inequality replay; does not call synthesis/constraint solving."""
    try:
        _check_keys(prepared,proof.slopes,proof.offsets)
        for e in prepared.arcs:
            for i in (e.lo,e.hi):
                lhs = proof.slopes[e.src]*i+proof.offsets[e.src]
                rhs = proof.slopes[e.dst]*(e.slope*i+e.shift)+proof.offsets[e.dst]
                if lhs <= rhs:
                    return False
        return True
    except (ValueError,TypeError,AttributeError):
        return False


def modular_constraints(prepared: Prepared, modulus: int, scale: int,
                        multipliers: Mapping[str,int], phases: Mapping[str,int]) -> tuple[tuple[str,str,int], ...]:
    _integer(modulus,scale)
    if modulus <= 0 or scale <= 0:
        raise ValueError('modulus and scale must be positive')
    _check_keys(prepared,multipliers,phases)
    result = []
    for e in prepared.arcs:
        au,av = multipliers[e.src],multipliers[e.dst]
        cu,cv = phases[e.src],phases[e.dst]
        if (av*e.slope-au) % modulus:
            raise ValueError('modular coefficient synchronization fails')
        delta = (av*e.shift+cv-cu) % modulus
        wraps = residue_ge(e.lo,e.hi,modulus,au,cu,modulus-delta)
        n = e.hi-e.lo+1
        # If even one nonwrapping occurrence exists it gives the stricter bound.
        c = 1+scale*delta-(scale*modulus if wraps == n else 0)
        result.append((e.src,e.dst,c))
    return tuple(result)


def synthesize_modular(prepared: Prepared, modulus: int, scale: int,
                       multipliers: Mapping[str,int], phases: Mapping[str,int]) -> ModularProof | None:
    constraints = modular_constraints(prepared,modulus,scale,multipliers,phases)
    h = solve_offsets((f.name for f in prepared.packet.families),constraints)
    return None if h is None else ModularProof(modulus,scale,dict(multipliers),dict(phases),h)


def verify_modular(prepared: Prepared, proof: ModularProof) -> bool:
    """Replay both actually present wrap classes, without calling the producer."""
    try:
        _integer(proof.modulus,proof.scale)
        M,D = proof.modulus,proof.scale
        if M <= 0 or D <= 0:
            return False
        _check_keys(prepared,proof.multipliers,proof.phases,proof.offsets)
        for e in prepared.arcs:
            au,av = proof.multipliers[e.src],proof.multipliers[e.dst]
            cu,cv = proof.phases[e.src],proof.phases[e.dst]
            if (av*e.slope-au) % M:
                return False
            delta = (av*e.shift+cv-cu) % M
            w = residue_ge(e.lo,e.hi,M,au,cu,M-delta)
            difference = proof.offsets[e.src]-proof.offsets[e.dst]-D*delta
            if w < e.hi-e.lo+1 and difference < 1:
                return False
            if w > 0 and difference+D*M < 1:
                return False
        return True
    except (ValueError,TypeError,AttributeError):
        return False


def one_critical_vertex(prepared: Prepared) -> bool:
    """Combinatorial condition only. Does not certify a manifold or a knot."""
    return prepared.counts[0] == 1 and not any(prepared.counts[1:])


def expand(prepared: Prepared, limit: int = 1_000_000):
    """Capped explicit oracle; never used by compressed verification."""
    total = sum(f.hi-f.lo+1 for f in prepared.packet.families)
    if total > limit:
        raise ValueError('explicit expansion cap exceeded')
    dims = {(f.name,i):f.dim for f in prepared.packet.families for i in range(f.lo,f.hi+1)}
    covers = set()
    for c in prepared.packet.covers:
        for i in range(c.lo,c.hi+1):
            covers.add(((c.upper,i),(c.lower,c.slope*i+c.shift)))
    matches = set()
    for m in prepared.packet.matching:
        c = prepared.packet.covers[m.cover]
        for i in range(m.lo,m.hi+1):
            matches.add(((c.upper,i),(c.lower,c.slope*i+c.shift)))
    return dims,covers,matches


def explicit_acyclic(prepared: Prepared, limit: int = 1_000_000) -> bool:
    dims,covers,matches = expand(prepared,limit)
    adj = defaultdict(list)
    incoming = dict.fromkeys(dims,0)
    for u,v in covers:
        if (u,v) in matches:
            u,v = v,u
        adj[u].append(v)
        incoming[v] += 1
    queue = deque(u for u in dims if incoming[u] == 0)
    count = 0
    while queue:
        u = queue.popleft(); count += 1
        for v in adj[u]:
            incoming[v] -= 1
            if incoming[v] == 0:
                queue.append(v)
    return count == len(dims)


def explicit_collapse_remainder(prepared: Prepared, limit: int = 1_000_000):
    """Remaining cells after replaying free pairs, or None if replay gets stuck."""
    dims,covers,matches = expand(prepared,limit)
    parents = {u:set() for u in dims}
    faces = {u:set() for u in dims}
    for u,v in covers:
        parents[v].add(u); faces[u].add(v)
    match_upper = {v:u for u,v in matches}
    alive = set(dims)
    queue = deque(match_upper)
    removed = 0
    while queue:
        v = queue.popleft()
        if v not in alive:
            continue
        u = match_upper[v]
        if u not in alive or parents[u] or parents[v] != {u}:
            continue
        affected = (faces[u] | faces[v])-{u,v}
        alive.remove(u); alive.remove(v); removed += 1
        for x in faces[u]:
            parents[x].discard(u)
        for x in faces[v]:
            parents[x].discard(v)
        for x in affected:
            if x in match_upper:
                queue.append(x)
            for y in faces[x]:
                if y in match_upper:
                    queue.append(y)
    return frozenset(alive) if removed == len(matches) else None


def explicit_collapse(prepared: Prepared, limit: int = 1_000_000) -> bool:
    """Separate point-collapse oracle using free faces, not rank inequalities."""
    remaining = explicit_collapse_remainder(prepared,limit)
    dims = {f.name:f.dim for f in prepared.packet.families}
    return remaining is not None and len(remaining)==1 and dims[next(iter(remaining))[0]]==0


def reflect(prepared: Prepared, reversed_names: set[str]) -> tuple[Packet, dict[str,tuple[int,int]]]:
    """Exact family reindexing i -> lo+hi-i. Source provenance is unchanged."""
    changes = {f.name:(-1,f.lo+f.hi) if f.name in reversed_names else (1,0)
               for f in prepared.packet.families}
    covers = []
    for c in prepared.packet.covers:
        ru,cu = changes[c.upper]; rv,cv = changes[c.lower]
        lo,hi = _image(c.lo,c.hi,ru,cu)
        covers.append(Cover(c.upper,c.lower,lo,hi,rv*c.slope*ru,rv*(c.slope*cu+c.shift-cv)))
    matching = []
    for m in prepared.packet.matching:
        c = prepared.packet.covers[m.cover]
        r,b = changes[c.upper]
        lo,hi = _image(m.lo,m.hi,r,b)
        matching.append(Match(m.cover,lo,hi))
    return Packet(prepared.packet.families,tuple(covers),tuple(matching)),changes


def _wire(value):
    if type(value) is int and value.bit_length() > 256:
        return {'bigint_hex':hex(value)}
    if isinstance(value,dict):
        return {str(k):_wire(v) for k,v in value.items()}
    if isinstance(value,(tuple,list)):
        return [_wire(v) for v in value]
    return value


def dumps_certificate(packet: Packet, proof: AffineProof | ModularProof) -> str:
    return json.dumps(_wire({'schema':'ranked-morse-v1','packet':asdict(packet),
                            'rank_kind':'affine' if isinstance(proof,AffineProof) else 'modular',
                            'proof':asdict(proof)}),sort_keys=True,separators=(',',':'))


def loads_certificate(text: str) -> tuple[Packet, AffineProof | ModularProof]:
    def hook(obj):
        if set(obj) == {'bigint_hex'}:
            if not isinstance(obj['bigint_hex'],str):
                raise ValueError('invalid hexadecimal integer')
            return int(obj['bigint_hex'],16)
        return obj
    obj = json.loads(text,object_hook=hook)
    if obj['schema'] != 'ranked-morse-v1':
        raise ValueError('unknown schema')
    p = obj['packet']
    packet = Packet(tuple(Family(**x) for x in p['families']),tuple(Cover(**x) for x in p['covers']),
                    tuple(Match(**x) for x in p['matching']))
    if obj['rank_kind'] not in ('affine','modular'):
        raise ValueError('unknown rank kind')
    proof = (AffineProof if obj['rank_kind']=='affine' else ModularProof)(**obj['proof'])
    return packet,proof
