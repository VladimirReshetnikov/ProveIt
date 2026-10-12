"""Occurrence-preserving flag compiler. No global rank refinement occurs."""
from __future__ import annotations
from dataclasses import dataclass, asdict
from functools import lru_cache
from atlas import Atlas, Family, Chart, Mark, Polytope, simplex, submasks, bits, mask_image, validate, digest, from_data, Check, noop

@dataclass(frozen=True)
class Carrier:
    output: str
    source: str
    flag: tuple[int, ...]

@dataclass(frozen=True)
class Certificate:
    schema: str
    source_sha256: str
    result: Atlas
    carriers: tuple[Carrier, ...]

@lru_cache(maxsize=None)
def ending_flags(poly: Polytope, top: int) -> tuple[tuple[int, ...], ...]:
    result=[(top,)]
    for f in poly.faces():
        if f != top and f & ~top == 0:
            result.extend(chain+(top,) for chain in ending_flags(poly,f))
    return tuple(sorted(result,key=lambda x:(len(x),x)))

def compile_flags(source: Atlas, check: Check = noop, *, validate_source: bool = True) -> Certificate:
    # Public callers should keep validation enabled. The internal switch exists
    # only for controlled kernel-only measurements, not for source authentication.
    if validate_source: index=validate(source,check)
    else:
        from atlas import Index
        index=Index({p.name:p for p in source.polytopes},{f.name:f for f in source.families},{},{})
        for c in source.charts: index.charts.setdefault((c.upper,c.face),[]).append(c)
    carriers=[]; families=[]; names={}; charts=[]; marks=[]
    for number,f in enumerate(source.families):
        p=index.polys[f.poly]
        for chain in ending_flags(p,p.full):
            check(); name=f'F{number}:'+'.'.join(format(g,'x') for g in chain)
            names[f.name,chain]=name
            families.append(Family(name,f'D{len(chain)-1}',f.lo,f.hi))
            carriers.append(Carrier(name,f.name,chain))
    source_marks={}
    for m in source.marks: source_marks.setdefault(m.family,[]).append(m)
    for carrier in carriers:
        check(); f=index.families[carrier.source]; p=index.polys[f.poly]; chain=carrier.flag
        for m in source_marks.get(f.name,[]): marks.append(Mark(m.label,carrier.output,m.lo,m.hi))
        for face in submasks((1<<len(chain))-1):
            if face==(1<<len(chain))-1: continue
            kept=tuple(chain[j] for j in bits(face))
            vertex_map=tuple(range(len(kept)))
            if kept[-1]==p.full:
                charts.append(Chart(carrier.output,face,f.lo,f.hi,names[f.name,kept],1,0,vertex_map))
            else:
                for c in index.charts[f.name,kept[-1]]:
                    image_chain=tuple(mask_image(g,c.face,c.vertex_map) for g in kept)
                    charts.append(Chart(carrier.output,face,c.lo,c.hi,names[c.lower,image_chain],c.slope,c.shift,vertex_map))
    polys=tuple(simplex(d) for d in range(1+max(len(c.flag)-1 for c in carriers)))
    return Certificate('affine-flag-regularization-v1',digest(source),Atlas(polys,tuple(families),tuple(charts),tuple(marks)),tuple(carriers))


def certificate_data(certificate: Certificate) -> dict: return asdict(certificate)

def certificate_from_data(data: dict) -> Certificate:
    if set(data)!={'schema','source_sha256','result','carriers'}: raise ValueError('wrong certificate keys')
    return Certificate(data['schema'],data['source_sha256'],from_data(data['result']),
                       tuple(Carrier(c['output'],c['source'],tuple(c['flag'])) for c in data['carriers']))


def inventory(atlas: Atlas) -> dict:
    p={p.name:p for p in atlas.polytopes}
    counts=[0,0,0,0]
    for f in atlas.families: counts[p[f.poly].dim]+=f.hi-f.lo
    return {'families':len(atlas.families),'charts':len(atlas.charts),
            'marked_intervals':len(atlas.marks),'cell_counts':counts,
            'euler_characteristic':sum((-1)**d*c for d,c in enumerate(counts))}
