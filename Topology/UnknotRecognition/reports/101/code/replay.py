"""Independent symbolic flag replay: no call/import of the flag compiler.

Completeness is checked by face-poset dynamic counts, not by rerunning the
producer's flag enumeration. Output chart partitions may differ from the
producer's partition, provided their represented maps agree everywhere.
The trusted arithmetic/model layer atlas.py is shared and explicitly audited.
"""
from __future__ import annotations
from collections import Counter
from atlas import Atlas, Polytope, validate, digest, bits, mask_image, equal_affine, covered, simplex, Check, noop


def flag_counts(poly: Polytope) -> tuple[int,...]:
    ways={}
    for f in poly.faces():
        vector=[1,0,0,0]
        for g,v in ways.items():
            if g & ~f==0:
                for j in range(3): vector[j+1]+=v[j]
        ways[f]=tuple(vector)
    return ways[poly.full]


def _intervals_equal(a,b,lo,hi):
    endpoints={lo,hi}
    for intervals in (a,b):
        for x,y in intervals: endpoints.update((max(lo,x),min(hi,y)))
    events=sorted(x for x in endpoints if lo<=x<=hi)
    return all(covered(a,x,y)==covered(b,x,y) for x,y in zip(events,events[1:]))


def verify(source: Atlas, certificate, check: Check = noop) -> bool:
    """Return False for malformed proof; cooperative cancellation propagates.

    The caller supplies/authenticates source. A matching digest is only a
    binding, never a claim that an arbitrary atlas is a native normal cut.
    """
    try:
        return _verify(source,certificate,check)
    except (ValueError,TypeError,KeyError,AttributeError,IndexError):
        return False


def _verify(source: Atlas, certificate, check: Check) -> bool:
    si=validate(source,check)
    if certificate.schema!='affine-flag-regularization-v1' or certificate.source_sha256!=digest(source): return False
    oi=validate(certificate.result,check)
    if set(oi.polys)!={f'D{p.dim}' for p in oi.polys.values()}: return False
    if any(p!=simplex(p.dim) for p in oi.polys.values()): return False
    meta={}; unique=set(); counts=Counter()
    if len(certificate.carriers)!=len(oi.families): return False
    for c in certificate.carriers:
        check()
        if c.output in meta or c.output not in oi.families or c.source not in si.families: return False
        f=si.families[c.source]; p=si.polys[f.poly]; chain=c.flag
        if (not isinstance(chain,tuple) or not chain or chain[-1]!=p.full
            or any(type(x) is not int or x not in p.faces() for x in chain)
            or any(a==b or a & ~b for a,b in zip(chain,chain[1:]))): return False
        key=(c.source,chain)
        if key in unique: return False
        unique.add(key); meta[c.output]=c
        o=oi.families[c.output]
        if o.lo!=f.lo or o.hi!=f.hi or oi.polys[o.poly].dim!=len(chain)-1: return False
        counts[c.source,len(chain)-1]+=1
    for f in si.families.values():
        target=flag_counts(si.polys[f.poly])
        if tuple(counts[f.name,d] for d in range(4))!=target: return False
    # Each claimed chart's semantics must equal the original occurrence chart.
    # Output totality/coverage was checked above, so no producer-generated table
    # is required to prove completeness of the face maps.
    for c in certificate.result.charts:
        check(); upper=meta[c.upper]; lower=meta[c.lower]
        kept=tuple(upper.flag[j] for j in bits(c.face))
        if c.vertex_map!=tuple(range(len(kept))): return False
        p=si.polys[si.families[upper.source].poly]
        if kept[-1]==p.full:
            if lower.source!=upper.source or lower.flag!=kept or not equal_affine(c.slope,c.shift,1,0,c.lo,c.hi): return False
        else:
            for d in si.charts[upper.source,kept[-1]]:
                lo,hi=max(c.lo,d.lo),min(c.hi,d.hi)
                if lo>=hi: continue
                expected=tuple(mask_image(g,d.face,d.vertex_map) for g in kept)
                if (lower.source!=d.lower or lower.flag!=expected
                    or not equal_affine(c.slope,c.shift,d.slope,d.shift,lo,hi)): return False
    labels={m.label for m in source.marks}|{m.label for m in certificate.result.marks}
    for name,c in meta.items():
        f=oi.families[name]
        for label in labels:
            if not _intervals_equal(si.marks.get((label,c.source),[]),oi.marks.get((label,name),[]),f.lo,f.hi): return False
    return True
