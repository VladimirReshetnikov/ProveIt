"""Executed bridge to the prior modular-Morse arithmetic format.

It exports regular incidence, not a knot verdict. The supplied cone matching
is only for authenticated disjoint copies of one convex polytope; it is not
a discovery algorithm for arbitrary normal-cut components.
"""
from __future__ import annotations
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'third_party'))
import ranked_morse as rm
from atlas import bits,validate
from replay import verify


def packet_from_flags(source,certificate):
    if not verify(source,certificate): raise ValueError('flag certificate rejected')
    idx=validate(certificate.result)
    families=tuple(rm.Family(f.name,idx.polys[f.poly].dim,f.lo,f.hi-1) for f in certificate.result.families)
    covers=[]
    for c in certificate.result.charts:
        p=idx.polys[idx.families[c.upper].poly]
        if len(bits(c.face))==p.dim:
            covers.append(rm.Cover(c.upper,c.lower,c.lo,c.hi-1,c.slope,c.shift))
    return rm.Packet(families,tuple(covers),())


def convex_cone_certificate(poly,copies,source,certificate):
    """Check exact source construction before issuing its explicit cone matching."""
    from sources import polytope_ball
    if source!=polytope_ball(poly,copies): raise ValueError('not the authenticated convex-copy source')
    packet=packet_from_flags(source,certificate)
    names={(c.source,c.flag):c.output for c in certificate.carriers}
    full=poly.full; top=f'C{full:x}'; matched=[]; offsets={}
    cover_index={(c.upper,c.lower):j for j,c in enumerate(packet.covers)}
    for meta in certificate.carriers:
        if meta.source==top:
            d=len(meta.flag)-1
            offsets[meta.output]=0 if d==0 else 2*d-1
        else:
            mask=int(meta.source[1:],16); vertices=bits(mask)
            lifted=tuple(sum(1<<vertices[j] for j in bits(face)) for face in meta.flag)+(full,)
            upper=names[top,lifted]
            j=cover_index[upper,meta.output]; c=packet.covers[j]
            matched.append(rm.Match(j,c.lo,c.hi))
            offsets[meta.output]=2*(len(meta.flag)-1)+2
    packet=rm.Packet(packet.families,packet.covers,tuple(matched))
    proof=rm.AffineProof({f.name:0 for f in packet.families},offsets)
    prepared=rm.prepare(packet)
    if not rm.verify_affine(prepared,proof): raise ArithmeticError('cone rank failed')
    if prepared.counts!=(copies,)+(0,)*(len(prepared.counts)-1): raise ArithmeticError('wrong cone critical cells')
    return packet,proof,prepared.counts
