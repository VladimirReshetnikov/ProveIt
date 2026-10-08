"""Conservative explicit-to-port audit bridge; not an asymptotic compression claim.

Input matrices are already scalar and closed. The bridge chooses vertex-disjoint
arrows as A and factors D+A degree by degree. It uses a zero-length register.
The resulting certificate verifies the algebra; diagram provenance remains external.
"""
from __future__ import annotations
from . import gf2
from .automata import product_register
from .complexes import TemplateBlock, PortComplex


def from_dense(rows: list[int], degrees: list[int]) -> PortComplex:
    n = len(rows)
    if len(degrees) != n or any(type(h) is not int for h in degrees):
        raise ValueError('invalid degree array')
    gf2.check_rows(rows,n)
    if any(gf2.mul(rows,rows)):
        raise ValueError('input differential does not square to zero')
    used = set()
    a = [0]*n
    for target,row in enumerate(rows):
        for source in gf2.bits(row):
            if degrees[target] != degrees[source]+1:
                raise ValueError('differential is not degree one')
            if source not in used and target not in used:
                a[target] = 1 << source
                used.update((source,target))
    residual = gf2.add(rows,a)
    port_degrees, ucols, vrows = [], [], []
    for degree in sorted(set(degrees)):
        sources = [i for i,h in enumerate(degrees) if h == degree]
        targets = [i for i,h in enumerate(degrees) if h == degree+1]
        sub = [sum(((residual[t] >> s)&1) << j for j,s in enumerate(sources))
               for t in targets]
        u,v = gf2.rank_factor(sub,len(sources))
        for col,row in zip(gf2.transpose(u,len(v)),v):
            ucols.append(sum(((col >> j)&1) << t for j,t in enumerate(targets)))
            vrows.append(sum(((row >> j)&1) << s for j,s in enumerate(sources)))
            port_degrees.append(degree)
    r = len(port_degrees)
    urows = gf2.transpose(ucols,n)
    vcols = gf2.transpose(vrows,n)
    value = 0
    for t in range(n):
        value |= urows[t] << (t*r)
        value |= vcols[t] << ((n+t)*r)
    reg = product_register([[]],[value],2*n*r)
    return PortComplex((TemplateBlock(tuple(a),tuple(degrees),reg),),tuple(port_degrees))


def from_closed_fastscan(scan) -> PortComplex:
    """Duck-typed audit adapter for the inspected interned-list FastScan API.

    Refuses open frontiers, non-scalar coefficients, dead targets and inconsistent
    bookkeeping. This function does not authenticate that scan came from a knot.
    Tested with API-shaped fixtures and independent cube complexes, NOT a complete
    upstream checkout. Running it after full elimination is generally redundant.
    """
    if scan.points:
        raise ValueError('port rank adapter requires a closed frontier')
    if not (len(scan.mid) == len(scan.deg) == len(scan.out)):
        raise ValueError('inconsistent FastScan array lengths')
    live = [i for i,mid in enumerate(scan.mid) if mid is not None]
    if len(live) != scan.live:
        raise ValueError('inconsistent FastScan live count')
    if len({scan.mid[i] for i in live}) > 1:
        raise ValueError('closed frontier has different matching identifiers')
    numbering = {old:new for new,old in enumerate(live)}
    rows = [0]*len(live)
    degrees = [scan.deg[i] for i in live]
    for source in live:
        for target,coefficient in scan.out[source].items():
            if type(coefficient) is not int or coefficient not in (0,1):
                raise ValueError('non-scalar coefficient at closed frontier')
            if target not in numbering:
                raise ValueError('differential targets a cancelled object')
            if coefficient:
                rows[numbering[target]] ^= 1 << numbering[source]
    return from_dense(rows,degrees)
