"""Exact minimum port count, preserving degree, register lengths and widths.

This minimizes rank-one channels for the SUPPLIED base A: r_min=rank(D-A).
It does not optimize the choice of A or the Boolean register representation.
"""
from __future__ import annotations
from . import gf2
from .automata import Register
from .complexes import TemplateBlock, PortComplex, analyze, _fields


def minimize_ports(c: PortComplex) -> tuple[PortComplex, dict]:
    analyze(c)  # includes symbolic degree and square-zero validation
    r=c.ports
    evals=[(b.size,b.register.reachable()['evaluation_rows']) for b in c.blocks]
    group_data=[]
    new_degrees=[]
    umap=[0]*r;vtmap=[0]*r
    for degree in sorted(set(c.port_degrees)):
        js=[j for j,h in enumerate(c.port_degrees) if h==degree]
        k=len(js)
        def restrict(value):return sum(((value >> j)&1) << i for i,j in enumerate(js))
        urows=[];vcols=[]
        for d,values in evals:
            for value in values:
                u,v=_fields(value,d,r)
                urows.extend(restrict(x) for x in u)
                vcols.extend(restrict(x) for x in v)
        p=gf2.independent(urows)
        qcols=gf2.independent(vcols)
        q=gf2.transpose(qcols,k)
        middle=gf2.mul(p,q)
        s,t=gf2.rank_factor(middle,len(qcols))
        hp,_=gf2.generalized_inverse(p,k)
        hq,_=gf2.generalized_inverse(q,len(qcols))
        utransform=gf2.mul(hp,s)
        vtransform_t=gf2.transpose(gf2.mul(t,hq),k)
        offset=len(new_degrees)
        for i,j in enumerate(js):
            umap[j]=utransform[i] << offset
            vtmap[j]=vtransform_t[i] << offset
        new_degrees.extend([degree]*len(t))
        group_data.append({'degree':degree,'old_ports':k,
                           'u_rank':len(p),'v_rank':len(qcols),
                           'update_rank':len(t),'interaction_rows':middle,
                           'interaction_columns':len(qcols)})
    nr=len(new_degrees)
    blocks=[]
    for b in c.blocks:
        new_outputs=[]
        for output in b.register.outputs:
            uu,vv=_fields(output,b.size,r)
            value=0
            for i in range(b.size):
                value |= gf2.row_mul(uu[i],umap) << (i*nr)
                value |= gf2.row_mul(vv[i],vtmap) << ((b.size+i)*nr)
            new_outputs.append(value)
        reg=Register(b.register.widths,b.register.transitions,b.register.initial,
                     tuple(new_outputs),2*b.size*nr)
        blocks.append(TemplateBlock(b.differential,b.degrees,reg))
    result=PortComplex(tuple(blocks),tuple(new_degrees))
    return result, {'old_ports':r,'minimum_ports_for_fixed_base':nr,'groups':group_data,
                    'scope':'Exact rank of D-A; does not optimize A or register width.'}
