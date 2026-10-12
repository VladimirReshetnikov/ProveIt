"""Additive input adapter for ProveIt report 91's graph-grammar.v1 schema.

Contract reviewed at commit d5c9a97fac1803258ea675297e4a7b22b78dd79b,
src/sparse_cuts.py blob 5ee84ac65474d315f50f0b1640094ec7a6da3450.
This is graph-schema compatibility, NOT an importer of native source geometry.
"""
from __future__ import annotations
from copy import deepcopy
from gauge_cuts import validate

def translate(source: dict, threshold: int=3) -> dict:
    if not isinstance(source,dict) or source.get('schema')!='proveit.graph-grammar.v1':raise ValueError('unsupported report-91 schema')
    nodes=source.get('nodes')
    if not isinstance(nodes,list) or not nodes:raise ValueError('missing nodes')
    out=[];widths=[]
    for i,z in enumerate(nodes):
        if not isinstance(z,dict):raise ValueError('bad node')
        terms=z.get('terminals');kind=z.get('kind')
        if not isinstance(terms,list) or any(type(t) is not int or t<0 for t in terms) or len(set(terms))!=len(terms):raise ValueError('bad terminals')
        if kind=='leaf':
            n=z.get('vertices');edges=z.get('edges');isolated=z.get('isolated_vertices',[])
            if type(n) is not int or n<1 or not isinstance(edges,list):raise ValueError('bad leaf inventory')
            seen=set(terms)
            for e in edges:
                if not isinstance(e,list) or len(e)!=3 or any(type(v) is not int or not 0<=v<n for v in e[:2]) or type(e[2]) is not int or e[2]<1:raise ValueError('bad source edge')
                seen.update(e[:2])
            if any(t>=n for t in terms):raise ValueError('bad terminal')
            if not isinstance(isolated,list) or any(type(v) is not int or not 0<=v<n for v in isolated) or len(set(isolated))!=len(isolated) or seen&set(isolated):raise ValueError('bad private isolated inventory')
            if n>1 and len(seen|set(isolated))!=n:raise ValueError('unlisted private vertices')
            # This allocation occurs only AFTER the explicit inventory bound.
            out.append({'op':'leaf','vertices':list(range(n)),'edges':deepcopy(edges),'terminals':terms[:]})
        elif kind in ('map','join'):
            ch=[z.get('child')] if kind=='map' else [z.get('left'),z.get('right')]
            maps=[z.get('mapping')] if kind=='map' else [z.get('left_map'),z.get('right_map')]
            if any(type(j) is not int or not 0<=j<i for j in ch):raise ValueError('non-acyclic source')
            out.append({'op':kind,'children':ch,'maps':deepcopy(maps),'keep':terms[:]})
        else:raise ValueError('unknown source operation')
        widths.append(len(terms))
    root=source.get('root',len(nodes)-1)
    if type(root) is not int or not 0<=root<len(nodes):raise ValueError('bad selected root')
    if root!=len(nodes)-1:
        r=widths[root];out.append({'op':'map','children':[root],'maps':[list(range(r))],'keep':list(range(r))})
    target={'k':threshold,'nodes':out};validate(target);return target
