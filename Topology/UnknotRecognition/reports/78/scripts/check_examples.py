#!/usr/bin/env python3
import sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'src'))
from span_excess import HeightModel,replay_band,replay_edge_then_span
from span_excess.jsonio import load
from span_excess.pachner import replay_history
from span_excess.geometry import expand_surface
for name in ('interval_band.json','solid_torus_band.json'):
    p=load(ROOT/'examples'/name)
    assert replay_band(HeightModel.from_dict(p['model']),p['answer'])
    print(name, 'complete arithmetic replay passed')
for i,p in enumerate(load(ROOT/'examples/transported_solid_tori.json')):
    g=replay_history(p['geometry']['history']);m=HeightModel.from_dict(p['model'])
    assert tuple(g.tetrahedra)==m.vertices and tuple(g.heights)==m.heights
    assert g.n==m.n
    # Reconstruct the geometric edge objective, not just the supplied arithmetic.
    _,c,d=g.incidence()
    assert m.edges==tuple((a,b,w,d[(a,b)]-2) for (a,b),w in sorted(c.items()))
    assert replay_edge_then_span(m,p['lexicographic'])
    s=expand_surface(g,p['lexicographic']['potential'])
    assert len(s['components'])==1 and 2*s['euler']==p['lexicographic']['score2']
    print('transported solid torus',i,'geometry, arithmetic, and literal mesh replay passed')
