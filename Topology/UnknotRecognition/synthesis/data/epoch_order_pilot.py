from unittest.mock import patch
from time import perf_counter
from fastunknot import Diagram
from fastunknot.normal_pachner_search import pachner_seed_decide
from fastunknot.normal_transport_verify import verify_transport_disk_certificate
from fastunknot.cocycle_transport import _collapse_region,_move_region,_region_heights,bipyramid_cocycle_score
from fastunknot.normal_surface_geometry import _EDGES
import fastunknot.pachner_cover_search as cover
from causal_research.native import diagram_cases
original=cover._events

def ordered(state,allow,check):
    positions={cell:i for i,cell in enumerate(state.cells)};items=[]
    for event in original(state,allow,check):
        check()
        if event.kind=='down':
            region=_collapse_region(state.raw['tetrahedra'],[(positions[c],*_EDGES[p])for c,p in event.ports],check)
        else:
            c,p=event.ports[0];region=_move_region(state.raw['tetrahedra'],dict(schema='pachner-23-v1',tetrahedron=positions[c],face=p))
        score=bipyramid_cocycle_score(_region_heights(region,state.heights,check))
        key=(0,-score['euler_loss'],-score['normal_disc_increase'],event.key)if event.kind=='down'else(1,score['euler_loss'],score['normal_disc_increase'],event.key)
        items.append((key,event))
    return tuple(event for _,event in sorted(items,key=lambda x:x[0]))

for name in ('optimized-positive','genus-one-miss','survivor-08','random-14'):
    source=next(s for s in diagram_cases()if s['name']==name);d=Diagram.from_pd(source['pd'])
    for policy in ('lexical','euler'):
        start=perf_counter()
        with patch.object(cover,'_events',side_effect=ordered if policy=='euler'else original):
            answer=pachner_seed_decide(d,max_upward=1,max_region_size=6,max_nodes=1000,max_work=2000000,shellings=True,optimize=True)
        if answer['status']=='UNKNOT':assert verify_transport_disk_certificate(d,answer['certificate'])
        print(name,policy,answer['status'],answer['work'],perf_counter()-start,answer['stats'].get('search'),flush=True)
