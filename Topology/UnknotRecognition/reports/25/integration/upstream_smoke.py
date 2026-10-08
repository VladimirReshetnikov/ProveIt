#!/usr/bin/env python3
"""UNEXECUTED HERE: optional checked-Diagram/provenance adapter smoke test.

This does not time or run the complete recognizer, test all backends, or replace
its maintained regression suite. Usage:
python integration/upstream_smoke.py --upstream /path/to/UnknotRecognition/fast
"""
import argparse
import json
import sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
p=argparse.ArgumentParser();p.add_argument('--upstream',required=True);args=p.parse_args()
upstream=Path(args.upstream).resolve()
if not (upstream/'fastunknot'/'diagram.py').is_file():
    p.error('--upstream must name the maintained fast/ directory')
sys.path.insert(0,str(ROOT));sys.path.insert(0,str(upstream));sys.path.insert(0,str(Path(__file__).resolve().parent))
from fastunknot import Diagram
from cyclic_garside.oracles import old_barrier, geodesic_unknot
from probe import propose

cases=[('old_h1',4,old_barrier(1),3),('old_h4',4,old_barrier(4),3),
       ('geodesic_m5',3,geodesic_unknot(5),2)]
for m in (2,8):
    w=(-1,)*m+(3,)*m+(1,)*(m+1)+(-3,)*(m-1)+(2,)
    cases.append((f'rectangle_m{m}',4,w,3))
for name,b,word,k in cases:
    original=Diagram.from_braid(b,word)
    out=propose(original,radius=2,max_ticks=None,max_targets=None)
    assert out.status=='candidate', (name,out.status,out.reason)
    assert out.candidate.crossings==k
    assert out.candidate.braid_source[0]==b
    print(json.dumps(dict(case=name,status=out.status,input=len(word),output=k)))
# A PD-derived diagram has no checked source and must bypass the probe.
original=Diagram.from_braid(3,(1,2))
plain=Diagram.from_pd(original.pd)
assert propose(plain).status=='skipped'
print(json.dumps(dict(adapter_smoke='passed',complete_recognizer_tested=False)))
