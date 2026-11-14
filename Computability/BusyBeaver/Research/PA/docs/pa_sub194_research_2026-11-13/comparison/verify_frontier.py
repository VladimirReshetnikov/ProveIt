#!/usr/bin/env python3
"""Verify the complete42-class194-state literal frontier without Git/network.
Does not prove machine behavior, Con(PA) calibration, or a state lower bound.
"""
from pathlib import Path
import json,hashlib,collections
from machine_classes import classify
HERE=Path(__file__).resolve().parent
records=json.loads((HERE/'frontier42.json').read_text())
seen=set()
for r in records:
 b=(HERE/r['table']).read_bytes()
 if hashlib.sha256(b).hexdigest()!=r['sha256']:raise ValueError('bytes: '+r['table'])
 i=classify(b)
 if i['states']!=194 or len(i['halting'])!=1:raise ValueError('shape: '+r['table'])
 if i['table']!=r['graph_class']:raise ValueError('graph: '+r['table'])
 if i['table'] in seen:raise ValueError('duplicate graph: '+r['table'])
 seen.add(i['table'])
if len(seen)!=42:raise ValueError('frontier must cover42 graph classes')
counts=dict(collections.Counter(r['status'] for r in records))
if counts!={'reported construction':28,'auxiliary':9,'rejected':5}:raise ValueError(counts)
print(json.dumps({'status':'PASS','working_states':194,'distinct_transition_graphs':len(seen),'reported_status_counts':counts,'comparison':'Any spanning start; exact write/read symbols and L/R.','scope':'Byte integrity, table shape and structural identity only. Report-derived evidence categories not freshly re-proved.'},indent=2))
