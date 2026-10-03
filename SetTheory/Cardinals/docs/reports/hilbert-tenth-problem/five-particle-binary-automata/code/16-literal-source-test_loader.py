#!/usr/bin/env python3
import json
from pathlib import Path
from loader import from_tape,from_counters,five_particle_input,target_ledger
R=Path(__file__).resolve().parent
count=0

def reject(fn,*args,**kwargs):
    global count
    try:fn(*args,**kwargs)
    except (TypeError,ValueError):count+=1;return
    raise RuntimeError('Invalid input accepted')
for x in (-1,True,1.0,'1',None):
    reject(from_counters,x,0);reject(from_counters,0,x);reject(from_counters,0,0,x);reject(from_counters,0,0,0,x)
for x in (0,2,3,5,7,11,2310):reject(from_counters,0,0,cofactor=x)
for x in ('2','10x',2,False,None):reject(from_tape,x,'');reject(from_tape,'',x)
for a,b in [(0,0),(7,0),(11,0),(1,1),(True,0),(1,False),(-1,0),(1.0,0),('1',0)]:reject(five_particle_input,dict(control='START',counter0=a,counter1=b))
reject(five_particle_input,dict(control='HALT',counter0=1,counter1=0))
reject(five_particle_input,dict(control='START',counter0=1,counter1=0,extra=0))
reject(five_particle_input,from_tape('',''),ledger={'Z':0,'S':0})
for a in (1,2,3,5,13,30,169):
    coords=five_particle_input(dict(control='START',counter0=a,counter1=0))
    if len(set(coords))!=5:raise RuntimeError('Particle count')
g=target_ledger();g['Z']=0
if target_ledger()['Z']!=20380380:raise RuntimeError('Ledger mutation leaked')
out=dict(status='passed',invalid_inputs_rejected=count,clean_inputs_accepted=7,caller_ledger_override='removed',source_identity='SHA256 pinned before deriving constants')
(R/'loader-api-receipt.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
