#!/usr/bin/env python3
"""A state-neutral association using an already present decoder pair.

This is a search experiment, not a smaller machine. It tests whether local
source association and a literal table edit can survive all-site replay.
"""
from pathlib import Path
from functools import lru_cache
import json, time
import explore as e
import review_affine_source as review

HERE=Path(__file__).resolve().parent
before=e.STATES[226][0]
assert len(e.STATES[226])==len(e.STATES[193])==len(e.STATES[207])==1
assert e.T[226,0] == (0,'R',193) and e.T[226,1] == (1,'R',231)
assert e.T[193,0] == (0,'R',190) and e.T[193,1] == (1,'R',213)
assert e.T[207,0] == (0,'R',213) and e.T[207,1] == (1,'R',231)
after=('N',e.STATES[190][0],e.STATES[207][0])
assert before==('N',('N',after[1],after[2][1]),after[2][2])
assert e.bc(after[1])[0]==0 and e.bc(before[2])[1]==0

@lru_cache(None)
def replace(t):
    if t==before:return after
    if t[0]=='L':return t
    return ('N',replace(t[1]),replace(t[2]))

new=replace(e.ORIGINAL)
cert=e.rmpath.certificate(e.ORIGINAL,new)
table=e.T.copy();table[226,0]=(0,'R',190);table[226,1]=(1,'R',207)
rows=''.join(f'{q} {b} {w} {d} {t}\n'for(q,b),(w,d,t)in sorted(table.items()))
(HERE/'rotation226_246_old.tm').write_text(rows)
sites=[]
for p,edge in e.paths(new):
    op=edge[0];arg=edge[1] if len(edge)>1 else None
    code=dict(inc='CI',dec='CD',brk='CB',cont='CC',halt='CH')[op]
    sites.append((p,code,e.PHYSICAL[arg] if code in ('CI','CD') else arg))
(HERE/'rotation226_sites_physical.json').write_text(json.dumps(sites)+'\n')
affine=review.module(e.BASE/'sources/prior/prefix_affine.py')
started=time.monotonic()
out=dict(status='PENDING',states=246,rm_bisimulation_entries=len(cert),
    old_max_zero_run=e.maxzeros(e.ORIGINAL),new_max_zero_run=e.maxzeros(new),
    table_edits={'226/0':'0 R 190','226/1':'1 R 207'},
    remaining_incoming_193=[x for x in e.INCOMING[193] if x!=(226,0)])
try:
    out['affine']=review.check_sites(affine,{(str(q),b):(w,d,str(t))for(q,b),(w,d,t)in table.items()},sites)
    out['status']='PASS'
except Exception as err:
    out['status']='FAIL';out['error']=repr(err)
out['seconds']=time.monotonic()-started
(HERE/'rotation226_result.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
