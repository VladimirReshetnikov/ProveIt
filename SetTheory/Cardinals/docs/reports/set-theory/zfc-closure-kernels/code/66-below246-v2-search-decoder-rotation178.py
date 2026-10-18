#!/usr/bin/env python3
"""Test the one-state association (23,(24,206)) -> ((23,24),206)."""
from pathlib import Path
from functools import lru_cache
import json, time
import explore as e
import review_affine_source as review

HERE=Path(__file__).resolve().parent
before=e.STATES[178][0]
assert e.T[178,0]==(0,'R',23)and e.T[178,1]==(1,'R',208)
assert e.T[208,0]==(0,'R',24)and e.T[208,1]==(1,'R',206)
assert e.T[16,0]==(0,'R',23)and e.T[16,1]==(1,'R',24)
assert e.INCOMING[208]==[(178,1)]
after=('N',e.STATES[16][0],e.STATES[206][0])
assert before==('N',after[1][1],('N',after[1][2],after[2]))
assert all(e.bc(t)==(0,0)for t in(before[1],before[2][1],before[2][2]))
@lru_cache(None)
def replace(t):
    if t==before:return after
    return t if t[0]=='L'else('N',replace(t[1]),replace(t[2]))
new=replace(e.ORIGINAL)
table=e.T.copy();table[178,0]=(0,'R',16);table[178,1]=(1,'R',206)
del table[208,0];del table[208,1]
rows=''.join(f'{q} {b} {w} {d} {t}\n'for(q,b),(w,d,t)in sorted(table.items()))
(HERE/'rotation178_245_old.tm').write_text(rows)
sites=[];logical=[]
for p,edge in e.paths(new):
    op=edge[0];arg=edge[1]if len(edge)>1 else None
    code=dict(inc='CI',dec='CD',brk='CB',cont='CC',halt='CH')[op]
    logical.append((p,code,arg));sites.append((p,code,e.PHYSICAL[arg]if code in('CI','CD')else arg))
(HERE/'rotation178_sites_physical.json').write_text(json.dumps(sites)+'\n')
(HERE/'rotation178_sites_logical.json').write_text(json.dumps(logical)+'\n')
started=time.monotonic();cert=e.rmpath.certificate(e.ORIGINAL,new)
def bits(p):return ''.join('1'if x else'0'for x in p)
(HERE/'rotation178_bisimulation.json').write_text(json.dumps(dict(
    status='REGISTER_PROGRAM_BISIMULATION_ONLY; TM candidate fails context checks',
    start_pair=0,entries=[[bits(a),bits(b),nz,z]for a,b,nz,z in cert]),indent=2)+'\n')
out=dict(status='PENDING',states=245,rm_bisimulation_entries=len(cert),
    old_max_zero_run=e.maxzeros(e.ORIGINAL),new_max_zero_run=e.maxzeros(new),
    max_leaf_depth=max(len(p)for p,_,_ in sites),
    table_edits={'178/0':'0 R 16','178/1':'1 R 206'},deleted_state=208)
affine=review.module(e.BASE/'sources/prior/prefix_affine.py')
oldrun=affine.run
def checked_run(table,pc,branch,*args,**kwargs):
    try:return oldrun(table,pc,branch,*args,**kwargs)
    except Exception as err:raise AssertionError(('site',pc,branch,repr(err)))from err
affine.run=checked_run
try:
    out['affine']=review.check_sites(affine,{(str(q),b):(w,d,str(t))for(q,b),(w,d,t)in table.items()},sites)
    out['status']='PASS'
except Exception as err:out['status']='FAIL';out['error']=repr(err)
out['seconds']=time.monotonic()-started
(HERE/'rotation178_result.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
