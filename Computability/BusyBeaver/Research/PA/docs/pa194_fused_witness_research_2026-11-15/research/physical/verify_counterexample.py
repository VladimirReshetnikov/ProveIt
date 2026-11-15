#!/usr/bin/env python3
"""Literal proof replay: primary halts, while the 1-to-3 quotient has a zero ray."""
import json,hashlib
from pathlib import Path
import search_runtime as sr
HERE=Path(__file__).resolve().parent
def require(p,message):
    if not p:raise ValueError(message)
def verify(name,rows):
    r=json.loads((HERE/(name+'_physical_counterexample.json')).read_text())
    q,h,t=r['start'],r['initial_head'],set(r['initial_ones'])
    for k,tr in enumerate(r['trace']):
        bit=int(h in t)
        require([q,bit,*rows[q,bit]]==tr,('wrong transition',name,k))
        w,d,q=rows[q,bit]
        (t.add if w else t.discard)(h);h+=d
    require(len(r['trace'])==r['steps'],'wrong step count')
    require((q,h,sorted(t))==(r['state'],r['head'],r['ones']),'wrong endpoint')
    if r['classification']=='halt':require(q==254,'not halted')
    elif r['classification']=='left_zero_ray':
        require(rows[q,0]==(0,-1,q),'not an unchanged-zero left self-loop')
        require(not t or h<min(t),'nonzero tape ahead of left ray')
    else:raise ValueError('unproved endpoint')
    return {'name':name,'steps':r['steps'],'classification':r['classification'],'state':q,'head':h,'ones':len(t)}
original=verify('primary',sr.M)
mutant=sr.merge(1,3,[1,0]);bad=verify('merge1_3',mutant);blank=verify('merge1_3_blank',mutant)
require(len(mutant)==386,'wrong rejected state count')
require(original['classification']=='halt' and bad['classification']=='left_zero_ray','not a halting inequivalence')
result={'status':'verified explicit runtime inequivalence','initial_site':0,'register_values':[0]*10,'primary':original,'rejected_193':bad,'rejected_blank_start':blank,'proof':'Once left of the complete finite support, the 0-L-self-loop preserves all tape cells and moves left forever; induction proves nonhalting.'}
(HERE/'counterexample_replay_receipt.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
