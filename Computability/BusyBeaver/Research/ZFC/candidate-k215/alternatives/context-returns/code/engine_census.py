#!/usr/bin/env python3
"""Recompute engine row usage after the last source selector bit.

This is a synthesis filter. Every candidate must separately pass the complete
symbolic primitive proof and blank startup, and its source must be calibrated.
"""
import json, sys, time, argparse, hashlib
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / 'upstream'
ap = argparse.ArgumentParser(description=__doc__)
ap.add_argument('--table',type=Path,default=BASE/'k215.native.tm')
ap.add_argument('--sites',type=Path,default=ROOT/'machine/sites215.json')
ap.add_argument('--output',type=Path,required=True)
a = ap.parse_args()
sys.path.insert(0, str(ROOT / 'code/runtime-inputs/runtime'))
import symbolic_runtime as s

T = s.r.table(a.table)
mapping = {int(k): int(v) for k,v in json.loads((ROOT/'code/runtime-inputs/inputs/legacy_mapping.json').read_text()).items()}
for q in {q for q,b in T}|{254}:
    mapping.setdefault(q,q+1000)
inverse = {v:k for k,v in mapping.items()}
L = {(mapping[q],b):(w,d,mapping[z]) for (q,b),(w,d,z) in T.items()}
lemmas,blocks=s.prove_blocks(L)
protected=set()
blockrows=set()
for bl in blocks:
    for event in bl['trace']:
        if event[0]!='list':blockrows.add((inverse[event[1][0]],event[1][1]))
protected.update(blockrows)
allrows=set(); decoded=set(); leafacts={}; counts={}; sites=json.loads(a.sites.read_text())
start=time.monotonic(); rules=0
for i,site in enumerate(sites):
    pc,op,arg=site
    for positive in ((False,True) if op=='CD' else (False,)):
        ans=s.case(L,lemmas,site,positive,keep_trace=True)
        rules+=ans['symbolic_steps']
        motion=s.ZERO; phase='decode'; got=False
        for event in ans['trace']:
            if event[0]=='list':
                key=event[1];motion=s.add(motion,s.var(12) if key[1]==1 else s.neg(s.var(12)));continue
            kind,row=event[:2]
            native=(inverse[row[0]],row[1]); allrows.add(native)
            if native[0]==84 and motion==s.ZERO:
                phase='decode'
            if phase=='decode' and motion==s.num(len(pc)-1):
                got=True;phase='entry'
                leafacts.setdefault((op,arg,int(pc[-1])),set()).add((row[2],row[3],inverse[row[4]]))
            if phase=='engine':
                protected.add(native);counts[native]=counts.get(native,0)+1
            elif phase=='decode':decoded.add(native)
            width=s.num(1) if kind=='literal' else event[2]
            motion=s.add(motion,width if row[3]==1 else s.neg(width))
            if phase=='entry':phase='engine'
        assert got,site
    if (i+1)%1000==0:print(i+1,len(protected),round(time.monotonic()-start,2),flush=True)
out={'status':'ALL_PRIMITIVES_REDERIVED','scope':'Engine row synthesis filter only; last source selector edge excluded.',
     'sites':len(sites),'cases':sum(2 if x[1]=='CD' else 1 for x in sites),'rules':rules,
     'rows':sorted(protected),'blockrows':sorted(blockrows),'decode_rows':sorted(decoded),
     'allrows':sorted(allrows),'leafactions':[[op,arg,bit,[list(a)for a in sorted(acts)]]for(op,arg,bit),acts in leafacts.items()],
     'seconds':time.monotonic()-start}
out['table_sha256']=hashlib.sha256(a.table.read_bytes()).hexdigest()
out['sites_sha256']=hashlib.sha256(a.sites.read_bytes()).hexdigest()
path=a.output;path.parent.mkdir(parents=True,exist_ok=True);path.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items()if k not in('rows','blockrows','decode_rows','allrows','leafactions')},indent=2))
print('engine_states',len({q for q,b in protected}),'decoder_only',sorted({q for q,b in T}-{q for q,b in protected}))
