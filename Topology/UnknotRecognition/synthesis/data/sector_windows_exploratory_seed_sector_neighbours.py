import json,sys,time
from pathlib import Path
ROOT=Path('/home/codex/.codex/worktrees/9348/Proofs/Topology/UnknotRecognition');sys.path.insert(0,str(ROOT/'fast'))
from fastunknot import Diagram
from fastunknot.diagram_exterior import diagram_exterior
from fastunknot.normal_cocycle import _rank_one_cocycle_seed_details,_Budget,CocycleLimit
from fastunknot.cocycle_span import minimize_cocycle_span
from fastunknot.sector_sparse import PreparedSectorSource
from fastunknot.normal_sector import _discover_in_kernel
from fastunknot.normal_seed_verify import verify_normal_seed_certificate
from fastunknot.integer_codec import json_safe
rows=json.load(open(ROOT/'synthesis/data/lex-audit.json'))['source_cases'];lookup={r['source']['name']:r['source']for r in rows}
result=[]
for name in ['genus-one-miss','random-22','random-112','trefoil']:
 s=lookup[name];d=Diagram.from_pd(s['pd']);raw=diagram_exterior(d);seed,prep=_rank_one_cocycle_seed_details(raw);shared=PreparedSectorSource(raw)
 opt=minimize_cocycle_span(seed['vertices'],seed['heights'])['coordinates'];seen=set();records=[];found=False;start=time.perf_counter()
 for stage,coords in [('optimized',opt),('raw',seed['coordinates'])]:
  base=tuple(next((q for q in range(3)if row[4+q]),-1)for row in coords)
  k0=shared.build([(i,q)for i,q in enumerate(base)if q>=0]);d0=len(k0.basis)
  for t in range(len(base)):
   for q in (-1,0,1,2):
    if q==base[t]:continue
    signature=base[:t]+(q,)+base[t+1:]
    if signature in seen:continue
    seen.add(signature);allowed=[(i,z)for i,z in enumerate(signature)if z>=0];k=shared.build(allowed);dim=len(k.basis);assert dim<=d0+1
    entry=dict(stage=stage,tetrahedron=t,old_type=base[t],new_type=q,dimension=dim,support=allowed)
    budget=_Budget(lambda:None,300000)
    if dim<=3:
     try:
      a=_discover_in_kernel(k,phase='standard',max_bases=100,check=budget.tick);entry.update(status=a['status'],stats=a['stats'])
      if a['status']=='DISC_FOUND':
       c=a['certificate'];proof=dict(schema='diagram-normal-disc-v1',input_pd=[list(r)for r in d.pd],triangulation=raw,coordinates=c['coordinates'],disc_certificate=c['disk_certificate']);assert verify_normal_seed_certificate(d,proof);entry['proof']=proof;found=True;print('DISC',name,stage,t,base[t],q,dim,flush=True)
     except CocycleLimit:entry.update(status='CAPPED',work=budget.work)
    records.append(entry)
    if found:break
   if found:break
  if found:break
 print(name,'queries',len(records),'found',found,'seconds',time.perf_counter()-start,flush=True)
 result.append(dict(source=s,triangulation=raw,records=records,found=found,seconds=time.perf_counter()-start))
open('/tmp/unknot-seed-sector-neighbours.json','w').write(json.dumps(json_safe(result),indent=2)+'\n')
