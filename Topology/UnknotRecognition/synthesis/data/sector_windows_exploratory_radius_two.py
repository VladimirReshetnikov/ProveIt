import json,sys,time,itertools
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
s=next(r['source']for r in json.load(open(ROOT/'synthesis/data/lex-audit.json'))['source_cases']if r['source']['name']=='genus-one-miss');d=Diagram.from_pd(s['pd']);raw=diagram_exterior(d);seed,prep=_rank_one_cocycle_seed_details(raw);shared=PreparedSectorSource(raw)
coords=minimize_cocycle_span(seed['vertices'],seed['heights'])['coordinates'];base=tuple(next((q for q in range(3)if row[4+q]),-1)for row in coords);d0=len(shared.build([(i,q)for i,q in enumerate(base)if q>=0]).basis)
rows=[];start=time.perf_counter();found=None
for positions in itertools.combinations(range(len(base)),2):
 for choices in itertools.product(*[tuple(q for q in (-1,0,1,2)if q!=base[t])for t in positions]):
  signature=list(base)
  for t,q in zip(positions,choices):signature[t]=q
  allowed=[(t,q)for t,q in enumerate(signature)if q>=0];k=shared.build(allowed);dim=len(k.basis);assert dim<=d0+2
  budget=_Budget(lambda:None,300000)
  try:a=_discover_in_kernel(k,phase='standard',max_bases=100,check=budget.tick)
  except CocycleLimit:a=dict(status='CAPPED',stats={},work=budget.work)
  r=dict(positions=positions,choices=choices,dimension=dim,status=a['status'],rays=a.get('stats',{}).get('emitted_rays'),work=budget.work);rows.append(r)
  if a['status']=='DISC_FOUND':
   c=a['certificate'];found=dict(schema='diagram-normal-disc-v1',input_pd=[list(x)for x in d.pd],triangulation=raw,coordinates=c['coordinates'],disc_certificate=c['disk_certificate']);assert verify_normal_seed_certificate(d,found);print('DISC',positions,choices,flush=True);break
  if len(rows)%1000==0:print('queries',len(rows),'seconds',time.perf_counter()-start,flush=True)
 if found:break
answer=dict(source=s,triangulation=raw,base_signature=base,base_nullity=d0,radius=2,records=rows,proof=found,seconds=time.perf_counter()-start)
open('/tmp/unknot-radius-two.json','w').write(json.dumps(json_safe(answer),indent=2)+'\n');print('COMPLETE',len(rows),bool(found),answer['seconds'],flush=True)
