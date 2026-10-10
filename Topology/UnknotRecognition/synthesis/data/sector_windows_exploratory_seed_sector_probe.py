import json,sys,time
from pathlib import Path
ROOT=Path('/home/codex/.codex/worktrees/9348/Proofs/Topology/UnknotRecognition')
sys.path.insert(0,str(ROOT/'fast'))
from fastunknot import Diagram
from fastunknot.diagram_exterior import diagram_exterior
from fastunknot.normal_cocycle import _rank_one_cocycle_seed_details,_Budget,CocycleLimit
from fastunknot.cocycle_span import minimize_cocycle_span
from fastunknot.cocycle_trees import _prepared_tree_candidates
from fastunknot.sector_sparse import PreparedSectorSource
from fastunknot.normal_sector import sector_rays,_discover_in_kernel
from fastunknot.normal_seed_verify import verify_normal_seed_certificate
from fastunknot.integer_codec import json_safe
rows=json.load(open(ROOT/'synthesis/data/lex-audit.json'))['source_cases']
sources={r['source']['name']:r['source']for r in rows}
records=[]
for name in ['genus-one-miss','random-22','random-112','trefoil','figure-eight']:
 if name not in sources:sources[name]=dict(name=name,pd=Diagram.from_braid(3,[1,-2,1,-2]).pd,expected='KNOTTED')
 source=sources[name];d=Diagram.from_pd(source['pd']);raw=diagram_exterior(d);seed,prepared=_rank_one_cocycle_seed_details(raw);shared=PreparedSectorSource(raw)
 candidates=[('raw',seed['coordinates'])]
 candidates += [('tree'+str(c['trial']),c['coordinates'])for c in _prepared_tree_candidates(prepared,seed['heights'],trials=4,check=lambda:None)if not c['duplicate']]
 candidates.append(('optimized',minimize_cocycle_span(seed['vertices'],seed['heights'])['coordinates']))
 seen=set();out=[]
 for stage,coords in candidates:
  support=tuple((t,q)for t,row in enumerate(coords)for q in range(3)if row[4+q])
  if support in seen:continue
  seen.add(support);start=time.perf_counter();k=shared.build(support);dim=len(k.basis)
  entry=dict(stage=stage,support=support,allowed=len(support),dimension=dim,build_seconds=time.perf_counter()-start)
  print(name,stage,len(support),dim,flush=True)
  if dim<=3:
   budget=_Budget(lambda:None,500000);start=time.perf_counter()
   try:
    result=_discover_in_kernel(k,phase='standard',max_bases=1000,check=budget.tick);entry.update(status=result['status'],query_seconds=time.perf_counter()-start,stats=result['stats'])
    if result['status']=='DISC_FOUND':
     c=result['certificate'];outer=dict(schema='diagram-normal-disc-v1',input_pd=[list(r)for r in d.pd],triangulation=raw,coordinates=c['coordinates'],disc_certificate=c['disk_certificate'])
     assert verify_normal_seed_certificate(d,outer);entry['outer_certificate']=outer;print('DISC',name,stage,flush=True)
   except CocycleLimit:entry.update(status='CAPPED',work=budget.work)
  out.append(entry)
 records.append(dict(source=source,triangulation=raw,queries=out))
open('/tmp/unknot-seed-sector-probe.json','w').write(json.dumps(json_safe(records),indent=2)+'\n')
