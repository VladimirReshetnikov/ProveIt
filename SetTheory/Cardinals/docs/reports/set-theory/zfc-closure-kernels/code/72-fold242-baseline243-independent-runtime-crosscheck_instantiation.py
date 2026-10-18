"""Independent concrete cross-check; no candidate scripts executed/imported."""
from pathlib import Path
import json,random,sys,hashlib
if not __debug__ or sys.flags.optimize:raise RuntimeError('Enabled assertions required')
import independent_runtime as r
import symbolic_runtime as s
P=Path(__file__).resolve().parent
T=P.parent/'sources/candidate-combined243__zfc_combined243_old.tm'
t=r.table(T);lemmas,_=s.prove_blocks(t)
ss=json.loads((P.parent/'sources/candidate-combined243__sites_logical.json').read_text())
rng=random.Random(24320261018);checks=[]
for index in [0,1,6,7,8,41,893,6323,6458]+rng.sample(range(len(ss)),95):
 site=ss[index]
 for pos in ((False,True) if site[1]=='CD' else (False,)):
  answer=s.case(t,lemmas,site,pos)
  regs=[rng.randrange(25) for _ in range(9)];spares=[rng.randrange(20) for _ in range(rng.randrange(1,10))];gap=rng.randrange(100)
  if site[1]=='CD':regs[site[2]]=rng.randrange(1,26) if pos else 0
  vs=[1,gap]+regs+[spares[0],sum(2+v for v in spares[1:])]
  if site[1]=='CD':vs[2+site[2]]=regs[site[2]]-1 if pos else 0
  duration=sum(a*b for a,b in zip(answer['duration'],vs));motion=sum(a*b for a,b in zip(answer['motion'],vs))
  actual,n,_=r.run(t,site[0],regs,spares,gap,limit=100000)
  want=r.expected(site,regs,spares,gap)
  assert n==duration and actual[1]==motion
  assert actual[0]==254 if want is None else actual==want[0]
  # Separately implemented dense tape, run for the mathematically derived time.
  initial=r.frame(site[0],regs,spares,gap);low=min(initial)-duration-2;high=max(initial)+duration+2
  cells=bytearray(high-low+1)
  for x in initial:cells[x-low]=1
  h=-low;q=96
  for _ in range(duration):
   w,d,target=t[q,cells[h]];cells[h]=w;h+=d;q=target
  dense=(q,h+low,{i+low for i,b in enumerate(cells) if b})
  assert dense==actual
  checks.append({'site_index':index,'positive':pos,'duration':duration,'sparse_dense_full_tape_equal':True})
result={'status':'PASS','symbolic_duration_and_motion_instantiations':len(checks),'dense_sparse_entire_tape_checks':len(checks),'table_sha256':hashlib.sha256(T.read_bytes()).hexdigest(),'scope':'Additional finite implementation testing; not the premise for quantified runtime proof','checks':checks}
(P/'runtime_crosschecks.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='checks'},indent=2))
