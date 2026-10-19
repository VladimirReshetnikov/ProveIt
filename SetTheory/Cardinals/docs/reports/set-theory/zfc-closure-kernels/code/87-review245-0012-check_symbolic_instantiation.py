"""Concrete cross-check of our self-authored symbolic proof constructor.
This file tests implementation; it is not a premise for quantified induction.
"""
import random,json
import independent_runtime as r
import symbolic_runtime as s
rng=random.Random(20261018)
t=r.table(r.BASE/'candidate-routing245/zfc_routing245_old.tm');lemmas,_=s.prove_blocks(t)
ss=json.loads((r.BASE/'certificate__sites_logical.json').read_text())
checks=[]
for index in [0,1,41,894,6459]+rng.sample(range(len(ss)),95):
 site=ss[index]
 for pos in ((False,True) if site[1]=='CD' else (False,)):
  answer=s.case(t,lemmas,site,pos)
  regs=[rng.randrange(15) for _ in range(9)];spares=[rng.randrange(10) for _ in range(rng.randrange(1,6))];gap=rng.randrange(0,80)
  if site[1]=='CD':regs[site[2]]=rng.randrange(1,16) if pos else 0
  variables=[1,gap]+regs+[spares[0],sum(2+v for v in spares[1:])]
  if site[1]=='CD':variables[2+site[2]]=regs[site[2]]-1 if pos else 0
  predicted_steps=sum(a*b for a,b in zip(answer['duration'],variables))
  predicted_motion=sum(a*b for a,b in zip(answer['motion'],variables))
  actual,steps,_=r.run(t,site[0],regs,spares,gap,limit=100000)
  wanted=r.expected(site,regs,spares,gap)
  assert steps==predicted_steps,(index,site,pos,steps,predicted_steps)
  assert actual[1]==predicted_motion,(index,actual[1],predicted_motion)
  assert actual[0]==254 if wanted is None else actual==wanted[0]
  checks.append({'site_index':index,'positive':pos,'actual_steps':steps,'symbolic_steps_instantiated':predicted_steps})
# Replay two sparse witness traces independently on a dense tape.
for name in ['obvious244_witness_41','scanner244_witness_41']:
 w=json.loads((r.OUT/(name+'.json')).read_text());offset=100000;cells=bytearray(200001)
 for x in r.frame(w['site'][0],w['registers'],w['spares']):cells[offset+x]=1
 q=96;p=offset
 for tick,before,head,read,write,d,target in w['trace']:
  assert q==before and p-offset==head and cells[p]==read
  cells[p]=write;p+=d;q=target
 actual={'state':q,'head':p-offset,'ones':[i-offset for i,x in enumerate(cells) if x]}
 assert actual==w['actual']
report={'status':'PASS','symbolic_duration_and_full_tape_instantiations':len(checks),'dense_witness_replays':2,'scope':'Implementation cross-check only; universal argument uses symbolic induction rules','checks':checks}
(r.OUT/'symbolic_implementation_crosschecks.json').write_text(json.dumps(report,indent=2)+'\n')
print({k:v for k,v in report.items() if k!='checks'})
