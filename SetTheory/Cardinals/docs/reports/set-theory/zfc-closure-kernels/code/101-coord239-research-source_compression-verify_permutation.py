from pathlib import Path
import sys,time,json,hashlib
import independent_runtime as r
import symbolic_runtime as s
from collections import Counter
if not __debug__:raise RuntimeError('Assertions must be enabled.')
a,b=map(int,sys.argv[1:3]);perm=list(range(9));perm[a],perm[b]=b,a
r.PHY=tuple(perm[x]for x in (6,2,0,4,3,7,8,5,1));name=f'perm_{a}_{b}'
T=r.table(name+'.tm');S=json.loads(Path('sites_logical.json').read_text());lemmas,blocks=s.prove_blocks(T)
t0=time.monotonic();count=0;rules=0;rows=set();minimum=None;opcounts=Counter()
for i,site in enumerate(S):
 for pos in ([False,True]if site[1]=='CD'else[False]):
  try:ans=s.case(T,lemmas,site,pos)
  except Exception as exc:
   result=dict(status='FAIL',site_index=i,site=site,positive=pos,message=str(exc),passed=count)
   Path(name+'_full_runtime.json').write_text(json.dumps(result,indent=2)+'\n');print(result,flush=True);raise
  count+=1;rules+=ans['symbolic_steps'];rows|=ans['rows'];minimum=ans['duration'][0]if minimum is None else min(minimum,ans['duration'][0]);opcounts[site[1]]+=1
 if i%1000==0:print('PASS',i,count,round(time.monotonic()-t0,2),flush=True)
assert count==8386
result=dict(status='PASS_ALL_UNBOUNDED_INSTRUCTION_CASES',swap=[a,b],physical=list(r.PHY),working_states=len(T)//2,guarded_cases=count,symbolic_steps=rules,used_rows=len(rows),minimum_constant_steps=minimum,operation_counts=dict(opcounts),block_lemmas=blocks,sha256=hashlib.sha256(Path(name+'.tm').read_bytes()).hexdigest(),source_sha256=hashlib.sha256(Path('sites_logical.json').read_bytes()).hexdigest(),seconds=time.monotonic()-t0,scope='Literal steps, unary-loop induction, and generic finite-block-list induction on nine independent arbitrary registers, arbitrary nonempty spare list, and every source instruction case. Ordinary executable mathematical certificate; not a proof-assistant kernel theorem.')
Path(name+'_full_runtime.json').write_text(json.dumps(result,indent=2)+'\n');print({k:v for k,v in result.items()if k!='block_lemmas'},flush=True)
