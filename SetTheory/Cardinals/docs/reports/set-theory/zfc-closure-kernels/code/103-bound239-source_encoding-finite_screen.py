"""Finite all-site sanity screen; this does not replace quantified runtime proof.

Uses the independent literal TM interpreter shipped unchanged in ../validation.
Default inputs are the deliberately rejected direct reassociation attempt.
"""
from pathlib import Path
import argparse,sys,json,importlib.util,time
sys.dont_write_bytecode=True
H=Path(__file__).resolve().parent
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('machine',nargs='?',type=Path,default=H/'reassoc239_old.tm')
p.add_argument('sites',nargs='?',type=Path,default=H/'reassoc239_sites.json')
p.add_argument('--output',type=Path)
p.add_argument('--limit',type=int,default=10000)
a=p.parse_args()
lib=H.parent/'validation/independent_runtime.py'
spec=importlib.util.spec_from_file_location('independent_runtime',lib)
r=importlib.util.module_from_spec(spec);spec.loader.exec_module(r)
tab=r.table(a.machine);ss=json.loads(a.sites.read_text());fail=[];total=0;start=time.time()
for site in ss:
 for pos in ((False,True) if site[1]=='CD' else (False,)):
  regs=[0]*9
  if pos:regs[site[2]]=1
  target=r.expected(site,regs,[0]);actual,steps,_=r.run(tab,site[0],regs,limit=a.limit)
  good=(actual[0]==254) if target is None else actual==target[0]
  total+=1
  if not good:fail.append(dict(index=total-1,site=site,positive=pos,steps=steps,laststate=actual[0],lasthead=actual[1]))
result=dict(scope='FINITE_SANITY_ONLY',cases=total,failed=len(fail),failures=fail,seconds=time.time()-start)
if a.output:
 a.output.write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({k:v for k,v in result.items() if k!='failures'}))
else:print(json.dumps(result,indent=2))
