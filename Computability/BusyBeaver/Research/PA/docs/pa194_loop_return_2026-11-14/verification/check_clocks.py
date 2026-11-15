#!/usr/bin/env python3
"""Bind all four finite duration certificates and check the relative time bound."""
from pathlib import Path
import json,hashlib,collections,sys
ROOT=Path(__file__).resolve().parents[1]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def check(output=None):
 assert __debug__ and not sys.flags.optimize
 results=[];loop_results=[]
 bound=[1000,8]+[4]*9+[2,2]
 for child,parent in [('PA194LCG','PA194AX11GH'),('PA194LCGS','PA194AX11GHS')]:
  allcontracts=[]
  for name,mp,cp in [(child,ROOT/'machines'/child,ROOT/'verification/results'/child),(parent,ROOT/'inputs'/parent,ROOT/'inputs'/parent/'independent')]:
   cs=json.loads((cp/'contracts.json').read_text());rc=json.loads((cp/'receipt.json').read_text());sites=json.loads((mp/'sites.json').read_text())
   assert sha(mp/'machine.tm')==rc['dense_sha256']and sha(mp/'machine.native.tm')==rc['native_sha256']
   assert sha(cp/'contracts.json')==rc['contracts_sha256']
   required=[(i,b)for i,(_,op,a)in enumerate(sites)for b in([False,True]if op=='dec'else[False])]
   assert [(x['site'],x['positive'])for x in cs]==required
   for row in cs:
    d=row['duration'];assert len(d)==13 and d[0]>=3 and all(type(v)is int and 0<=v<=b for v,b in zip(d,bound))
   results.append({'name':name,'contracts':len(cs),'maximum_coefficients':[max(x['duration'][i]for x in cs)for i in range(13)],'coefficient_envelope':bound,'status':'PASS'})
   allcontracts.append(cs)
  new,old=allcontracts;delta={}
  for a,b in zip(new,old):
   assert(a['site'],a['positive'])==(b['site'],b['positive'])
   d=[x-y for x,y in zip(a['duration'],b['duration'])];assert not any(d[1:])
   delta[a['site'],a['positive']]=d[0]
  oldsites=json.loads((ROOT/'inputs'/parent/'sites.json').read_text());loops=[]
  for i in range(len(oldsites)-4):
   chunk=oldsites[i:i+5]
   if all(row[1:]==['inc',1]for row in chunk[:4])and chunk[4][1:]==['continueTo',2]:
    oldpaths=[r[0]for r in chunk]
    # Only the tree occurrence being reassociated: all five addresses change.
    newchunk=json.loads((ROOT/'machines'/child/'sites.json').read_text())[i:i+5]
    if all(x[0]!=y[0]for x,y in zip(chunk,newchunk)):
     ds=[delta[j,False]for j in range(i,i+5)];assert sum(ds)==4
     loops.append({'first_site':i,'site_deltas':ds,'iteration_delta':4})
  assert len(loops)==61
  loop_results.append({'name':child,'constructor_loops':len(loops),'loop_cases':loops,'constant_delta_histogram':dict(collections.Counter(delta.values()))})
 out={'status':'PASS','machines':results,'loop_comparison':loop_results,'witness_bound':'Theta(t)=60000+13*(t+1)^2+1147*(t+1)','scope':'All parent and child affine coefficients checked. Source growth and weak-arithmetic induction are proved in report/relative_proof.tex.'}
 if output:Path(output).write_text(json.dumps(out,indent=2)+'\n')
 return out
if __name__=='__main__':
 out=check(ROOT/'verification/clock_receipt.json');print(json.dumps({'status':out['status'],'contracts':sum(x['contracts']for x in out['machines']),'loops_per_machine':[x['constructor_loops']for x in out['loop_comparison']],'bound':out['witness_bound']},indent=2))
