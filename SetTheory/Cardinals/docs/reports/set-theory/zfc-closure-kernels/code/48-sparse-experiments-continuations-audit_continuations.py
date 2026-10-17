#!/usr/bin/env python3
"""Independent audit of the finite continuation certificate and saved searches."""
from collections import defaultdict,Counter
from pathlib import Path
import hashlib,json,re,sys
from continuation_search import Framework,strict

BASE=Path(__file__).resolve().parent

def independent_control(raw):
 text=raw.decode().partition('Definition p254_tab')[2].partition('[')[2].partition('].')[0]
 atom=r'(?:CN \d+|CI \d+|CD \d+|CB \d+|CC \d+|CH)'
 nodes=re.findall(r'\(('+atom+r'),\s*('+atom+r')\)',text)
 def edge(q,b):
  x=nodes[q][b].split();return x[0],int(x[1])if len(x)>1 else None
 paths=[]
 def visit(q,p):
  for b in [0,1]:
   op,r=edge(q,b);out=p+[b]
   if op=='CN':visit(r,out)
   else:paths.append((out,op,r))
 visit(0,[])
 index={tuple(p):i for i,(p,_,_)in enumerate(paths)}
 def decode(p):
  q=0;k=0;got=[]
  while True:
   b=p[k]if k<len(p)else 0;k+=1;got.append(b)
   op,r=edge(q,b)
   if op!='CN':
    assert not any(p[k:]);return index[tuple(got)]
   q=r
 def inc(p):
  out=p[:];carry=1
  for j in range(len(out)-1,-1,-1):
   v=out[j]+carry;out[j]=v%2;carry=v//2
  return out
 def cut(p,b,n):
  for j in range(len(p)-1,-1,-1):
   n-=p[j]==b
   if n==0:return p[:j]
  return []
 cases=[];targets=[]
 for s,(p,op,r) in enumerate(paths):
  for z in ([True,False]if op=='CD'else[None]):
   cases.append((s,''.join(map(str,p)),op,r,z))
   if op=='CH':targets.append(None);continue
   if op=='CI'or op=='CD'and not z:nextp=inc(p)
   elif op=='CD':nextp=inc(cut(p,0,1))
   elif op=='CB':nextp=inc(p if r==0 else cut(p,0,r))
   elif op=='CC':nextp=p if r==0 else cut(p,1,r)
   else:raise AssertionError(op)
   targets.append(decode(nextp))
 return cases,targets

def main():
 fw=Framework();cases,targets=independent_control((BASE/'Prog254.v').read_bytes())
 assert cases==fw.cases and targets==fw.targets
 jumps=0
 for i,(_,op,r)in enumerate(fw.sites):
  if op in('CB','CC'):
   jumps+=1;(_,nxt),=fw.bysite[i]
   assert fw.closure[i]==fw.closure[nxt]and fw.rank[i]==fw.rank[nxt]+1
  else:assert fw.closure[i]==i and fw.rank[i]==0
 groups=defaultdict(list)
 for i in sorted(set(fw.closure.values())):groups[fw.classes[i]].append(i)
 signatures={}
 for cls,group in groups.items():
  sigs={(fw.sites[i][1],fw.sites[i][2],tuple(None if t is None else fw.classes[t]for c,t in fw.bysite[i]))for i in group}
  assert len(sigs)==1;signatures[cls]=next(iter(sigs))
 # Check both ordinary output acceptance and the mandatory stuttering exclusion.
 accepted=0;stutter_rejected=0;small_gap_rejected=0
 def frame(pc,gap,effect):
  return strict.canon([('b',1)],[('b',int(b))for b in pc]+[('r',0,1,gap-len(pc)),('b',1),('box',('plain',effect))])
 for i,(site,p,op,r,z)in enumerate(fw.cases):
  if op=='CH':continue
  target=fw.target[i];core=fw.closure[fw.targets[i]];pc=fw.sites[core][0]
  assert target==frame(pc,40,target.effect);accepted+=1
  assert not(target==frame(pc,39,target.effect));small_gap_rejected+=1
  if op in('CB','CC'):
   assert not(target==frame(p,40,None));stutter_rejected+=1
 ledgers={}
 for name in ['continuation-uniform.json','continuation-actions.json']:
  path=BASE/name;data=json.loads(path.read_text());recipes=data['recipes']
  assert data['status']=='completed'and data['completed']==data['planned']==len(recipes)
  assert not data['survivors']
  assert dict(Counter(x[3]for x in recipes))==data['failures']
  assert all(x[2]is not None and 0<=x[2]<len(fw.cases)for x in recipes)
  if data['mode']=='uniform':
   unique={(q,t)for q,t,*_ in recipes};assert len(unique)==len(recipes)
  else:
   unique={(q,tuple(t[0]),tuple(t[1]))for q,t,*_ in recipes};assert len(unique)==len(recipes)
  ledgers[name]={'recipes':len(recipes),'checks':data['checks'],'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'partition_and_uniqueness':'PASS','affine_checks_rerun_by_auditor':False}
 result={'status':'PASS','independent_control_successors':len(cases),'source_sites':len(fw.sites),'pure_jump_sites':jumps,
  'action_sites':len(set(fw.closure.values())),'control_equivalence_classes':len(groups),'max_jump_rank':max(fw.rank.values()),
  'all_bisimulation_class_obligations':'PASS','all_jump_rank_equations':'PASS','finite_terminal_jump_cycles':0,
  'nontrivial_action_classes':[[{'site':i,'path':fw.sites[i][0],'operation':fw.sites[i][1],'register':fw.sites[i][2]}for i in group]for group in groups.values()if len(group)>1],
  'representative_outputs_accepted':accepted,'same_site_jump_stutters_rejected':stutter_rejected,'gap39_outputs_rejected':small_gap_rejected,
  'search_ledger_audits':ledgers,'limits':['Ordinary Python and mathematical audit; not a kernel proof.','The independent audit does not rerun all affine candidate checks.','Search rejections do not imply global inequivalence or a state lower bound.']}
 (BASE/'continuation-audit.json').write_text(json.dumps(result,indent=2)+'\n')
 certificate={'schema':'ranked-continuation-certificate-v1','program_sha256':hashlib.sha256((BASE/'Prog254.v').read_bytes()).hexdigest(),
  'sites':[{'path':p,'operation':op,'register':r,'closure':fw.closure[i],'rank':fw.rank[i],'class':fw.classes[i]}for i,(p,op,r)in enumerate(fw.sites)],
  'targets':fw.targets}
 (BASE/'continuation-certificate.json').write_text(json.dumps(certificate,indent=2)+'\n')
 print(json.dumps(result,indent=2))

if __name__=='__main__':main()
