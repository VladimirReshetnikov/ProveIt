#!/usr/bin/env python3
"""Independently enumerate the stated finite syntactic substitution search."""
import hashlib,json,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];d=root/'research/nine-sharing-direct-elimination-frontier-search';src=root/'research/nine-sharing-sign23-octic-delta-candidate/seed.json';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();assert sha(src)=='ee6079ea26dd120fab39789f83034947c18e0c8806945a1fc75fca62e1c65d41';seed=json.loads(src.read_text());assert seed['witness_count']==23
rows=seed['residuals'];assert len({x['gate'] for x in rows})==len(rows)
def fold(t):
 if t[0]=='var':return (1,{t[1]},True)
 if t[0]=='num':return (0,set(),type(t[1]) is int and t[1]>=0)
 if t[0]=='port':return (0,set(),True)
 assert t[0] in ('add','sub','mul') and len(t)==3
 da,va,pa=fold(t[1]);db,vb,pb=fold(t[2]);return ((da+db if t[0]=='mul' else max(da,db)),va|vb,pa and pb and t[0]!='sub')
def subst(t,index,value):
 if t[0]=='var':return value if t[1]==index else t
 if t[0] in ('num','port'):return t
 return [t[0],subst(t[1],index,value),subst(t[2],index,value)]
def maxdeg(rs):return max(fold(r['expr'])[0] for r in rs)
assert maxdeg(rows)==4
queue=[([],rows)];seen={};cutoff=[]
while queue:
 path,rs=queue.pop(0);key=tuple(path);assert key not in seen;opts={}
 for row in rs:
  t=row['expr']
  if row['kind']!='positive' or t[0]!='sub' or t[1][0]!='var':continue
  i=t[1][1];deg,variables,positive=fold(t[2]);
  if i==0 or i in variables or not positive:continue
  new=[{'gate':x['gate'],'kind':x['kind'],'expr':subst(x['expr'],i,t[2])} for x in rs if x['gate']!=row['gate']];bound=maxdeg(new);opts[row['gate']]=(i,bound)
  if len(path)>=5:cutoff.append((key,row['gate']))
  else:queue.append((path+[row['gate']],new))
 seen[key]=(23-len(path),maxdeg(rs),opts)
assert not cutoff and len(seen)==65 and min(v[0] for v in seen.values())==19
stored=json.loads((d/'result.json').read_text());assert stored['status']=='PASS_FINITE_SYNTACTIC_SEARCH' and stored['source_sha256']==sha(src) and stored['states']==65
actual={tuple(x['eliminated']):(x['witness_count'],x['residual_degree_bound'],{z['gate']:(z['old_coordinate'],z['residual_degree_bound']) for z in x['options']}) for x in stored['all_states']};assert len(actual)==len(seen) and actual==seen
frontier={}
for count in range(19,24):
 best=min(v[1] for v in seen.values() if v[0]==count);paths={k for k,v in seen.items() if v[0]==count and v[1]==best};frontier[count]=(best,paths)
assert {n:v[0] for n,v in frontier.items()}=={19:22,20:10,21:7,22:6,23:4}
for row in stored['frontier']:
 best,paths=frontier[row['witness_count']];assert row['best_residual_degree_bound']==best and {tuple(x) for x in row['sequences']}==paths
assert len(stored['frontier'])==5
print(json.dumps({'status':'PASS_EXTERNAL_INDEPENDENT','states':len(seen),'frontier_residual_degree':{str(n):frontier[n][0] for n in sorted(frontier)},'cutoff_truncated':False,'scope':'finite positive direct-variable syntactic search only; not a general optimum or Lean/model theorem'},indent=2,sort_keys=True))
