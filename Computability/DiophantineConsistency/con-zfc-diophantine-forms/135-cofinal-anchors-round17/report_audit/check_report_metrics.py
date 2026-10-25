#!/usr/bin/env python3
"""Independent metric recollection from the published literal definitions."""
from pathlib import Path
import collections,hashlib,json
ROOT=Path(__file__).resolve().parents[1]
def need(b,m):
 if not b:raise ValueError(m)
def collect(ts):
 d={}
 for c,m in ts:
  need(type(c)==int and isinstance(m,list) and all(type(i)==int for i in m),'integer term')
  k=tuple(sorted(m));d[k]=d.get(k,0)+c
 return {m:c for m,c in d.items() if c}
def read(p):return json.loads((ROOT/p).read_text())
def inspect(row):
 if row['kind']=='dag':
  p=read(row['graph']);live=set()
  def visit(i):
   need(type(i)==int and 0<=i<len(p['nodes']),'gate index')
   if i in live:return
   live.add(i);g=p['nodes'][i]
   if g[0] in ('add','sub','mul'):
    need(len(g)==3 and g[1]<i and g[2]<i,'acyclic arithmetic gate');visit(g[1]);visit(g[2])
  visit(p['output']);need(live==set(range(len(p['nodes']))),'dead graph nodes')
  variables={g[1] for g in p['nodes'] if g[0]=='variable'}
  got={'variables':len(variables),'degree':p['exact_degree'],'operations':sum(p['nodes'][i][0] in ('add','sub','mul') for i in live)}
  need(set(p['variables'])==variables and p['domain']==row['domain'],'graph domain')
 else:
  p=read(row['polynomial']);terms=collect(p['terms']);need(len(terms)==len(p['terms']),'noncollected polynomial')
  n=p['variables'] if type(p['variables'])==int else len(p['variables'])
  used={i for m in terms for i in m};need(used==set(range(n)),'all coordinates live')
  got={'variables':n,'degree':max(map(len,terms)),'monomials':len(terms),'height':max(map(abs,terms.values())),'constant':terms.get((),0),'individual_degree':max(max(collections.Counter(m).values()) for m in terms if m)}
  need(p['domain']==row['domain'],'polynomial domain')
  if row['kind']=='sos':
   q=read(row['equation']);squares=[]
   need(len(q['variables'])==n and q['domain']==row['domain'],'equation coordinate count/domain')
   for r in q['residuals']:
    z=collect(r['terms']);need(max(map(len,z),default=0)<=2,'quadratic source')
    squares += [(a*b,list(m+n)) for m,a in z.items() for n,b in z.items()]
   need(collect(squares)==terms,'whole SOS polynomial mismatch');got['rows']=len(q['residuals'])
 for k,v in row['metrics'].items():need(got[k]==v,row['name']+' '+k)
 return {'name':row['name'],'domain':row['domain'],'metrics':got}
if __name__=='__main__':
 out=[inspect(r) for r in read('ENDPOINTS.json')['endpoints']]
 print(json.dumps({'status':'PASS','scope':'Literal final coefficients, dimensions, degrees, domains and live binary counts. Scalar exact degrees are separately proved by the complete graph auditor.','endpoints':out},indent=2))
