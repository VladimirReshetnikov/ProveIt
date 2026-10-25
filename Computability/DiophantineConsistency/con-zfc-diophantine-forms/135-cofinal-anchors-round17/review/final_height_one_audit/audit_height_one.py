"""Fresh independent arithmetic audit: no producer or incoming-code imports."""
from pathlib import Path
from collections import defaultdict,Counter
from fractions import Fraction
import json,hashlib,argparse,copy

def require(b,m):
 if not b:raise ValueError(m)
def poly(ts):
 d={}
 for c,m in ts:
  require(type(c)==int,'integer coefficient');m=tuple(sorted(m));d[m]=d.get(m,0)+c
 return {m:c for m,c in d.items() if c}
def add(a,b,s=1):
 r=a.copy()
 for m,c in b.items():r[m]=r.get(m,0)+s*c
 return {m:c for m,c in r.items() if c}
def mul(a,b):
 r={}
 for m,c in a.items():
  for n,d in b.items():k=tuple(sorted(m+n));r[k]=r.get(k,0)+c*d
 return {m:c for m,c in r.items() if c}
def subst(p,ss):
 r={}
 for m,c in p.items():
  q={():c}
  for i in m:q=mul(q,ss[i])
  r=add(r,q)
 return r

def audit(src,art,cert,digest):
 require(cert['source_sha256']==digest,'source hash')
 nv=len(src['variables']);norm=cert['normalization'];vs=norm['variables'];rows=norm['rows'];ns=len(vs)
 require(norm['original_variables']==nv and ns>=nv,'source dimension')
 subs=[]
 for i,v in enumerate(vs):
  if i<nv:
   require(v=={'kind':'original','source_index':i},'source coordinate');subs.append({(i,):1})
  elif v['kind']=='constant':
   require(type(v['value'])==int and v['value']>1,'constant');subs.append({():v['value']})
  else:
   require(v['kind']=='scale' and type(v['coefficient'])==int and v['coefficient']>1 and 0<=v['variable']<nv,'scale');subs.append({(v['variable'],):v['coefficient']})
 sourceimages={};pivots=set();rowimages=[]
 for r in rows:
  require(all(c in (-1,1) and len(m)<=2 for c,m in r['terms']),'normal terms');p=poly(r['terms']);image=subst(p,subs);rowimages.append(image)
  if r['kind']=='source':
   i=r['source_row'];require(i not in sourceimages and 0<=i<len(src['residuals']),'source row index');require(image==poly(src['residuals'][i]['terms']),'exact source row');sourceimages[i]=image
  else:
   require(r['kind'] in ('scale','constant') and not image,'constructor image');k=max(i for m in p for i in m)
   require(k>=nv and k not in pivots and p.get((k,))==1 and all(k not in m or m==(k,) for m in p),'monic triangular constructor');pivots.add(k)
 require(pivots==set(range(nv,ns)) and set(sourceimages)==set(range(len(src['residuals']))),'complete normalized source')
 final=art['variables'];n=len(final);aliases=defaultdict(set);flow=set();dummies=defaultdict(set);unitdummies=set();finalsubs=[]
 for i,v in enumerate(final):
  kind=v['kind']
  if kind=='flow':flow.add(i);finalsubs.append({})
  elif kind=='unit_dummy':unitdummies.add(i);finalsubs.append({():1})
  else:
   require(kind in ('alias','equality_dummy'),'coordinate kind');k=v['normalized_variable'];require(k is None or type(k)==int and 0<=k<ns,'logical range')
   (aliases if kind=='alias' else dummies)[k].add(i);finalsubs.append({():1} if k is None else subs[k])
 require(set(aliases)==set(range(ns))|{None},'each logical value represented')
 classes=[];quartic_pairs=[];covered=set();usedlogic=set()
 for cy in cert['equality_cycles']:
  k=cy['normalized_variable'];ids=cy['aliases'];require(k in aliases and k is not None and k not in usedlogic,'logical cycle');usedlogic.add(k)
  require(len(ids)==len(set(ids)) and not covered.intersection(ids),'cycle disjointness');require(set(ids)==aliases[k]|dummies[k],'cycle completeness');mode=cy.get('mode','cycle');require(mode in ('cycle','quartic_pair'),'equality mode')
  if mode=='quartic_pair':require(len(ids)==2 and len(dummies[k])==0,'quartic equality pair');quartic_pairs.append(ids)
  else:require(len(ids)==1 or len(ids)>=3,'cycle length');require(len(dummies[k])==(1 if len(aliases[k])==2 else 0),'minimal dummy');classes.append(ids)
  covered.update(ids)
 require(usedlogic==set(range(ns)),'all logical cycles')
 units=cert['unit_path'];require(len(units)>=2 and len(units)==len(set(units)) and set(units)==aliases[None]|unitdummies,'unit path');require(covered.isdisjoint(units) and covered.isdisjoint(flow) and flow.isdisjoint(units),'namespace disjointness');require(covered|set(units)|flow==set(range(n)),'coordinate coverage')
 flat=[(r,j,c,m) for r,row in enumerate(rows) for j,(c,m) in enumerate(row['terms'])];products=cert['products'];require(len(products)==len(flat),'occurrence total')
 for p,(r,j,c,m) in zip(products,flat):
  require((p['row'],p['occurrence'],p['sign'])==(r,j,c),'source occurrence');a,b=p['logical_factors'];require(sorted(x for x in [a,b] if x is not None)==sorted(m),'logical source monomial');require((len(m)==2)==(b is not None) and (len(m)>0)==(a is not None),'homogenization')
  require(len(p['factors'])==2,'quadratic source edge')
  for i,v in zip(p['factors'],[a,b]):require(i in aliases[v],'same-logical alias identification')
 squared_aliases={p['factors'][0] for p in products if p['factors'][0]==p['factors'][1]}
 for ids in quartic_pairs:require(not squared_aliases.intersection(ids),'quartic pair avoids square-edge collision')
 vertices=cert['vertices'];parts=[cert['hub_vertices']]+cert['row_blocks'];require(len(parts)==len(rows)+1,'block count');owners={}
 for i,block in enumerate(parts):
  require(block and len(block)==len(set(block)),'block shape')
  for v in block:require(v not in owners and type(v)==int and 0<=v<len(vertices),'vertex coverage');owners[v]=i
 require(set(owners)==set(range(len(vertices))),'complete vertices')
 incid=[{} for _ in vertices];external=[{} for _ in vertices];adj=[[] for _ in vertices];pairset=set();usedprod=set();usedflow=set()
 for e in cert['edges']:
  t,h=e['tail'],e['head'];require(t in owners and h in owners and t!=h,'edge endpoints');pa=tuple(sorted([t,h]));require(pa not in pairset,'simple graph');pairset.add(pa);c=e['coefficient'];m=e['monomial'];edge={tuple(sorted(m)):c}
  incid[t]=add(incid[t],edge);incid[h]=add(incid[h],edge,-1)
  if e['kind']=='prescribed':
   i=e['product'];require(i not in usedprod and 0<=i<len(products),'source edge occurrence');usedprod.add(i);p=products[i];require(c==p['sign'] and m==p['factors'] and owners[t]==p['row']+1 and owners[h]==0,'edge logical binding');image=subst(edge,finalsubs);external[t]=add(external[t],image);external[h]=add(external[h],image,-1)
  else:
   require(e['kind']=='free' and c==1 and len(m)==1 and m[0] in flow and m[0] not in usedflow and owners[t]==owners[h],'internal independent flow');usedflow.add(m[0]);adj[t].append((h,m[0],1));adj[h].append((t,m[0],-1))
 require(usedprod==set(range(len(products))) and usedflow==flow,'edge coverage')
 # Universal symbolic canonical lift: solve every tree with polynomial edge values.
 flowvalues={};residual_sum={}
 for p in rowimages:residual_sum=add(residual_sum,p)
 for partno,block in enumerate(parts):
  root=block[0];parent={root:None};order=[root]
  for v in order:
   for w,k,sgn in adj[v]:
    if w not in parent:parent[w]=(v,k,-sgn);order.append(w)
  require(set(order)==set(block) and sum(len(adj[v]) for v in block)==2*(len(block)-1),'internal spanning tree')
  for v in order[:0:-1]:
   w,k,sgn=parent[v];flowvalues[k]={m:-sgn*c for m,c in external[v].items()};external[w]=add(external[w],external[v]);external[v]={}
  expect={m:-c for m,c in residual_sum.items()} if partno==0 else rowimages[partno-1]
  require(external[root]==expect,'universal root divergence identity')
 for k,v in flowvalues.items():finalsubs[k]=v
 # All equality and unit relations vanish universally under the full lift.
 for ids in classes+quartic_pairs:
  require(all(finalsubs[i]==finalsubs[ids[0]] for i in ids),'universal alias equality')
 require(all(finalsubs[i]=={():1} for i in units),'universal unit anchor')
 for v,p in enumerate(incid):require(subst(p,finalsubs)==external[v],'whole symbolic divergence substitution')
 # Full coefficient audit, from literal squares, not a collision-free assumption.
 twice={}
 for p in incid:twice=add(twice,mul(p,p))
 for ids in classes:
  if len(ids)==1:continue
  for a,b in zip(ids,ids[1:]+ids[:1]):p={(a,):1,(b,):-1};twice=add(twice,mul(p,p))
 for a,b in quartic_pairs:
  for p in [{(a,a):1,(b,b):-1},{(a,a):1,tuple(sorted([a,b])):-1},{tuple(sorted([a,b])):1,(b,b):-1}]:twice=add(twice,mul(p,p))
 for a,b in [(None,units[0])]+list(zip(units,units[1:]))+[(units[-1],None)]:
  p=add({():1} if a is None else {(a,):1},{():1} if b is None else {(b,):1},-1);twice=add(twice,mul(p,p))
 require(all(c%2==0 for c in twice.values()),'integral half-energy');expected={m:c//2 for m,c in twice.items()};actual=poly(art['terms']);require(len(art['terms'])==len(actual),'collected support');require(actual==expected,'literal full polynomial identity');require(set(actual.values())=={-1,1} and actual.get(())==1,'height and unit constant');require({i for m in actual for i in m}==set(range(n)),'live final variables')
 return {'status':'pass','source_variables':nv,'source_rows':len(src['residuals']),'variables':n,'degree':max(map(len,actual)),'individual_degree':max(max(Counter(m).values()) for m in actual if m),'monomials':len(actual),'coefficient_height':1,'constant':1,'normalization_variables':ns,'normalization_rows':len(rows),'graph_vertices':len(vertices),'graph_edges':len(cert['edges']),'quartic_equality_pairs':len(quartic_pairs),'same_logical_factor_bindings':2*len(products),'exact_symbolic_lift_vertices':len(incid),'identity':'P(L(x)) = (sum_r R_r(x)^2 + (sum_r R_r(x))^2)/2, universally','scope':'Every coefficient and universal symbolic lift checked. Source consistency theorem remains inherited.'}

def main():
 p=argparse.ArgumentParser();p.add_argument('--source',required=True,type=Path);p.add_argument('--candidate',required=True,type=Path);p.add_argument('--output',required=True,type=Path);a=p.parse_args();raw=a.source.read_bytes();src=json.loads(raw);art=json.loads((a.candidate/'polynomial.json').read_text());cert=json.loads((a.candidate/'certificate.json').read_text());r=audit(src,art,cert,hashlib.sha256(raw).hexdigest());r['source_sha256']=hashlib.sha256(raw).hexdigest();r['polynomial_sha256']=hashlib.sha256((a.candidate/'polynomial.json').read_bytes()).hexdigest();r['certificate_sha256']=hashlib.sha256((a.candidate/'certificate.json').read_bytes()).hexdigest();a.output.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r))
if __name__=='__main__':main()
