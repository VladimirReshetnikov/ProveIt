#!/usr/bin/env python3
"""Independent frozen-source semantic edit, monic scale, projection and SOS checks."""
from pathlib import Path
from collections import defaultdict
import hashlib,json
P=Path(__file__).resolve().parents[1]
def pp(ts):return{tuple(m):c for c,m in ts}
def plus(*ps):
 d=defaultdict(int)
 for p in ps:
  for m,c in p.items():d[m]+=c
 return{m:c for m,c in d.items()if c}
def sc(p,k):return{m:c*k for m,c in p.items()if c*k}
def times(a,b):
 d=defaultdict(int)
 for m,c in a.items():
  for n,e in b.items():d[tuple(sorted(m+n))]+=c*e
 return{m:c for m,c in d.items()if c}
def square(p):return times(p,p)
def replace(p,v,f):
 d=defaultdict(int);powers=[{():1}]
 for m,c in p.items():
  degree=m.count(v)
  while len(powers)<=degree:powers.append(times(powers[-1],f))
  rest=tuple(x for x in m if x!=v)
  for mm,cc in powers[degree].items():d[tuple(sorted(rest+mm))]+=c*cc
 return{m:c for m,c in d.items()if c}
def need(t,msg):
 if not t:raise ValueError(msg)
def eq(a,b,msg):need(a==b,msg)
def rows(j):return[pp(r['terms'])for r in j['residuals']]
source=P/'incoming210/equations/principal210/equation.json';need(hashlib.sha256(source.read_bytes()).hexdigest()=='20a2108353a3756ed7d1ddfdc71695131dcf0b6d94039988d9565ac48e6e1f0a','source pin');s=json.loads(source.read_text());names={v['name']:i for i,v in enumerate(s['variables'])};V=lambda n:{(names[n],):1};t,z=names['t0'],names['cofinal.horizon_root'];labels={r['label']:i for i,r in enumerate(s['residuals'])};result=[]
for name in json.loads((P/'ENDPOINTS.json').read_text()):
 folder=P/name;c=json.loads((folder/'certificate.json').read_text());target=json.loads((folder/'equation.json').read_text());sem=c['semantic'];m=sem['m'];need(m==4 and sem['centered'],'proved selected family');rr=rows(s);h=sem['horizon_row'];eq(rr[h],{(t,):1,():-16,(z,z):-4},'old horizon');rr[h]={(t,):1,():-m,(z,):-2*m}
 frame=sem['frame'];f=frame['row'];atoms=[pp(x)for x in frame['old_atoms']];eq(rr[f],plus(V('shared.W'),{():-2},*[sc(square(a),-1)for a in atoms]),'old actual frame');need(len(atoms)==34,'34atoms');actual=[replace(a,t,{():m,(z,):2*m})for a in atoms];eq(actual,[pp(a)for a in frame['actual_atoms']],'affine actual atoms');support=sorted({x for a in actual for mon in a for x in mon});eq(support,frame['coordinates'],'support');budget=[abs(a.get((),0))+sum(cc*cc//4 for mon,cc in a.items()if mon)for a in actual];eq(budget,frame['bounds'],'atom budgets');need(max(budget)+1==22==frame['constant'],'constant22');need(max(sum(abs(v)for v in a.values())for a in actual)==13,'l1bound13');need(names['growth.F']in support,'F frame retained');rr[f]=plus(V('shared.W'),{():-22},*[{(x,x):-1}for x in support])
 F=V('growth.F');eold=plus(V('index2.Y'),sc(V('t0'),-1),sc(F,-1));enew=plus(V('index2.Y'),sc(V('index0.Y'),-1),sc(F,-1));delta=plus(square(enew),sc(square(eold),-1));d=sem['difference'];eq(delta,pp(d['delta']),'error difference delta');rr[d['row']]=plus(rr[d['row']],delta);eq(rr,rows(json.loads((folder/'unsplit_modified_source.json').read_text())),'entire semantic source')
 split=c['split'];exps=split['exponents'];n=len(s['variables']);nv=list(s['variables']);u=names['growth_pell.odd_half'];ff=names['growth.F'];last=t
 if exps:
  need(sum(exps)==19 and all(type(a)is int and a>=0 for a in exps),'exponent19');gi=split['row'];eq(rr[gi],{(ff,):1,(t,):-2**19,tuple(sorted((t,u))):-2**20},'old growth exact row')
  for k,a in enumerate(exps[:-1]):
   st=split['definitions'][k];need(st['coordinate']==n+k and st['previous']==last and st['factor']==2**a and st['row']==len(rr),'split unit definition record');rr.append({(n+k,):1,(last,):-2**a});nv.append({'name':f'growth_pell.split{k}','kind':'unit_defined_wire'});last=n+k
  rr[gi]={(ff,):1,(last,):-2**exps[-1],tuple(sorted((last,u))):-2**(exps[-1]+1)}
 mod=json.loads((folder/'modified_source.json').read_text());eq(rr,rows(mod),'all split source rows');eq(nv,mod['variables'],'split variable declaration')
 projection=c['projection'];eq(projection['replacement'],[[m,[]],[2*m,[z]]],'affine replacement record');need(projection['deleted_row']==h and projection['eliminated_coordinate']==t,'affine elimination record');keep=[j for j in range(len(nv))if j!=t];eq(keep,projection['retained_indices'],'retained order');ren={j:k for k,j in enumerate(keep)}
 rr=[{tuple(ren[j]for j in mon):co for mon,co in replace(p,t,{():m,(z,):2*m}).items()}for i,p in enumerate(rr)if i!=h]
 for i,j,k in c['row_operations']:
  need(type(k)is int and i!=j and 0<=i<len(rr)and 0<=j<len(rr),'integer reversible row operation');rr[i]=plus(rr[i],sc(rr[j],k))
 eq(rr,rows(target),'all final rows');eq(target['variables'],[nv[i]for i in keep],'all final variables');full=plus(*[square(p)for p in rr]);given=pp(json.loads((folder/'expanded_polynomial.json').read_text())['terms']);eq(full,given,'full expanded SOS');need({i for mon in full for i in mon}==set(range(len(keep))),'all variables actually occur')
 data={'profile':name,'equation_sha256':hashlib.sha256((folder/'equation.json').read_bytes()).hexdigest(),'variables':len(keep),'rows':len(rr),'degree':max(map(len,full)),'monomials':len(full),'height':max(map(abs,full.values())),'split_exponents':exps,'row_operations':len(c['row_operations']),'source_delta_split_projection_and_all_coefficients_pass':True};result.append(data);print(json.dumps(data),flush=True)

# A portable read-only run; a caller may redirect stdout to its own receipt.
print(json.dumps({'status':'PASS','method':'Second independent ring implementation; no producer/checker imports','results':result},indent=2))
