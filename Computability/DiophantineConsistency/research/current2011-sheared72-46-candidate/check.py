#!/usr/bin/env python3
"""Check fixed-port candidate graph and exact integer shear identity; no Lean."""
import collections,gzip,hashlib,json,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
D=Path(__file__).resolve().parents[2];P=D/'research/current2011-sheared72-46-candidate';O=D/'research/current2011-ordinary71-60-candidate';prime=1000000007
sha=lambda x:hashlib.sha256(x).hexdigest()
def need(v,s):
 if not v:raise RuntimeError(s)
gb=(P/'polynomial.json').read_bytes();pb=(O/'polynomial.json').read_bytes();g=json.loads(gb);p=json.loads(pb)
need(sha(gb)=='cfb30017781968c87e1fa7cba5d08a69b555a7c058ddb1e36b313c74b519e78f' and sha(pb)=='3c50ef12124daab13a6f67e03e273ecc91a5bed2fd3557a1343514b3b4171e27','graph pins')
new=[['y_old','+','V','y'],['y_old2','*','y_old','y_old'],['sum_yV','+','y_old','V'],['shear_prod','*','y','sum_yV'],['shear_aux','*','Aaux','shear_prod'],['Na','-','y_old2','shear_aux']]
need(g['source'][:55]==p['source'][:55] and g['source'][55:61]==new and g['source'][61:]==p['source'][60:] and g['coefficient_binding']==p['coefficient_binding'] and g['witnesses']==p['witnesses'] and g['witness_domain']==p['witness_domain'],'exact graph edit')
# Independently compare the auxiliary cut in Z[V,y,A]: original at Y=V+y.
def add(a,b,sign=1):
 c=dict(a)
 for k,v in b.items():c[k]=c.get(k,0)+sign*v
 return {k:v for k,v in c.items() if v}
def mul(a,b):
 c={}
 for x,u in a.items():
  for y,v in b.items():
   k=tuple(i+j for i,j in zip(x,y));c[k]=c.get(k,0)+u*v
 return {k:v for k,v in c.items() if v}
V={(1,0,0):1};Y={(0,1,0):1};A={(0,0,1):1};old=add(V,Y);old2=mul(old,old);orig=add(mul(A,add(mul(V,V),old2,-1)),old2);newvalue=add(old2,mul(A,mul(Y,add(old,V))),-1);need(orig==newvalue,'universal shear polynomial identity')
need(g['coefficient_binding']['path']=='../fourteen-nonzero-spheres/coefficients/','port path');values={}
for n,m in g['coefficient_binding']['ports'].items():
 f=(P/g['coefficient_binding']['path']/m['file']).resolve();z=f.read_bytes();raw=gzip.decompress(z);need(sha(z)==m['gzip_sha256'] and sha(raw)==m['raw_sha256'] and len(raw)==m['raw_bytes'] and int.from_bytes(raw,'big').bit_length()==m['bits'],'port '+n);values[n]=int.from_bytes(raw,'big')%prime
def poly(a,b,op):
 out=[0]*(len(a)+len(b)-1 if op=='*' else max(len(a),len(b)))
 if op=='*':
  for i,x in enumerate(a):
   for j,y in enumerate(b):out[i+j]=(out[i+j]+x*y)%prime
 else:
  for i,x in enumerate(a):out[i]=(out[i]+x)%prime
  for i,y in enumerate(b):out[i]=(out[i]+(y if op=='+' else -y))%prime
 while len(out)>1 and not out[-1]:out.pop()
 return out
w=g['witnesses'];deg={n:1 for n in w};deg.update({n:0 for n in values});ray={n:[0,1] for n in w};ray.update({n:[x] for n,x in values.items()});edges={};counts=collections.Counter();rows={r[0]:r for r in g['source']}
shape={'a':['a','+','E','Y'],'four_a':['four_a','*',4,'a'],'H':['H','+','four_a',3],'a2':['a2','*','a','a'],'Delta':['Delta','+','a2','H'],'ac':['ac','*','a','c'],'main_base':['main_base','+','X','ac'],'gammaH':['gammaH','*','gamma','H'],'main_root':['main_root','+','main_base','gammaH'],'main_square':['main_square','*','main_root','main_root'],'c2':['c2','*','c','c'],'Dc2':['Dc2','*','Delta','c2'],'N1':['N1','-','main_square','Dc2']};need(all(rows.get(k)==v for k,v in shape.items()),'N1 cancellation shape')
for n,op,a,b in g['source']:
 need(n not in deg and op in ('+','-','*') and all(type(x)==int or x in deg for x in (a,b)),'topology');u=0 if type(a)==int else deg[a];v=0 if type(b)==int else deg[b];deg[n]=u+v if op=='*' else max(u,v)
 if n=='N1':
  need((deg['X'],deg['a'],deg['c'],deg['H'],deg['gamma'])==(2,6,5,6,1),'N1 inputs');deg[n]=max(2*deg['X'],deg['X']+deg['a']+deg['c'],deg['gamma']+deg['H']+max(deg['X'],deg['a']+deg['c']),2*deg['gamma']+2*deg['H'],deg['H']+2*deg['c'])
 ray[n]=poly([a%prime] if type(a)==int else ray[a],[b%prime] if type(b)==int else ray[b],op);edges[n]=(a,b);counts[op]+=1
seen=set();leaves=set();todo=[g['output']]
while todo:
 n=todo.pop()
 if n in edges:
  if n not in seen:seen.add(n);todo.extend(edges[n])
 elif type(n)==str:leaves.add(n)
need(len(seen)==len(g['source'])==g['operations']==72 and leaves==set(w+g['fixed_numerals']),'liveness')
r=ray[g['output']];need(deg[g['output']]==len(r)-1==46 and r[-1]!=0,'exact degree')
print(json.dumps({'status':'PASS_CANDIDATE_GRAPH_IDENTITY_AND_DEGREE','graph_sha256':sha(gb),'operations':len(seen),'counts':dict(counts),'degree_upper':deg[g['output']],'ray_degree':len(r)-1,'ray_leading_coefficient_mod_1000000007':r[-1],'identity':'candidate at positive (v,y) equals parent at same other coordinates and parent y=V+y','scope':'Exact external polynomial identity and fixed-byte degree only; reverse positivity, all-model zero bridge and iPRA endpoint unchecked.'},indent=2,sort_keys=True))
