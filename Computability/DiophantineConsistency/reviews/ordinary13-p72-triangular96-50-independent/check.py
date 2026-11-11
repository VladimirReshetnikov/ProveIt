#!/usr/bin/env python3
import gzip,hashlib,json,subprocess,sys
from collections import Counter,defaultdict
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
base=Path(__file__).resolve().parents[2];p=base/'research/ordinary13-p72-triangular97-50'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for f,h in {'README.md':'78e4c5b320453786a8e9405cb9d60e372355c11f36eed9c48d24fab8117b7098','check.py':'36d76ce43ee8c8d116bba5a9b0ed5aebde7a1aa4b577ba7d5517829c758efd7e','polynomial.json':'16bfa31fbc1ed5dee7d30fe79b8c91d123dba8195934bd01d1231356c1114198','polynomial96.json':'957d0a60112a67222a8ae576d3304e400ce20493b54a159918c6a947a814d758','result.json':'c17acc0d79f668aa5800036c6bba3028dceee4be5cfb7017870d0b5aa88c9620'}.items():assert sha(p/f)==h
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check.py')],cwd=base,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=120);assert not r.stderr and r.stdout==(p/'result.json').read_bytes()
p72=base/'con-zfc-diophantine-forms/72-congruence-sextic/positive13';oldpath=p72/'p13_degree28.json';bindpath=p72/'ACTIVE_BINDING.json';proof=p72/'PROOF13.md'
assert sha(oldpath)=='1968b1a0c887eb5a94794d8fdd7635f56432da4d235e81cf5ce4ab4790840d49' and sha(bindpath)=='6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf' and sha(proof)=='8fedebfd59e18d25bb7e08f607e5e57be2386a3492fd8da31b6f25a1e6caf2c5'
g97=json.loads((p/'polynomial.json').read_text());g96=json.loads((p/'polynomial96.json').read_text());old=json.loads(oldpath.read_text()); B=json.loads(bindpath.read_text()); graphs=[old,g97,g96]
assert len(old['source'])==98 and all(g['witnesses']==old['witnesses'] and g['fixed_ports']==old['fixed_ports'] for g in graphs)
assert len(old['witnesses'])==13 and len(old['fixed_ports'])==4
assert g97['derived_fixed_leaves']['L2']==['*','L','L'] and g96['derived_fixed_leaves']==g97['derived_fixed_leaves']
expected97=old['source'][:84]+[['g85','*','Delta','g25'],['ysum','+','yhat','Vhat'],['g87','*','g81','ysum'],['g88','*','g85','g87'],['g89','-','yhat2','g88'],['Aa','-','g89','L2']]+old['source'][91:]
assert g97['source']==expected97
expected96=expected97[:23]+[['g71','*','Delta','c2'],['j','*','i','g71'],['g85','*','j','j'],['sf','*','Delta','f2m'],['sg','*','b2','g85'],['As','-','sf','sg']]+[r for r in expected97[28:] if r[0] not in ('g71','g85')]
assert g96['source']==expected96
for g,N,counts in [(g97,97,{'+':26,'-':15,'*':56}),(g96,96,{'+':26,'-':15,'*':55})]:
 rows=g['source'];assert len(rows)==N and Counter(x[1] for x in rows)==counts
 have=set(g['witnesses']+g['fixed_ports']+list(g['derived_fixed_leaves']));deg={x:1 for x in g['witnesses']};deg.update({x:0 for x in have if x not in deg})
 for n,op,a,b in rows:
  assert n not in have and all(type(x)==int or x in have for x in (a,b));get=lambda x:0 if type(x)==int else deg[x]
  deg[n]=get(a)+get(b) if op=='*' else max(get(a),get(b));have.add(n)
 needed={g['output']}
 for n,op,a,b in reversed(rows):
  if n in needed:needed.update((a,b))
 assert all(n in needed for n,_,_,_ in rows) and set(g['witnesses']+g['fixed_ports'])<=needed and deg[g['output']]==50
# Small multivariate ring; cuts connect unchanged and transformed residual subgraphs.
def atom(x):return {(x,):1}
def add(a,b,sgn=1):
 d=defaultdict(int,a)
 for k,v in b.items():d[k]+=sgn*v
 return {k:v for k,v in d.items() if v}
def mul(a,b):
 d=defaultdict(int)
 for x,u in a.items():
  for y,v in b.items():d[tuple(sorted(x+y))]+=u*v
 return {k:v for k,v in d.items() if v}
cuts={x:atom(x) for x in ('Delta','c2','i','f2m','b2','Vhat','g81','L2','A0','A1')};cuts['Kfinal']=mul(cuts['b2'],cuts['L2'])
def evalcut(g):
 v=dict(cuts)
 for n,op,a,b in g['source']:
  if n in v:continue
  if a in v and b in v:v[n]=mul(v[a],v[b]) if op=='*' else add(v[a],v[b],1 if op=='+' else -1)
 return v
v0,v97,v96=map(evalcut,graphs);gap=add(mul(v0['yhat'],v0['yhat']),mul(v0['Vhat'],v0['Vhat']),-1)
assert v97['g87']==gap==v96['g87']
assert mul(v0['b2'],v97['Aa'])==add(v0['Aa'],mul(mul(v0['Delta'],gap),v0['As']))
assert v96['Aa']==v97['Aa'] and v97['As']==v0['As'] and v96['As']==mul(v0['Delta'],v0['As'])
# Check the full sum-of-squares tails also match their displayed components.
for v in (v0,v97,v96):
 sq=lambda x:mul(v[x],v[x]);assert v['g97']==add(add(sq('A0'),sq('A1')),add(sq('Aa'),sq('As')))
prime=1000000007
assert all(prime%d for d in range(2,int(prime**.5)+1))
ports={}
for name,meta in B['ports'].items():
 rawg=(p72/meta['path']).read_bytes();assert hashlib.sha256(rawg).hexdigest()==meta['sha256_gzip'];raw=gzip.decompress(rawg);assert len(raw)==meta['raw_bytes'] and hashlib.sha256(raw).hexdigest()==meta['sha256_raw'];val=int.from_bytes(raw,'little');assert val>0 and val.bit_length()==meta['bits'];ports[name]=val%prime
# Different weighted affine diagonal from the author's all-t ray.
def plus(a,b,s):
 out=[0]*max(len(a),len(b))
 for i in range(len(out)):out[i]=((a[i] if i<len(a) else 0)+s*(b[i] if i<len(b) else 0))%prime
 while len(out)>1 and out[-1]==0:out.pop()
 return out
def mult(a,b):
 out=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):out[i+j]=(out[i+j]+x*y)%prime
 while len(out)>1 and out[-1]==0:out.pop()
 return out
leads=[]
for g in (g97,g96):
 v={k:[(i+2)%prime,i+1] for i,k in enumerate(g['witnesses'])};v.update({k:[x] for k,x in ports.items()})
 def ev(x):
  if type(x)==int:return [x%prime]
  if type(x)==str:return v[x]
  op,a,b=x;A=ev(a);B=ev(b);return mult(A,B) if op=='*' else plus(A,B,1 if op=='+' else -1)
 for n,expr in g['derived_fixed_leaves'].items():v[n]=ev(expr)
 for n,op,a,b in g['source']:
  A=ev(a);B=ev(b);v[n]=mult(A,B) if op=='*' else plus(A,B,1 if op=='+' else -1)
 assert len(v[g['output']])==51 and v[g['output']][-1]!=0;leads.append(v[g['output']][-1])
assert leads[0]==leads[1]
print(json.dumps({'status':'PASS_SCOPED_INDEPENDENT_REVIEW','author_receipt_reproduced':True,'operations':[97,96],'degree_upper':50,'independent_weighted_ray_leading_mod_prime':leads[0],'ray_prime':prime,'scope':'External pointwise transformation and fixed-port degree; no Lean, file semantics or new P72 ancestry proof.'},indent=2))
