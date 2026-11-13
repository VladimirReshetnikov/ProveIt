#!/usr/bin/env python3
"""Independent RGS partition enumeration and fixed-port factor degree checks."""
import collections,gzip,hashlib,itertools,json,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('requires python3 -I -S -B')
D=Path(__file__).resolve().parents[2];P=D/'research/sphere-factor-partition-screen';G=D/'research/fourteen-nonzero-spheres/polynomial71.json';S=G.parent;prime=1000000007
def H(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def need(v,s):
 if not v:raise RuntimeError(s)
need(H(P/'check.py')=='4d2c0d070bccc0e95f731395f1a12268cfdf55a0b32761935a16b8e9877da97f' and H(P/'result.json')=='6fcefc6496055f132b01c31e45fdf75f0231d59f1006a5899bded4370de54904','screen pins');need(H(G)=='937752350556a94539584db8f646ff9e02d25a7113e6d4af70ac22c1b1e01ad2','graph pin');g=json.loads(G.read_text());need(len(g['source'])==71 and g['source'][61][0]=='U','prefix')
factors=('N0','N1','U','Nt','Z');edges={r[0]:r[2:] for r in g['source']};seen=set();todo=list(factors)
while todo:
 n=todo.pop()
 if n in edges and n not in seen:seen.add(n);todo.extend(edges[n])
need(seen=={r[0] for r in g['source'][:62]},'all 62 prefix gates required by five factors')
# Check N1 cancellation shape before using its exact degree-18 bound.
r={z[0]:z for z in g['source']};need(all(r[n]==v for n,v in {'a':['a','+','E','Y'],'four_a':['four_a','*',4,'a'],'H':['H','+','four_a',3],'a2':['a2','*','a','a'],'Delta':['Delta','+','a2','H'],'ac':['ac','*','a','c'],'main_base':['main_base','+','X','ac'],'gammaH':['gammaH','*','gamma','H'],'main_root':['main_root','+','main_base','gammaH'],'main_square':['main_square','*','main_root','main_root'],'c2':['c2','*','c','c'],'Dc2':['Dc2','*','Delta','c2'],'N1':['N1','-','main_square','Dc2']}.items()),'N1 shape')
deg={n:1 for n in g['witnesses']};deg.update({n:0 for n in g['fixed_numerals']});poly={n:[0,1] for n in g['witnesses']}
for n,m in g['coefficient_binding']['ports'].items():
 z=(S/'coefficients'/m['file']).read_bytes();need(hashlib.sha256(z).hexdigest()==m['gzip_sha256'],'gzip '+n);raw=gzip.decompress(z);need(hashlib.sha256(raw).hexdigest()==m['raw_sha256'] and len(raw)==m['raw_bytes'],'raw '+n);poly[n]=[int.from_bytes(raw,'big')%prime]
def univ(x,y,op):
 z=[0]*(len(x)+len(y)-1 if op=='*' else max(len(x),len(y)))
 if op=='*':
  for i,a in enumerate(x):
   for j,b in enumerate(y):z[i+j]=(z[i+j]+a*b)%prime
 else:
  for i,a in enumerate(x):z[i]=(z[i]+a)%prime
  for i,b in enumerate(y):z[i]=(z[i]+(1 if op=='+' else -1)*b)%prime
 while len(z)>1 and not z[-1]:z.pop()
 return z
for n,o,x,y in g['source'][:62]:
 dx=deg[x] if isinstance(x,str) else 0;dy=deg[y] if isinstance(y,str) else 0;deg[n]=dx+dy if o=='*' else max(dx,dy)
 if n=='N1':
  need((deg['X'],deg['a'],deg['c'],deg['H'],deg['gamma'])==(2,6,5,6,1),'degree inputs');deg[n]=max(2*deg['X'],deg['X']+deg['a']+deg['c'],deg['gamma']+deg['H']+max(deg['X'],deg['a']+deg['c']),2*deg['gamma']+2*deg['H'],deg['H']+2*deg['c'])
 poly[n]=univ(poly[x] if isinstance(x,str) else [x%prime],poly[y] if isinstance(y,str) else [y%prime],o)
want={'N0':22,'N1':18,'U':30,'Nt':2,'Z':34};need({x:deg[x] for x in factors}==want,'factor bounds');need(all(len(poly[x])-1==want[x] and poly[x][-1] for x in factors),'factor lower rays')
# Independent exhaustive enumeration via restricted-growth strings over five positions.
parts=[]
for labels in itertools.product(range(5),repeat=5):
 if labels[0]!=0 or any(labels[j]>1+max(labels[:j]) for j in range(1,5)):continue
 blocks=tuple(tuple(factors[i] for i,x in enumerate(labels) if x==k) for k in range(max(labels)+1));parts.append(blocks)
need(len(parts)==52 and len(set(parts))==52,'Bell(5)');out={}
for k in range(1,6):
 q=[p for p in parts if len(p)==k]; need(len(q)==[1,15,25,10,1][k-1],'Stirling count');operation=62+(5-k)+k+1+(k-1)+(k>1);scores={p:2*max(sum(want[x] for x in block) for block in p) for p in q};best=min(scores.values());opt={frozenset(map(frozenset,p)) for p,v in scores.items() if v==best};out[str(k)]={'count':len(q),'operations':operation,'best_degree':best,'optimal_count':len(opt)}
 need((operation,best)==[(68,212),(70,108),(71,80),(72,68),(73,68)][k-1],'optimum')
 original=json.loads((P/'result.json').read_text())['summary'][str(k)];given={frozenset(map(frozenset,p)) for p in original['optimal_partitions']};need(original['count']==len(q) and original['operations']==[operation] and original['best_degree']==best and given==opt,'author partition table')
a=subprocess.run([sys.executable,'-I','-S','-B',str(P/'check.py')],capture_output=True);need(a.returncode==0 and a.stdout==(P/'result.json').read_bytes(),'author rerun')
print(json.dumps({'status':'PASS_SCOPED_INDEPENDENT_REVIEW','partitions':52,'summary':out,'factor_degrees':want,'factor_leading_residues_mod_1000000007':{x:poly[x][-1] for x in factors},'scope':'Specified unshared 62-prefix product/square partition family only; no zero-equivalence or global circuit lower bound.'},indent=2,sort_keys=True))
