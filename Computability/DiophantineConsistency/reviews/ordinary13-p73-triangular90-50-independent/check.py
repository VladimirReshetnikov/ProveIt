#!/usr/bin/env python3
import gzip,hashlib,json,subprocess,sys
from collections import Counter,defaultdict
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
base=Path(__file__).resolve().parents[2];p=base/'research/ordinary13-p73-triangular91-50';D=base/'con-zfc-diophantine-forms'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for f,h in {'README.md':'2dab13394a1c66aa84f8412e83739d0416e0eb879a1765b9e8f27be1849f6e12','check.py':'74929d544ceacdd139b855f716254515b639c0830d670463c6cd58b7984fb75f','p73_rewrite91_30.json':'474152760b9b915e6346f0bff6b41b1db57a3634ed8dd1cf49483c2e5cc36180','p73_90.json':'25abb3eb6cf9908b5e97f9099fa83e93f89d18faa098836895f81662abbd5833','p73_91.json':'8f0e22b74373c5b73874971dc0b5fd6f17e7755d19c5c43c2087a778ff7fa5ae','p61_92.json':'5997d125070c4f55c383a009107cf7b3726f15a67cdeab588326170aa1f79c04','result.json':'89b35220ee24a4905a844100eff82db6890c2ea86196dfd6d452ee5caef45163'}.items():assert sha(p/f)==h
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check.py')],cwd=base,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=120);assert not r.stderr and r.stdout==(p/'result.json').read_bytes()
p73=D/'73-guard-reanchoring/positive';p61=D/'61-congruence-carriers/positive';p72=D/'72-congruence-sextic/positive13'
files=[(p73/'p13_degree30.json','e96cd6c8950711a6a26392b27c1ab531cb9df37277e0426cc40cdd1138846a5b'),(p61/'p13_degree34.json','515c29db7e07406dc70289b405bf59221480e2ebc3b22fdac01ee2de30b30b43'),(p73/'PROOF.md','96c5d29cb8276ec802b301e5606a3d7223dbc6426cc926c1c4298b7aac3a2e57'),(p61/'ACTIVE_BINDING.json','99a0944bbf09b368b227413312bc94e9c439578cc99582de18e2ca1339ff33b9'),(p72/'ACTIVE_BINDING.json','6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf')]
for f,h in files:assert sha(f)==h
orig=json.loads(files[0][0].read_text());orig61=json.loads(files[1][0].read_text());b61=json.loads(files[3][0].read_text());b72=json.loads(files[4][0].read_text());gs={n:json.loads((p/n).read_text()) for n in ('p73_rewrite91_30.json','p73_90.json','p73_91.json','p61_92.json')}
# Independently inspect ordered source edits and named consumers.
def reassociation(old,new):
 oldrows=old['source']; newrows=new['source'];rmap={r[0]:r for r in oldrows};assert rmap['M']==['M','*','q3','qm'] and rmap['g22']==['g22','*','k','qm'] and rmap['W']==['W','+',1,'g22'] and rmap['g35']==['g35','*','W','q3']
 assert [r[0] for r in oldrows if 'g22' in r[2:]]==['W'] and [r[0] for r in oldrows if 'W' in r[2:]]==['g35']
 expected=[]
 for row in oldrows:
  if row[0] in ('g22','W'):continue
  expected.extend([['kM','*','k','M'],['g35','+','q3','kM']] if row[0]=='g35' else [row])
 assert newrows==expected
reassociation(orig,gs['p73_rewrite91_30.json']);reassociation(gs['p73_91.json'],gs['p73_90.json'])
# The exact source delta leaves the two carrier residual computations unchanged,
# except the already-proved g35 sharing in the 90-gate graph.
for fn,par,removed,added,modified in [
 ('p73_91.json',orig,{'I','Kaux','g71','g72'},{'iDc','scaled_f2m','shared_square'},{'As','g80','g81','g82'}),
 ('p73_90.json',orig,{'I','Kaux','W','g22','g71','g72'},{'iDc','kM','scaled_f2m','shared_square'},{'As','g35','g80','g81','g82'}),
 ('p61_92.json',orig61,{'I','Kaux','g72','g73'},{'iDc','scaled_f2m','shared_square'},{'As','g81','g82','g83'})]:
 a={r[0]:r for r in par['source']};b={r[0]:r for r in gs[fn]['source']}
 assert set(a)-set(b)==removed and set(b)-set(a)==added
 assert {n for n in set(a)&set(b) if a[n]!=b[n]}==modified
# Every parent and transformed graph shares its original interface.
for n,g in gs.items():
 par=orig61 if n.startswith('p61') else orig
 assert all(g[k]==par[k] for k in ('witnesses','fixed_numerals','residuals','output')) and len(g['witnesses'])==13 and len(g['fixed_numerals'])==4
 assert set(g['fixed_numerals'])=={'beta','K0','MC','MF'}
# Check full graph topology, gate and all input liveness, and degree upper propagation.
degrees={}
for n,g in [('parent',orig),*gs.items()]:
 ready=set(g['witnesses']+g['fixed_numerals']);deg={x:1 for x in g['witnesses']};deg.update({x:0 for x in g['fixed_numerals']})
 for name,op,a,b in g['source']:
  assert name not in ready and op in ('+','-','*') and all(type(x)==int or x in ready for x in (a,b));get=lambda x:0 if type(x)==int else deg[x]
  deg[name]=get(a)+get(b) if op=='*' else max(get(a),get(b));ready.add(name)
 need={g['output']}
 for name,op,a,b in reversed(g['source']):
  if name in need:need.update((a,b))
 assert all(name in need for name,_,_,_ in g['source']) and set(g['witnesses']+g['fixed_numerals'])<=need
 target={'parent':92,'p73_rewrite91_30.json':91,'p73_90.json':90,'p73_91.json':91,'p61_92.json':92}[n];assert len(g['source'])==target
 if n in ('p73_90.json','p73_91.json','p61_92.json'):assert deg[g['output']]==50
 degrees[n]=deg
# Exact multivariate integer polynomials for cuts around actual transformed subgraphs.
def atom(x):return {(x,):1}
def add(a,b,s=1):
 d=defaultdict(int,a)
 for k,v in b.items():d[k]+=s*v
 return {k:v for k,v in d.items() if v}
def mul(a,b):
 d=defaultdict(int)
 for x,u in a.items():
  for y,v in b.items():d[tuple(sorted(x+y))]+=u*v
 return {k:v for k,v in d.items() if v}
one={():1};cuts={x:atom(x) for x in ('Delta','c2','i','f2m','V','u','A0','A1')}
def evalcut(g):
 v=dict(cuts)
 def ev(x):
  if type(x)==int:return {():x} if x else {}
  return v.get(x)
 for n,op,a,b in g['source']:
  if n in v:continue
  aa,bb=ev(a),ev(b)
  if aa is not None and bb is not None:v[n]=mul(aa,bb) if op=='*' else add(aa,bb,1 if op=='+' else -1)
 return v
for parent,child in ((orig,gs['p73_91.json']),(orig,gs['p73_90.json']),(orig61,gs['p61_92.json'])):
 old,new=evalcut(parent),evalcut(child);y=add(cuts['V'],cuts['u']);gap=add(mul(y,y),mul(cuts['V'],cuts['V']),-1)
 assert new['As']==mul(cuts['Delta'],old['As']) and new['Aa']==add(old['Aa'],mul(mul(cuts['Delta'],gap),old['As']))
 for graph,v in ((parent,old),(child,new)):
  sq=lambda x:mul(v[x],v[x]); assert v[graph['output']]==add(add(sq('A0'),sq('A1')),add(sq('Aa'),sq('As')))
# Formal one-gate sharing and first-norm degree cancellation.
q3,qm,k,M,ell,d=map(atom,('q3','qm','k','M','ell','d'))
assert mul(add(one,mul(k,qm)),q3)==add(q3,mul(k,mul(q3,qm)))
a0=add(mul(add(mul(M,ell),d),add(mul(M,ell),d)),mul(mul(M,M),add(one,mul(ell,add(ell,k)))),-1)
a0b=add(add(mul(d,d),mul(mul(M,ell),add(add(d,d),mul(M,k),-1))),mul(M,M),-1)
assert a0==a0b
src={r[0]:r for r in orig['source']}
for row in [['g30','+','ell','k'],['g31','+','g30','r'],['g32','*','M','g31'],['g33','*','Y','qm'],['g34','+','g32','g33'],['g35','*','W','q3'],['g36','*','Bt','g35'],['root0','-','g34','g36'],['g38','*','ell','g30'],['rad0','+',1,'g38'],['g40','*','root0','root0'],['g41','*','M','M'],['g42','*','g41','rad0'],['A0','-','g40','g42'],['g78','+','V','u'],['y2','*','g78','g78'],['g80','*','V','V'],['g81','-','y2','g80'],['g82','*','Kaux','g81'],['g83','-','y2','g82'],['Aa','-','g83',1]]:assert src[row[0]]==row
z=degrees['parent'];assert z['M']<=4 and z['ell']<=4 and z['k']<=1 and z['r']<=1 and z['Y']<=1 and z['qm']<=1 and z['q3']<=3 and z['W']<=2 and z['Bt']<=2
assert z['Delta']<=4 and z['f2m']<=2 and z['V']<=6 and z['A1']<=14 and z['As']<=14
# d <=7 implies A0<=15; factored gap<=7 implies Aa<=13: total <=30.
assert max(2*15,2*14,2*13,2*14)==30
P=1000000007;assert all(P%x for x in range(2,int(P**.5)+1));ports={}
assert set(b61['ports'])==set(b72['ports'])=={'beta','K0','MC','MF'}
for n,m in b72['ports'].items():
 assert b61['ports'][n]['sha256']==m['sha256_raw'] and b61['ports'][n]['gzip_sha256']==m['sha256_gzip']
 packed=(p72/m['path']).read_bytes();assert hashlib.sha256(packed).hexdigest()==m['sha256_gzip'];raw=gzip.decompress(packed);assert hashlib.sha256(raw).hexdigest()==m['sha256_raw'] and len(raw)==m['raw_bytes'];value=int.from_bytes(raw,'little');assert value>0 and value.bit_length()==m['bits'];ports[n]=value%P
# Different weighted affine ray through each of 13 unknowns, checking full graphs.
def padd(a,b,s):
 out=[((a[i] if i<len(a) else 0)+s*(b[i] if i<len(b) else 0))%P for i in range(max(len(a),len(b)))]
 while len(out)>1 and not out[-1]:out.pop()
 return out
def pmul(a,b):
 o=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):o[i+j]=(o[i+j]+x*y)%P
 while len(o)>1 and not o[-1]:o.pop()
 return o
leaders={}
for n,g in [('parent',orig),*gs.items()]:
 v={x:[i+2,i+1] for i,x in enumerate(g['witnesses'])};v.update({k:[z] for k,z in ports.items()})
 for name,op,a,b in g['source']:
  A=[a%P] if type(a)==int else v[a];B=[b%P] if type(b)==int else v[b]
  v[name]=pmul(A,B) if op=='*' else padd(A,B,1 if op=='+' else -1)
 expected=30 if n in ('parent','p73_rewrite91_30.json') else 50
 assert len(v[g['output']])==expected+1 and v[g['output']][-1]!=0;leaders[n]=v[g['output']][-1]
assert leaders['parent']==leaders['p73_rewrite91_30.json'] and leaders['p73_91.json']==leaders['p73_90.json']
print(json.dumps({'status':'PASS_SCOPED_INDEPENDENT_REVIEW','author_receipt_reproduced':True,'primary_operations_degrees':[[91,30],[90,50]],'weighted_ray_leaders':leaders,'prime':P,'scope':'External graph, exact ring and fixed-port degree checks; no Lean, file binding or foundational replay.'},indent=2))
