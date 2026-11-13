#!/usr/bin/env python3
"""Prove exact zeta cut, check live natural85 graph and authenticated ray; no Lean."""
from pathlib import Path
import gzip,hashlib,json,random,subprocess,sys
P=Path(__file__).resolve().parent;D=P.parents[1]
H=lambda b:hashlib.sha256(b).hexdigest()
def load(path,sha):
 b=path.read_bytes();assert H(b)==sha,(str(path),H(b));return json.loads(b)
a=load(D/'research/ordinary14-root74-natural-cancel86/candidate.json','0211a1bcac635af617090facdc3b7f98d18ad94579027df840532d87ae5a5170')
b=load(P/'candidate.json','24a5ddfdabeae36eb40867239fdc5dfd53ba60d611f0e83268ffb9bfbac85957')
assert a['domain']==b['domain']=='nonnegative integers' and a['witnesses']==b['witnesses'] and a['fixed_numerals']==b['fixed_numerals']
assert b['parent_sha256']=='0211a1bcac635af617090facdc3b7f98d18ad94579027df840532d87ae5a5170'
assert a['operations']==len(a['source'])==86 and b['operations']==len(b['source'])==85 and a['output']==b['output']=='out'
expected=[]
for row in a['source']:
 n=row[0]
 if n in ('zeta','g52'):continue
 if n=='k':expected.extend([['kbase','+','eta','n_zeta'],['k','+','kbase',1]])
 elif n=='r0':expected.append(['r0','-','kbase','R'])
 else:expected.append(row)
assert b['source']==expected
arows={n:(op,x,y) for n,op,x,y in a['source']};brows={n:(op,x,y) for n,op,x,y in b['source']}
for n,row in {'zeta':('+','n_zeta',1),'k':('+','eta','zeta'),'g52':('-','k','R'),'r0':('-','g52',1)}.items():assert arows[n]==row
for n,row in {'kbase':('+','eta','n_zeta'),'k':('+','kbase',1),'r0':('-','kbase','R')}.items():assert brows[n]==row
uses=lambda key:[r[0] for r in a['source'] if key in r[2:]]
assert uses('zeta')==['k'] and uses('g52')==['r0']
known=set(b['witnesses']+b['fixed_numerals']);assert len(known)==18
for n,op,x,y in b['source']:
 assert n not in known and op in ('+','-','*')
 assert all(type(z) is int or z in known for z in (x,y));known.add(n)
live={'out'}
for n,op,x,y in reversed(b['source']):
 if n in live:live.update(z for z in (x,y) if isinstance(z,str))
assert all(r[0] in live for r in b['source']) and set(b['witnesses']+b['fixed_numerals'])<=live
# Exact sparse integer-polynomial cuts.
def C(c):return {():c} if c else {}
def X(name):return {(name,):1}
def add(a,b,sgn=1):
 r=a.copy()
 for k,v in b.items():r[k]=r.get(k,0)+sgn*v
 return {k:v for k,v in r.items() if v}
eta,nz,R=map(X,('eta','n_zeta','R'))
kbase=add(eta,nz); kold=add(eta,add(nz,C(1))); knew=add(kbase,C(1))
assert kold==knew
assert add(add(kold,R,-1),C(1),-1)==add(kbase,R,-1)
# Congruence of all common nodes, using only the two established cut identities.
interner={}
def intern(*key):
 if key not in interner:interner[key]=len(interner)
 return interner[key]
left={x:intern('input',x) for x in a['witnesses']+a['fixed_numerals']};right=left.copy()
def arg(env,z):return intern('const',z) if type(z) is int else env[z]
B={r[0]:r for r in b['source']};checked=0
for n,op,x,y in a['source']:
 left[n]=intern(op,arg(left,x),arg(left,y))
 if n in ('zeta','g52'):continue
 if n=='k':
  assert left['eta']==right['eta'] and left['n_zeta']==right['n_zeta']
  right['kbase']=intern('+',right['eta'],right['n_zeta'])
  right['k']=intern('+',right['kbase'],intern('const',1))
  left[n]=right[n]=intern('proved_equal_cut',n)
 elif n=='r0':
  assert left['R']==right['R'] and left['k']==right['k']
  right[n]=intern('-',right['kbase'],right['R'])
  left[n]=right[n]=intern('proved_equal_cut',n)
 else:
  _,o,u,v=B[n];right[n]=intern(o,arg(right,u),arg(right,v));assert left[n]==right[n],n
 checked+=1
assert left['out']==right['out'] and checked==84
# Finite full-graph controls including signed ports and signed/natural inputs.
def calc(g,env):
 e=env.copy()
 for n,op,x,y in g['source']:
  x=x if type(x) is int else e[x];y=y if type(y) is int else e[y]
  e[n]=x+y if op=='+' else x-y if op=='-' else x*y
 return e
rng=random.Random(147485)
for limits in ((-5,6),(0,7)):
 for _ in range(250):
  env={v:rng.randrange(*limits) for v in b['witnesses']};env.update({v:rng.randrange(-5,6) for v in b['fixed_numerals']})
  aa=calc(a,env);bb=calc(b,env)
  assert all(aa[n]==bb[n] for n,_,_,_ in a['source'] if n not in ('zeta','g52'))
# Replay the source certificate for 86, including the inherited degree upper bound.
parentcheck=D/'research/ordinary14-root74-natural-cancel86/check.py';assert H(parentcheck.read_bytes())=='a2d45e7346c9d41e157318b67cf19a412e5a4f35b4a031c1a7073d5c8058ab05'
parentresult=D/'research/ordinary14-root74-natural-cancel86/result.json';assert H(parentresult.read_bytes())=='f19c4f42c52605ccebef713e7fbe3705ab2145c8136a783e90a884158bc47eda'
r=subprocess.run([sys.executable,'-I','-S','-B',str(parentcheck)],cwd=D,capture_output=True,check=True,timeout=120);assert not r.stderr and r.stdout==parentresult.read_bytes()
pr=json.loads(parentresult.read_bytes());assert pr['degree_upper_from_replayed_88']==107 and pr['ray_degree']==107
# Authenticate actual P72/P115 port bytes and independently evaluate 85 on n_i=t.
p72=D/'con-zfc-diophantine-forms/72-congruence-sextic/positive13'
bind=load(p72/'ACTIVE_BINDING.json','6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf')
b115=load(D/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json','dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01')
fixed={}
for n,m in bind['ports'].items():
 assert b115['ports'][n]['sha256_raw']==m['sha256_raw'] and b115['ports'][n]['sha256_gzip']==m['sha256_gzip']
 z=(p72/m['path']).read_bytes();assert H(z)==m['sha256_gzip'];raw=gzip.decompress(z);assert len(raw)==m['raw_bytes'] and H(raw)==m['sha256_raw'];fixed[n]=int.from_bytes(raw,'little')
assert set(fixed)==set(b['fixed_numerals']);prime=1000000007

def trim(a):
 while len(a)>1 and a[-1]==0:a.pop()
 return a
def padd(a,b,sgn):return trim([((a[i] if i<len(a) else 0)+sgn*(b[i] if i<len(b) else 0))%prime for i in range(max(len(a),len(b)))])
def pmul(a,b):
 z=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):z[i+j]=(z[i+j]+x*y)%prime
 return trim(z)
e={v:[0,1] for v in b['witnesses']};e.update({v:[x%prime] for v,x in fixed.items()})
def val(x):return [x%prime] if type(x) is int else e[x]
for n,op,x,y in b['source']:
 x,y=val(x),val(y);e[n]=pmul(x,y) if op=='*' else padd(x,y,1 if op=='+' else -1)
assert len(e['out'])-1==107 and e['out'][-1]==419359493
print(json.dumps({'scope':'external natural-domain exact cut equivalence and authenticated P72/P115 degree; no Lean/formal or PDF binding','inputs':14,'operations':85,'exact_cut_identities':2,'shared_dag_nodes_checked':checked,'all_gates_inputs_ports_live':True,'signed_and_natural_controls':500,'degree_upper_from_replayed_86':107,'ray_prime':prime,'ray_degree':len(e['out'])-1,'ray_leader':e['out'][-1]},sort_keys=True,indent=2))
