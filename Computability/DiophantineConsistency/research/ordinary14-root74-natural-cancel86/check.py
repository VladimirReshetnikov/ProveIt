#!/usr/bin/env python3
"""Exact cut identities and authentic-port degree for natural 86 SLP; no Lean."""
from pathlib import Path
import gzip,hashlib,json,random,subprocess,sys
P=Path(__file__).resolve().parent;D=P.parents[1]
H=lambda b:hashlib.sha256(b).hexdigest()
def load(path,sha):
 b=path.read_bytes();assert H(b)==sha,(str(path),H(b));return json.loads(b)
a=load(D/'research/ordinary14-root74-natural-shift88/candidate.json','85675d2db0c6a40e0f759b9b67351cc74d8bc374ea7f85f85ea754eae8f9276d')
b=load(P/'candidate.json','0211a1bcac635af617090facdc3b7f98d18ad94579027df840532d87ae5a5170')
assert a['domain']==b['domain']=='nonnegative integers' and a['witnesses']==b['witnesses'] and a['fixed_numerals']==b['fixed_numerals']
assert b['parent_sha256']=='85675d2db0c6a40e0f759b9b67351cc74d8bc374ea7f85f85ea754eae8f9276d'
assert a['operations']==len(a['source'])==88 and b['operations']==len(b['source'])==86 and a['output']==b['output']=='out'
expected=[]
for row in a['source']:
 n=row[0]
 if n in ('F','h'):continue
 if n=='qF':expected.append(['qF','-','qm','n_F'])
 elif n=='guard_base':expected.append(['guard_base','-','g27','n_F'])
 elif n=='bt_quotient':expected.append(['bt_quotient','*','qm','n_h'])
 else:expected.append(row)
assert b['source']==expected
arows={n:(op,x,y) for n,op,x,y in a['source']};brows={n:(op,x,y) for n,op,x,y in b['source']}
for n,row in {'F':('+','n_F',1),'h':('+','n_h',1),'q':('+',1,'qm'),
              'qF':('-','q','F'),'guard_base':('+','g27','qF'),
              'bt_quotient':('*','qm','h'),'guard':('-','guard_base','bt_quotient')}.items():
 assert arows[n]==row,(n,arows[n])
for n,row in {'qF':('-','qm','n_F'),'guard_base':('-','g27','n_F'),
              'bt_quotient':('*','qm','n_h'),'guard':('-','guard_base','bt_quotient')}.items():
 assert brows[n]==row,(n,brows[n])
# These are the only old uses of the removed input increments and intermediate cuts.
uses=lambda key:[r[0] for r in a['source'] if key in r[2:]]
assert uses('F')==['qF'] and uses('h')==['bt_quotient']
assert uses('guard_base')==['guard'] and uses('bt_quotient')==['guard']
known=set(b['witnesses']+b['fixed_numerals']);assert len(known)==18
for n,op,x,y in b['source']:
 assert n not in known and op in ('+','-','*')
 assert all(type(z) is int or z in known for z in (x,y));known.add(n)
live={'out'}
for n,op,x,y in reversed(b['source']):
 if n in live:live.update(z for z in (x,y) if isinstance(z,str))
assert all(r[0] in live for r in b['source']) and set(b['witnesses']+b['fixed_numerals'])<=live
# Exact sparse polynomial identities over Z[qm,nF,nh,g27], no random hash.
def C(c):return {():c} if c else {}
def X(name):return {(name,):1}
def add(a,b,sgn=1):
 r=a.copy()
 for k,v in b.items():r[k]=r.get(k,0)+sgn*v
 return {k:v for k,v in r.items() if v}
def mul(a,b):
 r={}
 for x,v in a.items():
  for y,w in b.items():
   k=tuple(sorted(x+y));r[k]=r.get(k,0)+v*w
 return {k:v for k,v in r.items() if v}
qm,nF,nh,g27=map(X,('qm','n_F','n_h','g27'))
qFold=add(add(C(1),qm),add(nF,C(1)),-1);qFnew=add(qm,nF,-1);assert qFold==qFnew
oldguard=add(add(g27,qFold),mul(qm,add(nh,C(1))),-1)
newguard=add(add(g27,nF,-1),mul(qm,nh),-1);assert oldguard==newguard
# Exact downstream DAG congruence, with qF/guard cut equalities as shared atoms.
# guard_base and bt_quotient are only used by guard and intentionally differ.
interner={}
def intern(*key):
 if key not in interner:interner[key]=len(interner)
 return interner[key]
left={x:intern('input',x) for x in a['witnesses']+a['fixed_numerals']};right=left.copy()
def arg(env,z):return intern('const',z) if type(z) is int else env[z]
B={r[0]:r for r in b['source']};checked=0
for n,op,x,y in a['source']:
 left[n]=intern(op,arg(left,x),arg(left,y))
 if n in ('F','h','guard_base','bt_quotient'):continue
 if n in ('qF','guard'):
  # Their integer-ring cut identities were checked above after their inputs agree.
  if n=='qF':assert left['qm']==right['qm']
  else:assert left['g27']==right['g27'] and left['qF']==right['qF'] and left['qm']==right['qm']
  left[n]=right[n]=intern('proved_equal_cut',n)
 else:
  _,o,u,v=B[n];right[n]=intern(o,arg(right,u),arg(right,v));assert left[n]==right[n],n
 checked+=1
assert left['out']==right['out'] and checked==84
# Finite full-graph controls include arbitrary signed and natural inputs/ports.
def calc(g,env):
 e=env.copy()
 for n,op,x,y in g['source']:
  x=x if type(x) is int else e[x];y=y if type(y) is int else e[y]
  e[n]=x+y if op=='+' else x-y if op=='-' else x*y
 return e
rng=random.Random(147486)
for limits in ((-5,6),(0,7)):
 for _ in range(250):
  env={v:rng.randrange(*limits) for v in b['witnesses']};env.update({v:rng.randrange(-5,6) for v in b['fixed_numerals']})
  aa=calc(a,env);bb=calc(b,env)
  assert all(aa[n]==bb[n] for n,_,_,_ in b['source'] if n not in ('guard_base','bt_quotient'))
# Reproduce the reviewed 88 certificate (including the exact sparse 107 bound).
parentcheck=D/'research/ordinary14-root74-natural-shift88/check.py';assert H(parentcheck.read_bytes())=='5035b757c42ac25266c4ae19c471785d481522dde29951d8ba184e06de5bb7be'
parentresult=D/'research/ordinary14-root74-natural-shift88/result.json';assert H(parentresult.read_bytes())=='c2b714d6527a17487ce51493453b7b900ed5c1d0743366195dd84df3d65ce24a'
r=subprocess.run([sys.executable,'-I','-S','-B',str(parentcheck)],cwd=D,capture_output=True,check=True,timeout=90);assert not r.stderr and r.stdout==parentresult.read_bytes()
pr=json.loads(parentresult.read_bytes());assert pr['degree_upper']==107 and pr['ray_degree']==107
# Authenticate actual P72/P115 port bytes and independently evaluate 86 on n_i=t.
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
print(json.dumps({'scope':'external natural-domain exact cut equivalence and authenticated P72/P115 degree; no Lean/formal or PDF binding','inputs':14,'operations':86,'removed_increment_gates':2,'exact_cut_identities':2,'shared_dag_nodes_checked':checked,'all_gates_inputs_ports_live':True,'signed_and_natural_controls':500,'degree_upper_from_replayed_88':107,'ray_prime':prime,'ray_degree':len(e['out'])-1,'ray_leader':e['out'][-1]},sort_keys=True,indent=2))
