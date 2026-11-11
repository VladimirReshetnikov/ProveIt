#!/usr/bin/env python3
"""Exact graph delta, guard identity and compact44 degree ray; no Lean."""
import gzip,hashlib,json,random,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and not sys.flags.optimize
D=Path(__file__).resolve().parents[2];P=Path(__file__).resolve().parent
def pin(p,h):raw=p.read_bytes();assert hashlib.sha256(raw).hexdigest()==h,p;return raw
old=json.loads(pin(D/'research/ordinary14-shifted-guard87-probe/candidate.json','405dbed5bf465dacac2246e6e8b2c53bcb3dda9b4b13ba277f4a18cdd43ae210'));g=json.loads(pin(P/'candidate.json','ecd34ccc9032fd7f2ef1b767b2182fe4d43aa82389b1a6857832c3dd3891c371'))
assert old['witnesses'][:-1]==g['witnesses'][:-1] and old['witnesses'][-1]=='omega' and g['witnesses'][-1]=='h' and old['fixed_numerals']==g['fixed_numerals']
assert [row[0] for row in old['source'] if 'g25' in row[2:]]==['g26'];expected=[]
for n,op,a,b in old['source']:
 if n=='g25':assert [n,op,a,b]==['g25','*','K0','q'];continue
 if n=='g26':assert [n,op,a,b]==['g26','+','X','g25'];b='K0'
 expected.append([n,op,'h' if a=='omega' else a,'h' if b=='omega' else b])
assert g['source']==expected and len(expected)==86 and g['output']==old['output']
known=set(g['witnesses']+g['fixed_numerals']);used={g['output']}
for n,op,a,b in expected:assert n not in known and op in '+-*' and all(isinstance(x,int) or x in known for x in (a,b));known.add(n)
for n,op,a,b in reversed(expected):
 if n in used:used.update(x for x in (a,b) if isinstance(x,str))
assert all(r[0] in used for r in expected) and set(g['witnesses']+g['fixed_numerals'])<=used
counts={o:sum(row[1]==o for row in expected) for o in '+-*'}
# Free-ring proof of old_guard(omega=h+C*K)=new_guard for q=b+1.
def add(a,b,s=1):
 z=a.copy()
 for k,v in b.items():z[k]=z.get(k,0)+s*v
 return {k:v for k,v in z.items() if v}
def mul(a,b):
 z={}
 for k,v in a.items():
  for l,w in b.items():
   t=tuple(sorted(k+l));z[t]=z.get(t,0)+v*w
 return {k:v for k,v in z.items() if v}
def v(n):return {(n,):1}
C,X,K,F,b,h=map(v,('C','X','K','F','b','h'));one={():1};q=add(one,b);omega=add(h,mul(C,K));oldguard=add(add(mul(C,add(X,mul(K,q))),F,-1),mul(b,omega),-1);newguard=add(add(mul(C,add(X,K)),F,-1),mul(b,h),-1);assert oldguard==newguard
def calc(graph,vals):
 vals=vals.copy()
 for n,op,a,b in graph['source']:
  a=a if isinstance(a,int) else vals[a];b=b if isinstance(b,int) else vals[b];vals[n]=a+b if op=='+' else a-b if op=='-' else a*b
 return vals
rng=random.Random(0x8626)
for _ in range(50):
 vals={x:rng.randrange(-4,5) for x in g['witnesses']+g['fixed_numerals']};new=calc(g,vals);parentvals={x:vals[x] for x in old['witnesses'][:-1]+old['fixed_numerals']};parentvals['omega']=vals['h']+new['C']*vals['K0'];prior=calc(old,parentvals)
 assert prior['guard']==new['guard'] and all(prior[n]==new[n] for n in ('A0','A1','Fa','g72','guarded_out'))
# Positive scalar guard control (not a full equation zero).
vals={n:1 for n in g['witnesses']+g['fixed_numerals']};vals.update(beta=3,K0=2,J=1,F=1,alpha=2,X=17,h=6);a=calc(g,vals);assert a['C']==1 and a['guard']==0 and vals['h']+a['C']*vals['K0']==8
# Pin the decoder used for old-to-new h positivity and reproduce its receipt.
Q=D/'reviews/ordinary14-shifted-guard87-calibration-decoder-independent';pin(Q/'check.py','3e3b490dee0502f592d960a7192947674bac02d70101f1e89bc982ea4cb93163');pin(Q/'result.json','d58c405d5d1e0d9dd02847419d5c01b8a1f4d0a4d3b2f8e0866dc8948c01ba1e');r=subprocess.run([sys.executable,'-I','-S','-B',str(Q/'check.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=120);assert not r.stderr and r.stdout==(Q/'result.json').read_bytes()
root=D/'con-zfc-diophantine-forms/72-congruence-sextic/positive13';B=json.loads(pin(root/'ACTIVE_BINDING.json','6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf'));C0=json.loads(pin(D/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json','dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01'));ports={}
for n,m in B['ports'].items():
 assert C0['ports'][n]['sha256_raw']==m['sha256_raw'] and C0['ports'][n]['sha256_gzip']==m['sha256_gzip'];raw=gzip.decompress(pin(root/m['path'],m['sha256_gzip']));assert len(raw)==m['raw_bytes'] and hashlib.sha256(raw).hexdigest()==m['sha256_raw'];ports[n]=int.from_bytes(raw,'little')
assert ports['beta']>=46 and 0<ports['MC']<ports['beta'] and 0<ports['MF']<2*ports['beta'] and 0<=ports['K0']<(ports['beta']+1)**2
mod=1000000007;env={n:[0,1] for n in g['witnesses']};env.update({n:[x%mod] for n,x in ports.items()})
def trim(a):
 while len(a)>1 and not a[-1]:a.pop()
 return a
def pol(op,x,y):
 if op!='*':return trim([((x[i] if i<len(x) else 0)+(1 if op=='+' else -1)*(y[i] if i<len(y) else 0))%mod for i in range(max(len(x),len(y)))])
 z=[0]*(len(x)+len(y)-1)
 for i,a in enumerate(x):
  for j,b in enumerate(y):z[i+j]=(z[i+j]+a*b)%mod
 return trim(z)
for n,op,a,b in expected:env[n]=pol(op,[a%mod] if isinstance(a,int) else env[a],[b%mod] if isinstance(b,int) else env[b])
assert len(env['guarded_out'])==27 and env['guarded_out'][-1]!=0
print(json.dumps({'operations':86,'operation_breakdown':counts,'all_gates_inputs_ports_live':True,'exact_guard_shear':True,'K0_times_q_only_used_in_deleted_node':True,'positive_guard_control':True,'prime':mod,'ray_degree':len(env['guarded_out'])-1,'ray_leader':env['guarded_out'][-1],'scope':'proposed standard-positive existence equivalence at compact44 conditional on reviewed decoder; no Lean or PDF binding'},sort_keys=True,indent=2))
