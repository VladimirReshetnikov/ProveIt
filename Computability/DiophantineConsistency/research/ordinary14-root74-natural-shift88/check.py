#!/usr/bin/env python3
"""External exact-DAG shift and authenticated specialized degree; no Lean."""
from pathlib import Path
import gzip,hashlib,json,random
D=Path(__file__).resolve().parents[2];P=Path(__file__).resolve().parent
H=lambda b:hashlib.sha256(b).hexdigest()
def load(path,sha):
 b=path.read_bytes();assert H(b)==sha,(str(path),H(b));return json.loads(b)
p=load(D/'research/ordinary14-positive-guard74/candidate.json','e70af4f896013695368180743f514c027faa86f8b3cedd5479b22e64e4c26093')
c=load(P/'candidate.json','85675d2db0c6a40e0f759b9b67351cc74d8bc374ea7f85f85ea754eae8f9276d')
assert p['domain']=='strictly positive integers' and c['domain']=='nonnegative integers'
old=p['witnesses'];new=c['witnesses'];assert len(old)==len(new)==14 and new==['n_'+n for n in old]
assert c['parent_sha256']=='e70af4f896013695368180743f514c027faa86f8b3cedd5479b22e64e4c26093'
assert c['fixed_numerals']==p['fixed_numerals'] and c['output']==p['output']=='out'
assert c['source']==[[x,'+',y,1] for x,y in zip(old,new)]+p['source'] and c['operations']==len(c['source'])==88
known=set(new+c['fixed_numerals']);assert len(known)==18
for n,op,x,y in c['source']:
 assert n not in known and op in ('+','-','*')
 assert all(type(z) is int or z in known for z in (x,y));known.add(n)
live={'out'}
for n,op,x,y in reversed(c['source']):
 if n in live:live.update(z for z in (x,y) if isinstance(z,str))
assert all(n in live for n,_,_,_ in c['source'])
assert set(new+c['fixed_numerals'])<=live
# Exact structural equality of every parent gate after input substitution.
# IDs are hash-consed tuples, with no algebraic or probabilistic equality.
interner={}
def intern(*key):
 if key not in interner:interner[key]=len(interner)
 return interner[key]
def literal(x):return intern('const',x) if type(x) is int else None
one=intern('const',1);lhs={n:intern('input',n) for n in new};ports={n:intern('port',n) for n in c['fixed_numerals']};lhs.update(ports)
rhs={x:intern('+',lhs[y],one) for x,y in zip(old,new)};rhs.update(ports)
def operand(env,z):return literal(z) if type(z) is int else env[z]
for n,op,x,y in c['source']:
 lhs[n]=intern(op,operand(lhs,x),operand(lhs,y))
for n,op,x,y in p['source']:
 rhs[n]=intern(op,operand(rhs,x),operand(rhs,y));assert lhs[n]==rhs[n],n
# Independently exercise signed and natural valuations, including boundaries.
def calc(g,env):
 e=env.copy()
 for n,op,x,y in g['source']:
  x=x if type(x) is int else e[x];y=y if type(y) is int else e[y]
  e[n]=x+y if op=='+' else x-y if op=='-' else x*y
 return e
rng=random.Random(147488)
for limits in ((-5,6),(0,7)):
 for _ in range(250):
  env={v:rng.randrange(*limits) for v in new};env.update({v:rng.randrange(-5,6) for v in c['fixed_numerals']})
  oldenv={x:env[y]+1 for x,y in zip(old,new)};oldenv.update({v:env[v] for v in c['fixed_numerals']})
  a=calc(c,env);b=calc(p,oldenv);assert all(a[n]==b[n] for n,_,_,_ in p['source'])
# Actual P72 payloads, cross-pinned to P115 byte hashes; no expansion of powers.
p72=D/'con-zfc-diophantine-forms/72-congruence-sextic/positive13'
bind=load(p72/'ACTIVE_BINDING.json','6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf')
b115=load(D/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json','dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01')
fixed={}
for name,m in bind['ports'].items():
 assert b115['ports'][name]['sha256_raw']==m['sha256_raw'] and b115['ports'][name]['sha256_gzip']==m['sha256_gzip']
 z=(p72/m['path']).read_bytes();assert H(z)==m['sha256_gzip'];raw=gzip.decompress(z)
 assert len(raw)==m['raw_bytes'] and H(raw)==m['sha256_raw'];fixed[name]=int.from_bytes(raw,'little')
assert set(fixed)==set(c['fixed_numerals'])
prime=1000000007
# Upper bound tracks total degree in the 14 natural inputs, not a numerical ray.
degree={v:1 for v in new};degree.update({v:0 for v in c['fixed_numerals']})
for n,op,x,y in c['source']:
 dx=0 if type(x) is int else degree[x];dy=0 if type(y) is int else degree[y]
 degree[n]=dx+dy if op=='*' else max(dx,dy)
naive_upper=degree['out'];assert naive_upper==111
# The first main-square terms cancel. Check the exact cut from literal rows.
rows={n:(op,x,y) for n,op,x,y in c['source']}
for n,row in {'g19':('*','a','c'),'b0':('+','X','g19'),'g58':('*','U','b0'),
              'g59':('*','H','shift'),'Dstar':('+','g58','g59'),'g17':('*','a','a'),
              'Delta':('+','H','g17'),'g61':('*','Dstar','Dstar'),'g62':('*','U','U'),
              'c2':('*','c','c'),'g63':('*','Delta','c2'),'g64':('+',1,'g63'),
              'g65':('*','g62','g64'),'A1':('-','g61','g65')}.items():assert rows[n]==row,(n,rows[n])
# Independent sparse-integer polynomial identity, variables U,X,H,S,a,c.
def pa(a,b,sign=1):
 o=a.copy()
 for k,v in b.items():o[k]=o.get(k,0)+sign*v
 return {k:v for k,v in o.items() if v}
def pm(a,b):
 o={}
 for x,v in a.items():
  for y,w in b.items():
   k=tuple(i+j for i,j in zip(x,y));o[k]=o.get(k,0)+v*w
 return {k:v for k,v in o.items() if v}
def pv(i):return {tuple(int(k==i) for k in range(6)):1}
def pc(k):return {(0,)*6:k} if k else {}
U,X,H,S,A,C=map(pv,range(6));P=pa(pm(U,X),pm(H,S));B=pm(pm(U,A),C)
Dstar=pa(P,B);Delta=pa(H,pm(A,A));U2=pm(U,U);C2=pm(C,C)
lhs=pa(pm(Dstar,Dstar),pm(U2,pa(pc(1),pm(Delta,C2))),-1)
rhs=pa(pa(pm(P,P),pm(pc(2),pm(P,B))),pm(U2,pa(pc(1),pm(H,C2))),-1)
assert lhs==rhs
pbound=max(degree['U']+degree['X'],degree['H']+degree['shift'])
bbound=degree['U']+degree['a']+degree['c']
main_upper=max(2*pbound,pbound+bbound,2*degree['U'],2*degree['U']+degree['H']+2*degree['c'])
assert (pbound,bbound,main_upper)==(13,17,30)
upper=degree['F0']+main_upper+degree['Fa']+degree['Fs']+degree['guard']
assert upper==107,upper
# Full graph on n_i=t, with actual P72 ports reduced modulo prime.
def trim(a):
 while len(a)>1 and a[-1]==0:a.pop()
 return a
def add(a,b,sgn):return trim([((a[i] if i<len(a) else 0)+sgn*(b[i] if i<len(b) else 0))%prime for i in range(max(len(a),len(b)))])
def mul(a,b):
 z=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):z[i+j]=(z[i+j]+x*y)%prime
 return trim(z)
e={v:[0,1] for v in new};e.update({v:[x%prime] for v,x in fixed.items()})
def val(x):return [x%prime] if type(x) is int else e[x]
for n,op,x,y in c['source']:
 a,b=val(x),val(y);e[n]=mul(a,b) if op=='*' else add(a,b,1 if op=='+' else -1)
assert len(e['out'])-1==107 and e['out'][-1]==419359493
print(json.dumps({'scope':'external natural-domain DAG substitution and authenticated P72/P115-port degree; no Lean/formal or PDF binding','inputs':14,'operations':88,'increment_gates':14,'parent_gates':74,'all_gates_inputs_ports_live':True,'exact_structural_parent_gates':len(p['source']),'signed_and_natural_controls':500,'naive_dag_degree_upper':naive_upper,'main_cancellation_degree_upper':main_upper,'degree_upper':upper,'ray_prime':prime,'ray_degree':len(e['out'])-1,'ray_leader':e['out'][-1]},sort_keys=True,indent=2))
