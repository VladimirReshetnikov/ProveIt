#!/usr/bin/env python3
from pathlib import Path
from itertools import product
from math import factorial
import gzip,hashlib,json,random,subprocess,sys
P=Path(__file__).resolve().parent;D=P.parents[1];A=D/'research/ordinary14-root74-natural-shift88'
def H(p):return hashlib.sha256(p.read_bytes()).hexdigest()
pins={A/'README.md':'66f38f5730b24d426f30d6f655dd8b1efbb4f795f936c57c4413f87723010320',A/'candidate.json':'85675d2db0c6a40e0f759b9b67351cc74d8bc374ea7f85f85ea754eae8f9276d',A/'check.py':'5035b757c42ac25266c4ae19c471785d481522dde29951d8ba184e06de5bb7be',A/'result.json':'c2b714d6527a17487ce51493453b7b900ed5c1d0743366195dd84df3d65ce24a'}
tail=b"\nIndependent external review: [natural shift 88](../../reviews/ordinary14-root74-natural-shift88-independent/README.md).\n"
for p,h in pins.items():
 if p==A/'README.md':
  data=p.read_bytes();assert hashlib.sha256(data).hexdigest()=='0185d2f62752456d2a3d939c6d577d42138164dc90c1eb2da1e7a062e8565ac8'
  assert data.endswith(tail) and hashlib.sha256(data[:-len(tail)]).hexdigest()==h
 else:assert H(p)==h,(str(p),H(p),h)
a=json.loads((D/'research/ordinary14-positive-guard74/candidate.json').read_bytes());b=json.loads((A/'candidate.json').read_bytes());old=a['witnesses'];new=b['witnesses'];assert new==['n_'+x for x in old] and len(new)==14
assert b['source'][:14]==[[x,'+',n,1] for x,n in zip(old,new)] and b['source'][14:]==a['source'] and len(b['source'])==88
needed={'out'}
for n,op,x,y in reversed(b['source']):
 if n in needed:needed.update(z for z in (x,y) if isinstance(z,str))
assert all(n in needed for n,_,_,_ in b['source']) and set(new+b['fixed_numerals'])<=needed
# Exact polynomial identity via independent sparse dictionary arithmetic.
def add(*ps):
 z={}
 for p in ps:
  for k,v in p.items():z[k]=z.get(k,0)+v
 return {k:v for k,v in z.items() if v}
def neg(p):return {k:-v for k,v in p.items()}
def mul(p,q):
 z={}
 for a,x in p.items():
  for b,y in q.items():
   k=tuple(i+j for i,j in zip(a,b));z[k]=z.get(k,0)+x*y
 return {k:v for k,v in z.items() if v}
def var(i):return {tuple(int(i==j) for j in range(6)):1}
U,X,H0,S,a,c=[var(i) for i in range(6)];one={(0,)*6:1}
Dstar=add(mul(U,add(X,mul(a,c))),mul(H0,S));Delta=add(H0,mul(a,a));A1=add(mul(Dstar,Dstar),neg(mul(mul(U,U),add(one,mul(Delta,mul(c,c))))))
Q=add(mul(U,X),mul(H0,S));B=mul(mul(U,a),c);rhs=add(mul(Q,Q),mul({(0,)*6:2},mul(Q,B)),neg(mul(mul(U,U),add(one,mul(H0,mul(c,c))))))
assert A1==rhs
rows={r[0]:r[1:] for r in b['source']}
for name,row in {'g19':['*','a','c'],'b0':['+','X','g19'],'g58':['*','U','b0'],'g59':['*','H','shift'],'Dstar':['+','g58','g59'],'g17':['*','a','a'],'Delta':['+','H','g17'],'g61':['*','Dstar','Dstar'],'g62':['*','U','U'],'c2':['*','c','c'],'g63':['*','Delta','c2'],'g64':['+',1,'g63'],'g65':['*','g62','g64'],'A1':['-','g61','g65']}.items():assert rows[name]==row
d={x:1 for x in new};d.update({x:0 for x in b['fixed_numerals']})
for n,op,x,y in b['source']:
 dx=0 if type(x) is int else d[x];dy=0 if type(y) is int else d[y];d[n]=dx+dy if op=='*' else max(dx,dy)
Dq=max(d['U']+d['X'],d['H']+d['shift']);Db=d['U']+d['a']+d['c'];main=max(2*Dq,Dq+Db,2*d['U'],2*d['U']+d['H']+2*d['c']);assert (Dq,Db,main)==(13,17,30)
assert d['F0']+main+d['Fa']+d['Fs']+d['guard']==107
# Evaluate at 108 points and recover the t^107 coefficient by finite differences.
base=D/'con-zfc-diophantine-forms/72-congruence-sextic/positive13';j=base/'ACTIVE_BINDING.json';assert H(j)=='6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf';bind=json.loads(j.read_bytes());k=D/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json';assert H(k)=='dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01';other=json.loads(k.read_bytes());prime=1000000007;fixed={}
for name,m in bind['ports'].items():
 assert other['ports'][name]['sha256_raw']==m['sha256_raw'] and other['ports'][name]['sha256_gzip']==m['sha256_gzip']
 p=base/m['path'];rawz=p.read_bytes();assert hashlib.sha256(rawz).hexdigest()==m['sha256_gzip'];raw=gzip.decompress(rawz);assert len(raw)==m['raw_bytes'] and hashlib.sha256(raw).hexdigest()==m['sha256_raw'];fixed[name]=int.from_bytes(raw,'little')%prime
assert set(fixed)==set(b['fixed_numerals'])
def evaluate(t):
 env={x:t for x in new};env.update(fixed)
 for name,op,x,y in b['source']:
  x=x if type(x) is int else env[x];y=y if type(y) is int else env[y]
  env[name]=({'+':lambda:x+y,'-':lambda:x-y,'*':lambda:x*y}[op]())%prime
 return env['out']
vals=[evaluate(t) for t in range(108)]
for _ in range(107):vals=[(vals[i+1]-vals[i])%prime for i in range(len(vals)-1)]
lead=vals[0]*pow(factorial(107),-1,prime)%prime;assert lead==419359493
r=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=120);assert not r.stderr and r.stdout==(A/'result.json').read_bytes()
print(json.dumps({'scope':'external SLP and authenticated specialization, no Lean/PDF binding or minimality','pins':{str(p.relative_to(D)):h for p,h in pins.items()},'live_operations':88,'increment_gates':14,'parent_gates':74,'upper_degree':107,'finite_difference_prime':prime,'finite_difference_order':107,'leading_coefficient':lead,'author_receipt_replayed':True},sort_keys=True,indent=2))
