#!/usr/bin/env python3
"""Independent graph structure and degree ray; no Lean or unbounded proof."""
import gzip, hashlib, json, math
from pathlib import Path
D=Path(__file__).resolve().parents[2]
def digest(b): return hashlib.sha256(b).hexdigest()
def load(path,h):
 b=(D/path).read_bytes();assert digest(b)==h,path
 return json.loads(b)
p=load('research/ordinary13-unit-product80/candidate.json','449adf0f03f08cbb73b4ca8c823cb88b79111243c93705b5404f89d18568a22b')
n=load('research/ordinary13-natural-unit-product89/candidate.json','1d865512c2c78580af0d6a5285c009e5fa03deb141dc711dc5e3adb0b268938d')
assert p['domain']=='strictly positive integers' and n['domain']=='nonnegative integers'
assert n['witnesses']==['n_'+x for x in p['witnesses']] and n['fixed_numerals']==p['fixed_numerals']
a={v[0]:v[1:] for v in p['source']}; b={v[0]:v[1:] for v in n['source']}
assert len(a)==80 and len(b)==89
raw={'f','r','y'}
for x in set(p['witnesses'])-raw-{'zeta'}: assert b[x]==['+','n_'+x,1]
assert a['k']==['+','eta','zeta'] and a['g52']==['-','k','R'] and a['r0']==['-','g52',1]
assert b['kbase']==['+','eta','n_zeta'] and b['k']==['+','kbase',1] and b['r0']==['-','kbase','R']
rename={x:'n_'+x for x in raw}
shared=set(a)-{'k','g52','r0'}
for x in shared:
 op,l,r=a[x];assert b[x]==[op,rename.get(l,l),rename.get(r,r)],x
assert set(b)==shared|{'kbase','k','r0'}|(set(p['witnesses'])-raw-{'zeta'})
known=set(n['witnesses']+n['fixed_numerals'])
for name,op,l,r in n['source']:
 assert name not in known and op in ('+','-','*')
 assert all(type(x) is int or x in known for x in (l,r))
 known.add(name)
live={'out'}
for name,op,l,r in reversed(n['source']):
 if name in live:live.update(x for x in (l,r) if isinstance(x,str))
assert set(b)|set(n['witnesses'])|set(n['fixed_numerals']) <= live
# Verify first-factor residual, root-switch dependency, and other factor independence.
expected={'Bt':['-','g27','F'],'g27':['*','C','g26'],'g26':['+','X','K0'],
 'g31':['+','g30','r'],'g30':['+','ell','k'],'folded_kBt':['*','k','Bt'],
 'folded_g31':['-','g31','folded_kBt'],'g32':['*','qm','folded_g31'],
 'Z':['-','g32','Bt'],'g38':['*','Z','Z'],'g39':['*','qm','qm'],
 'g40':['*','ell','g30'],'g41':['+',1,'g40'],'g42':['*','g39','g41'],
 'A0':['-','g38','g42'],'F0':['+',1,'A0'],'E':['*','X','Y'],
 'kY':['*','Y','k'],'ell':['*','E','kY']}
for name,row in expected.items():assert a[name]==row,name
assert [name for name,op,x,y in p['source'] if x=='r' or y=='r']==['g31']
def deps(out):
 todo=[out];seen=set()
 while todo:
  t=todo.pop()
  if t in seen:continue
  seen.add(t)
  if t in a: todo.extend(x for x in a[t][1:] if isinstance(x,str))
 return seen
assert all('r' not in deps(x) for x in ('F1','Fa','Fs'))
# Independent root-switch algebra at a nontrivial, abstract integer assignment.
m,k,betaB,B=1,2,3,3
ell=m*k;delta=1+ell*(ell+k);tau=math.isqrt(delta)
assert tau*tau==delta and ell<tau<ell+k
Z=betaB*(ell+k-k*B)-B
assert Z==-betaB*tau and Z+betaB*(2*tau)==-Z
# Authenticate bytes and independently compute specialized all-diagonal ray.
bind=load('con-zfc-diophantine-forms/72-congruence-sextic/positive13/ACTIVE_BINDING.json','6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf')
b115=load('con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json','dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01')
ports={}
for name,meta in bind['ports'].items():
 assert b115['ports'][name]['sha256_raw']==meta['sha256_raw'] and b115['ports'][name]['sha256_gzip']==meta['sha256_gzip']
 packed=(D/'con-zfc-diophantine-forms/72-congruence-sextic/positive13'/meta['path']).read_bytes()
 assert digest(packed)==meta['sha256_gzip']; rawbytes=gzip.decompress(packed)
 assert len(rawbytes)==meta['raw_bytes'] and digest(rawbytes)==meta['sha256_raw']
 ports[name]=int.from_bytes(rawbytes,'little')
assert set(ports)==set(n['fixed_numerals']) and ports['beta']>0
prime=1000000007
# Polynomials are sparse degree->coefficient dictionaries, modulo prime.
def norm(q):return {k:v%prime for k,v in q.items() if v%prime}
def plus(q,r,sign=1):
 t=q.copy()
 for k,v in r.items():t[k]=t.get(k,0)+sign*v
 return norm(t)
def times(q,r):
 t={}
 for i,x in q.items():
  for j,y in r.items():t[i+j]=t.get(i+j,0)+x*y
 return norm(t)
e={x:{1:1} for x in n['witnesses']};e.update({x:norm({0:v}) for x,v in ports.items()})
def val(x):return norm({0:x}) if type(x) is int else e[x]
for name,op,l,r in n['source']:
 x,y=val(l),val(r);e[name]=times(x,y) if op=='*' else plus(x,y,-1 if op=='-' else 1)
assert max(e['out'])==99 and e['out'][99]==663418019
print(json.dumps({'scope':'independent exact graph edits, root-dependency checks and authenticated degree ray; no Lean or unbounded proof',
 'parent_operations':len(a),'candidate_operations':len(b),'shared_parent_rows_checked':len(shared),
 'ray_degree':99,'ray_leader':663418019,'ray_prime':prime,'abstract_root_switch_control':True},sort_keys=True,indent=2))
