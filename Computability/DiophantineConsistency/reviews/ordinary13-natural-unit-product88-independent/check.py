#!/usr/bin/env python3
"""Independent graph edit, forced-J structure and degree ray; no Lean."""
import gzip,hashlib,json
from pathlib import Path
D=Path(__file__).resolve().parents[2]
def h(x):return hashlib.sha256(x).hexdigest()
def load(path,digest):
 b=(D/path).read_bytes();assert h(b)==digest,path
 return json.loads(b)
a=load('research/ordinary13-natural-unit-product89/candidate.json','1d865512c2c78580af0d6a5285c009e5fa03deb141dc711dc5e3adb0b268938d')
b=load('research/ordinary13-natural-unit-product88/candidate.json','95fdd3495b777a0bdf64c95f6dd24cda660dee42f0508c76fdb081da21f42a5a')
assert a['domain']==b['domain']=='nonnegative integers'
assert a['witnesses']==b['witnesses'] and a['fixed_numerals']==b['fixed_numerals']
old={x[0]:x[1:] for x in a['source']}; new={x[0]:x[1:] for x in b['source']}
assert len(old)==89 and len(new)==88 and set(old)-set(new)=={'J'} and set(new)<=set(old)
assert old['J']==['+','n_J',1]
for name,row in new.items():
 op,l,r=old[name];assert row==[op,'n_J' if l=='J' else l,'n_J' if r=='J' else r],name
assert [name for name,op,l,r in a['source'] if l=='J' or r=='J']==['qm','g50']
needed={'F':['+','n_F',1],'alpha':['+','n_alpha',1],'w':['+','n_w',1],
 'qm':['*','n_J','beta'],'q':['+',1,'qm'],'X':['*','q','w'],'qF':['-','q','F'],
 'C':['-','qF','alpha'],'g26':['+','X','K0'],'g27':['*','C','g26'],
 'Bt':['-','g27','F'],'g32':['*','qm','folded_g31'],'Z':['-','g32','Bt'],
 'g38':['*','Z','Z'],'g39':['*','qm','qm'],'g42':['*','g39','g41'],
 'A0':['-','g38','g42'],'F0':['+',1,'A0']}
for n,r in needed.items():assert new[n]==r,n
seen=set(b['witnesses']+b['fixed_numerals'])
for n,op,l,r in b['source']:
 assert n not in seen and op in ('+','-','*') and all(type(x) is int or x in seen for x in (l,r));seen.add(n)
live={'out'}
for n,op,l,r in reversed(b['source']):
 if n in live:live.update(x for x in (l,r) if isinstance(x,str))
assert set(new)|set(b['witnesses'])|set(b['fixed_numerals']) <= live
# When J=0 and K0>=0, C<0, X+K0>0, so B<0. The following is a
# finite control, not a replacement for that universal ordered argument.
for F in range(1,10):
 for alpha in range(1,10):
  for w in range(1,10):
   for K0 in range(10):
    C=1-F-alpha;B=C*(w+K0)-F
    assert C<0 and B<0 and -B>0
# Without K0>=0 this simple exclusion can fail; it is not a full graph zero.
assert (1-1-1)*(1-2)-1==0
bind=load('con-zfc-diophantine-forms/72-congruence-sextic/positive13/ACTIVE_BINDING.json','6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf')
b115=load('con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json','dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01')
ports={}
for n,item in bind['ports'].items():
 assert b115['ports'][n]['sha256_raw']==item['sha256_raw'] and b115['ports'][n]['sha256_gzip']==item['sha256_gzip']
 z=(D/'con-zfc-diophantine-forms/72-congruence-sextic/positive13'/item['path']).read_bytes()
 assert h(z)==item['sha256_gzip'];raw=gzip.decompress(z)
 assert len(raw)==item['raw_bytes'] and h(raw)==item['sha256_raw']
 ports[n]=int.from_bytes(raw,'little')
assert set(ports)==set(b['fixed_numerals']) and ports['beta']>0 and ports['K0']>=0
p=1000000007
def clean(v):return {d:x%p for d,x in v.items() if x%p}
def add(a,b,sgn):
 z=a.copy()
 for d,x in b.items():z[d]=z.get(d,0)+sgn*x
 return clean(z)
def mul(a,b):
 z={}
 for i,x in a.items():
  for j,y in b.items():z[i+j]=z.get(i+j,0)+x*y
 return clean(z)
e={x:{1:1} for x in b['witnesses']};e.update({x:clean({0:v}) for x,v in ports.items()})
def atom(x):return clean({0:x}) if type(x) is int else e[x]
for n,op,l,r in b['source']:
 x,y=atom(l),atom(r);e[n]=mul(x,y) if op=='*' else add(x,y,-1 if op=='-' else 1)
assert max(e['out'])==99 and e['out'][99]==663418019
print(json.dumps({'scope':'independent graph edit, forced-J structure and authenticated degree ray; no Lean or unbounded proof',
 'parent_operations':len(old),'candidate_operations':len(new),'graph_rows_checked':len(new),
 'ray_degree':99,'ray_leader':663418019,'ray_prime':p,'nonnegative_K0_is_used':True},sort_keys=True,indent=2))
