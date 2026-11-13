#!/usr/bin/env python3
"""Independent graph edit, fixed-port and finite-difference checks; no Lean."""
from pathlib import Path
import hashlib,json,math,zlib
D=Path(__file__).resolve().parents[2]
def sha(x):return hashlib.sha256(x).hexdigest()
def load(path,digest):
 data=(D/path).read_bytes();assert sha(data)==digest,path;return json.loads(data)
p=load('research/ordinary13-cfold88-28/candidate.json','9497efb00c1059897dd6d57522267af90910224f2d37f8901b99dfc28086e333')
c=load('research/ordinary13-natural-cfold97-degree28/candidate.json','8c56deec58c4fbe29ab024fc5a61628ec0d677858c9bc6eb066b4f81244ee2e6')
assert p['domain']=='strictly positive integers' and c['domain']=='nonnegative integers'
assert c['witnesses']==['n_'+n for n in p['witnesses']] and len(c['witnesses'])==13
assert p['fixed_numerals']==c['fixed_numerals']==['beta','K0','MC','MF']
old={r[0]:r[1:] for r in p['source']};new={r[0]:r[1:] for r in c['source']}
assert len(old)==88 and len(new)==97
added={'F','alpha','i','T','X','Y','eta','u','gamma','kbase'}
assert set(new)-set(old)==added and set(old)-set(new)=={'g52'}
for n in added-{'kbase'}:assert new[n]==['+','n_'+n,1]
assert old['k']==['+','eta','zeta'] and new['kbase']==['+','eta','n_zeta'] and new['k']==['+','kbase',1]
assert old['g52']==['-','k','R'] and old['r0']==['-','g52',1] and new['r0']==['-','kbase','R']
rename={'J':'n_J','f':'n_f','r':'n_r'}
for n in set(old)&set(new)-{'k','r0'}:
 op,x,y=old[n];assert new[n]==[op,rename.get(x,x),rename.get(y,y)],n
# Verify topology, live nodes and all leaf use.
seen=set(c['witnesses']+c['fixed_numerals']);assert len(seen)==17
leaves={n:{n} for n in seen}
for n,op,x,y in c['source']:
 assert n not in seen and op in ('+','-','*') and all(type(a) is int or a in seen for a in (x,y))
 leaves[n]=set().union(*(leaves[a] for a in (x,y) if isinstance(a,str)));seen.add(n)
live={'out'}
for n,op,x,y in reversed(c['source']):
 if n in live:live.update(x for x in (x,y) if isinstance(x,str))
assert set(new)|set(c['witnesses'])|set(c['fixed_numerals'])<=live
assert all('n_r' not in leaves[n] for n in ('A1','Fa','g72')) and 'n_r' in leaves['A0']
shape={'qm':['*','n_J','beta'],'q':['+',1,'qm'],'q3':['*','q','q2'],'M':['*','q3','qm'],
 'qF':['-','q','F'],'C':['-','qF','alpha'],'g25':['*','K0','q'],'g26':['+','X','g25'],
 'g27':['*','C','g26'],'g28':['*','F','q'],'Bt':['-','g27','g28'],
 'g31':['+','g30','n_r'],'folded_kBt':['*','k','C'],'folded_g31':['-','g31','folded_kBt'],
 'g32':['*','M','folded_g31'],'g33':['*','Y','qm'],'g34':['+','g32','g33'],
 'folded_q3Bt':['*','q3','Bt'],'Z':['-','g34','folded_q3Bt'],
 'A0sq':['*','A0','A0'],'A1sq':['*','A1','A1'],'Fam':['-','Fa',1],
 'Fam2':['*','Fam','Fam'],'Fsm2':['*','g72','g72'],'sum01':['+','A0sq','A1sq'],
 'sum23':['+','Fam2','Fsm2'],'out':['+','sum01','sum23']}
for n,v in shape.items():assert new[n]==v,n
# Authenticate all four payloads against both binding records. This uses zlib
# and a finite-difference ray instead of the candidate's polynomial expansion.
root='con-zfc-diophantine-forms/72-congruence-sextic/positive13/'
a=load(root+'ACTIVE_BINDING.json','6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf')
b=load('con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json','dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01')
ports={}
for name,m in a['ports'].items():
 assert all(m[k]==b['ports'][name][k] for k in ('sha256_raw','sha256_gzip','raw_bytes','bits'))
 z=(D/root/m['path']).read_bytes();raw=zlib.decompress(z,31)
 assert sha(z)==m['sha256_gzip'] and sha(raw)==m['sha256_raw'] and len(raw)==m['raw_bytes']
 ports[name]=int.from_bytes(raw,'little');assert ports[name].bit_length()==m['bits']
assert ports['beta']>=46 and ports['K0']>=0 and 0<ports['MC']<ports['beta'] and 0<ports['MF']<2*ports['beta']
prime=1000000007
def ev(t):
 e={n:t for n in c['witnesses']};e.update({n:v%prime for n,v in ports.items()})
 def val(x):return x if type(x) is int else e[x]
 for n,op,x,y in c['source']:
  x,y=val(x),val(y);e[n]=(x+y if op=='+' else x-y if op=='-' else x*y)%prime
 return e['out']
row=[ev(x) for x in range(29)]
for _ in range(28):row=[(b-a)%prime for a,b in zip(row,row[1:])]
lead=row[0]*pow(math.factorial(28),-1,prime)%prime
assert lead==59132194
print(json.dumps({'scope':'independent graph and degree checks; calibration and norm descent inherited, no Lean',
 'inputs':13,'parent_gates':88,'candidate_gates':97,'degree_upper_inherited':28,
 'degree_ray_method':'28th finite difference','ray_leader':lead,'ray_prime':prime,
 'fixed_port_bounds_checked':True,'other_residuals_independent_of_r':True},sort_keys=True,indent=2))
