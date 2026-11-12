#!/usr/bin/env python3
"""Independent finalizer, modulo-four and degree-ray review; no Lean."""
from pathlib import Path
import hashlib,itertools,json,math,zlib
D=Path(__file__).resolve().parents[2]
def sha(b):return hashlib.sha256(b).hexdigest()
def load(path,digest):
 b=(D/path).read_bytes();assert sha(b)==digest,path;return json.loads(b)
p=load('research/ordinary13-natural-cfold97-degree28/candidate.json','8c56deec58c4fbe29ab024fc5a61628ec0d677858c9bc6eb066b4f81244ee2e6')
c=load('research/ordinary13-natural-cfold-product96/candidate.json','1b15bd32233780c03d0a23105499bbf6cdc521b48f6160fe77c7493a6eaf2970')
assert p['domain']==c['domain']=='nonnegative integers' and p['witnesses']==c['witnesses'] and len(c['witnesses'])==13
assert p['fixed_numerals']==c['fixed_numerals']==['beta','K0','MC','MF']
a={r[0]:r[1:] for r in p['source']};b={r[0]:r[1:] for r in c['source']}
assert len(a)==97 and len(b)==96
removed={'A0sq','A1sq','Fam','Fam2','Fsm2','sum01','sum23','out'}
added={'F0','F1','Fs','P01','P012','P0123','out'}
assert set(a)-removed==set(b)-added
assert all(a[n]==b[n] for n in set(a)-removed)
assert {n:b[n] for n in added}=={'F0':['+',1,'A0'],'F1':['+',1,'A1'],'Fs':['+',1,'g72'],
 'P01':['*','F0','F1'],'P012':['*','P01','Fa'],'P0123':['*','P012','Fs'],'out':['-','P0123',1]}
assert {n:a[n] for n in removed}=={'A0sq':['*','A0','A0'],'A1sq':['*','A1','A1'],
 'Fam':['-','Fa',1],'Fam2':['*','Fam','Fam'],'Fsm2':['*','g72','g72'],
 'sum01':['+','A0sq','A1sq'],'sum23':['+','Fam2','Fsm2'],'out':['+','sum01','sum23']}
# Verify expression shapes used by the sign exclusions, and live topology.
shape={'qm':['*','n_J','beta'],'q':['+',1,'qm'],'q2':['*','q','q'],'q3':['*','q','q2'],
 'M':['*','q3','qm'],'g30':['+','ell','k'],'g38':['*','Z','Z'],'g39':['*','M','M'],
 'g40':['*','ell','g30'],'g41':['+',1,'g40'],'g42':['*','g39','g41'],'A0':['-','g38','g42'],
 'g15':['*',4,'a'],'H':['+',3,'g15'],'g17':['*','a','a'],'Delta':['+','H','g17'],
 'c2':['*','c','c'],'g61':['*','Dstar','Dstar'],'g62':['*','U','U'],'g63':['*','Delta','c2'],
 'g64':['+',1,'g63'],'g65':['*','g62','g64'],'A1':['-','g61','g65'],
 'f2':['*','n_f','n_f'],'rho':['-','f2',1],'Q':['*','Delta','rho'],
 'I':['*','c2','i'],'g71':['*','I','I'],'g72':['-','g71','Q'],
 'g78':['+','V','u'],'y2':['*','g78','g78'],'g80':['+','g78','V'],
 'g81':['*','u','g80'],'g82':['*','Q','g81'],'Fa':['-','y2','g82']}
for n,row in shape.items():assert b[n]==row,n
seen=set(c['witnesses']+c['fixed_numerals'])
for n,op,x,y in c['source']:
 assert n not in seen and op in ('+','-','*') and all(type(t) is int or t in seen for t in (x,y));seen.add(n)
live={'out'}
for n,op,x,y in reversed(c['source']):
 if n in live:live.update(t for t in (x,y) if isinstance(t,str))
assert set(b)|set(c['witnesses'])|set(c['fixed_numerals'])<=live
# Exhaust all residues needed for the universal factor-unit proof.
for bb,z,h in itertools.product(range(4),repeat=3):
 M=((bb+1)**3*bb)%4
 assert M%2==0 and (1+z*z-M*M*(1+h))%4 in (0,1,2)
for a,c0,U,d in itertools.product(range(4),repeat=4):
 delta=(a*a+4*a+3)%4
 assert delta in (0,3) and (1+d*d-U*U*(1+delta*c0*c0))%4 in (0,1,2)
for a,f,V,u,I in itertools.product(range(4),repeat=5):
 delta=(a*a+4*a+3)%4;Q=(delta*(f*f-1))%4;y=V+u
 assert Q in (0,1)
 assert (u*(u+2*V)-(y*y-V*V))%4==0
 assert (y*y-Q*u*(u+2*V))%4 in (0,1)
 assert (1+I*I-Q)%4 in (0,1,2)
# Independently authenticate the byte snapshot and use finite differences,
# rather than coefficient propagation, to establish the degree lower bounds.
root='con-zfc-diophantine-forms/72-congruence-sextic/positive13/'
x=load(root+'ACTIVE_BINDING.json','6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf')
y=load('con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json','dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01')
ports={}
for n,m in x['ports'].items():
 assert all(m[k]==y['ports'][n][k] for k in ('sha256_gzip','sha256_raw','raw_bytes','bits'))
 packed=(D/root/m['path']).read_bytes();raw=zlib.decompress(packed,31)
 assert sha(packed)==m['sha256_gzip'] and sha(raw)==m['sha256_raw'] and len(raw)==m['raw_bytes']
 ports[n]=int.from_bytes(raw,'little');assert ports[n].bit_length()==m['bits']
assert set(ports)==set(c['fixed_numerals'])
prime=1000000007
def ev(t):
 e={n:t for n in c['witnesses']};e.update({n:v%prime for n,v in ports.items()})
 def val(x):return x if type(x) is int else e[x]
 for n,op,x,y in c['source']:
  x,y=val(x),val(y);e[n]=(x+y if op=='+' else x-y if op=='-' else x*y)%prime
 return e
values=[ev(i) for i in range(51)]
def leader(name,d):
 row=[v[name] for v in values[:d+1]]
 for _ in range(d):row=[(b-a)%prime for a,b in zip(row,row[1:])]
 return row[0]*pow(math.factorial(d),-1,prime)%prime
expected={'F0':14,'F1':13,'Fa':13,'Fs':10,'out':50}
leaders={n:leader(n,d) for n,d in expected.items()}
assert all(leaders.values()) and leaders['out']==604845992
assert math.prod(leaders[n] for n in ('F0','F1','Fa','Fs'))%prime==leaders['out']
print(json.dumps({'scope':'external all-integer finalizer proof and degree checks; inherited calibration, no Lean',
 'inputs':13,'candidate_gates':96,'parent_gates':97,'factor_degrees_inherited':expected,
 'ray_method':'finite differences','ray_prime':prime,'ray_leaders':leaders,
 'all_four_factor_unit_exclusions_mod_4':True},sort_keys=True,indent=2))
