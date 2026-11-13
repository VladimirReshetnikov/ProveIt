#!/usr/bin/env python3
"""Check the integer-unit finalizer and authenticated degree; no Lean."""
from pathlib import Path
import gzip,hashlib,itertools,json,random
P=Path(__file__).resolve().parent;D=P.parents[1]
def digest(b):return hashlib.sha256(b).hexdigest()
def load(path,sha):
 b=path.read_bytes();assert digest(b)==sha,str(path);return json.loads(b)
a=load(D/'research/ordinary13-natural-cfold97-degree28/candidate.json','8c56deec58c4fbe29ab024fc5a61628ec0d677858c9bc6eb066b4f81244ee2e6')
b=load(P/'candidate.json','1b15bd32233780c03d0a23105499bbf6cdc521b48f6160fe77c7493a6eaf2970')
assert a['domain']==b['domain']=='nonnegative integers' and a['witnesses']==b['witnesses'] and a['fixed_numerals']==b['fixed_numerals']
assert b['parent_sha256']==digest((D/'research/ordinary13-natural-cfold97-degree28/candidate.json').read_bytes())
deleted={'A0sq','A1sq','Fam','Fam2','Fsm2','sum01','sum23','out'}
expected=[row for row in a['source'] if row[0] not in deleted]
expected += [['F0','+',1,'A0'],['F1','+',1,'A1'],['Fs','+',1,'g72'],
             ['P01','*','F0','F1'],['P012','*','P01','Fa'],['P0123','*','P012','Fs'],['out','-','P0123',1]]
assert b['source']==expected and a['operations']==97 and b['operations']==len(expected)==96
known=set(b['witnesses']+b['fixed_numerals'])
for n,op,x,y in expected:
 assert n not in known and op in ('+','-','*') and all(type(z) is int or z in known for z in (x,y));known.add(n)
live={'out'}
for n,op,x,y in reversed(expected):
 if n in live:live.update(z for z in (x,y) if isinstance(z,str))
assert all(n in live for n,_,_,_ in expected) and set(b['witnesses']+b['fixed_numerals'])<=live
# Exhaust the integer residue argument for every restricted factor.
for bb,z,other in itertools.product(range(4),repeat=3):
 M=((bb+1)**3*bb)%4
 assert (1+z*z-M*M*other)%4!=3
for aa,c,U,D0 in itertools.product(range(4),repeat=4):
 delta=aa*aa+4*aa+3
 assert (1+D0*D0-U*U*(1+delta*c*c))%4!=3
for aa,f,y,V,I in itertools.product(range(4),repeat=5):
 Q=(aa*aa+4*aa+3)*(f*f-1)
 assert (y*y-Q*(y*y-V*V))%4!=3
 assert (1+I*I-Q)%4!=3
def calc(g,v,modulus):
 e=v.copy()
 for n,op,x,y in g['source']:
  x=x if type(x) is int else e[x];y=y if type(y) is int else e[y]
  e[n]=(x+y if op=='+' else x-y if op=='-' else x*y)%modulus
 return e
rng=random.Random(139650)
for mod in (4,17,1009):
 for _ in range(100):
  v={x:rng.randrange(-5,6) for x in b['witnesses']+b['fixed_numerals']}
  aa,bb=calc(a,v,mod),calc(b,v,mod)
  assert bb['F0']==(1+aa['A0'])%mod and bb['F1']==(1+aa['A1'])%mod
  assert bb['Fs']==(1+aa['g72'])%mod and bb['Fa']==aa['Fa']
p72=D/'con-zfc-diophantine-forms/72-congruence-sextic/positive13'
bind=load(p72/'ACTIVE_BINDING.json','6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf')
b115=load(D/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json','dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01')
fixed={}
for n,m in bind['ports'].items():
 assert b115['ports'][n]['sha256_raw']==m['sha256_raw'] and b115['ports'][n]['sha256_gzip']==m['sha256_gzip']
 z=(p72/m['path']).read_bytes();assert digest(z)==m['sha256_gzip']
 raw=gzip.decompress(z);assert len(raw)==m['raw_bytes'] and digest(raw)==m['sha256_raw']
 fixed[n]=int.from_bytes(raw,'little')
assert set(fixed)==set(b['fixed_numerals'])
prime=1000000007
def trim(a):
 while len(a)>1 and a[-1]==0:a.pop()
 return a
def add(a,b,sgn):return trim([((a[i] if i<len(a) else 0)+sgn*(b[i] if i<len(b) else 0))%prime for i in range(max(len(a),len(b)))])
def mul(a,b):
 z=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):z[i+j]=(z[i+j]+x*y)%prime
 return trim(z)
e={v:[0,1] for v in b['witnesses']};e.update({v:[x%prime] for v,x in fixed.items()})
def val(x):return [x%prime] if type(x) is int else e[x]
for n,op,x,y in expected:
 x,y=val(x),val(y);e[n]=mul(x,y) if op=='*' else add(x,y,1 if op=='+' else -1)
assert len(e['out'])-1==50 and e['out'][-1]==604845992
print(json.dumps({'scope':'external pointwise unit finalizer; no Lean, iPRA or PDF binding',
                  'variables':13,'operations':96,'all_gates_inputs_ports_live':True,
                  'signed_modular_controls':300,'ray_degree':len(e['out'])-1,
                  'ray_leader':e['out'][-1],'ray_prime':prime,
                  'factor_ray_degrees':{n:len(e[n])-1 for n in ('F0','F1','Fa','Fs')}},sort_keys=True,indent=2))
