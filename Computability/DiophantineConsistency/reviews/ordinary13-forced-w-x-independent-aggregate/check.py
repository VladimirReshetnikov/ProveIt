#!/usr/bin/env python3
"""Independent graph and modular-ray controls for three 13-input variants."""
from pathlib import Path
import gzip, hashlib, json, math
D=Path(__file__).resolve().parents[2]
def read(path, digest):
 b=path.read_bytes(); assert hashlib.sha256(b).hexdigest()==digest, path
 return json.loads(b)
cases=[
 ('ordinary13-natural-forced-w86','75d3110827afc1ef14a5ed2367229e81c645d3394beba2c04d255f53ffeefe50','ordinary13-natural-forced-gamma87','e753c7c5f8110b9f15e84c9f0da88847a54486f442b60b11812ca3688ca55e21','w','n_w',86,99,663418019),
 ('ordinary13-natural-cfold-forced-x95-degree28','5fd11fa456867a2ed4f3b5bc58db59caab0f58736019ee864403d62124aced4e','ordinary13-natural-cfold-forced-gamma96-degree28','f23a4f8b5b7761cd2226f71235f34dfa9cf362f5567b10589a1859106a00be81','X','n_X',95,28,59132194),
 ('ordinary13-natural-cfold-forced-x94-degree50','07eefb9e44f827bbb6b613903fc7b1a7b08bcf1d9685517628a7cdb754cee535','ordinary13-natural-cfold-forced-gamma95-degree50','732e96e5d7278fb08357910e5f9b4aad2a248bc8e86c7ec89328bbf20039a889','X','n_X',94,50,604845992)]
p72=D/'con-zfc-diophantine-forms/72-congruence-sextic/positive13'
bind=read(p72/'ACTIVE_BINDING.json','6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf')
sync=read(D/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json','dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01')
ports={}
for n,m in bind['ports'].items():
 assert sync['ports'][n]['sha256_raw']==m['sha256_raw'] and sync['ports'][n]['sha256_gzip']==m['sha256_gzip']
 gz=(p72/m['path']).read_bytes(); assert hashlib.sha256(gz).hexdigest()==m['sha256_gzip']
 raw=gzip.decompress(gz); assert len(raw)==m['raw_bytes'] and hashlib.sha256(raw).hexdigest()==m['sha256_raw']
 ports[n]=int.from_bytes(raw,'little')
assert ports['beta']>0 and ports['K0']>=0
prime=1000000007
out=[]
for name,chash,parent,phash,cut,inp,count,degree,lead in cases:
 a=read(D/'research'/parent/'candidate.json',phash); b=read(D/'research'/name/'candidate.json',chash)
 assert b['parent_sha256']==phash and a['domain']==b['domain']=='nonnegative integers'
 assert a['witnesses']==b['witnesses'] and a['fixed_numerals']==b['fixed_numerals']
 assert len(a['source'])==count+1 and len(b['source'])==count and len(b['witnesses'])==13
 assert [cut,'+',inp,1] in a['source']
 transform=lambda x:inp if x==cut else x
 assert b['source']==[[n,op,transform(x),transform(y)] for n,op,x,y in a['source'] if n!=cut]
 rows={n:[op,x,y] for n,op,x,y in b['source']}
 assert rows['qm']==['*','n_J','beta'] and rows['q']==['+',1,'qm']
 assert rows['U']==['*','Y','q2'] and rows['H']==['+',3,'g15'] and rows['g15']==['*',4,'a']
 assert rows['E']==['*','X' if cut=='w' else 'n_X','Y'] and rows['a']==['+','E','Y']
 assert rows['g19']==['*','a','c'] and rows['b0']==['+','X' if cut=='w' else 'n_X','g19']
 assert rows['Delta']==['+','H','g17'] and rows['g17']==['*','a','a']
 assert rows['g61']==['*','Dstar','Dstar'] and rows['A1']==['-','g61','g65']
 assert rows['g58']==['*','U','b0'] and rows['g59']==['*','H','shift'] and rows['Dstar']==['+','g58','g59']
 if cut=='w':
  assert rows['X']==['*','q','n_w'] and rows['Y']==['*','q3','s'] and rows['Bt']==['-','g27','F']
  assert rows['g26']==['+','X','K0'] and rows['g27']==['*','C','g26'] and rows['Z']==['-','g32','Bt']
 else:
  assert rows['M']==['*','q3','qm'] and rows['Z']==['-','g34','folded_q3Bt'] and rows['g33']==['*','Y','qm'] and rows['Y']==['+','n_Y',1]
  assert rows['g25']==['*','K0','q'] and rows['g26']==['+','n_X','g25'] and rows['g27']==['*','C','g26'] and rows['g28']==['*','F','q'] and rows['Bt']==['-','g27','g28']
  assert rows['g32']==['*','M','folded_g31'] and rows['g34']==['+','g32','g33'] and rows['folded_q3Bt']==['*','q3','Bt']
 known=set(b['witnesses']+b['fixed_numerals'])
 for n,op,x,y in b['source']:
  assert n not in known and op in ('+','-','*') and all(type(z) is int or z in known for z in (x,y)); known.add(n)
 live={'out'}
 for n,op,x,y in reversed(b['source']):
  if n in live: live.update(z for z in (x,y) if isinstance(z,str))
 assert all(n in live for n,*_ in b['source']) and set(b['witnesses']+b['fixed_numerals'])<=live
 def ev(t):
  e={n:t for n in b['witnesses']};e.update({n:v%prime for n,v in ports.items()})
  for n,op,x,y in b['source']:
   x=x if type(x) is int else e[x];y=y if type(y) is int else e[y]
   e[n]=(x+y if op=='+' else x-y if op=='-' else x*y)%prime
  return e['out']
 row=[ev(t) for t in range(degree+1)]
 for _ in range(degree): row=[(v-u)%prime for u,v in zip(row,row[1:])]
 assert row[0]*pow(math.factorial(degree),-1,prime)%prime==lead
 out.append({'candidate':name,'live_gates':count,'ray_degree_lower_bound':degree,'ray_leading_coefficient':lead})
# Mod 4 check for the three universal restricted factor exclusions.
for a in range(4):
 delta=(a*a+4*a+3)%4
 for f in range(4):
  Q=(delta*(f*f-1))%4
  for y in range(4):
   for v in range(4): assert (y*y-Q*(y*y-v*v))%4!=3
  for i in range(4): assert (1+i*i-Q)%4!=3
  for c in range(4):
   for u in range(4):
    for d in range(4): assert (1+d*d-u*u*(1+delta*c*c))%4!=3
print(json.dumps({'scope':'external graph edits, port hashes, residue controls and modular finite-difference lower bounds; no Lean or endpoint proof','cases':out,'ray_prime':prime},indent=2,sort_keys=True))
