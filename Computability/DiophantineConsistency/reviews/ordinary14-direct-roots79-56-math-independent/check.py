#!/usr/bin/env python3
"""Independent graph, port, recurrence and ray controls; no Lean."""
from pathlib import Path
from collections import Counter
import gzip,hashlib,json,subprocess,sys
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-direct-roots79-56';P=D/'research/ordinary14-qcube85-tradeoff'
def sha(x):return hashlib.sha256(x.read_bytes()).hexdigest()
assert sha(A/'candidate.json')=='fd4f02aef44ccd1b61227f66f65e7aa8a0f751fbc24b766a124ee31656b2c56e'
assert sha(P/'candidate.json')=='0f302fc8d7fe4dea66ec48c9e29def6a4d6737d536ddf0cf8043bd7627a985c7'
readme=(A/'README.md').read_bytes()
tail=b'\nIndependent mathematical review is recorded in\n`../../reviews/ordinary14-direct-roots79-56-math-independent/`.\n'
assert hashlib.sha256(readme).hexdigest()=='1daeea11664c0d7aac68701e1d8c62183545476e5b51163d03c13a7727c649c3' and readme.endswith(tail)
assert hashlib.sha256(readme[:-len(tail)]).hexdigest()=='27b0aedba8232b78c3c35d8a604f077229d78d613f8421262672e1398f4471fc'
c=json.loads((A/'candidate.json').read_bytes());p=json.loads((P/'candidate.json').read_bytes());assert len(c['source'])==79 and len(p['source'])==85
assert c['witnesses']==['y' if x=='u' else x for x in p['witnesses']] and c['fixed_numerals']==p['fixed_numerals']
assert [r for r in p['source'] if 'r' in r[2:]]==[['g31','-','g30','r']]
assert [r for r in p['source'] if 'u' in r[2:]]==[['g78','+','V','u'],['g81','*','u','g80']]
expected=[]
for row in p['source']:
 name,op,a,b=row
 if name in ('M','g31','Z','g39','g42','g78','g80'):continue
 if name=='g38':assert row==['g38','*','Z','Z'];row=['g38','*','r','r']
 elif name=='A0':assert row==['A0','-','g38','g42'];row=['A0','-','g38','g41']
 elif name=='y2':assert row==['y2','*','g78','g78'];expected.extend([['y2','*','y','y'],['V2','*','V','V']]);continue
 elif name=='g81':assert row==['g81','*','u','g80'];row=['g81','-','y2','V2']
 expected.append(row)
assert c['source']==expected and c['output']==p['output']
# Exact auxiliary substitution and first-factor identities in the free polynomial ring.
def plus(a,b,sgn=1):
 z=a.copy()
 for m,v in b.items():z[m]=z.get(m,0)+sgn*v
 return {m:v for m,v in z.items() if v}
def mul(a,b):
 z={}
 for x,a0 in a.items():
  for y,b0 in b.items():
   m=tuple(sorted(x+y));z[m]=z.get(m,0)+a0*b0
 return {m:v for m,v in z.items() if v}
def v(n):return {(n,):1}
V,u,M,L,D0=map(v,('V','u','M','L','D'));y=plus(V,u)
assert plus(mul(y,y),mul(V,V),-1)==mul(u,plus(y,V))
assert plus(mul(mul(M,L),mul(M,L)),mul(mul(M,M),D0),-1)==mul(mul(M,M),plus(mul(L,L),D0,-1))
seen=set(c['witnesses']+c['fixed_numerals']);live={c['output']}
for name,op,a,b in c['source']:
 assert name not in seen and op in '+-*' and all(isinstance(t,int) or t in seen for t in (a,b));seen.add(name)
for name,op,a,b in reversed(c['source']):
 if name in live:live.update(x for x in (a,b) if isinstance(x,str))
assert all(row[0] in live for row in c['source']) and set(c['witnesses']+c['fixed_numerals'])<=live
# Independent integer Pell descent and square-gap small controls, not an unbounded proof.
import math
for m in range(1,51):
 for k in range(3,601):
  t=math.isqrt(1+m*(m+1)*k*k)
  if t*t==1+m*(m+1)*k*k:
   tp=(2*m+1)*t-2*m*(m+1)*k;kp=(2*m+1)*k-2*t
   assert 0<kp<k and tp>0 and tp*tp-m*(m+1)*kp*kp==1 and k>=8*m+4
for a in range(2,20):
 for cc in range(2,2*(a+2)):
  z=1+((a+2)**2-1)*cc*cc
  assert ((a+2)*cc-1)**2<z<((a+2)*cc)**2
root=D/'con-zfc-diophantine-forms/72-congruence-sextic/positive13';B=json.loads((root/'ACTIVE_BINDING.json').read_bytes());Q=json.loads((D/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json').read_bytes());ports={}
for name,t in B['ports'].items():
 z=(root/t['path']).read_bytes();raw=gzip.decompress(z)
 assert hashlib.sha256(z).hexdigest()==t['sha256_gzip']==Q['ports'][name]['sha256_gzip']
 assert hashlib.sha256(raw).hexdigest()==t['sha256_raw']==Q['ports'][name]['sha256_raw'] and len(raw)==t['raw_bytes']
 ports[name]=int.from_bytes(raw,'little')
assert ports['beta']==2**590069-1
assert ports['beta']>=46 and ports['K0']>=0 and 0<ports['MC']<ports['beta'] and 0<ports['MF']<2*ports['beta']
prime=1000000007
def trim(z):
 while len(z)>1 and z[-1]==0:z.pop()
 return z
def pol(op,a,b):
 if op!='*':return trim([((a[i] if i<len(a) else 0)+(1 if op=='+' else -1)*(b[i] if i<len(b) else 0))%prime for i in range(max(len(a),len(b)))])
 z=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):z[i+j]=(z[i+j]+x*y)%prime
 return trim(z)
env={x:[i+2,i+3] for i,x in enumerate(c['witnesses'])};env.update({x:[y%prime] for x,y in ports.items()})
for name,op,a,b in c['source']:env[name]=pol(op,[a%prime] if isinstance(a,int) else env[a],[b%prime] if isinstance(b,int) else env[b])
assert len(env[c['output']])==57 and env[c['output']][-1]!=0
for packet in (A,D/'reviews/ordinary14-qcube85-tradeoff-independent'):
 r=subprocess.run([sys.executable,'-I','-S','-B',str(packet/'check.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=120)
 assert not r.stderr and r.stdout==(packet/'result.json').read_bytes()
print(json.dumps({'scope':'external graph and conditional arithmetic reasoning; no Lean/iPRA/PDF conclusion','operations':79,'counts':dict(Counter(row[1] for row in c['source'])),'all_live':True,'two_root_identities':True,'degree_lower_ray':56,'ray_prime':prime,'ray_leader':env[c['output']][-1],'author_readme_sha256':hashlib.sha256(readme[:-len(tail)]).hexdigest(),'author_checker_sha256':sha(A/'check.py')},sort_keys=True,indent=2))
