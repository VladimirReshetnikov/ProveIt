#!/usr/bin/env python3
"""Independent graph, port, recurrence and ray controls; no Lean."""
from pathlib import Path
from collections import Counter
import gzip,hashlib,json,subprocess,sys
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-aux-root78';P=D/'research/ordinary14-direct-pell79'
def sha(x):return hashlib.sha256(x.read_bytes()).hexdigest()
assert sha(A/'candidate.json')=='d579ba32a40eed91a336b0015086104e1d1a7c6569092f757328769a3128ab43'
assert sha(P/'candidate.json')=='5c5e2c089d0f10450374219e9d74883235fd0ef3b10d31d6df09a7dc498e2507'
readme=(A/'README.md').read_bytes()
tail=b'\nIndependent mathematical review is recorded in\n`../../reviews/ordinary14-aux-root78-math-independent/`.\n'
assert hashlib.sha256(readme).hexdigest()=='461164edefa8b442580c9d186fa1bf1ade7f4d128c9cbc70bbb112f1af52d938' and readme.endswith(tail)
assert hashlib.sha256(readme[:-len(tail)]).hexdigest()=='68bcc75baae9290ec00545a1aee53d6147536bfb997787a3db87419354a14a2c'
c=json.loads((A/'candidate.json').read_bytes());p=json.loads((P/'candidate.json').read_bytes());assert len(c['source'])==78 and len(p['source'])==79
assert c['witnesses']==['y' if x=='u' else x for x in p['witnesses']] and c['fixed_numerals']==p['fixed_numerals']
assert [r for r in p['source'] if 'u' in r[2:]]==[['g78','+','V','u'],['g81','*','u','g80']]
oldnodes={r[0]:r for r in p['source']}
assert oldnodes['g78']==['g78','+','V','u'] and oldnodes['g80']==['g80','+','g78','V'] and oldnodes['g81']==['g81','*','u','g80']
# (V+u)^2−V²=u*(2V+u) exactly, as a sparse coefficient identity.
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
V={('V',):1};u={('u',):1};y=plus(V,u)
assert plus(mul(y,y),mul(V,V),-1)==mul(u,plus(y,V))
expected=[]
for row in p['source']:
 name,op,a,b=row
 if name in ('g78','g80','g81'):continue
 if name=='y2':assert row==['y2','*','g78','g78'];row=['y2','*','y','y']
 if name=='g82':expected.extend([['V2','*','V','V'],['g81','-','y2','V2']])
 expected.append(row)
assert c['source']==expected and c['output']==p['output']
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
assert len(env[c['output']])==61 and env[c['output']][-1]!=0
for packet in (A,D/'reviews/ordinary14-direct-pell79-math-independent'):
 r=subprocess.run([sys.executable,'-I','-S','-B',str(packet/'check.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=120)
 assert not r.stderr and r.stdout==(packet/'result.json').read_bytes()
print(json.dumps({'scope':'external graph and conditional arithmetic reasoning; no Lean/iPRA/PDF conclusion','operations':78,'counts':dict(Counter(row[1] for row in c['source'])),'all_live':True,'auxiliary_substitution':'y=V+u','degree_lower_ray':60,'ray_prime':prime,'ray_leader':env[c['output']][-1],'author_readme_sha256':hashlib.sha256(readme[:-len(tail)]).hexdigest(),'author_checker_sha256':sha(A/'check.py')},sort_keys=True,indent=2))
