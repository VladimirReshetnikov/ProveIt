#!/usr/bin/env python3
"""Independent graph, port, recurrence and ray controls; no Lean."""
from pathlib import Path
from collections import Counter
import gzip,hashlib,json,subprocess,sys
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-direct-pell79';P=D/'research/ordinary14-qcube84-probe'
def sha(x):return hashlib.sha256(x.read_bytes()).hexdigest()
assert sha(A/'candidate.json')=='5c5e2c089d0f10450374219e9d74883235fd0ef3b10d31d6df09a7dc498e2507'
assert sha(P/'candidate.json')=='cc1e1f58416c964d02906af8ef2378f74f1ca94b7806bcc8ae670a31d5f08b61'
readme=(A/'README.md').read_bytes()
tail=b'\nIndependent mathematical review is recorded in\n`../../reviews/ordinary14-direct-pell79-math-independent/`.\n'
assert hashlib.sha256(readme).hexdigest()=='e41adb864cd5b18cc345b79886c21b28d575d235f3a16715bf262ebacf061035' and readme.endswith(tail)
assert hashlib.sha256(readme[:-len(tail)]).hexdigest()=='a5ec6623c6bdf198d3a05c4223865e10ff5ea3df45c6403b547a4836a284f6ac'
c=json.loads((A/'candidate.json').read_bytes());p=json.loads((P/'candidate.json').read_bytes());assert len(c['source'])==79 and len(p['source'])==84
assert c['witnesses']==p['witnesses'] and c['fixed_numerals']==p['fixed_numerals']
assert [row[0] for row in p['source'] if 'r' in row[2:]]==['g31']
expected=[]
for row in p['source']:
 if row[0] in ('M','g31','Z','g39','g42'):continue
 if row[0]=='g38':assert row==['g38','*','Z','Z'];expected.append(['g38','*','r','r'])
 elif row[0]=='A0':assert row==['A0','-','g38','g42'];expected.append(['A0','-','g38','g41'])
 else:expected.append(row)
assert c['source']==expected and c['output']==p['output']
seen=set(c['witnesses']+c['fixed_numerals']);live={c['output']}
for name,op,a,b in c['source']:
 assert name not in seen and op in '+-*' and all(isinstance(t,int) or t in seen for t in (a,b));seen.add(name)
for name,op,a,b in reversed(c['source']):
 if name in live:live.update(x for x in (a,b) if isinstance(x,str))
assert all(row[0] in live for row in c['source']) and set(c['witnesses']+c['fixed_numerals'])<=live
# Symbolic first residual identity in independent polynomial indeterminates.
def plus(a,b,sign=1):
 z=a.copy()
 for key,n in b.items():z[key]=z.get(key,0)+sign*n
 return {k:n for k,n in z.items() if n}
def times(a,b):
 z={}
 for m,x in a.items():
  for n,y in b.items():
   key=tuple(sorted(m+n));z[key]=z.get(key,0)+x*y
 return {k:n for k,n in z.items() if n}
def v(k):return {(k,):1}
M,L,D0=map(v,('M','L','D'));old=plus(times(times(M,L),times(M,L)),times(times(M,M),D0),-1)
assert old==times(times(M,M),plus(times(L,L),D0,-1))
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
for packet in (A,D/'reviews/ordinary14-qcube84-probe-math-independent'):
 r=subprocess.run([sys.executable,'-I','-S','-B',str(packet/'check.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=120)
 assert not r.stderr and r.stdout==(packet/'result.json').read_bytes()
print(json.dumps({'scope':'external graph and conditional arithmetic reasoning; no Lean/iPRA/PDF conclusion','operations':79,'counts':dict(Counter(row[1] for row in c['source'])),'all_live':True,'exact_first_factor_identity':True,'degree_lower_ray':60,'ray_prime':prime,'ray_leader':env[c['output']][-1],'author_readme_sha256':hashlib.sha256(readme[:-len(tail)]).hexdigest(),'author_checker_sha256':sha(A/'check.py')},sort_keys=True,indent=2))
