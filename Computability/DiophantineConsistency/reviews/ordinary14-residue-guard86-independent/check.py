#!/usr/bin/env python3
"""Independent graph/port/ray checks; not an unbounded proof or Lean."""
from pathlib import Path
from collections import Counter
import hashlib,json,gzip,subprocess,sys
D=Path(__file__).resolve().parents[2]; A=D/'research/ordinary14-residue-guard86'; P=D/'research/ordinary14-shifted-guard87-probe'
def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
assert digest(A/'candidate.json')=='ecd34ccc9032fd7f2ef1b767b2182fe4d43aa82389b1a6857832c3dd3891c371'
assert digest(P/'candidate.json')=='405dbed5bf465dacac2246e6e8b2c53bcb3dda9b4b13ba277f4a18cdd43ae210'
old=json.loads((P/'candidate.json').read_bytes()); new=json.loads((A/'candidate.json').read_bytes())
readme=(A/'README.md').read_bytes()
tail=b'\nIndependent external review is recorded in\n`../../reviews/ordinary14-residue-guard86-independent/`.\n'
assert hashlib.sha256(readme).hexdigest()=='d18599f319d453842e05bf804ece9b5963ca1ae65593bde9f47370171ab21fca'
assert readme.endswith(tail) and hashlib.sha256(readme[:-len(tail)]).hexdigest()=='6e6c72a16ac1f8fee57d9868f0dc9e1a78cd55e4a13fcd79ff725624747e9e63'
o=old['source']; n=new['source']; assert len(o)==87 and len(n)==86
assert [r for r in o if 'g25' in r[2:]]==[['g26','+','X','g25']]
expected=[]
for row in o:
 name,op,a,b=row
 if name=='g25':
  assert row==['g25','*','K0','q'];continue
 if name=='g26': assert row==['g26','+','X','g25']; b='K0'
 expected.append([name,op, 'h' if a=='omega' else a,'h' if b=='omega' else b])
assert expected==n and old['output']==new['output']
assert old['witnesses'][:-1]==new['witnesses'][:-1] and old['witnesses'][-1]=='omega' and new['witnesses'][-1]=='h' and old['fixed_numerals']==new['fixed_numerals']
avail=set(new['witnesses']+new['fixed_numerals']); needed={new['output']}
for name,op,a,b in n:
 assert name not in avail and op in ('+','-','*') and all(isinstance(x,int) or x in avail for x in (a,b));avail.add(name)
for name,op,a,b in reversed(n):
 if name in needed:needed.update(x for x in (a,b) if isinstance(x,str))
assert all(row[0] in needed for row in n) and set(new['witnesses']+new['fixed_numerals'])<=needed
counts=Counter(r[1] for r in n);assert counts=={'+':23,'-':17,'*':46}
# Symbolically compare guards with omega=h+C*K and q=1+b.
def add(x,y,sgn=1):
 z=x.copy()
 for m,c in y.items():z[m]=z.get(m,0)+sgn*c
 return {m:c for m,c in z.items() if c}
def mul(x,y):
 z={}
 for a,b in x.items():
  for c,d in y.items():
   m=tuple(sorted(a+c));z[m]=z.get(m,0)+b*d
 return {m:c for m,c in z.items() if c}
def v(s):return {(s,):1}
C,X,K,F,b,h=(v(s) for s in ('C','X','K','F','b','h'))
assert add(add(mul(C,add(X,mul(K,add({():1},b)))),F,-1),mul(b,add(h,mul(C,K))),-1)==add(add(mul(C,add(X,K)),F,-1),mul(b,h),-1)
# Reauthenticate bytes and compute a different nonuniform affine ray mod prime.
root=D/'con-zfc-diophantine-forms/72-congruence-sextic/positive13'; binding=json.loads((root/'ACTIVE_BINDING.json').read_bytes()); b115=json.loads((D/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json').read_bytes()); ports={}
for name,meta in binding['ports'].items():
 packed=(root/meta['path']).read_bytes();raw=gzip.decompress(packed)
 assert hashlib.sha256(packed).hexdigest()==meta['sha256_gzip']==b115['ports'][name]['sha256_gzip']
 assert hashlib.sha256(raw).hexdigest()==meta['sha256_raw']==b115['ports'][name]['sha256_raw'] and len(raw)==meta['raw_bytes']
 ports[name]=int.from_bytes(raw,'little')
assert ports['beta']>=46 and 0<ports['MC']<ports['beta'] and 0<ports['MF']<2*ports['beta'] and 0<=ports['K0']<(ports['beta']+1)**2
p=1000000007
def trim(z):
 while len(z)>1 and z[-1]==0:z.pop()
 return z
def op(a,b,typ):
 if typ!='*':return trim([((a[i] if i<len(a) else 0)+(1 if typ=='+' else -1)*(b[i] if i<len(b) else 0))%p for i in range(max(len(a),len(b)))])
 z=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):z[i+j]=(z[i+j]+x*y)%p
 return trim(z)
env={x:[i+2,i+3] for i,x in enumerate(new['witnesses'])};env.update({x:[val%p] for x,val in ports.items()})
for name,typ,a,b in n:env[name]=op([a%p] if isinstance(a,int) else env[a],[b%p] if isinstance(b,int) else env[b],typ)
assert len(env[new['output']])==27 and env[new['output']][-1]!=0
for packet in (A,D/'reviews/ordinary14-shifted-guard87-calibration-decoder-independent',D/'reviews/ordinary14-shifted-guard87-probe-independent'):
 out=subprocess.run([sys.executable,'-I','-S','-B',str(packet/'check.py')],cwd=D,check=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=120)
 assert not out.stderr and out.stdout==(packet/'result.json').read_bytes()
print(json.dumps({'scope':'external graph checks and conditional standard-integer maps; no Lean/PDF claim','operations':len(n),'counts':dict(counts),'live':True,'guard_identity':True,'degree_lower_ray':26,'ray_prime':p,'ray_leader':env[new['output']][-1],'author_readme_sha256':hashlib.sha256(readme[:-len(tail)]).hexdigest(),'author_check_sha256':digest(A/'check.py')},sort_keys=True,indent=2))
