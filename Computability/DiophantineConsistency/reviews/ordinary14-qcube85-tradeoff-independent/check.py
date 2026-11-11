#!/usr/bin/env python3
"""Independent source, substitution, and port-specific degree-ray checks."""
from pathlib import Path
from collections import Counter
import gzip,hashlib,json,subprocess,sys
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-qcube85-tradeoff';P=D/'research/ordinary14-residue-guard86'
def sha(x):return hashlib.sha256(x.read_bytes()).hexdigest()
assert sha(A/'candidate.json')=='0f302fc8d7fe4dea66ec48c9e29def6a4d6737d536ddf0cf8043bd7627a985c7'
assert sha(P/'candidate.json')=='ecd34ccc9032fd7f2ef1b767b2182fe4d43aa82389b1a6857832c3dd3891c371'
readme=(A/'README.md').read_bytes()
tail=b'\nIndependent external review is recorded in\n`../../reviews/ordinary14-qcube85-tradeoff-independent/`.\n'
assert hashlib.sha256(readme).hexdigest()=='e9d519f59708750edb43f8671b41b3690432afb1d4d006046be5804904fa9cf2' and readme.endswith(tail)
assert hashlib.sha256(readme[:-len(tail)]).hexdigest()=='dbeea9e220340febe9de18a206f8dfde3a63bfec53d266e2db67c459c0e65447'
c=json.loads((A/'candidate.json').read_bytes());p=json.loads((P/'candidate.json').read_bytes())
assert len(c['source'])==85 and len(p['source'])==86 and c['witnesses']==['s' if x=='Y' else x for x in p['witnesses']] and c['fixed_numerals']==p['fixed_numerals']
expected=[]
for row in p['source']:
 if row[0]=='q3':expected.extend([row,['Y','*','q3','s']])
 elif row[0]=='g32':assert row==['g32','*','M','g31'];expected.append(['Z','*','M','g31'])
 elif row[0]=='g33':assert row==['g33','*','Y','qm']
 elif row[0]=='Z':assert row==['Z','+','g32','g33']
 else:expected.append(row)
assert c['source']==expected and c['output']==p['output']
seen=set(c['witnesses']+c['fixed_numerals']);live={c['output']}
for name,op,a,b in c['source']:
 assert name not in seen and op in '+-*' and all(isinstance(t,int) or t in seen for t in (a,b));seen.add(name)
for name,op,a,b in reversed(c['source']):
 if name in live:live.update(x for x in (a,b) if isinstance(x,str))
assert all(row[0] in live for row in c['source']) and set(c['witnesses']+c['fixed_numerals'])<=live
# Exact sparse polynomial identity in free variables q,b,s,L,k,r; M=q³b.
def add(a,b,sign=1):
 z=a.copy()
 for mon,v in b.items():z[mon]=z.get(mon,0)+sign*v
 return {mon:v for mon,v in z.items() if v}
def mul(a,b):
 z={}
 for m,x in a.items():
  for n,y in b.items():
   key=tuple(sorted(m+n));z[key]=z.get(key,0)+x*y
 return {k:v for k,v in z.items() if v}
def v(x):return {(x,):1}
q,b,s,L,k,r=map(v,['q','b','s','L','k','r']);q3=mul(mul(q,q),q);M=mul(q3,b)
assert add(mul(M,add(add(add(L,k),r,-1),s,-1)),mul(mul(q3,s),b))==mul(M,add(add(L,k),r,-1))
root=D/'con-zfc-diophantine-forms/72-congruence-sextic/positive13'; B=json.loads((root/'ACTIVE_BINDING.json').read_bytes()); Q=json.loads((D/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json').read_bytes());ports={}
for name,t in B['ports'].items():
 z=(root/t['path']).read_bytes(); raw=gzip.decompress(z)
 assert hashlib.sha256(z).hexdigest()==t['sha256_gzip']==Q['ports'][name]['sha256_gzip']
 assert hashlib.sha256(raw).hexdigest()==t['sha256_raw']==Q['ports'][name]['sha256_raw'] and len(raw)==t['raw_bytes']
 ports[name]=int.from_bytes(raw,'little')
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
for packet in (A,D/'reviews/ordinary14-residue-guard86-independent'):
 r=subprocess.run([sys.executable,'-I','-S','-B',str(packet/'check.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=120)
 assert not r.stderr and r.stdout==(packet/'result.json').read_bytes()
print(json.dumps({'scope':'external exact graph and positive-zero maps; no Lean/iPRA/PDF conclusion','operations':85,'counts':dict(Counter(row[1] for row in c['source'])),'all_live':True,'exact_first_expression_identity':True,'degree_lower_ray':56,'ray_prime':prime,'ray_leader':env[c['output']][-1],'author_readme_sha256':hashlib.sha256(readme[:-len(tail)]).hexdigest(),'author_checker_sha256':sha(A/'check.py')},sort_keys=True,indent=2))
