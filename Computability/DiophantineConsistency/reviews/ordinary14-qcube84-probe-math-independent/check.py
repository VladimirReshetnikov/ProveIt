#!/usr/bin/env python3
"""Independent graph, port, recurrence and ray controls; no Lean."""
from pathlib import Path
from collections import Counter
import gzip,hashlib,json,subprocess,sys
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-qcube84-probe';P=D/'research/ordinary14-qcube85-tradeoff'
def sha(x):return hashlib.sha256(x.read_bytes()).hexdigest()
assert sha(A/'candidate.json')=='cc1e1f58416c964d02906af8ef2378f74f1ca94b7806bcc8ae670a31d5f08b61'
assert sha(P/'candidate.json')=='0f302fc8d7fe4dea66ec48c9e29def6a4d6737d536ddf0cf8043bd7627a985c7'
for name,h in {
 'Lean/DiophantineConsistency/Compact44/P72Exact.lean':'a07730d92aefd39d86083d037f4772bacd7741788e2fff1f7669d33fa0ad05d3',
 'Lean/DiophantineConsistency/Compact44/P72Power.lean':'f46584fb3977ae5fc33b31bee18e8c27435d97bea10138f163af2de5ee66d462',
 'Lean/DiophantineConsistency/ArithmeticPellPowerRecovery.lean':'636b64ce7d7625603b41412ec6acade846e82e64bef36e55cd09cc0f1e09e390',
 'Lean/DiophantineConsistency/ArithmeticAdaptiveMersenne2011.lean':'c8a132e1b28bd1cf1ed76d80e953d5568ff0c77f566ad7b2b66715c8be9641ef',
 'reviews/ordinary14-shifted-guard87-calibration-decoder-independent/README.md':'fe4d686bba5dc30375c3835d91cb29ed7a92ac7f25cd5b10a49b787ea30dc99a'}.items():assert sha(D/name)==h
readme=(A/'README.md').read_bytes()
tail=b'\nIndependent mathematical review is recorded in\n`../../reviews/ordinary14-qcube84-probe-math-independent/`.\nA separate independent decoder review is recorded in\n`../../reviews/ordinary14-qcube84-probe-independent/`.\n'
assert hashlib.sha256(readme).hexdigest()=='9d7bc547fb920fa4fe9b74b06f53c0f23c64a88b30515eb4b89eaa1cbcc918ac' and readme.endswith(tail)
assert hashlib.sha256(readme[:-len(tail)]).hexdigest()=='acae6a2a27ef8d38c6f104fed7fd23d1ce7d18ade04fe7fe12a7691360c75312'
c=json.loads((A/'candidate.json').read_bytes());p=json.loads((P/'candidate.json').read_bytes());assert len(c['source'])==84 and len(p['source'])==85
assert c['witnesses']==['w' if x=='X' else x for x in p['witnesses']] and c['fixed_numerals']==p['fixed_numerals']
expected=[]
for row in p['source']:
 if row[0]=='q': expected.extend([row,['X','*','q','w']])
 elif row[0]=='g55':assert row==['g55','*','E','q']
 elif row[0]=='g56':assert row==['g56','+','g54','g55']
 elif row[0]=='shift':assert row==['shift','-','g56','r0'];expected.append(['shift','-','g54','r0'])
 else:expected.append(row)
assert c['source']==expected and c['output']==p['output']
seen=set(c['witnesses']+c['fixed_numerals']);live={c['output']}
for name,op,a,b in c['source']:
 assert name not in seen and op in '+-*' and all(isinstance(t,int) or t in seen for t in (a,b));seen.add(name)
for name,op,a,b in reversed(c['source']):
 if name in live:live.update(x for x in (a,b) if isinstance(x,str))
assert all(row[0] in live for row in c['source']) and set(c['witnesses']+c['fixed_numerals'])<=live
# Exact symbolic shift identity with X=q*w, Y=q³*s; monomials are tuples.
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
q,w,s,g=map(v,('q','w','s','gamma'));Y=times(times(times(q,q),q),s);X=times(q,w);U=times(Y,times(q,q));E=times(X,Y)
assert plus(times(U,plus(g,w,-1)),times(E,q))==times(U,g)
# Pell projection quotient recurrence: z_0=0,z_(j+1)=2z_j+y_j.
for a in range(2,14):
 x,y,z=1,0,0
 for t in range(1,20):
  x,y,z=(a+2)*x+((a+2)**2-1)*y,x+(a+2)*y,2*z+y
  assert x==2**t+a*y+(4*a+3)*z
  if t>=2:assert z>=2**(t-2)
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
for packet in (A,D/'reviews/ordinary14-qcube85-tradeoff-independent'):
 r=subprocess.run([sys.executable,'-I','-S','-B',str(packet/'check.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=120)
 assert not r.stderr and r.stdout==(packet/'result.json').read_bytes()
print(json.dumps({'scope':'external graph and conditional arithmetic reasoning; no Lean/iPRA/PDF conclusion','operations':84,'counts':dict(Counter(row[1] for row in c['source'])),'all_live':True,'exact_shift_identity':True,'degree_lower_ray':60,'ray_prime':prime,'ray_leader':env[c['output']][-1],'author_readme_sha256':hashlib.sha256(readme[:-len(tail)]).hexdigest(),'author_checker_sha256':sha(A/'check.py')},sort_keys=True,indent=2))
