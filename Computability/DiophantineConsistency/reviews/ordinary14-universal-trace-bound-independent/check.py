#!/usr/bin/env python3
"""Independent external trace/graph controls; never invokes Lean."""
import gzip,hashlib,json,math,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-universal-trace-bound'
def sha(d):return hashlib.sha256(d).hexdigest()
def pin(p,h):
 d=p.read_bytes();assert sha(d)==h,str(p);return d
candidate=json.loads(pin(A/'candidate.json','71073ea15ceeddac9d9bf9324238d03af346b5075eedb78351f29f19079d3862'))
pin(A/'check.py','3d3f1f24bdfbe4fe3ce90b663a260c62dacd3d630833a4a42f789204bb2c57cc')
receipt=pin(A/'result.json','678ab0868d8933efb0192552f39e96602728a446ea74c0139e1ef28b499589a3')
readme=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-universal-trace-bound-independent/`.\n')
assert readme.endswith(tail) and sha(readme[:-len(tail)])=='64a156419a1b89fc8c7427285de0c1dfd2d194e1389752f49bc32bb8a7d4a96c'
parent=json.loads(pin(D/'research/ordinary14-positive-guard74/candidate.json','e70af4f896013695368180743f514c027faa86f8b3cedd5479b22e64e4c26093'))
pin(D/'Lean/DiophantineConsistency/ArithmeticPellPowerRecovery.lean','636b64ce7d7625603b41412ec6acade846e82e64bef36e55cd09cc0f1e09e390')
assert candidate['source']==[r for r in parent['source'] if r[0]!='X']
assert candidate['witnesses']==['X' if x=='w' else x for x in parent['witnesses']]
assert candidate['fixed_numerals']==parent['fixed_numerals'] and len(candidate['source'])==73
known=set(candidate['witnesses']+candidate['fixed_numerals']);rows={}
for n,op,x,y in candidate['source']:
 assert n not in known and op in ('+','-','*') and all(isinstance(a,int) or a in known for a in (x,y))
 known.add(n);rows[n]=(x,y)
live=set();todo=[candidate['output']]
while todo:
 n=todo.pop()
 if n in live or n not in rows:continue
 live.add(n);todo.extend(rows[n])
assert len(live)==73
root=D/'con-zfc-diophantine-forms/72-congruence-sextic/positive13'
binding=json.loads(pin(root/'ACTIVE_BINDING.json','6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf'))
b115=json.loads(pin(D/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json','dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01'))
prime=1000000007;fixed={}
for name,meta in binding['ports'].items():
 assert b115['ports'][name]['sha256_raw']==meta['sha256_raw'] and b115['ports'][name]['sha256_gzip']==meta['sha256_gzip']
 raw=gzip.decompress(pin(root/meta['path'],meta['sha256_gzip']))
 assert len(raw)==meta['raw_bytes'] and sha(raw)==meta['sha256_raw']
 fixed[name]=int.from_bytes(raw,'little')%prime
def trim(p):
 while len(p)>1 and p[-1]==0:p.pop()
 return p
def add(a,b,sgn):return trim([((a[i] if i<len(a) else 0)+sgn*(b[i] if i<len(b) else 0))%prime for i in range(max(len(a),len(b)))])
def mul(a,b):
 out=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):out[i+j]=(out[i+j]+x*y)%prime
 return trim(out)
polys={n:[0,3*i+5] for i,n in enumerate(candidate['witnesses'])};polys.update({n:[v] for n,v in fixed.items()})
def val(x):return [x%prime] if isinstance(x,int) else polys[x]
for n,op,x,y in candidate['source']:
 a,b=val(x),val(y);polys[n]=mul(a,b) if op=='*' else add(a,b,1 if op=='+' else -1)
ray=polys[candidate['output']];assert len(ray)-1==100 and ray[-1]!=0
def pell(p,n):
 x,y=1,0;D0=p*p-1
 for _ in range(n):x,y=p*x+D0*y,x+p*y
 return x,y
cases=intervals=0
for X in range(1,11):
 for Y in range(1,21):
  a=Y*(X+1);Aparam=a+2;m=X*Y*Y;P=2*m+1
  lhs=X*(2*Aparam-1)**2-(X+1)**2*(2*P)
  assert lhs==12*X*Y*(X+1)+9*X-2*(X+1)**2 and lhs>0
  for N in range(1,6):
   R=2*N+1;d,c=pell(Aparam,R);tau,y=pell(P,N+1);k=2*y
   assert c*2*(2*P)**N>=k*(2*Aparam-1)**(2*N)
   if Y*k<c<(Y+1)*k:
    assert 2**(R-2)<=Y and 0<2**R<=4*Y<4*a+3 and 0<X<4*a+3
    if (d-X-a*c)%(4*a+3)==0:assert X==2**R
    intervals+=1
   cases+=1
assert intervals
for m in range(2,41):
 for k in range(1,101):
  z=m*(m+1)*k*k-1
  assert math.isqrt(z)**2!=z
N=17;R=2*N+1;X=2**R
total=sum(math.comb(2*N,j)*X**(N-j) for j in range(N+1));assert total%2==0
Y=total//2;q=3;a=Y*(X+1);m=X*Y*Y;d,c=pell(a+2,R);tau,y=pell(2*m+1,N+1);k=2*y
assert Y%q**3==0 and X%q!=0 and R+1<q**4 and Y*k<c<(Y+1)*k
assert tau*tau==1+m*(m+1)*k*k and d*d==1+(a+1)*(a+3)*c*c
assert (d-X-a*c)%(4*a+3)==0
digest=sha(Y.to_bytes((Y.bit_length()+7)//8,'little'))
assert digest=='f4a97f4b243ae8b62c6c163f151e00aca018af63dd828955e94bae6cffc2751c'
r=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=90)
assert not r.stderr and r.stdout==receipt
print(json.dumps({'scope':'external proof review and finite controls only; no Lean or full graph zero',
 'prelink_readme_sha256':sha(readme[:-len(tail)]),'graph_rows':len(live),
 'distinct_weighted_ray_degree':len(ray)-1,'distinct_weighted_ray_leader':ray[-1],
 'pell_cases':cases,'interval_cases':intervals,'toy_Y_bits':Y.bit_length(),
 'toy_Y_sha256_little_endian':digest,'toy_q_does_not_divide_X':True},sort_keys=True,indent=2))
