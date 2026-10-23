if not __debug__: raise SystemExit('Optimized Python is not permitted: assertions are audit checks.')
"""New-owned diagnostic checker; no received program is executed or imported."""
import gzip,hashlib,json,random
from pathlib import Path
import numpy as np
HERE=Path(__file__).resolve().parent

def load(name):return json.loads((HERE/name).read_text())
def val(x,env):return env[x] if isinstance(x,str) else x

def eval_circuit(packet,w,coeff,p):
 env=dict(w,**coeff)
 for name,op,a,b in packet['source']:
  x,y=val(a,env),val(b,env)
  env[name]=({'+':lambda:x+y,'-':lambda:x-y,'*':lambda:x*y}[op]())%p
 return env

def retained(w,coeff):
 J,F,al,z,h,i,T,s,wv,eta,zeta,t=[w[n] for n in ['J','F','alpha','z','h','i','T','s','w','eta','zeta','t']]
 beta,K0,MC,MF=[coeff[n] for n in ['beta','K0','MC','MF']]
 qq=beta*J+1;X=wv*qq;Y=s*qq**3;E=X*Y;k=eta+zeta;c=k*Y+eta;aa=E+Y;H=4*aa+3;de=aa*aa+H
 ell=E*k*Y;A=1+ell*(ell+k);G=1+de*c*c;b0=X+aa*c
 R=((qq-1)*(qq-F)+al)*(qq*qq-1)+(MC+qq*MF)*J
 I=i*c*c;D=1+de*I*I;Q=(de*I)**2;d=Q-1;v=c*T;b=c+R*D
 ee=Q*(D*v*v+b*b)-1;B=2*Q*v*b;M=k*(I*I+T*T);L=H*M+1;W=b0+H*t
 Nk=k-h*E-R;Nt=(K0+wv)*(qq-F-al)+qq-F-z*(qq-1)
 return dict(A=A,G=G,D=D,d=d,v=v,b=b,e=ee,B=B,M=M,L=L,H=H,W=W,Nk=Nk,Nt=Nt)

# A generic basis [sqrt(A)^a sqrt(G)^g sqrt(D)^f] with a,g,f in {0,1}.
# Multiplication uses only bit identities and is unrelated to the emitted scalar evaluator.
def radical_norm(q,p):
 rad=[q['A']%p,q['G']%p,q['D']%p]
 def mul(a,b):
  out=[0]*8
  for i in range(8):
   for j in range(8):
    c=a[i]*b[j];both=i&j
    for h in range(3):
     if both>>h&1:c*=rad[h]
    out[i^j]=(out[i^j]+c)%p
  return out
 def add(a,b):return [(x+y)%p for x,y in zip(a,b)]
 def scale(a,k):return [x*k%p for x in a]
 out=[1]+[0]*7
 for sa in [-1,1]:
  for sg in [-1,1]:
   for sf in [-1,1]:
    lin=[q['W'], -q['H']*q['M']*sa, -q['L']*sg,0,0,0,0,0]
    fac=scale(mul(lin,lin),q['d']);fac[0]=(fac[0]-q['H']**2*q['e'])%p;fac[4]=(fac[4]+q['H']**2*q['B']*sf)%p
    out=mul(out,fac)
 assert out[1:]==[0]*7,out
 return out[0]

def kernel_scalar(q,p):
 H,M,L,W,G,d,A=q['H'],q['M'],q['L'],q['W'],q['G'],q['d'],q['A']
 dn=d*(H*M)**2*A;He=H*H*q['e'];j=H**4*q['D']*q['B']**2
 tr=2*d*(W*W+L*L*G);kn=d*d*(W*W-L*L*G)**2
 at=tr-2*(dn+He);bt=(dn-He)**2-j-kn;co=16*dn*j
 vr=at*(at*tr+2*bt)-co;ur=bt*bt-at*at*kn
 return (ur*ur+tr*ur*vr+kn*vr*vr)%p

def degree_test(packet,p,seed):
 rng=random.Random(seed);env={n:np.array([rng.randrange(1,p),rng.randrange(1,p)],dtype=np.int64) for n in packet['witnesses']}
 for n in packet['fixed_numerals']:env[n]=np.array([rng.randrange(1,p)],dtype=np.int64)
 def get(x):return env[x] if isinstance(x,str) else np.array([x%p],dtype=np.int64)
 for name,op,a,b in packet['source']:
  x,y=get(a),get(b)
  if op=='*':z=np.convolve(x,y)%p
  else:
   z=np.zeros(max(len(x),len(y)),dtype=np.int64);z[:len(x)]+=x;z[:len(y)]+=y if op=='+' else -y;z%=p
  while len(z)>1 and z[-1]==0:z=z[:-1]
  env[name]=z
 return {name:len(env[name])-1 for name in ['Nk','Nt','N',packet['output']]}

def liveness(packet):
 available=set(packet['witnesses']+packet['fixed_numerals']);by={}
 for row in packet['source']:
  n,op,a,b=row;assert n not in available and op in '+-*'
  assert all(not isinstance(x,str) or x in available for x in (a,b)),row
  available.add(n);by[n]=(a,b)
 roots=[packet['output']] if 'output' in packet else [x for pair in packet['comparisons'] for x in pair if isinstance(x,str)]
 live=set();todo=roots[:]
 while todo:
  n=todo.pop()
  if n in live:continue
  live.add(n)
  if n in by:todo.extend(x for x in by[n] if isinstance(x,str))
 assert live==available,(available-live)
 ledger=dict(operations=len(by),multiplications=sum(r[1]=='*' for r in packet['source']),additions_subtractions=sum(r[1]!='*' for r in packet['source']))
 assert ledger==packet['ledger'];return ledger

def main():
 product=load('positive12_product.json');system=load('positive12_system.json');report={}
 report['ledgers']={p['name']:liveness(p) for p in [product,system]}
 rng=random.Random(2026102301);passes=0
 for prime in [251,65521,1000003]:
  for j in range(60):
   w={n:rng.randrange(-12,13) for n in product['witnesses']};coeff={n:rng.randrange(-15,16) for n in product['fixed_numerals']}
   env=eval_circuit(product,w,coeff,prime);data=retained(w,coeff);direct=radical_norm(data,prime)
   assert direct==env['N']==kernel_scalar(data,prime),(prime,j)
   assert env[product['output']]==(data['Nk']*data['Nt']*(1+direct)-1)%prime
   passes+=1
 report['independent_eight_branch_norm_assignments']=passes
 report['degree_specializations']=[degree_test(product,65521,199),degree_test(product,65519,502)]
 for row in report['degree_specializations']:assert row=={'Nk':7,'Nt':2,'N':1072,'polynomial':1081},row
 fixtures=0
 for S in range(2,9):
  for tau in range(2,5):
   H=7;M=13;g=17;f=2;v=3;b=5;Q=S*S;y=1;L=H*M+1;W=L*g+H*(M*tau+y)
   q=dict(H=H,M=M,L=L,W=W,G=g*g,A=tau*tau,D=f*f,d=Q-1,e=Q*(f*f*v*v+b*b)-1,B=2*Q*v*b)
   assert Q*(v*f-b)**2-(Q-1)*y*y==1
   for p in [251,65521]:assert kernel_scalar(q,p)==radical_norm(q,p)==0
   fixtures+=1
 report['synthetic_full_radical_kernel_witnesses']=fixtures
 # Independent finite tests of the new strict inequalities under the inherited weak bounds.
 bounds=0
 for _ in range(500):
  qq=rng.randrange(16,70);X=qq*rng.randrange(1,10**5);Y=qq**3*rng.randrange(1,30);E=X*Y
  R=rng.randrange(3*qq+1,qq**4-2);k=E+R+rng.randrange(1,1000);eta=rng.randrange(1,k);c=k*Y+eta
  aa=E+Y;H=4*aa+3;de=aa*aa+H;I=rng.randrange(1,15)*c*c;D=1+de*I*I;Q=(de*I)**2;d=Q-1
  T=10**rng.randrange(0,30)+rng.randrange(1,1000);v=c*T;b=c+R*D;M=k*(I*I+T*T);ell=E*k*Y;A=1+ell*(ell+k)
  small=M*k*Y*Y
  assert small>4*b and small*small>16*v*v*D
  assert d*A*M*M>2*Q*(D*v*v+b*b)
  assert (aa+1)*c-(ell+k)>k*Y*Y
  bounds+=1
 report['strict_separation_bound_assignments']=bounds

 # Congruence test is a diagnostic supplement to the polynomial identity in the proof.
 parity=0
 for _ in range(400):
  w={n:rng.randrange(-9,10) for n in product['witnesses']};coeff={n:rng.randrange(-9,10) for n in product['fixed_numerals']}
  env=eval_circuit(product,w,coeff,4);assert env['N'] in [0,1];parity+=1
 report['mod4_guard_assignments']=parity
 bind=load('COEFFICIENT_BINDING.json');payload={}
 actual={}
 for port,entry in bind['coefficient_files'].items():
  raw=(HERE/entry['path']).read_bytes();raw=gzip.decompress(raw) if entry['path'].endswith('.gz') else raw;sha=hashlib.sha256(raw).hexdigest();assert sha==entry['sha256']
  number=int.from_bytes(raw,'little');assert number.bit_length()==entry['bit_length'];assert len(raw)==entry['bytes']
  payload[port]=dict(sha256=sha,bytes=len(raw),bit_length=number.bit_length())
  actual[{'K':'K0','MF_source':'MF'}.get(port,port)]=number%65521
 report['coefficient_payloads']=payload
 for _ in range(12):
  w={n:rng.randrange(1,15) for n in product['witnesses']};env=eval_circuit(product,w,actual,65521)
  assert env['N']==radical_norm(retained(w,actual),65521)
 report['actual_bound_coefficient_residue_assignments']=12
 report['scope']='Arithmetic diagnostics only, not a finite proof of the inherited compiler, K215 calibration, or consistency.'
 (HERE/'CHECK_RESULTS.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
if __name__=='__main__':main()
