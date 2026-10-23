"""Independent exact modular radical algebra and integer upper-bound diagnostics."""
import json,random,math
from pathlib import Path
ROOT=Path(__file__).resolve().parent
rng=random.Random(962023)
p=1000003

def evaluate(packet, vals):
 v=vals.copy()
 for n,op,x,y in packet['source']:
  x=v[x] if isinstance(x,str) else x;y=v[y] if isinstance(y,str) else y
  v[n]=(x+y if op=='+' else x-y if op=='-' else x*y)%p
 return v

def radical_norm(vals,kind):
 J,F,al,z,h,i,T,s,w,eta,zeta,t=[vals[n] for n in ['J','F','alpha','z','h','i','T','s','w','eta','zeta','t']]
 beta,K0,MC,MF=[vals[n] for n in ['beta','K0','MC','MF']]
 q=beta*J+1;C=q-F-al;X=w*q;Y=s*q**3;E=X*Y;k=eta+zeta;c=k*Y+eta;aa=E+Y;H=4*aa+3;de=aa*aa+H;ell=E*k*Y;A=1+ell*(ell+k);G=1+de*c*c;b0=X+aa*c
 R=((q-1)*(q-F)+al)*(q*q-1)+(MC+q*MF)*J;I=i*c*c;D=1+de*I*I;Q=(de*I)**2;d=Q-1;v=c*T;b=c+R*D;ee=Q*(D*v*v+b*b)-1;Ba=2*Q*v*b
 uu=k**4*i;M0=uu*(uu+T);M=2*M0 if kind=='half_aux' else M0;L=H*M+1
 shift=0 if kind=='base' else b
 if kind in ['ac_aux','ac2_aux','half_aux']:
  delta=aa*c-ell
  if kind!='ac_aux':delta+=2*c
  shift+=M0*(2*delta-k) if kind=='half_aux' else M*delta
 if kind.endswith('aux'):shift+=v*(aa+2)*I
 W=b0+H*(t+shift)
 rad=[A%p,G%p,D%p]
 def const(x):return [x%p]+[0]*7
 def plus(x,y):return [(a+b)%p for a,b in zip(x,y)]
 def scale(x,s):return [a*s%p for a in x]
 def mult(x,y):
  out=[0]*8
  for a in range(8):
   for bb in range(8):
    coeff=x[a]*y[bb]
    for bit in range(3):
     if a&bb&(1<<bit):coeff*=rad[bit]
    out[a^bb]=(out[a^bb]+coeff)%p
  return out
 total=const(1)
 for st in [-1,1]:
  for sg in [-1,1]:
   for sf in [-1,1]:
    zz=const(W);zz[1]=-H*M*st%p;zz[2]=-L*sg%p
    factor=plus(scale(mult(zz,zz),d),const(-H*H*ee));factor[4]=sf*H*H*Ba%p
    total=mult(total,factor)
 assert total[1:]==[0]*7
 return total[0]
checks=0
for file in sorted(ROOT.glob('*_product.json')):
 obj=json.loads(file.read_text())
 for trial in range(40):
  vals={n:rng.randrange(-7,8) for n in obj['witnesses']+obj['fixed_numerals']}
  v=evaluate(obj,vals);expected=radical_norm(vals,obj['variant'])
  assert v['N']==expected,(file,trial,v['N'],expected)
  assert v[obj['output']]==(v['Nk']*v['Nt']*(1+expected)-1)%p
  checks+=1
bounds=0
for q in [16,17,31,256]:
 for w in [1,2,1000]:
  for s in [1,2,200]:
   for h in [1,2,100]:
    X=w*q;Y=s*q**3;E=X*Y
    for eps in [-1,1]:
     R=q**4-3;k=R+eps+h*E;eta=k-1;c=k*Y+eta;aa=E+Y;delta=(aa+2)**2-1
     for i,T in [(1,1),(2,100),(100,2),(1,10**12),(10**12,1)]:
      I=i*c*c;D=1+delta*I*I;v=c*T;b=c+R*D;u=k**4*i;M=u*(u+T);ceil=math.isqrt(D)+1
      assert 2*(v*ceil+b)<M*k*Y*Y
      assert (aa+2)*I<2*math.isqrt(D)
      bounds+=1
result={'modular_radical_products':checks,'integer_upper_bound_cases':bounds,'all_pass':True,'scope':'Finite diagnostics supplement the uniform proof; arbitrary ports only used for polynomial identities, not compiler equivalence.'}
(ROOT/'CHECKS.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
