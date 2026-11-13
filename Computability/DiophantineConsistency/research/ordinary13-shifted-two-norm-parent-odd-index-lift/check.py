#!/usr/bin/env python3
"""Bounded exact checks for the m=1 mod 4 explicit positive-auxiliary lift."""
import hashlib,json,math,subprocess,sys,resource
from pathlib import Path
resource.setrlimit(resource.RLIMIT_AS,(256*1024**2,256*1024**2))
resource.setrlimit(resource.RLIMIT_CPU,(15,15))
resource.setrlimit(resource.RLIMIT_CORE,(0,0))
root=Path(__file__).resolve().parents[2];here=Path(__file__).resolve().parent
for p,h in json.loads((here/'pins.json').read_text()).items():assert hashlib.sha256((root/p).read_bytes()).hexdigest()==h,p
prev=root/'research/ordinary13-shifted-two-norm-parent-explicit-index-lift'
r=subprocess.run([sys.executable,'-I','-S','-B',str(prev/'check.py')],cwd=root,check=True,text=True,capture_output=True)
assert r.stdout==(prev/'receipt.json').read_text()
def pell(A,n,mod=None):
 D=A*A-1
 def mul(x,y):
  out=(x[0]*y[0]+D*x[1]*y[1],x[0]*y[1]+x[1]*y[0])
  return tuple(z%mod for z in out) if mod else out
 r=(1,0);a=(A,1)
 while n:
  if n&1:r=mul(r,a)
  a=mul(a,a);n//=2
 return r
# Exact toy with nontrivial alternate sign/index: c=1 permits any rank.
A=2;m=1;g,c=pell(A,m);h=2*m*c;f,v=pell(A,h);D=A*A-1
assert (c,h,f,v)==(1,2,7,4) and f%2==1
I=D*v;L=2*h*f-m;R=2
assert L==27 and L%4==3 and (R+m)%c==0
assert pell(A,2*h*f,f*f)==(f*f-1,0)
x,y=pell(I,L);assert x%I==0;V=x//I
num=V+c+f*f*R;assert num%(f*f*c)==0
T=num//(f*f*c);assert T>0 and V==f*f*(T*c-R)-c
assert I*I==D*(f*f-1) and y*y-I*I*(y*y-V*V)==1
# Nontrivial c=209 test: verify the entire auxiliary quotient condition
# modulo f²c without materializing the enormous L-th Pell coordinates.
A2=2;m2=5;_,c2=pell(A2,m2);h2=2*m2*c2;f2,v2=pell(A2,h2);D2=A2*A2-1
assert c2==209 and v2%(c2*c2)==0 and f2%2==1
I2=D2*v2;L2=2*h2*f2-m2;R2=c2-m2;mod=f2*f2*c2
assert R2>0 and (R2+m2)%c2==0 and L2%4==3
assert pell(A2,2*h2*f2,f2*f2)==(f2*f2-1,0)
# Quotient x_(2j+1)(I)/I via its order-two recurrence modulo f²c.
t=I2*I2%mod; j=(L2-1)//2;coeff=(4*t-2)%mod
v0=1;v1=(4*t-3)%mod
# Matrix [[coeff,-1],[1,0]]^(j-1) applied to [v1,v0].
def mm(a,b):return ((a[0]*b[0]+a[1]*b[2])%mod,(a[0]*b[1]+a[1]*b[3])%mod,(a[2]*b[0]+a[3]*b[2])%mod,(a[2]*b[1]+a[3]*b[3])%mod)
z=(1,0,0,1);a=(coeff,mod-1,1,0);e=j-1
while e:
 if e&1:z=mm(z,a)
 a=mm(a,a);e//=2
Vmod=(z[0]*v1+z[1]*v0)%mod
assert (Vmod+c2+f2*f2*R2)%mod==0
print(json.dumps({'m_one_mod_four_branch':True,'exact_toy_m':m,'exact_toy_R':R,
 'exact_toy_L':L,'exact_toy_positive_T':T>0,'nontrivial_modular_toy_c':c2,
 'nontrivial_modular_toy_m':m2,'nontrivial_modular_toy_R':R2,
 'nontrivial_auxiliary_ordinate_expanded':False,
 'sufficient_rank_condition':'c divides R+m',
 'unconditional_reverse_bridge_proved':False,'actual_graph_zero_constructed':False,
 'lean_executed':False},indent=2,sort_keys=True))
