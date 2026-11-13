#!/usr/bin/env python3
"""Bounded independent modular checks for h=2*m*c and L=m."""
import hashlib,json,math,subprocess,sys
from pathlib import Path
root=Path(__file__).resolve().parents[2];here=Path(__file__).resolve().parent
for name,digest in json.loads((here/'pins.json').read_text()).items():assert hashlib.sha256((root/name).read_bytes()).hexdigest()==digest,name
prev=root/'research/ordinary13-shifted-two-norm-parent-crt-sufficient-condition'
r=subprocess.run([sys.executable,'-I','-S','-B',str(prev/'check.py')],check=True,text=True,capture_output=True)
assert r.stdout==(prev/'receipt.json').read_text()
def ppow(A,n,mod):
 D=(A*A-1)%mod
 def mul(x,y):return ((x[0]*y[0]+D*x[1]*y[1])%mod,(x[0]*y[1]+x[1]*y[0])%mod)
 x=(1,0);u=(A%mod,1)
 while n:
  if n&1:x=mul(x,u)
  u=mul(u,u);n//=2
 return x
def pell(A,n):
 D=A*A-1;x,y=1,0
 for _ in range(n):x,y=A*x+D*y,x+A*y
 return x,y
controls=0
for A in range(2,8):
 for m in (1,3,5,7):
  g,c=pell(A,m);assert c>0
  h=2*m*c
  assert ppow(A,h,c*c)==(1%(c*c),0)
  assert math.gcd(4*h,c)==c
  controls+=1
# Exact toy satisfying m!=R, used as a sanity check, not an actual graph zero.
A=2;m=3;g,c=pell(A,m);assert c==15
h=2*m*c;f,v=pell(A,h);D=A*A-1
assert v%(c*c)==0 and f*f-D*v*v==1
I=D*v;R=18;L=m
assert (R-m)%c==0 and m%4==3
aux_x,y=pell(I,L);assert aux_x%I==0;V=aux_x//I
assert (V+c)%(f*f)==0 and (V+R)%c==0
num=V+c+f*f*R;assert num%(f*f*c)==0
T=num//(f*f*c);assert T==2 and V==f*f*(T*c-R)-c
assert y*y-I*I*(y*y-V*V)==1
print(json.dumps({'prior_general_conditional_receipt_reproduced':True,
 'bounded_explicit_period_controls':controls,'chosen_h':'2*m*c',
 'auxiliary_index':'m','toy_m':m,'toy_R':R,'toy_T':T,'toy_m_equals_R':False,
 'hypotheses':'m=3 mod 4 and c divides R-m',
 'unconditional_reverse_bridge_proved':False,'actual_graph_zero_constructed':False,
 'lean_executed':False},indent=2,sort_keys=True))
