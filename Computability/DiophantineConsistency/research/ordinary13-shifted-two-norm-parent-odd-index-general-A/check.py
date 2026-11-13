#!/usr/bin/env python3
"""Check parity-free Pell doubling and exact odd-A arithmetic controls."""
import hashlib,json,subprocess,sys
from pathlib import Path
root=Path(__file__).resolve().parents[2];here=Path(__file__).resolve().parent
for name,digest in json.loads((here/'pins.json').read_text()).items():assert hashlib.sha256((root/name).read_bytes()).hexdigest()==digest,name
prev=root/'research/ordinary13-shifted-two-norm-parent-odd-index-lift'
r=subprocess.run(['timeout','20s',sys.executable,'-I','-S','-B',str(prev/'check.py')],cwd=root,check=True,text=True,capture_output=True)
assert r.stdout==(prev/'receipt.json').read_text()
def pell(A,n):
 D=A*A-1
 def mul(u,v):return (u[0]*v[0]+D*u[1]*v[1],u[0]*v[1]+u[1]*v[0])
 x=(1,0);z=(A,1)
 while n:
  if n&1:x=mul(x,z)
  z=mul(z,z);n//=2
 return x
def ppowmod(A,n,mod):
 D=(A*A-1)%mod
 def mul(u,v):return ((u[0]*v[0]+D*u[1]*v[1])%mod,(u[0]*v[1]+u[1]*v[0])%mod)
 x=(1,0);z=(A%mod,1)
 while n:
  if n&1:x=mul(x,z)
  z=mul(z,z);n//=2
 return x
controls=0
for A in range(2,16):
 for j in range(1,15):
  x,y=pell(A,j);u,v=pell(A,2*j)
  assert u==2*x*x-1 and u%2==1
  controls+=1
# Actual odd-multiplier m=1 branch, positive T and R != m.
A=3;m=1;_,c=pell(A,m);h=2*m*c;f,v=pell(A,h);D=A*A-1;I=D*v
assert c==1 and h==2 and f==17 and v%(c*c)==0 and f%2==1
L=2*h*f-m;R=2
assert L==67 and L%4==3 and (R+m)%c==0
assert ppowmod(A,2*h*f,f*f)==(f*f-1,0)
x,y=pell(I,L);assert x%I==0;V=x//I
assert (V+c+f*f*R)%(f*f*c)==0
T=(V+c+f*f*R)//(f*f*c)
assert T>=1 and V==f*f*(T*c-R)-c
assert y*y-I*I*(y*y-V*V)==1
# Odd A with c>1, 3 mod 4 case, checks the other half of the union.
A2=3;m2=3;_,c2=pell(A2,m2);h2=2*m2*c2;f2,v2=pell(A2,h2)
assert c2==35 and v2%(c2*c2)==0 and f2%2==1
I2=(A2*A2-1)*v2;R2=m2+c2
x2,y2=pell(I2,m2);V2=x2//I2
assert x2%I2==0 and (V2+c2+f2*f2*R2)%(f2*f2*c2)==0
T2=(V2+c2+f2*f2*R2)//(f2*f2*c2)
assert T2>=1 and V2==f2*f2*(T2*c2-R2)-c2
assert y2*y2-I2*I2*(y2*y2-V2*V2)==1
print(json.dumps({'predecessor_receipt_reproduced':True,'pell_doubling_controls':controls,
 'odd_A_m1_toy':[A,m,c,L,R],'odd_A_m3_toy':[A2,m2,c2,R2],
 'odd_multiplier_even_index_f_odd':True,'combined_odd_index_sufficient_condition':True,
 'actual_graph_zero_constructed':False,'unconditional_reverse_bridge_proved':False,
 'Lean_executed':False},indent=2,sort_keys=True))
