#!/usr/bin/env python3
"""Static graph binding, bounded period tests and exact nontrivial CRT control."""
import hashlib,json,math
from pathlib import Path
root=Path(__file__).resolve().parents[2];here=Path(__file__).resolve().parent
for p,h in json.loads((here/'pins.json').read_text()).items():assert hashlib.sha256((root/p).read_bytes()).hexdigest()==h,p
parent=json.loads((root/'research/ordinary13-eta-zero-graph-adapter-audit/prototype.json').read_text())
two=json.loads((root/'research/ordinary9-shifted-free-aux-two-norm64/candidate.json').read_text())
def trees(g):
 env={x:('in',x) for x in g['witnesses']+g['fixed_numerals']}
 for n,op,a,b in g['source']:
  a=env[a] if isinstance(a,str) else ('num',a);b=env[b] if isinstance(b,str) else ('num',b)
  env[n]=(op,a,b)
 return env
p,t=trees(parent),trees(two)
for key in ('A0','A1','R','a','c','H','Delta','Dstar'):assert p[key]==t[key],key
rows={x[0]:x[1:] for x in parent['source']}
for k,v in {'kbase':['+','n_eta','n_zeta'],'k':['+','kbase',1],'i':['+','n_i',1],
 'T':['+','n_T',1],'I':['*','c2','i'],'Q':['*','Delta','rho'],
 'g72':['-','g71','Q'],'V':['-','g76','c'],'y2':['*','n_y','n_y'],
 'Fa':['-','y2','g82'],'F0':['+',1,'A0'],'F1':['+',1,'A1'],
 'Fs':['+',1,'g72'],'P01':['*','F0','F1'],'P012':['*','P01','Fa'],
 'P0123':['*','P012','Fs'],'out':['-','P0123',1]}.items():assert rows[k]==v,(k,rows[k])
# Binary powering of a Pell unit modulo a chosen modulus.
def modpow(A,n,mod):
 D=(A*A-1)%mod
 def mul(x,y):return ((x[0]*y[0]+D*x[1]*y[1])%mod,(x[0]*y[1]+x[1]*y[0])%mod)
 z=(1,0);w=(A%mod,1)
 while n:
  if n&1:z=mul(z,w)
  w=mul(w,w);n//=2
 return z
period_checks=0
for A in range(2,9):
 x,y=1,0;D=A*A-1
 for h in range(1,8):
  x,y=A*x+D*y,x+A*y
  # The paired coordinates (1,0) give the full matrix identity.
  assert modpow(A,4*h*x,x*x)==(1,0)
  period_checks+=1
# Independently compare bounded integer-polynomial Chebyshev recurrences.
def addpoly(a,b,sgn=1):
 out=[(a[j] if j<len(a) else 0)+sgn*(b[j] if j<len(b) else 0) for j in range(max(len(a),len(b)))]
 while len(out)>1 and out[-1]==0:out.pop()
 return out
def mulpoly(a,b):
 out=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):out[i+j]+=x*y
 return out
p0,p1=[1],[1,0,-4];q0,q1=[1],[-1,0,4];z0,z1=1,-3
for j in range(12):
 assert p0==[(-1)**j*x for x in q0] and z0==(-1)**j*(2*j+1)
 p0,p1=p1,addpoly(mulpoly([2,0,-4],p1),p0,-1)
 q0,q1=q1,addpoly(mulpoly([-2,0,4],q1),q0,-1)
 z0,z1=z1,-2*z1-z0
# Exact toy with m=3 but R=18: no m=R assumption.
A=2;D=3;m=3;c=15;h=90
f,v=1,0
for _ in range(h):f,v=A*f+D*v,f+A*v
assert v>0 and v%(c*c)==0 and f*f-D*v*v==1
I=D*v;i=I//(c*c);assert i>0 and I==c*c*i
R=18;P=4*h*f;assert math.gcd(P,c)==math.gcd(4*h,c) and (R-m)%math.gcd(P,c)==0
L=3;V=4*I*I-3;y=4*I*I-1
assert L%4==3 and (L-m)%P==0 and (L-R)%c==0
num=V+c+f*f*R;assert num%(f*f*c)==0
T=num//(f*f*c)
assert T==2 and V==f*f*(T*c-R)-c
assert I*I==D*(f*f-1) and y*y-I*I*(y*y-V*V)==1
print(json.dumps({'parent_and_two_norm_expression_trees_equal':8,
 'bounded_explicit_matrix_period_controls':period_checks,
 'odd_chebyshev_polynomial_controls':12,
 'toy_A':A,'toy_main_index':m,'toy_rank':R,'toy_auxiliary_index':L,
 'toy_h':h,'toy_T':T,'toy_m_equals_R':False,
 'sufficient_obligation':'m=3 mod 4 and gcd(4h,c) divides R-m',
 'unconditional_reverse_bridge_proved':False,'actual_graph_zero_constructed':False,
 'lean_executed':False},indent=2,sort_keys=True))
