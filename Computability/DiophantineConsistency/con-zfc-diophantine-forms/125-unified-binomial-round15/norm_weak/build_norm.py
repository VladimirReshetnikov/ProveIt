#!/usr/bin/env python3
"""Owned round-15 literal circuit generator. No imported upstream code."""
import json, hashlib
from pathlib import Path
from collections import Counter
ROOT=Path(__file__).resolve().parent
VARS=['j','C','z','h','r','v','w','T','c','n','s']
PORTS=['beta','K0','MC','MF','cone_A','cone_B']
class Dag:
 def __init__(self): self.nodes=[];self.index={}
 def node(self,k):
  k=tuple(k)
  if k not in self.index:self.index[k]=len(self.nodes);self.nodes.append(list(k))
  return E(self,self.index[k])
 def c(self,x):return x if isinstance(x,E) else self.node(('integer',x))
 def op(self,op,a,b):
  a,b=self.c(a),self.c(b);ra,rb=self.nodes[a.i],self.nodes[b.i]
  if ra[0]==rb[0]=='integer':return self.c(ra[1]+rb[1] if op=='add' else ra[1]-rb[1] if op=='sub' else ra[1]*rb[1])
  if op=='mul':
   if ra==['integer',0] or rb==['integer',0]:return self.c(0)
   if ra==['integer',1]:return b
   if rb==['integer',1]:return a
  if op=='add':
   if ra==['integer',0]:return b
   if rb==['integer',0]:return a
  if op=='sub':
   if rb==['integer',0]:return a
   if a.i==b.i:return self.c(0)
  if op in ['add','mul'] and a.i>b.i:a,b=b,a
  return self.node((op,a.i,b.i))
class E:
 def __init__(self,d,i):self.d=d;self.i=i
 def __add__(self,x):return self.d.op('add',self,x)
 def __radd__(self,x):return self.d.op('add',x,self)
 def __sub__(self,x):return self.d.op('sub',self,x)
 def __rsub__(self,x):return self.d.op('sub',x,self)
 def __mul__(self,x):return self.d.op('mul',self,x)
 def __rmul__(self,x):return self.d.op('mul',x,self)
 def __pow__(self,n):
  if n==0:return self.d.c(1)
  if n==1:return self
  h=self**(n//2)
  return h*h if n%2==0 else h*h*self

def export(name,d,out,regs,desc):
 live=set()
 def rec(i):
  if i in live:return
  live.add(i);r=d.nodes[i]
  if r[0] in ['add','sub','mul']:rec(r[1]);rec(r[2])
 rec(out.i);m={old:new for new,old in enumerate(sorted(live))};nodes=[]
 for i in sorted(live):
  r=d.nodes[i];nodes.append([r[0],m[r[1]],m[r[2]]] if r[0] in ['add','sub','mul'] else r)
 counts=Counter(r[0] for r in nodes if r[0] in ['add','sub','mul'])
 deg=[]
 for r in nodes:deg.append((deg[r[1]]+deg[r[2]] if r[0]=='mul' else max(deg[r[1]],deg[r[2]])) if r[0] in ['add','sub','mul'] else int(r[0]=='variable'))
 return dict(schema='integer-polynomial-dag-v1',name=name,domain='unrestricted integers',variables=VARS,variable_count=11,nodes=nodes,output=m[out.i],named_registers={k:m[e.i] for k,e in regs.items() if e.i in live},operation_counts=dict(counts),operations=sum(counts.values()),syntactic_degree_bound=deg[m[out.i]],coefficient_binding='coefficients/BINDING.json',description=desc)

def build(center=True,rational=False,norm_schedule='symmetric'):
 d=Dag();x={v:d.node(('variable',v)) for v in VARS};p={v:d.node(('coefficient',v)) for v in PORTS}
 j,C,z,h,r,v,w,T,c,n,s=[x[v] for v in VARS]
 J=6*j+1;qm=p['beta']*J;q=qm+1;q2=q*q;q3=q2*q
 W=12*w+4;X=q*W;Y=q*v;Eprod=X*Y;a=Eprod+Y;H=4*a+3;Delta=a*a+H
 F=(p['K0']+W)*C-z*qm
 R=(q*(q-F)-C)*(q2-1)+(p['MC']+q*p['MF'])*J
 k=R+1+h*Eprod;c2=c*c;eta=c-Y*k
 Derr=(p['cone_A']*F-q)**2+(p['cone_B']*C-q)**2
 Budget=k*k*(q2-Derr)-4*q2*eta*eta
 ell=Eprod*Y;L=ell*k;Dt=1+L*(L+k)
 if norm_schedule=='paired':
  D81=243*Budget-324;Dg81=81+D81*Dt*s*s;P81=Dt*Dg81
 else:
  D=3*Budget-4;Dg=1+D*Dt*s*s;P=Dt*Dg
 I=r*c2;strong=Delta*I*I;Df=strong+1;Q=Delta*strong;delta=Q-1
 b0=c-R+4*I*T;V=Df*b0-c;Cy=Q*V*V-1
 K=X*(3*c-2*X)+2;M=2*q2;Dcar=H*M;M2=M*M;M4=M2*M2;Dcar2=Dcar*Dcar;Dcar3=Dcar2*Dcar
 S=s*r*Dcar*M4;S2=S*S;zc=Dcar*T+M*K+H*(v-q2);zc2=zc*zc;Ac=(zc2+3*Dcar2)*(zc2*zc-19*Dcar3)
 shift=(V if rational else Q*V) if center else 0
 Z=S*(n+shift)-Ac;Z2=Z*Z
 A=9*S2*Df;B=S2*Cy if rational else S2*delta*Cy;G=S2*P81 if norm_schedule=='paired' else 81*S2*P
 if rational:
  AG=A+G;prod=A*G
  vnorm=delta*(Z2-AG)-B
  ynorm=vnorm*vnorm-4*delta*(delta*prod+B*AG)
  output=ynorm*ynorm-64*delta*delta*prod*B*(delta*Z2)
 else:
  if norm_schedule=='symmetric':
   AB=A+B;prod=A*B;vnorm=Z2-AB-G
   ynorm=vnorm*vnorm-4*(prod+G*AB)
   output=ynorm*ynorm-64*prod*G*Z2
  elif norm_schedule=='paired':
   vnorm=Z2+A-B-G;left=A*Z2;right=B*G
   ynorm=vnorm*vnorm-4*(left+right)
   output=ynorm*ynorm-64*left*right
  elif norm_schedule=='centered':
   W0=S*n-Ac;center0=S*Q*V
   omega=W0*W0+2*center0*W0+S2*(Q*(V*V+1)-1)
   vnorm=omega-A-G;AG=A+G
   ynorm=vnorm*vnorm-4*(A*G+B*AG)
   output=ynorm*ynorm-64*A*B*G*Z2
 regs={k:v for k,v in locals().items() if isinstance(v,E)}
 name='weak_'+('rational' if rational else 'integral')+('_centered' if center else '_direct')+('_expandedcut' if norm_schedule=='centered' else '_paired' if norm_schedule=='paired' else '')
 packet=export(name,d,output,regs,dict(center=center,rational=rational,norm_schedule=norm_schedule))
 packet['exact_degree']=416 if center else 456
 return packet
if __name__=='__main__':
 ps=[build(c,False,'paired') for c in [False,True]]
 for p in ps:(ROOT/(p['name']+'.json')).write_text(json.dumps(p,indent=2)+'\n')
 metrics=[{k:p[k] for k in ['name','variable_count','exact_degree','operations','operation_counts','syntactic_degree_bound']} for p in ps]
 (ROOT/'METRICS.json').write_text(json.dumps(metrics,indent=2)+'\n');print(json.dumps(metrics,indent=2))
