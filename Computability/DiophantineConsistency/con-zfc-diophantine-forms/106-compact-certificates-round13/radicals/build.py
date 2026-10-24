#!/usr/bin/env python3
"""Newly authored literal integer DAG builder. Never imports upstream code."""
import json, hashlib, shutil
from pathlib import Path
from collections import Counter
ROOT=Path(__file__).resolve().parent
BASE=['j','C','z','h','r','v','w','T','c','n','t','p2','p3']
PORTS=['beta','K0','MC','MF','cone_A','cone_B']
class E:
 def __init__(self,d,r): self.d,self.r=d,r
 def __add__(self,b): return self.d.op('add',self,b)
 def __radd__(self,a): return self.d.op('add',a,self)
 def __sub__(self,b): return self.d.op('sub',self,b)
 def __rsub__(self,a): return self.d.op('sub',a,self)
 def __mul__(self,b): return self.d.op('mul',self,b)
 def __rmul__(self,a): return self.d.op('mul',a,self)
 def __neg__(self): return self.d.op('mul',-1,self)
 def __pow__(self,n):
  out=1;a=self
  while n:
   if n&1:out=out*a
   n//=2
   if n:a=a*a
  return out
class DAG:
 def __init__(self,vs):self.vs=vs;self.nodes=[];self.memo={};self.named={}
 def leaf(self,n):return E(self,n)
 def raw(self,a):return a.r if isinstance(a,E) else a
 def op(self,op,a,b):
  a,b=self.raw(a),self.raw(b)
  if isinstance(a,int) and isinstance(b,int):return {'add':lambda:a+b,'sub':lambda:a-b,'mul':lambda:a*b}[op]()
  if op=='add' and (a==0 or b==0):return self.leaf(b if a==0 else a)
  if op=='sub' and b==0:return self.leaf(a)
  if op=='sub' and a==b:return 0
  if op=='mul':
   if a==0 or b==0:return 0
   if a==1 or b==1:return self.leaf(b if a==1 else a)
  if op in ('add','mul') and str(a)>str(b):a,b=b,a
  key=(op,a,b)
  if key not in self.memo:
   ident=f'n{len(self.nodes)}';self.memo[key]=ident;self.nodes.append({'id':ident,'op':op,'args':[a,b]})
  return self.leaf(self.memo[key])
 def tag(self,n,a):self.named[n]=self.raw(a);return a
 def finish(self,out,name,degree):
  out=self.raw(out);byid={x['id']:x for x in self.nodes};seen=set();todo=[out]
  while todo:
   r=todo.pop()
   if isinstance(r,int) or r in seen:continue
   seen.add(r)
   if r in byid:todo+=byid[r]['args']
  if not set(self.vs+PORTS)<=seen:raise ValueError(('dead leaves',set(self.vs+PORTS)-seen))
  ns=[x for x in self.nodes if x['id'] in seen]
  return dict(name=name,representation='division-free arithmetic DAG',domain='unrestricted integers',variables=self.vs,variable_count=len(self.vs),fixed_ports=PORTS,coefficient_binding='coefficients/BINDING.json',inputs=self.vs+PORTS,nodes=ns,output=out,named_registers={k:v for k,v in self.named.items() if isinstance(v,int) or v in seen},live_binary_operations=len(ns),operation_counts=dict(Counter(x['op'] for x in ns)),exact_degree=degree)
def norm3(x,a,b,C,d):
 x2=x*x;ab=a*b;s=a+b;dd=d*d;T=dd*ab;R=d*C;j=d*(x2-s)-C;k=j*j-4*(T+R*s)
 return k*k-64*T*R*x2
def norm4(x,a,b,c,C,d):
 x2=x*x;dd=d*d;ab=a*b;s=a+b
 q0=d*(x2+c-s)-C;q1=-2*d*x
 A0=q0*q0+c*q1*q1-4*(dd*ab+d*C*s);A1=2*q0*q1;z=64*dd*d*ab*C
 f0=A0*A0+c*A1*A1-z*(x2+c);f1=2*A0*A1+2*z*x
 return f0*f0-c*f1*f1
def norm5(x,a,b,c,g,C,d):
 def sq(v):
  A,B,E,G=v
  return (A*A+c*B*B+g*(E*E+c*G*G),2*(A*B+g*E*G),2*(A*E+c*B*G),2*(A*G+B*E))
 x2=x*x;t2=(x2+c+g,-2*x,-2*x,2);s=a+b;dd=d*d;ab=a*b
 q=(d*(t2[0]-s)-C,d*t2[1],d*t2[2],d*t2[3]);v=sq(q)
 T=(v[0]-4*(dd*ab+d*C*s),v[1],v[2],v[3]);v=sq(T);zz=64*dd*d*ab*C
 f=[v[i]-zz*t2[i] for i in range(4)]
 g0=f[0]*f[0]+g*f[2]*f[2]-c*(f[1]*f[1]+g*f[3]*f[3]);g1=2*(f[0]*f[2]-c*f[1]*f[3])
 return g0*g0-g*g1*g1

def build(mode):
 extra={'13':[],'14':['f'],'15':['f','gamma'],'15c':['f','p1'],'16':['f','gamma','p1']}[mode]
 d=DAG(BASE+extra);v={x:d.leaf(x) for x in d.vs+PORTS};tag=d.tag
 j,C,z,h,r,vv,w,T,c,n,t,p2,p3=[v[x] for x in BASE];beta,K0,MC,MF,cone_A,cone_B=[v[x] for x in PORTS]
 J=tag('J',6*j+1);q=tag('q',beta*J+1);q2=tag('q2',q*q);W=tag('W',12*w+4);X=tag('X',q*W);Y=tag('Y',q*vv);E0=tag('E',X*Y);a=tag('a',E0+Y);H=tag('H',4*a+3);Delta=tag('Delta',a*a+H)
 F=tag('F',(K0+W)*C-z*(q-1));R=tag('R',(q*(q-F)-C)*(q2-1)+(MC+q*MF)*J);k=tag('k',R+1+h*E0);eta=tag('eta',c-Y*k);Zeta=tag('Zeta',eta*(k-eta));u=tag('u',E0*Y*k);At=tag('At',u*(u+k)+1);c2=tag('c2',c*c);Am=tag('Am',1+Delta*c2);b0=tag('b0',X+a*c)
 cf=cone_A*F;cc=cone_B*C;dg=tag('dguard',cf*cc-(q-cf-cc)**2);Ag=tag('Ag',dg*Zeta-(t*t-dg-Zeta+1)**2-1-p2*p2-p3*(p3+1));I=tag('I',(2*r+1)*c2)
 if mode=='13':
  core=tag('strong_core',Delta*(I*I));Af=tag('Af',1+core);Q=tag('Q',Delta*core);V=tag('V',Af*(c*T-R)-c)
 else:
  f=v['f'];Q=tag('Q',I*I);S=tag('S',Q-Delta*(f*f-1));V=tag('V',f*c*T-f*f*R-c)
 delta=tag('delta',Q-1);Cy=tag('Cy',Q*V*V-1);M=tag('M',2*q2);defect=tag('defect',vv-q2)
 if mode in ['13','14','15c']:U=tag('U',M*H);U2=U*U
 M2=M*M
 if 'gamma' in extra:D=tag('D',(b0+H*v['gamma'])**2-Am)
 if 'p1' in extra:G=tag('G',Ag-v['p1']**2)
 if mode in ('13','14'):
  Z=tag('norm_z',U*(n+V)+M*b0+H*defect)
  if mode=='13':
   A=tag('rad_a',81*U2*Af);B=tag('rad_b',9*U2*At);C0=tag('rad_c',M2*Am);G0=tag('rad_g',729*U2*Ag);CN=tag('rad_num',U2*Cy);N=norm5(Z,A,B,C0,G0,CN,delta)
  else:
   A=tag('rad_a',9*U2*At);B=tag('rad_b',81*U2*Ag);C0=tag('rad_c',M2*Am);CN=tag('rad_num',U2*Cy);N=norm4(Z,A,B,C0,CN,delta)
 elif mode=='15':
  Z=tag('norm_z',M*(n+V)+defect);A=tag('rad_a',9*M2*At);B=tag('rad_b',81*M2*Ag);CN=tag('rad_num',M2*Cy);N=norm3(Z,A,B,CN,delta)
 elif mode=='15c':
  t0=tag('t0',2*u+k);Z=tag('norm_z',U*(n+3*t0+2*V)+2*M*b0+H*defect);A=tag('rad_a',36*U2*At);B=tag('rad_b',4*M2*Am);CN=tag('rad_num',4*U2*Cy);N=norm3(Z,A,B,CN,delta)
 else:
  t0=tag('t0',2*u+k);ell=tag('ell',k*k-4);xx=tag('xnum',M*n+defect);M4=M2*M2;V2=V*V
  jj=tag('jcenter',delta*(xx*xx+M*(6*t0+4*V)*xx+9*M2*ell)-4*M2*(V2-1));hh=tag('hcenter',12*delta*t0*V*M2)
  N=jj*(jj+2*hh)+144*delta*M4*(4*At*(1-V2)+delta*ell*V2)
 N=tag('norm',N)
 if mode=='13':out=N
 else:
  out=(1+N)*(1+S)
  if 'gamma' in extra:out=out*(1+D)
  if 'p1' in extra:out=out*(1+4*G)
  out=out-1
 deg={'13':1072,'14':378,'15':172,'15c':170,'16':98}[mode]
 return d.finish(out,'integer'+mode+'_degree'+str(deg),deg)

def main():
 metrics=[]
 for mode in ['13','14','15','15c','16']:
  p=build(mode);(ROOT/(p['name']+'.json')).write_text(json.dumps(p,indent=2)+'\n');metrics.append({k:p[k] for k in ['name','variable_count','exact_degree','live_binary_operations','operation_counts']})
 (ROOT/'METRICS.json').write_text(json.dumps(metrics,indent=2)+'\n');print(json.dumps(metrics,indent=2))
if __name__=='__main__':main()
