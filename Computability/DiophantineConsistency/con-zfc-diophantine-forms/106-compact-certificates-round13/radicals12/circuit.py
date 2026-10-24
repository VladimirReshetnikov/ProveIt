"""Local arithmetic DAG utilities, authored for this round; no upstream imports."""
from collections import Counter
PORTS=["beta","K0","MC","MF","cone_A","cone_B"]
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

