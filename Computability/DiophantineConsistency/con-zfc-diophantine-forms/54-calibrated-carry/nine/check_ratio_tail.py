#!/usr/bin/env python3
"""Independent arithmetic replay of the source-parametric tail implementation."""
import json,random
from pathlib import Path
from ratio_tail import append_ratio_tail,exact_degree
class Circuit:
 def __init__(self):self.nodes=[];self.intern={};self.pows={};self.names={}
 def node(self,k,*a):
  if k in ('add','mul'):a=tuple(sorted(a))
  key=(k,)+a
  if key not in self.intern:self.intern[key]=len(self.nodes);self.nodes.append((k,)+a)
  return self.intern[key]
 def c(self,n):return self.node('literal',n)
 def atom(self,n):return self.node('variable',n)
 def op(self,k,a,b):
  na,nb=self.nodes[a],self.nodes[b]
  x=na[1] if na[0]=='literal' else None;y=nb[1] if nb[0]=='literal' else None
  if x is not None and y is not None:return self.c(x+y if k=='add' else x-y if k=='sub' else x*y)
  if k=='add' and x==0:return b
  if k in ('add','sub') and y==0:return a
  if k=='mul':
   if x==0 or y==0:return self.c(0)
   if x==1:return b
   if y==1:return a
  return self.node(k,a,b)
 def add(self,*xs):
  out=self.c(0)
  for x in xs:out=self.op('add',out,x)
  return out
 def mul(self,*xs):
  out=self.c(1)
  for x in xs:out=self.op('mul',out,x)
  return out
 def sub(self,a,b):return self.op('sub',a,b)
 def pow(self,a,n):
  if n==0:return self.c(1)
  if n==1:return a
  if (a,n) not in self.pows:
   half=self.pow(a,n//2);out=self.mul(half,half)
   self.pows[a,n]=self.mul(out,a) if n%2 else out
  return self.pows[a,n]
 def save(self,name,a):self.names[name]=a;return a
 def run(self,inputs,p):
  vals=[]
  for node in self.nodes:
   k,*ab=node
   if k=='literal':v=ab[0]
   elif k=='variable':v=inputs[ab[0]]
   else:
    a,b=(vals[j] for j in ab);v=a+b if k=='add' else a-b if k=='sub' else a*b
   vals.append(v%p)
  return {n:vals[j] for n,j in self.names.items()}
 def ops(self,out):
  live=set();todo=[out]
  while todo:
   i=todo.pop()
   if i in live:continue
   live.add(i)
   if self.nodes[i][0] in ('add','sub','mul'):todo.extend(self.nodes[i][1:])
  return sum(self.nodes[i][0] in ('add','sub','mul') for i in live)
def direct(x,p,mode):
 def m(n):return n%p
 R,N,b,g,cap=(x[k] for k in ['R','N','b','g','cap']);h,s,w,phi,i,j,n=(x[k] for k in ['h','s','w','phi','i','j','n'])
 U=m(N*N*w);Y=m(N*N*s);M=m(R*Y);P=m(2*M*M*U);K=m(R+1+h*(P-1));A=m(M*(U+1));B1=m(2*R+1);W1=m(b*w);C=m(B1+W1+phi);J=m(4*A-5);Q=m(3*W1*C-2*(W1*W1-1));D=m((A*A-1)*C*C+1);k=m(i*J*C);E=m(k*D*C);F=m((A*A-1)*E*E+1);L=m(C*D+1-A);G=m(A+F*L);H=m(C+F*(B1+j*C));I=m((G*G-1)*H*H+1);a0=m((P*P-1)*K*K+1);a1=m(D*F*I);V0=m(P*K);margin=m((K*K-4*(C-K*Y)**2)*cap-8*g*K*K)
 if mode=='simple64':q=64;V1=m(k*(8*D*D-4*D-1)*G*H)
 else:
  q=2048**2;NN=m(2*G+L);NN1=m(2*k*k*D*(D-1)*L+3*C);NN2=m(2*k*k*(D-1)*L);NN3=m(2*k*k*(L-C));NN4=m(2*k*k*C)
  T6=m(k*((1024*D*D-512*D-128)*NN-64*NN1-40*NN2-28*NN3-21*NN4))
  correction=256*i*(k*k+2)+2048 if mode=='support2048' else i**3*(9*C*C*(64*A-239)-14*C*(64*A*A-304*A+603)+1024)+288*i+2048
  V1=m((T6+correction)*H)
 O=m(J*margin);theta=m(J*n+Q-O*(V0+V1));out=m((theta*theta-O*O*(a0+q*a1))**2-4*q*O**4*a0*a1)
 return {'A':A,'C':C,'D':D,'F':F,'G':G,'H':H,'I':I,'a0':a0,'a1':a1,'V0':V0,'V1':V1,'m':margin,'F9':out}
def main():
 rng=random.Random(841209);report=[]
 for mode in ['simple64','support2048','quotient2048']:
  ds=[]
  for cert in ([False] if mode=='support2048' else [False,True]):
   d=Circuit();x={n:d.atom(n) for n in ['R','N','b','g','cap','h','s','w','phi','i','j','n']};out=append_ratio_tail(d,R=x['R'],N=x['N'],b=x['b'],g=x['g'],cap=x['cap'],v=x,majorant=mode,certificate=cert);ds.append((d,out))
  tests=0
  for p in [1000000007,1000000009,2147483647]:
   for _ in range(150):
    vals={n:rng.randrange(p) for n in x};expected=direct(vals,p,mode)
    for d,out in ds:
     got=d.run(vals,p)
     assert all(got[k]==v for k,v in expected.items()),(mode,p,expected,got)
    tests+=1
  report.append({'majorant':mode,'primary_tail_operations':ds[0][0].ops(ds[0][1]),'modular_replays':tests,'certificate_checked':len(ds)>1})
 degree_checks=[]
 for mode in ['simple64','quotient2048']:
  for rr,nn,cc,rho,nu,kappa in [(3,1,3,16,4,32),(18386,4778,349,4,1,32),(18394,4776,341,7,3,5)]:
   d=Circuit();t=d.atom('t');R=d.mul(d.c(rho),d.pow(t,rr));N=d.mul(d.c(nu),d.pow(t,nn));cap=d.mul(d.c(kappa),d.pow(t,cc));vv={name:t for name in ['h','s','w','phi','i','j','n']};out=append_ratio_tail(d,R=R,N=N,b=t,g=t,cap=cap,v=vv,majorant=mode,certificate=True)
   heads=[]
   for node in d.nodes:
    kind,*ab=node
    if kind=='literal':head=(0,ab[0]) if ab[0] else (-1,0)
    elif kind=='variable':head=(1,1)
    else:
     (da,ca),(db,cb)=(heads[q] for q in ab)
     if kind=='mul':head=(da+db,ca*cb) if ca and cb else (-1,0)
     elif da>db:head=(da,ca)
     elif db>da:head=(db,-cb if kind=='sub' else cb)
     else:
      v=ca-cb if kind=='sub' else ca+cb
      assert v or da<=0,('unresolved degree cancellation',mode,rr,nn,node)
      head=(da,v) if v else (-1,0)
    heads.append(head)
   wantdegree=exact_degree(mode,rr,nn,cc)
   wanthead=(81*2**148*kappa**4*rho**154*nu**328 if mode=='quotient2048' else 2**158*kappa**4*rho**188*nu**400)
   assert heads[out]==(wantdegree,wanthead),(mode,heads[out],wantdegree,wanthead)
   degree_checks.append({'majorant':mode,'degree_R':rr,'degree_N':nn,'degree_cap':cc,'final_degree':wantdegree,'exact_leading_coefficient_checked':True})
 result={'status':'PASS','tail_variants':report,'independent_degree_checks':degree_checks,'note':'Sources treated as independent input registers. Tests are transcription checks, not a consistency proof.'}
 Path(__file__).with_name('RATIO_TAIL_CHECKS.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
