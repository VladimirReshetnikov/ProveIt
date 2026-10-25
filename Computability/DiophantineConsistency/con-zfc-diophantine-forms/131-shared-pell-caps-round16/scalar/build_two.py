#!/usr/bin/env python3
"""Eleven-integer product equations: complete polynomial DAGs.

All arithmetic is over Z. This producer records a finite polynomial;
semantic claims are in PROOF.md, not inferred from these measurements.
"""
import json
import argparse
from collections import Counter
from pathlib import Path

ROOT=Path(__file__).resolve().parent/'two_root'
VARS=['j','C','z','h','r','v','w','T','c','n','s']
PORTS=['beta','K0','MC','MF','cone_A','cone_B']

class DAG:
 def __init__(self): self.nodes=[];self.index={}
 def leaf(self,tag,value): return self.intern((tag,value))
 def intern(self,key):
  if key not in self.index: self.index[key]=len(self.nodes);self.nodes.append(list(key))
  return Expr(self,self.index[key])
 def val(self,x):
  if isinstance(x,Expr):
   if x.d is not self: raise ValueError('foreign DAG')
   return x
  if type(x) is not int: raise TypeError(x)
  return self.leaf('integer',x)
 def op(self,tag,a,b):
  a,b=self.val(a),self.val(b);aa,bb=self.nodes[a.i],self.nodes[b.i]
  if aa[0]==bb[0]=='integer':
   x,y=aa[1],bb[1];return self.val(x+y if tag=='add' else x-y if tag=='sub' else x*y)
  if tag=='mul':
   if aa==['integer',0] or bb==['integer',0]: return self.val(0)
   if aa==['integer',1]: return b
   if bb==['integer',1]: return a
  if tag=='add':
   if aa==['integer',0]: return b
   if bb==['integer',0]: return a
  if tag=='sub':
   if bb==['integer',0]: return a
   if a.i==b.i: return self.val(0)
  if tag in ['add','mul'] and a.i>b.i:a,b=b,a
  return self.intern((tag,a.i,b.i))
class Expr:
 def __init__(self,d,i):self.d,self.i=d,i
 def __add__(self,x):return self.d.op('add',self,x)
 def __radd__(self,x):return self.d.op('add',x,self)
 def __sub__(self,x):return self.d.op('sub',self,x)
 def __rsub__(self,x):return self.d.op('sub',x,self)
 def __mul__(self,x):return self.d.op('mul',self,x)
 def __rmul__(self,x):return self.d.op('mul',x,self)
 def __pow__(self,n):
  if n==0:return self.d.val(1)
  if n==1:return self
  h=self**(n//2);z=h*h;return z*self if n%2 else z

def export(name,d,output,regs,metadata):
 live=set();todo=[output.i]
 while todo:
  i=todo.pop()
  if i in live:continue
  live.add(i);r=d.nodes[i]
  if r[0] in ['add','sub','mul']:todo.extend(r[1:])
 remap={old:new for new,old in enumerate(sorted(live))};nodes=[]
 for old in sorted(live):
  row=d.nodes[old]
  nodes.append([row[0],remap[row[1]],remap[row[2]]] if row[0] in ['add','sub','mul'] else row)
 counts=Counter(r[0] for r in nodes if r[0] in ['add','sub','mul'])
 deg=[]
 for row in nodes:
  if row[0]=='mul':deg.append(deg[row[1]]+deg[row[2]])
  elif row[0] in ['add','sub']:deg.append(max(deg[row[1]],deg[row[2]]))
  else:deg.append(int(row[0]=='variable'))
 nm={k:remap[v.i] for k,v in regs.items() if v.i in remap}
 if {r[1] for r in nodes if r[0]=='variable'}!=set(VARS):raise ValueError('dead input')
 return dict(schema='integer-polynomial-dag-v1',name=name,domain='unrestricted integers',variables=VARS,variable_count=11,nodes=nodes,output=remap[output.i],named_registers=nm,operation_counts=dict(counts),operations=sum(counts.values()),syntactic_degree_bound=deg[remap[output.i]],register_degree_bounds={k:deg[v] for k,v in nm.items()},coefficient_binding='../coefficients/BINDING.json',**metadata)

def build(short_index=True):
 d=DAG();x={v:d.leaf('variable',v) for v in VARS};p={v:d.leaf('coefficient',v) for v in PORTS}
 J=6*x['j']+1;qm=p['beta']*J;q=qm+1;q2=q*q;q3=q2*q
 W=12*x['w']+4;X=q*W;Y=(2*x['v']+1)*q3;E=X*Y;a=E+Y;H=4*a+3;Delta=a*a+H
 F=(p['K0']+W)*x['C']-x['z']*qm
 R=(q*(q-F)-x['C'])*(q2-1)+(p['MC']+q*p['MF'])*J
 if short_index:q2four=4*q2;index_modulus=q2four*q2
 else:index_modulus=E
 k=R+1+x['h']*index_modulus;c=x['c'];c2=c*c
 eta=c-Y*k;coneF=p['cone_A']*F;coneC=p['cone_B']*x['C'];Derr=(coneF-q)**2+(coneC-q)**2
 Budget=k*k*(q2-Derr)-4*q2*eta*eta
 ell=E*Y;L=ell*k;Dt=1+L*(L+k);D=Budget-4;s2=x['s']
 guard_scale=Dt*s2;P=Dt+D*(guard_scale*guard_scale)
 U=x['r']*c2
 UP=U*P;strong=(Delta*U)*UP;Df=strong+1;Q=Delta*strong;delta=Q-1
 b=c-R+4*UP*x['T'];V=Df*b-c;Cy=Q*V*V-1;Da=delta*Cy
 K=X*(3*c-2*X)+2;H2=H*H;H3=H2*H
 S=x['s']*x['r']*H
 S2=S*S;zc=H*x['T']+K;zc2=zc*zc;Ac=(zc2+3*H2)*(zc2*zc-19*H3)
 Z=S*(x['n']+V)-Ac;Aux=S2*Cy;Guard=S2*P*Df;Inner=delta*(Z*Z-Guard)-Aux;output=Inner*Inner-4*delta*Aux*Guard
 name='product11_'+('short' if short_index else 'native')
 regs={k:v for k,v in locals().copy().items() if isinstance(v,Expr)}
 return export(name,d,output,regs,dict(short_index=short_index))

def produce():
 result=[]
 for short in [True]:
  p=build(short)
  exact=810 if short else 906
  p['exact_degree']=exact
  p['name']='two_root11_degree'+str(exact)
  result.append(p)
 return result

def main():
 parser=argparse.ArgumentParser();parser.add_argument('--check',action='store_true');args=parser.parse_args()
 packets=produce();metrics=[]
 files={}
 for p in packets:
  files[p['name']+'.json']=json.dumps(p,indent=2)+'\n'
  metrics.append({k:p[k] for k in ['name','variable_count','domain','operations','operation_counts','exact_degree','syntactic_degree_bound']})
 files['METRICS.json']=json.dumps(metrics,indent=2)+'\n'
 for name,body in files.items():
  if args.check:
   if (ROOT/name).read_text()!=body:raise ValueError('rebuild differs: '+name)
  else:(ROOT/name).write_text(body)
 print(json.dumps({'status':'PASS','mode':'check' if args.check else 'build','equations':metrics},indent=2))
if __name__=='__main__':main()
