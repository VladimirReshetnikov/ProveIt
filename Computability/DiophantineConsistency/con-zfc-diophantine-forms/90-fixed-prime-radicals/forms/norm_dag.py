#!/usr/bin/env python3
"""Division-free fixed multiquadratic norm DAGs; Python standard library only."""
from math import comb
from pathlib import Path
import json

class DAG:
 def __init__(self,inputs):self.inputs=list(inputs);self.nodes=[];self.memo={}
 def operation(self,op,a,b):
  if isinstance(a,int) and isinstance(b,int):return {'add':lambda:a+b,'sub':lambda:a-b,'mul':lambda:a*b}[op]()
  if op=='add':
   if a==0:return b
   if b==0:return a
  if op=='sub':
   if b==0:return a
   if a==b:return 0
  if op=='mul':
   if a==0 or b==0:return 0
   if a==1:return b
   if b==1:return a
  if op in ['add','mul'] and str(a)>str(b):a,b=b,a
  key=(op,a,b)
  if key in self.memo:return self.memo[key]
  ref='n'+str(len(self.nodes));self.nodes.append({'id':ref,'op':op,'args':[a,b]});self.memo[key]=ref;return ref
 def add(self,a,b):return self.operation('add',a,b)
 def sub(self,a,b):return self.operation('sub',a,b)
 def mul(self,a,b):return self.operation('mul',a,b)
 def pow(self,a,n):
  if n<0:raise ValueError('negative exponent')
  r=1
  while n:
   if n&1:r=self.mul(r,a)
   n//=2
   if n:a=self.mul(a,a)
  return r
 def sadd(self,items):
  out=0
  for item in items:out=self.add(out,item)
  return out
 def pmul(self,a,b):
  out=[0]*(len(a)+len(b)-1)
  for i,x in enumerate(a):
   for j,y in enumerate(b):out[i+j]=self.add(out[i+j],self.mul(x,y))
  return out
 def psub(self,a,b):return [self.sub(a[i] if i<len(a) else 0,b[i] if i<len(b) else 0) for i in range(max(len(a),len(b)))]
 def shift_even_odd(self,co,a):
  E=[0]*len(co);O=[0]*len(co)
  for k,ck in enumerate(co):
   for j in range(k+1):
    target=E if j%2==0 else O
    term=self.mul(self.mul(ck,comb(k,j)),self.pow(a,j//2))
    target[k-j]=self.add(target[k-j],term)
  while len(E)>1 and E[-1]==0:E.pop()
  while len(O)>1 and O[-1]==0:O.pop()
  return E,O
 def norm_coefficients(self,radicands):
  co=[0,1]
  for a in radicands:
   E,O=self.shift_even_odd(co,a)
   co=self.psub(self.pmul(E,E),[self.mul(a,x) for x in self.pmul(O,O)])
  return co
 def taylor(self,co,z):
  return [self.sadd(self.mul(self.mul(co[k],comb(k,j)),self.pow(z,k-j)) for k in range(j,len(co))) for j in range(len(co))]
 def clear_last(self,co,z,num,den):
  tc=self.taylor(co,z);m=(len(co)-1)//2
  E=self.sadd(self.mul(self.mul(tc[2*j],self.pow(num,j)),self.pow(den,m-j)) for j in range(m+1))
  O=self.sadd(self.mul(self.mul(tc[2*j+1],self.pow(num,j)),self.pow(den,m-1-j)) for j in range(m))
  return self.sub(self.mul(E,E),self.mul(self.mul(den,num),self.mul(O,O)))
 def finish(self,out,metadata):
  needed=set();byref={x['id']:x for x in self.nodes}
  def walk(ref):
   if isinstance(ref,int) or ref not in byref or ref in needed:return
   needed.add(ref)
   for arg in byref[ref]['args']:walk(arg)
  walk(out)
  nodes=[x for x in self.nodes if x['id'] in needed]
  return {'representation':'division-free arithmetic DAG','inputs':self.inputs,'nodes':nodes,'output':out,'live_binary_operations':len(nodes),**metadata}

def build(core_count):
 radicands=['A','B','D','G'][:core_count]
 d=DAG(['z']+radicands+['Cnum','delta']);co=d.norm_coefficients(radicands)
 out=d.clear_last(co,'z','Cnum','delta')
 return d.finish(out,{'root_count':core_count+1,'identity':f'delta**{2**core_count} * product over signs of (z + signed square roots of '+','.join(radicands)+',Cnum/delta)','integer_core_norm_degree':2**core_count,'integer_core_coefficients_low_to_high':co})

def evaluate(packet,inputs,modulus=None):
 values=dict(inputs)
 for node in packet['nodes']:
  a,b=[arg if isinstance(arg,int) else values[arg] for arg in node['args']]
  value=a+b if node['op']=='add' else a-b if node['op']=='sub' else a*b
  values[node['id']]=value if modulus is None else value%modulus
 out=packet['output'];return out if isinstance(out,int) else values[out]

if __name__=='__main__':
 directory=Path(__file__).resolve().parent
 for count in [3,4]:
  packet=build(count);path=directory/f'norm{count+1}_cleared_dag.json'
  path.write_text(json.dumps(packet,indent=2)+'\n')
  print(path.name,packet['live_binary_operations'],'live binary operations')
