#!/usr/bin/env python3
"""Authored branch-local quadratic certificate; no upstream code imported.
This is a local transition relation, not a completed consistency equation.
"""
import json
from pathlib import Path
from collections import defaultdict
OUT=Path(__file__).resolve().parent

def const(n): return {():n} if n else {}
def var(s): return {(s,):1}
def add(a,b):
 c=dict(a)
 for m,v in b.items(): c[m]=c.get(m,0)+v
 return {m:v for m,v in c.items() if v}
def neg(a): return {m:-v for m,v in a.items()}
def sub(a,b): return add(a,neg(b))
def scale(k,a): return {m:k*v for m,v in a.items() if k*v}
def mul(a,b):
 c=defaultdict(int)
 for m,v in a.items():
  for n,w in b.items(): c[tuple(sorted(m+n))]+=v*w
 return {m:v for m,v in c.items() if v}
def serial(p): return [{'monomial':list(m),'coefficient':v} for m,v in sorted(p.items())]
def psum(xs):
 p={}
 for x in xs: p=add(p,x)
 return p

class Branch:
 output_wires=False
 def __init__(self,name): self.name=name; self.rows=[]; self.wires=[];self.cache={}
 def wire(self,p):
  key=tuple(sorted(p.items()))
  if key not in self.cache:
   name='q'+str(len(self.wires)); q=var(name)
   self.cache[key]=q; self.wires.append({'name':name,'value':serial(p),'nonnegative':'constructor_product'})
   self.rows.append(sub(q,p))
  return self.cache[key]
 def I(self,a,b):
  s=add(a,b)
  if self.output_wires:return self.wire(add(scale(2,mul(s,add(s,const(1)))),scale(4,b)))
  q=self.wire(mul(s,add(s,const(1))))
  return add(scale(2,q),scale(4,b))
 def Rel(self,a,b):return add(self.I(a,b),const(1))
 def All(self,a,b):return add(self.I(a,b),const(2))
 def Eq(self,a,b):return add(self.I(a,b),const(3))
 def Neg(self,a):return self.I(a,const(1))
 def Ex(self,a,b):return self.Neg(self.All(a,self.Neg(b)))
 def Req(self,b,k,m):return self.All(b,self.I(m,self.Neg(self.All(b,self.I(m,self.Neg(self.Rel(b,k)))))))
 def Clos(self,a,b,k,m):return self.All(b,self.I(self.Rel(b,k),self.Neg(self.All(a,self.I(m,self.Neg(self.All(a,self.I(self.All(k,self.I(self.Rel(k,a),self.Rel(k,b))),self.Req(b,k,m)))))))))
 def Bundle(self,a,b,c):return self.Neg(self.I(self.I(self.Rel(a,b),self.All(c,self.Rel(a,b))),self.All(c,self.I(self.Clos(a,b,c,c),self.Neg(self.Req(b,c,c))))))
 def L(self,x,h,t):
  s=add(h,t)
  return sub(sub(scale(2,x),const(2)),add(mul(s,add(s,const(1))),scale(2,t)))
 def finish(self):
  quartic=psum(mul(r,r) for r in self.rows)
  return {'name':self.name,'wires':self.wires,'quadratic_residuals':[serial(p) for p in self.rows], 'sum_of_squares':serial(quartic), 'wire_count':len(self.wires),'residual_count':len(self.rows),'degree':max(map(len,quartic)),'monomials':len(quartic)}

def build(split_gate=False, horn=False):
 S,T,a,b,c,d=map(var,['S','T','a','b','c','d']); branches=[]
 p,q,v=map(var,['p','q','v'])
 names=['truth','rho1','rho2','rho3','rho4','rho5','rho6','growG','rho8','bundle','mp','gen']
 if split_gate: names[names.index('bundle'):names.index('bundle')+1]=['bundle_pos','bundle_neg']
 for name in names:
  x=Branch(name);I,Rel,All,Eq,Neg,Ex=x.I,x.Rel,x.All,x.Eq,x.Neg,x.Ex
  if name=='truth': h=const(0)
  elif name=='rho1': h=Ex(a,Eq(a,b))
  elif name=='rho2': h=I(All(a,I(b,c)),I(All(a,b),All(a,c)))
  elif name=='rho3': h=I(Eq(a,b),I(Rel(c,a),Rel(c,b)))
  elif name=='rho4': h=I(All(a,All(b,c)),All(b,All(a,c)))
  elif name=='rho5': h=I(Eq(c,a),I(Rel(c,b),Rel(a,b)))
  elif name=='rho6': h=I(Ex(a,All(a,b)),b)
  elif name=='growG': h=I(Eq(c,a),I(Eq(c,b),All(Rel(a,b),Eq(a,b))))
  elif name=='rho8': h=I(I(I(c,d),a),I(I(a,c),I(b,c)))
  elif name.startswith('bundle'):
   h=x.Bundle(a,b,c)
   # One additional natural wire for |(c-a)(c-b)|; squaring suffices for the gate.
   if split_gate:
    x.rows.append(sub(mul(sub(c,a),sub(c,b)),scale(1 if name=='bundle_pos' else -1,add(d,const(1)))))
   else:
    z=x.wire(mul(sub(c,a),sub(c,a))); z2=x.wire(mul(sub(c,b),sub(c,b)))
    x.rows.append(sub(mul(z,z2),mul(add(d,const(1)),add(d,const(1)))))
  elif name=='mp':
   if horn:
    z=add(p,v);x.rows.append(sub(q,add(scale(2,mul(z,add(z,const(1)))),scale(4,v))))
   else:x.rows.extend([x.L(S,I(a,b),d),x.L(d,a,c),x.L(T,b,c)])
  else:
   if horn:x.rows.extend([q,sub(v,All(a,p))])
   else:x.rows.extend([x.L(S,b,c),x.L(T,All(a,b),c)])
  if name not in ['mp','gen']:
   if horn:x.rows.extend([p,q,sub(v,h)])
   else:x.rows.append(x.L(T,h,S))
  branches.append(x.finish())
 return {'meaning':('branch-local padded Horn inference polynomial, not full Con(ZFC) equation' if horn else 'branch-local one-stack transition polynomial, not full Con(ZFC) equation'),'domain':'nonnegative integers','exposed':(['p','q','v'] if horn else ['S','T']),'base_witnesses':['a','b','c','d'],'common_wire_count':max(b['wire_count'] for b in branches),'witness_count':4+max(b['wire_count'] for b in branches),'polynomial':'product of all branch sum_of_squares polynomials; all q indices are SHARED','degree':sum(b['degree'] for b in branches),'branches':branches}

if __name__=='__main__':
 import sys
 split='--split-gate' in sys.argv
 obj=build(split);(OUT/('branch_scratch_split.json' if split else 'branch_scratch.json')).write_text(json.dumps(obj,indent=2)+'\n')
 print(json.dumps({k:v for k,v in obj.items() if k!='branches'},indent=2))
 print([(x['name'],x['wire_count'],x['residual_count'],x['degree']) for x in obj['branches']])

# Elimination of trailing bundle scratch wires is exact: substitute their defining
# polynomials in reverse order, then omit the defining equations.
def deserialize(xs):return {tuple(x['monomial']):x['coefficient'] for x in xs}
def substitute(p,name,value):
 out={}
 for m,c in p.items():
  q=const(c)
  for x in m:q=mul(q,value if x==name else var(x))
  out=add(out,q)
 return out

def free_gate_eliminate(k,horn=False):
 obj=build(False,horn)
 old=next(b for b in obj['branches'] if b['name']=='bundle')
 rows=[deserialize(r) for r in old['quadratic_residuals']]
 n=len(old['wires'])-2
 wires=old['wires'][:n]
 # Omit the two square-wire definitions and replace guard with literal quartic.
 a,b,c,d=map(var,['a','b','c','d'])
 p=mul(sub(c,a),sub(c,b))
 gate=sub(mul(p,p),mul(add(d,const(1)),add(d,const(1))))
 rows=rows[:n]+[gate]+rows[n+3:]
 for w in reversed(wires[-k:] if k else []):
  value=deserialize(w['value']);name=w['name'];index=int(name[1:])
  rows=[substitute(r,name,value) for i,r in enumerate(rows) if i!=index]
 if k:wires=wires[:-k]
 poly=psum(mul(r,r) for r in rows)
 old.update(wires=wires,wire_count=len(wires),residual_count=len(rows),quadratic_residuals=[serial(r) for r in rows],sum_of_squares=serial(poly),degree=max(map(len,poly)),monomials=len(poly))
 obj['common_wire_count']=max(b['wire_count'] for b in obj['branches']);obj['witness_count']=4+obj['common_wire_count'];obj['degree']=sum(b['degree'] for b in obj['branches'])
 obj['note']='Residuals field name is historical; bundle residuals may exceed quadratic. Eliminated trailing bundle wires='+str(k)
 return obj

if __name__=='__main__':
 for k in range(2):
  obj=free_gate_eliminate(k)
  (OUT/('branch_scratch_eliminate'+str(k)+'.json')).write_text(json.dumps(obj,indent=2)+'\n')
  print('Eliminate',k, 'witnesses',obj['witness_count'],'degree',obj['degree'],'bundle terms',next(b['monomials'] for b in obj['branches'] if b['name']=='bundle'))
