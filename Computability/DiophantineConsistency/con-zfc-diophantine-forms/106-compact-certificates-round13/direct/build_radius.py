#!/usr/bin/env python3
"""Radius-majorant variant of our independent short-beta direct materializer.
Replaces only the duplicate upper-bound source DAG by fixed binary powering.
The imported module is self-authored round13 code, not upstream code.
"""
import argparse, hashlib, json, pathlib
import build_direct as base
ORIGINAL_SOURCE = base.Circuit.source

class ExponentProof:
 def __init__(self):self.nodes=[];self.cache={};self.inputs={}
 def add_node(self,item):
  key=tuple(item)
  if key not in self.cache:self.cache[key]=len(self.nodes);self.nodes.append(list(item))
  return ('e',self.cache[key])
 def input(self,name):
  v=self.add_node(['input',name,1]);self.inputs[name]=v;return v
 def atom(self,a):
  if a[0]=='e':return a
  assert a[0]=='c';e=0;power=1
  while power<a[1]:e+=1;power*=4
  return self.add_node(['constant',a[1],e])
 def exp(self,a):return self.nodes[self.atom(a)[1]][-1]
 def add(self,a,b):
  if a==base.Z:return b
  if b==base.Z:return a
  if a[0]==b[0]=='c':return base.C(a[1]+b[1])
  a,b=self.atom(a),self.atom(b);return self.add_node(['add',a[1],b[1],max(self.exp(a),self.exp(b))+1])
 def mul(self,a,b):
  if a==base.Z or b==base.Z:return base.Z
  if a==base.O:return b
  if b==base.O:return a
  if a[0]==b[0]=='c':return base.C(a[1]*b[1])
  a,b=self.atom(a),self.atom(b);return self.add_node(['mul',a[1],b[1],self.exp(a)+self.exp(b)])
 sum=base.Circuit.sum;prod=base.Circuit.prod;sq=base.Circuit.sq;p_add=base.Circuit.p_add;p_mul=base.Circuit.p_mul;p_sq=base.Circuit.p_sq

class RadiusCircuit(base.Circuit):
 def __init__(self,*args,**kwargs):super().__init__(*args,**kwargs);self.radius_proof=None
 def source(self,env,index,short_beta=True):
  if self.radius_proof is not None:return super().source(env,index,short_beta=short_beta)
  p=ExponentProof();en={k:p.input(k) for k in env};ix=p.input('index');ep,fp=ORIGINAL_SOURCE(p,en,ix,short_beta=short_beta);needed=max(1,p.exp(ep),p.exp(fp));D=1 << (needed-1).bit_length()
  # Every actual upper input is one of N,x,y,m,M0,U. The 'a' coordinate is U.
  terms=[base.C(4),index,env['x'],env['y'],env['m'],env['M0'],env['a']]
  R=self.sum(terms)
  # Binary powering implements the literal fixed exponent D without Pell macros.
  out=base.O;power=R;n=D;chain=[]
  while n:
   if n&1:out=self.mul(out,power);chain.append({'action':'accumulate','remaining_exponent':n,'result':out})
   n//=2
   if n:power=self.sq(power);chain.append({'action':'square','remaining_exponent':n,'result':power})
  self.radius_proof={'radius_terms':terms,'radius_atom':R,'exponent':D,'minimum_sufficient_exponent':needed,'E_exponent':p.exp(ep),'F_exponent':p.exp(fp),'E_root':p.atom(ep),'F_root':p.atom(fp),'abstract_inputs':p.inputs,'exponent_nodes':p.nodes,'fixed_power_chain':chain,'height':out,'source_environment':env,'source_index':index,'reason':'R>=4 and every upper-source input<=R; add exponent=max+1, multiply exponent=sum'}
  return out,base.Z

def main():
 parser=argparse.ArgumentParser();parser.add_argument('--output',type=pathlib.Path,default=pathlib.Path(__file__).parent/'radius');parser.add_argument('--keep-affine',action='store_true');args=parser.parse_args()
 # The original local builder accepts no factory; substitution is confined to this process.
 old=base.Circuit;base.Circuit=RadiusCircuit
 try:b=base.build(short_beta=True,shared=True,oriented=True)
 finally:base.Circuit=old
 b.bindings['majorant']='radius fixed power, not a duplicate evaluation of source E,F';b.bindings['radius_majorant']=b.radius_proof
 eq,poly,aff=b.export(affine=not args.keep_affine);args.output.mkdir(parents=True,exist_ok=True)
 hashes={name:base.write(args.output/name,obj) for name,obj in [('equation.json',eq),('expanded_polynomial.json',poly),('affine_restoration.json',aff),('circuit.json',{'variables':b.vars,'residuals':b.rows,'macros':b.macros,'bindings':b.bindings}),('radius_certificate.json',b.radius_proof)]}
 receipt={'metrics':eq['metrics'],'sha256':hashes,'radius_exponent':b.radius_proof['exponent'],'abstract_source_nodes':len(b.radius_proof['exponent_nodes']),'fixed_power_multiplications':len(b.radius_proof['fixed_power_chain']),'builder_sha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),'base_builder_sha256':hashlib.sha256(pathlib.Path(base.__file__).read_bytes()).hexdigest(),'scope':'explicit quartic; fixed majorant exponent has a structural proof; not kernel certification'}
 base.write(args.output/'BUILD.json',receipt);print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
