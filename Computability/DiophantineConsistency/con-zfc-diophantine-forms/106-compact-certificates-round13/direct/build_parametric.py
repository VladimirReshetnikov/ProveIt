#!/usr/bin/env python3
"""Parametric positive-power certificates: define removable positive outputs.
A,Y,T,V,B and (in the natural variant) S,R are definitional expressions.
B=1+4Y(q4+1) makes B>1 directly, also with signed congruence quotients.
No upstream executable imports.
"""
import argparse,json,pathlib,hashlib
import build_direct as base
from build_compact import CompactCircuit
C,Z,O,TWO,FOUR=base.C,base.Z,base.O,base.TWO,base.FOUR
class ParametricCircuit(CompactCircuit):
 integer_mode=False
 def power(self,n,k):
  key=n,k
  if key in self.powers:return self.powers[key]
  tag='power'+str(len(self.powers));start=len(self.vars);m=self.v(tag+'.output');self.powers[key]=m
  a2,yk,gap,vd,X,U,q4,qB,qS,qR,qP=[self.v(tag+'.'+s) for s in ['a2','yk','gap','vd','X','U','q4_minus_one','B_mod_U.quotient','S_mod_U.quotient','R_mod_4Y.quotient','power_mod_T.quotient']]
  A=self.add(a2,TWO);Y=self.add(k,yk);T=self.sum([m,gap,O]);V=self.mul(self.sq(Y),self.add(vd,O));fourY=self.mul(FOUR,Y)
  B=self.add(O,self.mul(fourY,self.add(q4,O)))
  if self.integer_mode:
   S,R=self.v(tag+'.S'),self.v(tag+'.R')
   self.eq(S,self.add(X,self.mul(U,qS)),tag+'.S_definition');self.eq(R,self.add(k,self.mul(fourY,qR)),tag+'.R_definition')
  else:S=self.add(X,self.mul(U,qS));R=self.add(k,self.mul(fourY,qR))
  self.norm(A,X,Y,tag+'.norm_AXY');self.norm(A,U,V,tag+'.norm_AUV');self.norm(B,S,R,tag+'.norm_BSR')
  self.eq(B,self.add(A,self.mul(U,qB)),tag+'.B_mod_U')
  self.eq(self.add(X,self.mul(Y,n)),self.sum([self.mul(Y,A),m,self.mul(T,qP)]),tag+'.power_mod_T')
  self.eq(self.prod([TWO,A,n]),self.sum([T,self.sq(n),O]),tag+'.T_definition')
  W=self.add(n,k);self.norm(self.add(W,O),A,self.mul(W,self.v(tag+'.Z')),tag+'.last_norm')
  self.macros.append({'kind':'power','base':n,'exponent':k,'output':m,'start_variable':start,'end_variable':len(self.vars),'tag':tag,'parametric':True,'arithmetic_coordinates':{'A':A,'Y':Y,'T':T,'V':V,'B':B,'S':S,'R':R,'X':X,'U':U},'quotients':[qB,qS,qR,qP]})
  return m
 def congruent(self,a,b,m,label):
  if self.integer_mode and label=='CRT.evaluation':
   q=self.v(label+'.integer_quotient');self.eq(a,self.add(b,self.mul(m,q)),label+'.integer');self.macros.append({'kind':'integer_congruence','left':a,'right':b,'modulus':m,'quotient':q,'label':label})
  else:super().congruent(a,b,m,label)
def main():
 p=argparse.ArgumentParser();p.add_argument('--output',type=pathlib.Path,default=pathlib.Path(__file__).parent/'parametric');p.add_argument('--integer-template',action='store_true');p.add_argument('--keep-affine',action='store_true');args=p.parse_args();ParametricCircuit.integer_mode=args.integer_template
 old=base.Circuit;base.Circuit=ParametricCircuit
 try:b=base.build(short_beta=True,shared=True,oriented=True)
 finally:base.Circuit=old
 b.bindings['majorant']='dyadic radius bound';b.bindings['radius_majorant']=b.radius_proof;b.bindings['source_transform']='common-condition factored C222 Horn source';b.bindings['arithmetic_transform']='parametric positive-power certificates';b.bindings['integer_template']=args.integer_template
 if args.integer_template:b.bindings['unrestricted_integer_quotients']=[i for i,v in enumerate(b.vars) if v['name'].endswith(('.quotient','.integer_quotient')) and (v['name'].startswith('power') or v['name'].startswith('CRT.evaluation'))]
 eq,poly,aff=b.export(affine=not args.keep_affine)
 if args.integer_template:eq['domain']='mixed-domain intermediate; not final equation';poly['domain']=eq['domain']
 args.output.mkdir(parents=True,exist_ok=True)
 hashes={name:base.write(args.output/name,obj) for name,obj in [('equation.json',eq),('expanded_polynomial.json',poly),('affine_restoration.json',aff),('circuit.json',{'variables':b.vars,'residuals':b.rows,'macros':b.macros,'bindings':b.bindings}),('radius_certificate.json',b.radius_proof)]}
 receipt={'metrics':eq['metrics'],'sha256':hashes,'radius_exponent':b.radius_proof['exponent'],'builder_sha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),'scope':'explicit parametric-Pell quartic; mathematical equivalences separate; not kernel certification'};base.write(args.output/'BUILD.json',receipt);print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
