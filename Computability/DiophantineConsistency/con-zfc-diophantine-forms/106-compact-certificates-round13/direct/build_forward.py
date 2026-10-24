#!/usr/bin/env python3
"""All-forward Pell congruences atop the compact radius construction.
Completeness uses the explicit indexed-Pell construction with B>=A and
Pell sequences monotone in their parameter; see orientation proof.
"""
import argparse,hashlib,json,pathlib
import build_direct as base
from build_compact import CompactCircuit
class ForwardCircuit(CompactCircuit):
 def congruent(self,a,b,m,label):
  if label.startswith('power') and label.rsplit('.',1)[-1] in ('B_mod_U','S_mod_U','R_mod_4Y'):
   q=self.v(label+'.nonnegative_quotient');self.eq(a,self.add(b,self.mul(m,q)),label+'.forward')
   self.macros.append({'kind':'forward_congruence','label':label,'left':a,'right':b,'modulus':m,'quotient':q})
  else:super().congruent(a,b,m,label)
def main():
 p=argparse.ArgumentParser();p.add_argument('--output',type=pathlib.Path,default=pathlib.Path(__file__).parent/'forward');p.add_argument('--keep-affine',action='store_true');args=p.parse_args()
 old=base.Circuit;base.Circuit=ForwardCircuit
 try:b=base.build(short_beta=True,shared=True,oriented=True)
 finally:base.Circuit=old
 b.bindings['majorant']='dyadic radius bound';b.bindings['radius_majorant']=b.radius_proof;b.bindings['source_transform']='common-condition factored C222 Horn source';b.bindings['arithmetic_transform']='all four positive-Pell congruences forward'
 eq,poly,aff=b.export(affine=not args.keep_affine);args.output.mkdir(parents=True,exist_ok=True)
 hashes={name:base.write(args.output/name,obj) for name,obj in [('equation.json',eq),('expanded_polynomial.json',poly),('affine_restoration.json',aff),('circuit.json',{'variables':b.vars,'residuals':b.rows,'macros':b.macros,'bindings':b.bindings}),('radius_certificate.json',b.radius_proof)]}
 receipt={'metrics':eq['metrics'],'sha256':hashes,'radius_exponent':b.radius_proof['exponent'],'forward_indexed_congruences':sum(x['kind']=='forward_congruence' for x in b.macros),'builder_sha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),'scope':'explicit quartic; all-forward completeness proof separate; not kernel certification'}
 base.write(args.output/'BUILD.json',receipt);print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
