#!/usr/bin/env python3
"""Factored direct Horn source plus dyadic radius majorant.
All source transformations preserve zero sets over naturals, not polynomial identity.
Self-authored local builders only; no upstream executable imports.
"""
import argparse,hashlib,json,pathlib
import build_direct as base
from build_radius import ExponentProof
C,Z,O,TWO,FOUR=base.C,base.Z,base.O,base.TWO,base.FOUR
def compact_source(self,e,index,short_beta=True):
 ad,mu,sq=self.add,self.mul,self.sq
 def I(a,b):
  s=ad(a,b);return ad(mu(TWO,mu(s,ad(s,O))),mu(FOUR,b))
 def A(a,b):return ad(I(a,b),TWO)
 def M(a,b):return ad(I(a,b),O)
 def E(a,b):return ad(I(a,b),C(3))
 def neg(a):return I(a,O)
 def X(a,b):return neg(A(a,neg(b)))
 def req(x,k,f):return A(x,I(f,neg(A(x,I(f,neg(M(x,k)))))))
 def clos(x,y,k,f):
  subset=A(k,I(M(k,x),M(k,y)));tail=I(subset,req(y,k,f));tail=neg(A(x,tail));tail=neg(A(x,I(f,tail)));return A(y,I(M(y,k),tail))
 def bundle(x,y,z):
  nks=A(z,I(clos(x,y,z,z),neg(req(y,z,z))));vrel=I(M(x,y),A(z,M(x,y)));return neg(I(vrel,nks))
 a,b,c,d,p,q,v=[e[n] for n in ['a','b','c','d','p','q','v']]
 axioms=[X(a,E(a,b)),I(A(a,I(b,c)),I(A(a,b),A(a,c))),I(E(a,b),I(M(c,a),M(c,b))),I(A(a,A(b,c)),A(b,A(a,c))),I(E(c,a),I(M(c,b),M(a,b))),I(X(a,A(a,b)),b),I(E(c,a),I(E(c,b),A(M(a,b),E(a,b)))),I(I(I(c,d),a),I(I(a,c),I(b,c))),bundle(a,b,c)]
 # Truth and eight unconditional axioms share p=q=0.
 ordinary=(v,Z)
 for f in axioms[:-1]:ordinary=self.p_mul(ordinary,(v,f))
 ordinary=self.p_add((sq(p),Z),self.p_sq(ordinary))
 # The bundled axiom retains its nonzero side condition.
 gp,gn=self.p_sq((ad(sq(c),mu(a,b)),mu(c,ad(a,b))))
 guard=self.p_sq((gp,ad(gn,sq(ad(d,O)))))
 bundled=self.p_add((sq(p),Z),self.p_add(self.p_sq((v,axioms[-1])),guard))
 generalized=self.p_sq((v,A(a,p)))
 non_mp=self.p_add((sq(q),Z),self.p_mul(generalized,self.p_mul(ordinary,bundled)))
 total=self.p_mul(self.p_sq((q,I(p,v))),non_mp)
 carrier=ad(e['M0'],O)
 def weight(name):return ad(O,mu(e[name],carrier))
 D=ad(mu(ad(index,O),e['y']),O);Dp=ad(D,e['y'])
 rows=[(mu(e['Sp'],weight('v')),self.prod([e['S'],weight('p'),weight('q')])),(e['x'],ad(e['S'],mu(D,e['u']))),(e['x'],ad(e['Sp'],mu(Dp,e['vq'])))]
 if not short_beta:rows += [(D,self.sum([e['S'],e['r'],O])),(Dp,self.sum([e['Sp'],e['rp'],O]))]
 for r in rows:total=self.p_add(total,self.p_sq(r))
 return total

class CompactCircuit(base.Circuit):
 def __init__(self,*args,**kwargs):super().__init__(*args,**kwargs);self.radius_proof=None
 def source(self,env,index,short_beta=True):
  if self.radius_proof is not None:return compact_source(self,env,index,short_beta=short_beta)
  p=ExponentProof();en={k:p.input(k) for k in env};ix=p.input('index');ep,fp=compact_source(p,en,ix,short_beta=short_beta)
  needed=max(1,p.exp(ep),p.exp(fp));D=1 << (needed-1).bit_length()
  terms=[C(4),index,env['x'],env['y'],env['m'],env['M0'],env['a']];R=self.sum(terms)
  out=R;chain=[]
  for j in range(D.bit_length()-1):
   out=self.sq(out);chain.append({'squaring':j+1,'result':out,'exponent':1 << (j+1)})
  self.radius_proof={'radius_terms':terms,'radius_atom':R,'exponent':D,'minimum_sufficient_exponent':needed,'E_exponent':p.exp(ep),'F_exponent':p.exp(fp),'E_root':p.atom(ep),'F_root':p.atom(fp),'abstract_inputs':p.inputs,'exponent_nodes':p.nodes,'fixed_power_chain':chain,'height':out,'source_environment':env,'source_index':index,'source_transform':'factored Horn zero-set polynomial','reason':'R>=4 and every upper-source input<=R; add exponent=max+1, multiply exponent=sum'}
  return out,Z

def main():
 p=argparse.ArgumentParser();p.add_argument('--output',type=pathlib.Path,default=pathlib.Path(__file__).parent/'compact');p.add_argument('--keep-affine',action='store_true');args=p.parse_args()
 old=base.Circuit;base.Circuit=CompactCircuit
 try:b=base.build(short_beta=True,shared=True,oriented=True)
 finally:base.Circuit=old
 b.bindings['majorant']='dyadic radius bound';b.bindings['radius_majorant']=b.radius_proof;b.bindings['source_transform']='common-condition factored C222 Horn source'
 eq,poly,aff=b.export(affine=not args.keep_affine);args.output.mkdir(parents=True,exist_ok=True)
 hashes={name:base.write(args.output/name,obj) for name,obj in [('equation.json',eq),('expanded_polynomial.json',poly),('affine_restoration.json',aff),('circuit.json',{'variables':b.vars,'residuals':b.rows,'macros':b.macros,'bindings':b.bindings}),('radius_certificate.json',b.radius_proof)]}
 receipt={'metrics':eq['metrics'],'sha256':hashes,'radius_exponent':b.radius_proof['exponent'],'abstract_source_nodes':len(b.radius_proof['exponent_nodes']),'fixed_power_multiplications':len(b.radius_proof['fixed_power_chain']),'builder_sha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),'base_builder_sha256':hashlib.sha256(pathlib.Path(base.__file__).read_bytes()).hexdigest(),'bound_builder_sha256':hashlib.sha256(pathlib.Path(ExponentProof.__module__+'.py').read_bytes()).hexdigest() if pathlib.Path(ExponentProof.__module__+'.py').exists() else hashlib.sha256(pathlib.Path(__file__).with_name('build_radius.py').read_bytes()).hexdigest(),'scope':'explicit quartic and mathematical equivalences; not kernel certification'}
 base.write(args.output/'BUILD.json',receipt);print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
