#!/usr/bin/env python3
"""Compose the credited eight-column projection with round13 arithmetic.
Horizon padding bounds schema parameters; dyadic radii bound labels/source.
Beta quotient columns use x itself as bound. No upstream executable imports.
"""
import argparse,hashlib,json,pathlib
import build_direct as base
from build_parametric import ParametricCircuit
from build_radius import ExponentProof
C,Z,O,TWO,FOUR=base.C,base.Z,base.O,base.TWO,base.FOUR
def label_rules(self,e):
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
 a,b,c,d=[e[n] for n in ['a','b','c','d']]
 axioms=[X(a,E(a,b)),I(A(a,I(b,c)),I(A(a,b),A(a,c))),I(E(a,b),I(M(c,a),M(c,b))),I(A(a,A(b,c)),A(b,A(a,c))),I(E(c,a),I(M(c,b),M(a,b))),I(X(a,A(a,b)),b),I(E(c,a),I(E(c,b),A(M(a,b),E(a,b)))),I(I(I(c,d),a),I(I(a,c),I(b,c))),bundle(a,b,c)]
 gp,gn=self.p_sq((ad(sq(c),mu(a,b)),mu(c,ad(a,b))))
 guard=(gp,ad(gn,sq(ad(d,O))))
 rules=[{'name':'truth','labels':[Z,Z,Z],'guard':None}]
 names=['rho1','rho2','rho3','rho4','rho5','rho6','growG','rho8','bundle']
 for name,code in zip(names,axioms):rules.append({'name':name,'labels':[Z,Z,code],'guard':guard if name=='bundle' else None})
 rules += [{'name':'mp','labels':[a,I(a,b),b],'guard':None},{'name':'gen','labels':[b,Z,A(a,b)],'guard':None}]
 return rules

def projected_source(self,e,index):
 rules=label_rules(self,e);M=self.add(e['M0'],O);total=(O,Z);details=[]
 for rule in rules:
  p,q,v=rule['labels'];left=self.mul(e['Sp'],self.add(O,self.mul(v,M)));right=self.prod([e['S'],self.add(O,self.mul(p,M)),self.add(O,self.mul(q,M))]);branch=self.p_sq((left,right))
  if rule['guard'] is not None:branch=self.p_add(branch,self.p_sq(rule['guard']))
  total=self.p_mul(total,branch);details.append(dict(rule,accumulator=[left,right],branch_pair=branch))
 D=self.add(self.mul(self.add(index,O),e['y']),O);Dp=self.add(D,e['y'])
 beta=[(e['x'],self.add(e['S'],self.mul(D,e['u']))),(e['x'],self.add(e['Sp'],self.mul(Dp,e['vq'])))]
 for r in beta:total=self.p_add(total,self.p_sq(r))
 return total,{'rules':details,'beta_pairs':beta,'index':index,'environment':e}

def fixed_majorant(b,terms,proof,roots):
 needed=max(1,*[proof.exp(r) for r in roots]);D=1 << (needed-1).bit_length();R=b.sum(terms);out=R;chain=[]
 for j in range(D.bit_length()-1):out=b.sq(out);chain.append({'squaring':j+1,'result':out,'exponent':1 << (j+1)})
 return out,{'radius_terms':terms,'radius_atom':R,'exponent':D,'minimum_sufficient_exponent':needed,'root_exponents':[proof.exp(r) for r in roots],'roots':[proof.atom(r) for r in roots],'abstract_inputs':proof.inputs,'exponent_nodes':proof.nodes,'fixed_power_chain':chain,'height':out}

def build(integer_mode=False):
 b=ParametricCircuit(shared=True,oriented=True);b.integer_mode=integer_mode
 N=b.add(b.v('N0','outer'),O);x=b.v('x','outer');y0=b.v('y0','outer');M0=b.v('M0','outer');y=b.sum([M0,TWO,y0]);params={'t':N,'x':x,'y':y,'M0':M0}
 # All four schema parameters are at most the padded horizon N.
 lp=ExponentProof();le={n:lp.input(n) for n in ['a','b','c','d']};lrules=label_rules(lp,le);m,lcert=fixed_majorant(b,[C(4),N],lp,[v for r in lrules for v in r['labels']]);lcert['label_rules']=lrules;lcert['actual_parameter_bound']=N
 b.eq(b.power(b.add(m,O),N),b.add(M0,O),'carrier_power')
 u0,ut=b.v('endpoint.u0'),b.v('endpoint.ut');Dn=b.add(b.mul(b.add(N,O),y),O)
 b.eq(x,b.add(b.add(M0,TWO),b.mul(b.add(y,O),u0)),'endpoint.initial');b.eq(x,b.add(O,b.mul(Dn,ut)),'endpoint.final')
 names=['a','b','c','d','S','Sp','u','vq'];upper={n:N if n in ['a','b','c','d'] else y if n in ['S','Sp'] else x for n in names};lower={n:y if n in ['S','Sp'] else b.add(upper[n],O) for n in names}
 encoded={n:b.add(b.v('CRT.column.'+n),O) for n in names};idx=b.v('CRT.index')
 sp=ExponentProof();se={n:sp.input(n) for n in params|upper};ix=sp.input('index');pair,sdetail=projected_source(sp,se,ix);H,hcert=fixed_majorant(b,[C(4),N,x,y,M0],sp,list(pair));hcert['abstract_source']=sdetail;hcert['source_environment']=params|upper;hcert['source_index']=N
 T=b.fact(H);B=b.moduli_product(N,T)
 for name in names:
  val=b.choose(encoded[name],lower[name]);q=b.v('CRT.range_quotient.'+name);b.eq(val,b.mul(B,q),'CRT.range.'+name)
 qi=b.v('CRT.index_quotient');b.eq(b.add(O,b.mul(b.add(idx,O),T)),b.mul(B,qi),'CRT.index_constraint')
 (ee,ff),edetail=projected_source(b,params|encoded,idx);b.congruent(ee,ff,B,'CRT.evaluation')
 b.bindings={'parameters':params|{'m':m},'upper':upper,'range_lower_arguments':lower,'encoded_columns':encoded,'encoded_index':idx,'H':H,'factorial':T,'CRT_product':B,'encoded_E':ee,'encoded_F':ff,'row_coordinate_count':8,'label_bound_certificate':lcert,'radius_majorant':hcert,'encoded_source':edetail,'source_transform':'credited branch label projection, truth horizon padding, beta quotient bound x','integer_template':integer_mode}
 if integer_mode:b.bindings['unrestricted_integer_quotients']=[i for i,v in enumerate(b.vars) if v['name'].endswith(('.quotient','.integer_quotient')) and (v['name'].startswith('power') or v['name'].startswith('CRT.evaluation'))]
 return b

def main():
 p=argparse.ArgumentParser();p.add_argument('--output',type=pathlib.Path,default=pathlib.Path(__file__).parent/'projected');p.add_argument('--integer-template',action='store_true');args=p.parse_args();b=build(args.integer_template);eq,poly,aff=b.export()
 if args.integer_template:eq['domain']='mixed-domain intermediate; not final equation';poly['domain']=eq['domain']
 args.output.mkdir(parents=True,exist_ok=True);hashes={name:base.write(args.output/name,obj) for name,obj in [('equation.json',eq),('expanded_polynomial.json',poly),('affine_restoration.json',aff),('circuit.json',{'variables':b.vars,'residuals':b.rows,'macros':b.macros,'bindings':b.bindings}),('projection_certificate.json',{'label_bound':b.bindings['label_bound_certificate'],'radius_majorant':b.bindings['radius_majorant'],'encoded_source':b.bindings['encoded_source']})]}
 receipt={'metrics':eq['metrics'],'sha256':hashes,'label_bound_exponent':b.bindings['label_bound_certificate']['exponent'],'source_bound_exponent':b.bindings['radius_majorant']['exponent'],'builder_sha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),'scope':'explicit composition of credited projection with local parametric arithmetic; mathematical delta proof separate; no upstream code execution'};base.write(args.output/'BUILD.json',receipt);print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
