#!/usr/bin/env python3
"""Parity-padded factorial/Horn source and even-index Pell compiler."""
from pathlib import Path
import argparse, json, os, sys
from math import factorial
HERE=Path(__file__).resolve().parent
PACKAGED_ROUND=HERE.parent/'vendor/round14'
DEFAULT_ROUND=PACKAGED_ROUND if PACKAGED_ROUND.is_dir() else HERE/'ConZFC_Powered_Saturation_Factorial_Carriers_Round14_2026-10-24/ConZFC_Powered_Saturation_Factorial_Carriers_Round14_2026-10-24'
ROUND=Path(os.environ.get('CONZFC_ROUND14_ROOT',str(DEFAULT_ROUND)))
sys.path.insert(0,str(ROUND/'architecture'))
import build_derived_label_range as src
h,bp,ONE,TWO,const=src.h,src.bp,src.ONE,src.TWO,src.const
from build_equation import FOUR

class EvenMixin:
    def eq(self,left,right,label,guard=None):
        if label=='crt.aggregate_representative_bound':left=self.add(left,left)
        return super().eq(left,right,label,guard)

    def factorial(self,n):
        if n in self.factorials:return self.factorials[n]
        if self.factorials:raise ValueError('one factorial expected')
        tag='fact0';half=self.new(tag+'.half_output');out=self.mul(TWO,half)
        self.factorials[n]=out
        rho=self.mul(out,self.square(n));self.shared_factorial_radius=rho
        c=self.binomial(self.add(rho,n),n);numerator=self.power(self.add(rho,ONE),n)
        remainder,slack=self.new(tag+'.remainder'),self.new(tag+'.slack')
        self.eq(self.add(numerator,c),self.sum([self.mul(c,out),remainder,ONE]),tag+'.ceiling')
        self.eq(c,self.sum([remainder,slack,ONE]),tag+'.remainder_bound')
        self.macro_log.append({'macro':'factorial','output':out,'half_output':half,'n':n,'selfbounding_even_output':True})
        self.factorial_certificates.append({'input':n,'output':out,'half_output':half,'radius':rho,'binomial':c,'numerator':numerator,'remainder':remainder,'slack':slack,'selfbounding':True})
        self.factorial_radix={'H':n,'rho':rho,'numerator':numerator,'factorial':out}
        return out

    def _auxiliary_index(self):
        if self.common_index_parameters is None:
            _,A,_=self._scale()
            U,vm1,q4minus1,bq=[self.new('shared_index.'+s) for s in ('U','Vminus1','q4minus1','Bquotient')]
            V=self.add(vm1,ONE)
            self.norm(A,U,V,'shared_index.norm')
            B=self.add(ONE,self.mul(self.mul(FOUR,V),self.add(q4minus1,ONE)))
            self.eq(B,self.add(A,self.mul(U,bq)),'shared_index.B_mod_U')
            self.common_index_parameters=U,V,B
        return self.common_index_parameters

    def _index(self,k):
        if k in self.shared_indices:return self.shared_indices[k]
        definition=self.index_definitions.get(k)
        if definition and definition[0]=='add':
            _,a,b=definition
            if a in self.known_exponents and b in self.known_exponents:
                pair=self._combine(self._index(a),self._index(b))
                self.shared_indices[k]=pair
                self.index_derivations.append({'kind':'sum','target':k,'sources':[a,b],'pair':pair})
                return pair
        _,A,_=self._scale();U,V,B=self._auxiliary_index();tag='index'+str(len(self.shared_indices))
        X,Y,S,R=[self.new(tag+'.'+s) for s in ('X','Y','S','R')]
        self.norm(A,X,Y,tag+'.norm1');self.norm(B,S,R,tag+'.norm3')
        fourY=self.mul(FOUR,Y);sq,rq=[self.new(tag+'.'+s) for s in ('Squotient','Rquotient')]
        self.eq(S,self.add(X,self.mul(U,sq)),tag+'.S_mod_U')
        self.eq(R,self.add(k,self.mul(fourY,rq)),tag+'.R_mod_4Y')
        pair=X,Y;self.shared_indices[k]=pair;self.seed_indices[k]=pair
        return pair

    def finalize_power_frame(self):
        if self.shared_frame_finalized:return
        super().finalize_power_frame()
        if getattr(self,'modular_requests',None):
            if self.rows[-1]['label']!='shared.frame_definition':raise ValueError('frame is not terminal')
            self.rows.pop()
            atoms={a for (n,k),m in self.powers.items() for a in(n,k,m)}
            atoms.update(r['n'] for r in self.modular_requests)
            W,_,_=self._scale()
            self.eq(W,self.sum([TWO]+sorted(atoms)),'shared.frame_definition')
        self.radix_data['aggregate_capacity_multiplier']=2
        self.radix_data['bound']='2*aggregate_count*N^2'

class EvenBuilder(EvenMixin,h.HybridBuilder):pass
BUILD_CLASS=EvenBuilder
LAST_BUILDER=None

def construct(syntax='cantor',horizon_minimum=12):
    global LAST_BUILDER
    if horizon_minimum%2 or horizon_minimum<12:raise ValueError('even horizon floor >=12 required')
    bp.ng.direct_source=h.CANTOR_SOURCE
    if syntax!='cantor':h.shell_source.SHELL_SCHEME=syntax;bp.ng.direct_source=h.shell_source.direct_source
    b=BUILD_CLASS(positive_powers=True)
    rawbytes=(bp.ng.UP/'provenance/upstream/wire_eliminated_source.json').read_bytes();source=json.loads(rawbytes)
    t=b.add(b.mul(TWO,b.new('t0','outer')),const(horizon_minimum))
    x=b.add(b.mul(TWO,b.new('xhalf_minus1','outer')),TWO)
    F=b.factorial(t);r0=b.new('endpoint.r0');y=b.sum([F,b.mul(TWO,r0),TWO])
    params={'t':t,'x':x,'y':y,'F':F}
    u0,ut=[b.new('endpoint.'+n) for n in ('u0','ut')]
    dt=b.add(b.mul(b.add(t,ONE),y),ONE)
    b.eq(x,b.sum([F,ONE,b.mul(b.add(y,ONE),u0)]),'endpoint.first_quotient')
    b.eq(x,b.add(ONE,b.mul(dt,ut)),'endpoint.last_quotient')
    bounds={n:t if i<4 else y if i<6 else x for i,n in enumerate(src.LOCAL_NAMES)}
    encoded={n:b.mul(TWO,b.add(b.new('crt.encoded.'+n),ONE)) for n in src.LOCAL_NAMES}
    C=b.mul(TWO,b.add(b.new('crt.encoded_index_half_minus1'),ONE))
    bc=src.majorants(source);E=bc['emitted_exponent'];ell=bc['derived_label_majorant']['emitted_exponent']
    fm=factorial(horizon_minimum);a=fm.bit_length()-1
    if not(a*E<2**a and 2*E<=2**a and horizon_minimum*(3*ell+1)<=fm):raise ValueError('budget floor')
    R=b.sum([TWO,t,x,y,F]);K=b.mul(TWO,R)
    B=b.moduli_product(t,F);T=b.product_data['square'];N=b.power(B,K)
    b.amplification_data={'B':B,'K':K,'N':N,'F':F,'t':t,'R':R,'index':C,'local_degree_bound':E,'label_degree_bound':ell,'budget':'2R','horizon_minimum':horizon_minimum,'index_precision':'K','completeness_precision':'2K','floor_exponent':a,'factorial_floor':fm,'derived_label_radix_budget':'2*t*(3*ell+1)<=2F<K','parity_padded':True,'strict_column_bounds':True,'outer_values':params,'encoded_values':encoded}
    for n in src.LOCAL_NAMES:b.divisible_binomial(encoded[n],bounds[n],N,'crt.range.'+n)
    b.divisible_binomial(C,t,N,'crt.range.index');b.aggregate_requests=list(b.range_requests)
    iq=b.new('crt.index_quotient');b.eq(b.sum([C,T,ONE]),b.mul(B,iq),'crt.reciprocal_index_congruence')
    value,labels=src.source_and_labels(b,source,params|encoded,C)
    doublelabels=b.mul(TWO,labels);doublet=b.add(t,t)
    b.divisible_binomial(doublelabels,doublet,N,'crt.range.derived_label_sum')
    b.amplification_data['derived_label_sum']=labels;b.amplification_data['derived_range_argument']=doublelabels
    quotient=b.new('crt.nonnegative_quotient');b.eq(value,b.mul(N,quotient),'crt.nonnegative_evaluation')
    b.finalize_binomials();b.finalize_power_frame()
    LAST_BUILDER=b
    return b,rawbytes,bc

def generate(out,syntax='cantor',modular=False,horizon=12):
    global BUILD_CLASS
    if modular:
        from modular_factorial import ModularFactorialBuilder
        class EvenModularBuilder(EvenMixin,ModularFactorialBuilder):
            def power(self,n,k):
                key=n,k
                if not hasattr(self,'even_power_derivations'):self.even_power_derivations={}
                if key in self.even_power_derivations:return self.even_power_derivations[key]['output']
                definition={out:key for key,out in self.cache.items()}.get(k)
                if definition and definition[0]=='add' and definition[1]==definition[2] and (n,definition[1]) in self.powers:
                    previous=self.powers[n,definition[1]];out=self.square(previous)
                    self.even_power_derivations[key]={'base':n,'exponent':k,'half_exponent':definition[1],'half_output':previous,'output':out}
                    return out
                return super().power(n,k)
            def common_root_modulus(self,q,K):
                x=self.amplification_data['outer_values']['x']
                self.root_modulus_recipe={'kind':'N_times_dominant_denominator','exponent':x,'proof':'x>2t,y,t from even x>=2 and last endpoint'}
                return self.mul(self.amplification_data['N'],self.power(q,x))
        BUILD_CLASS=EvenModularBuilder
    else:BUILD_CLASS=EvenBuilder
    old=src.fc.construct;oldnames=src.fc.LOCAL_NAMES;src.fc.construct=construct;src.fc.LOCAL_NAMES=src.LOCAL_NAMES
    try:result=src.fc.generate(out,syntax,horizon)
    finally:src.fc.construct=old;src.fc.LOCAL_NAMES=oldnames
    result['parity_padded']=True;result['modular_numerators']=modular;h.write(Path(out)/'SUMMARY.json',result)
    h.write(Path(out)/'raw/parity_interface.json',{'even_power_derivations':list(getattr(LAST_BUILDER,'even_power_derivations',{}).values()),'strict_auxiliary_ordinate':LAST_BUILDER.common_index_parameters[1],'frame_contains_all_indices':True,'proof_domain':'nonnegative integers','horizon_minimum':horizon})
    return result

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);p.add_argument('--syntax',choices=['cantor','xx0','xy0'],default='cantor');p.add_argument('--modular',action='store_true');p.add_argument('--horizon',type=int,default=12)
    a=p.parse_args();print(json.dumps(generate(a.output,a.syntax,a.modular,a.horizon),indent=2))
