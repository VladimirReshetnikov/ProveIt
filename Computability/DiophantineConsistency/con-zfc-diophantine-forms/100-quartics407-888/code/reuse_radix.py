"""Reuse the large factorial numerator as a bounded-binomial radix.

Requires the direct source's H=R^E, E>=4; its first factorial is H!.
A single aggregate CRT representative bound replaces a separate radix power.
"""
from pathlib import Path
import json,sys,argparse
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE))
import build_fused as fused
from additive_index import AdditiveIndexPowerBuilder
from build_equation import ONE,TWO,const


class FactorialRadixMixin:
    def factorial(self,n):
        out=super().factorial(n)
        if not hasattr(self,'factorial_radix'):
            shift=self.add(n,TWO)
            rho=self.powers[(shift,shift)]
            numerator=self.powers[(self.add(rho,ONE),n)]
            self.factorial_radix={'H':n,'rho':rho,'numerator':numerator,'factorial':out}
        return out

    def finalize_binomials(self):
        if getattr(self,'binomials_finalized',False):raise ValueError('repeated finalization')
        self.binomials_finalized=True
        moduli={r[2] for r in self.range_requests}
        if len(moduli)!=1:raise ValueError('one common range modulus required')
        B=next(iter(moduli))
        rcount=len(self.range_requests)
        # Choosing positive canonical CRT representatives gives each n in[1,B].
        # The one aggregate inequality is intentionally weaker, but sufficient.
        aggregate=self.new('crt.aggregate_representative_slack')
        self.eq(self.mul(const(rcount),B),
                self.add(self.sum(n for n,_,_,_ in self.range_requests),aggregate),
                'crt.aggregate_representative_bound')
        radix_power=self.factorial_radix['numerator']
        q=self.mul(B,self.add(radix_power,ONE))
        for i,((n,k),out) in enumerate(self.binomials.items()):
            tag='choose'+str(i)
            numerator=self.power(self.add(q,ONE),n);den=self.power(q,k)
            h,r,rs,os=[self.new(tag+'.'+s) for s in ('high','remainder','rslack','oslack')]
            self.eq(numerator,self.add(self.mul(den,self.add(self.mul(q,h),out)),r),tag+'.digit')
            self.eq(den,self.sum([r,rs,ONE]),tag+'.remainder_bound')
            self.eq(q,self.sum([out,os,ONE]),tag+'.digit_bound')
        for i,(n,k,B,label) in enumerate(self.range_requests):
            num=self.power(self.add(q,ONE),n);den=self.power(q,k)
            h,r,s=[self.new('range'+str(i)+'.'+role) for role in ('quotient','remainder','slack')]
            self.eq(num,self.add(self.product([den,B,h]),r),label+'.quotient_multiple')
            self.eq(den,self.sum([r,s,ONE]),label+'.remainder_bound')
        self.radix_data={'upper_atoms':list(dict.fromkeys([n for n,k in self.binomials]+[n for n,_,_,_ in self.range_requests])),
                         'radix':q,'radix_multiple':B,'factorial_radix':self.factorial_radix,
                         'aggregate_range_count':rcount,'aggregate_slack':aggregate,
                         'exact_binomials':len(self.binomials),'range_binomials':len(self.range_requests)}


class ReusedRadixBuilder(FactorialRadixMixin,fused.FusedBuilder):pass
class AdditiveReusedRadixBuilder(FactorialRadixMixin,AdditiveIndexPowerBuilder,fused.FusedBuilder):pass

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True)
    p.add_argument('--additive',action='store_true');args=p.parse_args()
    cls=AdditiveReusedRadixBuilder if args.additive else ReusedRadixBuilder
    print(json.dumps(fused.generate(args.output,cls,caps=(4,16,64)),indent=2))
