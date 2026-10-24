#!/usr/bin/env python3
"""A radix based on the actual CRT representatives removes their aggregate bound."""
from pathlib import Path
import argparse,json,sys
BASE=Path(__file__).resolve().parents[1]/'round14'
sys.path.insert(0,str(BASE/'architecture'))
import build_derived_label_range as old
h,ONE=old.h,old.ONE

class SelfRadixBuilder(h.HybridBuilder):
    def finalize_binomials(self):
        if getattr(self,'binomials_finalized',False): raise ValueError('repeated finalization')
        self.binomials_finalized=True
        moduli={r[2] for r in self.range_requests}
        if len(moduli)!=1:raise ValueError('common modulus required')
        N=next(iter(moduli));K=self.amplification_data['K']
        reps=getattr(self,'aggregate_requests',self.range_requests)
        V=self.factorial_radix['numerator']
        total=self.sum(n for n,_,_,_ in reps)
        base=self.sum([V,ONE,total])
        q=self.mul(N,self.power(base,K))
        for i,((n,k),out) in enumerate(self.binomials.items()):
            tag='choose'+str(i)
            numerator=self.power(self.add(q,ONE),n);den=self.power(q,k)
            hi,r,rs,os=[self.new(tag+'.'+s) for s in ('high','remainder','rslack','oslack')]
            self.eq(numerator,self.add(self.mul(den,self.add(self.mul(q,hi),out)),r),tag+'.digit')
            self.eq(den,self.sum([r,rs,ONE]),tag+'.remainder_bound')
            self.eq(q,self.sum([out,os,ONE]),tag+'.digit_bound')
        for i,(n,k,modulus,label) in enumerate(self.range_requests):
            numerator=self.power(self.add(q,ONE),n);den=self.power(q,k)
            hi,r,s=[self.new('range'+str(i)+'.'+role) for role in ('quotient','remainder','slack')]
            self.eq(numerator,self.add(self.product([den,modulus,hi]),r),label+'.quotient_multiple')
            self.eq(den,self.sum([r,s,ONE]),label+'.remainder_bound')
        self.radix_data={'radix':q,'modulus':N,'K':K,'V':V,
                        'representative_sum':total,'base':base,'kind':'N*(V+1+sum(representatives))^K',
                        'aggregate_bound_removed':True,'independent_representatives':len(reps),
                        'exact_binomials':len(self.binomials),'range_binomials':len(self.range_requests)}

def generate(out,syntax='cantor',horizon_minimum=16):
    previous=h.HybridBuilder
    h.HybridBuilder=SelfRadixBuilder
    try:return old.generate(out,syntax,horizon_minimum)
    finally:h.HybridBuilder=previous

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True)
    p.add_argument('--syntax',choices=['cantor','xx0','xy0'],default='cantor')
    a=p.parse_args();print(json.dumps(generate(a.output,a.syntax),indent=2))
