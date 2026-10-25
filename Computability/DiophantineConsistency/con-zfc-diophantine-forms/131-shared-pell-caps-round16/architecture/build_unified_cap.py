#!/usr/bin/env python3
"""Compose fused factorial/product, one shared Pell cap, and a pure self radix.

Imports the reviewed incoming portable source read-only. Every generated file
is written beneath an explicit output directory. No exponent primitive survives.
"""
from pathlib import Path
import argparse, json, sys
sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
INCOMING = HERE.parent/'intake/ConZFC_Shared_Pell_Bound_261_2026-10-24/ConZFC_Shared_Pell_Bound_261_2026-10-24'
SOURCE_ROOT = HERE/'portable/source' if (HERE/'portable/source').is_dir() else INCOMING/'portable/source'
sys.path.insert(0, str(SOURCE_ROOT/'custom'))
import capped_pell as cap
import build_radix_R as rr
h, ONE = cap.h, cap.ONE

class UnifiedCappedBuilder(cap.CappedHybrid):
    """Square-radius factorial and actual-representative radix on the cap frame."""
    radix_kind = 'NH'
    def factorial(self, n):
        if n in self.factorials: return self.factorials[n]
        if self.factorials: raise ValueError('Exactly one factorial is supported')
        out = self.new('fact0.output'); self.factorials[n] = out
        rho = self.square(out); self.shared_factorial_radius = rho
        B = self.binomial(self.add(rho,n),n)
        V = self.power(self.add(rho,ONE),n)
        u,v = [self.new('fact0.'+s) for s in ('remainder','slack')]
        self.eq(self.add(V,B),self.sum([self.mul(B,out),u,ONE]),'fact0.ceiling')
        self.eq(B,self.sum([u,v,ONE]),'fact0.remainder_bound')
        self.macro_log.append({'macro':'factorial','output':out,'n':n,
            'square_output_radius':True,'shared_reciprocal_product':True})
        self.factorial_certificates.append({'input':n,'output':out,'radius':rho,
            'binomial':B,'numerator':V,'remainder':u,'slack':v,'selfbounding':True,
            'square_output_radius':True})
        self.factorial_radix={'H':n,'rho':rho,'numerator':V,'factorial':out}
        return out

    def finalize_binomials(self):
        if getattr(self,'binomials_finalized',False): raise ValueError('Repeated finalization')
        self.binomials_finalized=True
        if len(self.binomials)!=1: raise ValueError('Factorial/product fusion failed')
        if self.factorial_certificates[0]['binomial']!=self.product_data['product']:
            raise ValueError('Distinct factorial/product outputs')
        moduli={r[2] for r in self.range_requests}
        if len(moduli)!=1: raise ValueError('One amplified modulus required')
        N=next(iter(moduli));K=self.amplification_data['K']
        reps=self.aggregate_requests
        total=self.sum(n for n,_,_,_ in reps)
        H=self.add(total,ONE)
        if self.radix_kind=='NH':
            base=self.mul(N,H);q=self.power(base,K)
        elif self.radix_kind=='BH':
            base=self.mul(self.product_data['product'],H);q=self.power(base,K)
        elif self.radix_kind=='N_H':
            base=H;q=self.mul(N,self.power(base,K))
        else: raise ValueError(self.radix_kind)
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
        self.radix_data={'radix':q,'modulus':N,'K':K,'V':self.factorial_radix['numerator'],
            'representative_sum':total,'H':H,'base':base,'kind':self.radix_kind,
            'aggregate_bound_removed':True,'independent_representatives':len(reps),
            'exact_binomials':1,'range_binomials':len(self.range_requests),
            'bootstrap':'V<=BF<B^2<=N<=q; H>each representative'}
        self.amplification_data['unified_factorial_product']=True


def construct(syntax='cantor',horizon_minimum=16):
    if horizon_minimum<12:raise ValueError('Proof requires padded horizon at least 12')
    return rr.construct(syntax,horizon_minimum)


def generate(out,syntax='cantor',horizon_minimum=16,support_cap=96,radix_kind='NH',sparse=False):
    out=Path(out)
    class Target(UnifiedCappedBuilder):
        global_cap=not sparse
        pooled_residue=not sparse
    Target.radix_kind=radix_kind
    old_builder=h.HybridBuilder;old_contract=h.psd.contract
    old_construct,old_names=rr.fc.construct,rr.fc.LOCAL_NAMES
    h.HybridBuilder=Target
    h.psd.contract=lambda equation,support_cap=64:old_contract(equation,support_cap=generate_cap)
    generate_cap=support_cap
    rr.fc.construct,rr.fc.LOCAL_NAMES=construct,rr.LOCAL_NAMES
    try:result=rr.fc.generate(out,syntax,horizon_minimum)
    finally:
        h.HybridBuilder=old_builder;h.psd.contract=old_contract
        rr.fc.construct,rr.fc.LOCAL_NAMES=old_construct,old_names
    b=cap.CappedHybrid.latest
    cap_data={'cap':b.cap_parameters,'aggregate':b.cap_bound_certificate,
        'residue':b.cap_residue_certificate,
        'semantic_frame_atoms':sorted({a for (n,k),m in b.powers.items() for a in (n,k,m)}),
        'seed_count':len(b.seed_indices),
        'theorem':'one indexed cap, aggregate bound, pooled squared index errors' if not sparse else 'one indexed cap, individual bounds and residues'}
    h.write(out/'raw/cap_certificate.json',cap_data)
    meta_path=out/'raw/raw_audit_input.json'
    meta=json.loads(meta_path.read_text());meta['cap_certificate']=cap_data;h.write(meta_path,meta)
    result.update({'common_index_cap':True,'global_cap':not sparse,'pooled_residue':not sparse,
        'unified_factorial_product':True,'self_radix':radix_kind,'budget_R':True,'support_cap':support_cap})
    h.write(out/'SUMMARY.json',result)
    return result

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True)
    p.add_argument('--syntax',choices=['cantor','xx0','xy0'],default='cantor')
    p.add_argument('--horizon-minimum',type=int,default=16)
    p.add_argument('--support-cap',type=int,default=96)
    p.add_argument('--radix-kind',choices=['NH','BH','N_H'],default='NH')
    p.add_argument('--sparse',action='store_true')
    a=p.parse_args();print(json.dumps(generate(a.output,a.syntax,a.horizon_minimum,a.support_cap,a.radix_kind,a.sparse),indent=2))
