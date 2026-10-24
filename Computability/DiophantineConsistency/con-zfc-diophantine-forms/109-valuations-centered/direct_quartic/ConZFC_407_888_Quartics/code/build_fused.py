#!/usr/bin/env python3
"""Fused binomial-divisibility certificates and natural quadratic gates."""
from pathlib import Path
import argparse,json,hashlib
import build as ng
from build import syn,SharedProductPowerBuilder,ONE,ZERO,TWO,write_json
from build import contract,independent_verify,polynomial_and_metrics

class DeferredRangeMixin:
    def __init__(self,*args,**kwargs):
        super().__init__(*args,**kwargs)
        self.range_requests=[]
    def binomial(self,n,k):
        key=(n,k)
        if key not in self.binomials:
            out=self.new('choose'+str(len(self.binomials))+'.output')
            self.binomials[key]=out
            self.macro_log.append({'macro':'binomial','output':out,'n':n,'k':k})
        return self.binomials[key]
    def divisible_binomial(self,n,k,B,label):
        self.range_requests.append((n,k,B,label))
        self.macro_log.append({'macro':'binomial_divisible','n':n,'k':k,'modulus':B,'label':label})
    def finalize_binomials(self):
        if getattr(self,'binomials_finalized',False):raise ValueError('repeated finalization')
        self.binomials_finalized=True
        moduli={r[2] for r in self.range_requests}
        if len(moduli)!=1:raise ValueError('one common range modulus required')
        B=next(iter(moduli))
        upper=list(dict.fromkeys([n for n,k in self.binomials]+[n for n,k,_,_ in self.range_requests]))
        radix_power=self.power(TWO,self.sum(upper))
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
        self.radix_data={'upper_atoms':upper,'radix':q,'radix_multiple':B,
                         'exact_binomials':len(self.binomials),'range_binomials':len(self.range_requests)}

class FusedBuilder(DeferredRangeMixin,ng.NonnegativeBuilder):
    pass

def construct(builder_class=FusedBuilder,pad=True,canonical_index=True):
    b=builder_class(positive_powers=True)
    params={n:b.new(n+('0' if n in ('t','m') else ''),'outer')
            for n in ('t','x','y','M0') if pad}
    if not pad:
        params={n:b.new(n+('0' if n in ('t','m') else ''),'outer') for n in ('t','x','y','m','M0')}
    params['t']=b.add(params['t'],ONE)
    params['m']=params['t'] if pad else b.add(params['m'],ONE)
    t,x,y,m,M0=[params[n] for n in ('t','x','y','m','M0')]
    b.eq(b.power(b.add(m,ONE),t),b.add(M0,ONE),'carrier_power')
    u0,r0,ut=[b.new('endpoint.'+n) for n in ('u0','r0','ut')]
    dt=b.add(b.mul(b.add(t,ONE),y),ONE)
    b.eq(x,b.add(b.add(M0,TWO),b.mul(b.add(y,ONE),u0)),'endpoint.first_quotient')
    b.eq(y,b.sum([M0,r0,TWO]),'endpoint.first_remainder')
    b.eq(x,b.add(ONE,b.mul(dt,ut)),'endpoint.last_quotient')
    bounds={n:m if i<7 else y if i<9 else x for i,n in enumerate(syn.LOCAL_NAMES)}
    encoded={n:b.add(b.new('crt.encoded.'+n),ONE) for n in syn.LOCAL_NAMES}
    C=b.new('crt.encoded_index')
    sourcebytes=(ng.UP/'provenance/upstream/wire_eliminated_source.json').read_bytes()
    source=json.loads(sourcebytes)
    syn.source_pair_calculus=ng.direct_source
    cert=syn.majorant_certificate(source)
    R=b.sum([TWO,t,x,y,m,M0])
    cert['emitted_exponent']=1<<(cert['exponent']-1).bit_length()
    H=syn.fixed_power(b,R,cert['emitted_exponent'])
    T=b.factorial(H);B=b.moduli_product(t,T)
    for n in syn.LOCAL_NAMES:
        b.divisible_binomial(encoded[n],b.add(bounds[n],ONE),B,'crt.range.'+n)
    if canonical_index:
        b.eq(b.add(ONE,b.mul(b.add(C,ONE),T)),B,'crt.canonical_index')
    else:
        qi=b.new('crt.index_quotient')
        b.eq(b.add(ONE,b.mul(b.add(C,ONE),T)),b.mul(B,qi),'crt.index')
    ep,fp=ng.direct_source(b,source,params|encoded,C,False)
    if fp!=ZERO:raise ValueError('expected nonnegative source')
    cq=b.new('crt.nonnegative_quotient')
    b.eq(ep,b.mul(B,cq),'crt.nonnegative_evaluation')
    b.finalize_binomials();b.finalize_power_frame()
    return b,cert,sourcebytes

def generate(out,builder_class=FusedBuilder,pad=True,canonical_index=True,caps=(4,16,64)):
    out=Path(out);out.mkdir(parents=True,exist_ok=True)
    b,cert,src=construct(builder_class,pad,canonical_index)
    eq,poly,metrics=b.export(hashlib.sha256(src).hexdigest(),'fused_range_quartic',True)
    for name,item in [('equation.json',eq),('expanded_polynomial.json',poly),
                      ('majorant_certificate.json',cert),('macro_inventory.json',b.macro_log),
                      ('radix_certificate.json',b.radix_data),
                      ('gate_ledger.json',{'square_difference_gates':b.sqd_ledger,
                        'all_variables':b.variables,'all_rows':b.rows,'gates':b.gates})]:
        write_json(out/name,item)
    counts={'source':metrics}
    for cap in caps:
        target,cc=contract(eq,support_cap=cap,terminal_quadratic=True)
        receipt=independent_verify(eq,target,cc)
        pp,mm=polynomial_and_metrics(target['residuals'],len(target['variables']))
        dest=out/('cap'+str(cap));dest.mkdir(exist_ok=True)
        for name,item in [('equation.json',target),('expanded_polynomial.json',pp),
                          ('elimination_certificate.json',cc),('VERIFICATION.json',receipt)]:write_json(dest/name,item)
        counts[str(cap)]=mm
    counts['features']={'padded_horizon':pad,'canonical_index':canonical_index,
                         'ranges':len(b.range_requests),'exact_binomials':len(b.binomials),
                         'indices':len(b.shared_indices),'bases':len(b.shared_bases)}
    write_json(out/'METRICS.json',counts)
    return counts

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True)
    args=p.parse_args();print(json.dumps(generate(args.output),indent=2))
