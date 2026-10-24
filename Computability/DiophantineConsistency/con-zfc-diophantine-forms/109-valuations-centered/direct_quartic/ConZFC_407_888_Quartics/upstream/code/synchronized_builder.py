#!/usr/bin/env python3
"""Experimental synchronized compiler; all output data are ordinary quartics."""
from __future__ import annotations
import argparse
from hashlib import sha256
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
UPSTREAM = HERE.parent / 'provenance' / 'upstream'
sys.path.insert(0, str(UPSTREAM))
from build_equation import Builder, const, ZERO, ONE, TWO, require, write_json
from direct_source import source_pair_calculus

LOCAL_NAMES = ('p','q','v','a','b','c','d','S','Sp','u','vq')

def majorant_certificate(source):
    """A checkable exponent majorant for the actual nonnegative source DAG."""
    b = Builder(True)
    names = ('t','x','y','m','M0')
    atoms = {n:b.new(n) for n in names}
    bounds = {n: atoms['m'] if i < 7 else atoms['y'] if i < 9 else atoms['x']
              for i,n in enumerate(LOCAL_NAMES)}
    ep,fp = source_pair_calculus(b,source,atoms | bounds,atoms['t'],False)
    # H must dominate both polynomial sides and the index and every bound.
    total = b.sum([ep,fp,atoms['t'],atoms['x'],atoms['y'],atoms['m'],ONE])
    exponents = {a[1]:1 for a in atoms.values()}
    def weight(a):
        return max(0,(a[1]-1).bit_length()) if a[0]=='c' else exponents[a[1]]
    gates=[]
    for (op,a,c),out in b.cache.items():
        e = max(weight(a),weight(c))+1 if op=='add' else weight(a)+weight(c)
        exponents[out[1]]=e
        gates.append({'output':out[1],'operation':op,'left':list(a),
                      'right':list(c),'exponent':e})
    return {'schema':'nonnegative_circuit_power_majorant_v1',
            'base':'2+t+x+y+m+M0','inputs':names,'gates':gates,
            'output':list(total),'exponent':weight(total),
            'reason':'R>=2 and every input<=R; add uses max+1, product uses sum'}

class DeferredBinomialMixin:
    def binomial(self,n,k):
        key=(n,k)
        if key in self.binomials:
            return self.binomials[key]
        out=self.new(f'choose{len(self.binomials)}.output')
        self.binomials[key]=out
        self.macro_log.append({'macro':'binomial','output':out,'n':n,'k':k})
        return out

    def finalize_binomials(self):
        require(not getattr(self,'binomials_finalized',False),'binomials finalized twice')
        self.binomials_finalized=True
        upper=list(dict.fromkeys(n for n,k in self.binomials))
        exponent=self.sum(upper)
        q=self.add(self.power(TWO,exponent),ONE)
        for i,((n,k),out) in enumerate(self.binomials.items()):
            tag=f'choose{i}'
            numerator=self.power(self.add(q,ONE),n)
            denominator=self.power(q,k)
            h,r,rs,os=[self.new(tag+'.'+s) for s in ('high','remainder','rslack','oslack')]
            quotient=self.add(self.mul(q,h),out)
            self.eq(numerator,self.add(self.mul(denominator,quotient),r),tag+'.digit_division')
            self.eq(denominator,self.sum([r,rs,ONE]),tag+'.remainder_bound')
            self.eq(q,self.sum([out,os,ONE]),tag+'.digit_bound')
        self.shared_binomial_data={'upper_atoms':[list(a) for a in upper],
                                   'radix_atom':list(q),'exponent_atom':list(exponent),
                                   'binomials':len(self.binomials)}

def fixed_power(b,x,n):
    require(n>0,'positive fixed exponent required')
    out=ONE
    for digit in bin(n)[2:]:
        out=b.square(out)
        if digit=='1':
            out=b.mul(out,x)
    return out

def construct(builder_class,source):
    b=builder_class(positive_powers=True)
    params={n:b.new(n+('0' if n in ('t','m') else ''),'outer')
            for n in ('t','x','y','m','M0')}
    params['t']=b.add(params['t'],ONE)
    params['m']=b.add(params['m'],ONE)
    t,x,y,m,M0=[params[n] for n in ('t','x','y','m','M0')]
    b.eq(b.power(b.add(m,ONE),t),b.add(M0,ONE),'carrier_power')
    u0,r0,ut=[b.new('endpoint.'+n) for n in ('u0','r0','ut')]
    dt=b.add(b.mul(b.add(t,ONE),y),ONE)
    b.eq(x,b.add(b.add(M0,TWO),b.mul(b.add(y,ONE),u0)),'endpoint.first_quotient')
    b.eq(y,b.sum([M0,r0,TWO]),'endpoint.first_remainder')
    b.eq(x,b.add(ONE,b.mul(dt,ut)),'endpoint.last_quotient')
    bounds={n:m if i<7 else y if i<9 else x for i,n in enumerate(LOCAL_NAMES)}
    encoded={n:b.add(b.new('crt.encoded.'+n),ONE) for n in LOCAL_NAMES}
    C=b.new('crt.encoded_index')
    cert=majorant_certificate(source)
    R=b.sum([TWO,t,x,y,m,M0])
    # Any larger bound is valid.  A power-of-two exponent takes only squares.
    cert['emitted_exponent']=1 << (cert['exponent']-1).bit_length()
    H=fixed_power(b,R,cert['emitted_exponent'])
    T=b.factorial(H)
    B=b.moduli_product(t,T)
    for n in LOCAL_NAMES:
        chosen=b.binomial(encoded[n],b.add(bounds[n],ONE))
        quotient=b.new('crt.range_quotient.'+n)
        b.eq(chosen,b.mul(B,quotient),'crt.factorial_free_range.'+n)
    qi=b.new('crt.index_quotient')
    b.eq(b.add(ONE,b.mul(b.add(C,ONE),T)),b.mul(B,qi),'crt.index')
    ep,fp=source_pair_calculus(b,source,params|encoded,C,False)
    b.congruent(ep,fp,B,'crt.evaluation')
    if hasattr(b,'finalize_binomials'):
        b.finalize_binomials()
    if hasattr(b,'finalize_power_frame'):
        b.finalize_power_frame()
    return b,cert

def main():
    global source_pair_calculus
    parser=argparse.ArgumentParser()
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--independent-powers',action='store_true')
    parser.add_argument('--independent-binomials',action='store_true')
    parser.add_argument('--shared-index',action='store_true')
    parser.add_argument('--product-index',action='store_true')
    parser.add_argument('--factored-source',action='store_true')
    args=parser.parse_args()
    if args.factored_source:
        from direct_source_factored import source_pair_calculus
    if args.independent_powers:
        power_class=Builder
    else:
        if args.product_index:
            from shared_product_power import SharedProductPowerBuilder
            power_class=SharedProductPowerBuilder
        elif args.shared_index:
            from shared_index_power import SharedIndexPowerBuilder
            power_class=SharedIndexPowerBuilder
        else:
            from shared_power import SharedPowerBuilder
            power_class=SharedPowerBuilder
    if args.independent_binomials:
        builder_class=power_class
    else:
        class SynchronizedBuilder(DeferredBinomialMixin,power_class):
            pass
        builder_class=SynchronizedBuilder
    source_bytes=(UPSTREAM/'wire_eliminated_source.json').read_bytes()
    b,cert=construct(builder_class,json.loads(source_bytes))
    equation,polynomial,metrics=b.export(sha256(source_bytes).hexdigest(),
        'synchronized11',inline_affine=True)
    metrics['binomial_radix_shared']=not args.independent_binomials
    metrics['global_power_frame']=not args.independent_powers
    metrics['majorant_exponent']=cert['exponent']
    metrics['emitted_majorant_exponent']=cert['emitted_exponent']
    metrics['bounded_local_coordinates']=11
    metrics['shared_index_auxiliaries']=args.shared_index or args.product_index
    metrics['product_index_divisibility']=args.product_index
    metrics['factored_source']=args.factored_source
    if hasattr(b,'shared_indices'): metrics['pell_index_certificates']=len(b.shared_indices)
    if hasattr(b,'shared_bases'): metrics['distinct_power_bases']=len(b.shared_bases)
    args.output.mkdir(parents=True,exist_ok=True)
    hashes={name:write_json(args.output/name,data) for name,data in
            [('equation.json',equation),('expanded_polynomial.json',polynomial),
             ('majorant_certificate.json',cert),('macro_inventory.json',b.macro_log)]}
    write_json(args.output/'BUILD.json',{'metrics':metrics,'sha256':hashes,
          'builder_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),
          'source_sha256':sha256(source_bytes).hexdigest()})
    print(json.dumps(metrics,indent=2))

if __name__=='__main__': main()
