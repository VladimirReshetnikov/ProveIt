#!/usr/bin/env python3
"""Nine-column C222 compiler with a polynomial factorial bootstrap."""
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
from hybrid_source import source_pair_calculus

LOCAL_NAMES = ('v','a','b','c','d','S','Sp','u','vq')

def majorant_certificate(source):
    """A checkable exponent majorant for the actual nonnegative source DAG."""
    b = Builder(True)
    names = ('t','x','y','m','M0')
    atoms = {n:b.new(n) for n in names}
    bounds = {n: atoms['m'] if i < 5 else atoms['y'] if i < 7 else atoms['x']
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
    mm=b.mul(const(2),m)
    label_bound=b.sum([b.mul(TWO,b.mul(mm,b.add(mm,ONE))),b.mul(const(4),m),TWO])
    b.eq(b.power(b.add(label_bound,ONE),t),b.add(M0,ONE),'carrier_power')
    u0,r0,ut=[b.new('endpoint.'+n) for n in ('u0','r0','ut')]
    dt=b.add(b.mul(b.add(t,ONE),y),ONE)
    b.eq(x,b.add(b.add(M0,TWO),b.mul(b.add(y,ONE),u0)),'endpoint.first_quotient')
    b.eq(y,b.sum([M0,r0,TWO]),'endpoint.first_remainder')
    b.eq(x,b.add(ONE,b.mul(dt,ut)),'endpoint.last_quotient')
    bounds={n:m if i<5 else y if i<7 else x for i,n in enumerate(LOCAL_NAMES)}
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
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--radius',choices=['square','linear'],default='square')
    args=parser.parse_args()
    from bootstrap_factorial import BootstrapFactorialBuilder
    class CompleteBuilder(DeferredBinomialMixin,BootstrapFactorialBuilder):
        radius_mode=args.radius
    source_bytes=(UPSTREAM/'wire_eliminated_source.json').read_bytes()
    b,cert=construct(CompleteBuilder,json.loads(source_bytes))
    equation,polynomial,metrics=b.export(sha256(source_bytes).hexdigest(),
        ('hybrid9_squared_factorial_bootstrap' if args.radius=='square' else 'hybrid9_bootstrap_factorial'),inline_affine=True)
    metrics.update({'binomial_radix_shared':True,'global_power_frame':True,
        'majorant_exponent':cert['exponent'],'emitted_majorant_exponent':cert['emitted_exponent'],
        'bounded_local_coordinates':9,'shared_index_auxiliaries':True,
        'product_index_divisibility':True,'factored_source':True,
        'pell_index_certificates':len(b.shared_indices),'distinct_power_bases':len(b.shared_bases),
        'shifted_indices':0,'shared_factorial_radius':True,'bootstrap_factorial_radius':True})
    args.output.mkdir(parents=True,exist_ok=True)
    hashes={name:write_json(args.output/name,data) for name,data in
            [('equation.json',equation),('expanded_polynomial.json',polynomial),
             ('majorant_certificate.json',cert),('macro_inventory.json',b.macro_log),
             ('index_shift_certificate.json',[]),('factorial_radius_certificate.json',b.factorial_radius_log)]}
    write_json(args.output/'BUILD.json',{'metrics':metrics,'sha256':hashes,
          'builder_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),
          'source_sha256':sha256(source_bytes).hexdigest()})
    print(json.dumps(metrics,indent=2))

if __name__=='__main__': main()
