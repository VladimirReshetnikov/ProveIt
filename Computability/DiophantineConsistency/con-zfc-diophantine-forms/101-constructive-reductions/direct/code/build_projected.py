#!/usr/bin/env python3
"""Emit projected synchronized ordinary quartics and exact contractions."""
from pathlib import Path
import argparse, json, sys
from hashlib import sha256
HERE=Path(__file__).resolve().parent
UPSTREAM=HERE.parent/'provenance/upstream'
sys.path[:0]=[str(HERE),str(UPSTREAM)]
from build_equation import Builder, ONE, TWO
from shared_product_power import SharedProductPowerBuilder
from synchronized_builder import DeferredBinomialMixin, fixed_power
from projected_source import source_pair_calculus, label_bound_certificate
from affine_contract import contract, independent_verify, polynomial_and_metrics
from verify_synchronized import exact_expansion

LOCAL=('a','b','c','d','S','Sp','u','vq')

def majorant_certificate(source):
    b=Builder(True)
    names=('t','x','y','m','M0')
    atoms={n:b.new(n) for n in names}
    bounds={n:atoms['m'] if i<4 else atoms['y'] if i<6 else atoms['x']
            for i,n in enumerate(LOCAL)}
    ep,fp=source_pair_calculus(b,source,atoms|bounds,atoms['t'])
    total=b.sum([ep,fp,atoms['t'],atoms['x'],atoms['y'],atoms['m'],ONE])
    exponents={a[1]:1 for a in atoms.values()}
    def weight(a):
        return max(0,(a[1]-1).bit_length()) if a[0]=='c' else exponents[a[1]]
    gates=[]
    for (op,a,c),out in b.cache.items():
        e=max(weight(a),weight(c))+1 if op=='add' else weight(a)+weight(c)
        exponents[out[1]]=e
        gates.append({'output':out[1],'operation':op,'left':list(a),
                      'right':list(c),'exponent':e})
    exponent=weight(total)
    return {'schema':'nonnegative_circuit_power_majorant_v1','base':'2+t+x+y+m+M0',
            'inputs':names,'gates':gates,'output':list(total),'exponent':exponent,
            'emitted_exponent':1<<(exponent-1).bit_length(),
            'reason':'R>=2; each input<=R; add uses max+1, product uses sum'}

class ProjectedBuilder(DeferredBinomialMixin,SharedProductPowerBuilder): pass

def construct(source):
    b=ProjectedBuilder(True)
    params={n:b.new(n+('0' if n in ('t','m') else ''),'outer') for n in ('t','x','y','m','M0')}
    params['t']=b.add(params['t'],ONE);params['m']=b.add(params['m'],ONE)
    t,x,y,m,M0=[params[n] for n in ('t','x','y','m','M0')]
    label=label_bound_certificate(Builder)
    label_bound=fixed_power(b,b.add(m,TWO),label['emitted_exponent'])
    b.eq(b.power(b.add(label_bound,ONE),t),b.add(M0,ONE),'carrier_power')
    u0,r0,ut=[b.new('endpoint.'+n) for n in ('u0','r0','ut')]
    dt=b.add(b.mul(b.add(t,ONE),y),ONE)
    b.eq(x,b.add(b.add(M0,TWO),b.mul(b.add(y,ONE),u0)),'endpoint.first_quotient')
    b.eq(y,b.sum([M0,r0,TWO]),'endpoint.first_remainder')
    b.eq(x,b.add(ONE,b.mul(dt,ut)),'endpoint.last_quotient')
    bounds={n:m if i<4 else y if i<6 else x for i,n in enumerate(LOCAL)}
    encoded={n:b.add(b.new('crt.encoded.'+n),ONE) for n in LOCAL}
    C=b.new('crt.encoded_index')
    cert=majorant_certificate(source)
    R=b.sum([TWO,t,x,y,m,M0])
    H=fixed_power(b,R,cert['emitted_exponent'])
    T=b.factorial(H);B=b.moduli_product(t,T)
    for n in LOCAL:
        chosen=b.binomial(encoded[n],b.add(bounds[n],ONE))
        quotient=b.new('crt.range_quotient.'+n)
        b.eq(chosen,b.mul(B,quotient),'crt.factorial_free_range.'+n)
    qi=b.new('crt.index_quotient')
    b.eq(b.add(ONE,b.mul(b.add(C,ONE),T)),b.mul(B,qi),'crt.index')
    ep,fp=source_pair_calculus(b,source,params|encoded,C)
    b.congruent(ep,fp,B,'crt.evaluation')
    b.finalize_binomials();b.finalize_power_frame()
    return b,cert,label

def write(path,data):
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text(json.dumps(data,sort_keys=True,separators=(',',':'))+'\n')

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args();output=args.output
    raw=(UPSTREAM/'wire_eliminated_source.json').read_bytes();source=json.loads(raw)
    b,crt,label=construct(source)
    equation,poly,metrics=b.export(sha256(raw).hexdigest(),'projected_synchronized8',inline_affine=True)
    metrics.update({'binomial_radix_shared':True,'global_power_frame':True,
                    'bounded_local_coordinates':8,'label_bound_exponent':label['emitted_exponent'],
                    'majorant_exponent':crt['exponent'],'emitted_majorant_exponent':crt['emitted_exponent'],
                    'shared_index_auxiliaries':True,'product_index_divisibility':True,
                    'pell_index_certificates':len(b.shared_indices),'distinct_power_bases':len(b.shared_bases)})
    equation['metrics']=metrics
    census={}
    for fname,data in [('equation.json',equation),('expanded_polynomial.json',poly),
                       ('majorant_certificate.json',crt),('label_bound_certificate.json',label),
                       ('macro_inventory.json',b.macro_log)]:write(output/'source'/fname,data)
    exact_expansion(equation,poly);census['source']=metrics
    for cap in (4,16,64):
        target,certificate=contract(equation,support_cap=cap,terminal_quadratic=True)
        receipt=independent_verify(equation,target,certificate)
        polynomial,tm=polynomial_and_metrics(target['residuals'],len(target['variables']))
        receipt['expanded_polynomial_audit']=exact_expansion(target,polynomial)
        for fname,data in [('equation.json',target),('expanded_polynomial.json',polynomial),
                           ('elimination_certificate.json',certificate),('VERIFICATION.json',receipt)]:
            write(output/f'cap{cap}'/fname,data)
        census[f'cap{cap}']=tm
    write(output/'CENSUS.json',census)
    print(json.dumps(census,indent=2))
if __name__=='__main__':main()
