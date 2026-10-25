#!/usr/bin/env python3
"""Self-sized radix with K=x and strict beta quotient ranges."""
from pathlib import Path
from math import factorial
import argparse,json
from build_self_radix import SelfRadixBuilder,BASE,old
h,bp,fc,ONE,TWO,const,majorants = old.h,old.bp,old.fc,old.ONE,old.TWO,old.const,old.majorants
source_and_labels=old.source_and_labels
LOCAL_NAMES=('a','b','c','d','S','Sp','u','vq')

def construct(syntax='cantor', horizon_minimum=16):
    bp.ng.direct_source=h.CANTOR_SOURCE
    if syntax!='cantor':
        h.shell_source.SHELL_SCHEME=syntax
        bp.ng.direct_source=h.shell_source.direct_source
    b=h.HybridBuilder(positive_powers=True)
    src=(bp.ng.UP/'provenance/upstream/wire_eliminated_source.json').read_bytes()
    source=json.loads(src)
    t=b.add(b.new('t0','outer'),const(horizon_minimum))
    x,y=[b.new(n,'outer') for n in ('x','y')]
    F=b.factorial(t)
    params={'t':t,'x':x,'y':y,'F':F}
    u0,r0,ut=[b.new('endpoint.'+n) for n in ('u0','r0','ut')]
    dt=b.add(b.mul(b.add(t,ONE),y),ONE)
    b.eq(x,b.sum([F,ONE,b.mul(b.add(y,ONE),u0)]),'endpoint.first_quotient')
    b.eq(y,b.sum([F,r0,ONE]),'endpoint.first_remainder')
    b.eq(x,b.add(ONE,b.mul(dt,ut)),'endpoint.last_quotient')
    bounds={n:t if i<4 else y if i<6 else x for i,n in enumerate(LOCAL_NAMES)}
    encoded={n:b.add(b.new('crt.encoded.'+n),ONE) for n in LOCAL_NAMES}
    C=b.add(b.new('crt.encoded_index_minus_one'),ONE)
    bc=majorants(source)
    E=bc['emitted_exponent'];ell=bc['derived_label_majorant']['emitted_exponent']
    Fmin=factorial(horizon_minimum);a=Fmin.bit_length()-1
    if not (a*E<2**a and 2*E<=2**a and 2*Fmin>=3*ell*(horizon_minimum+1)):
        raise ValueError('derived label budget requires reproof')
    R=b.sum([TWO,t,x,y,F]);K=x
    B=b.moduli_product(t,F);T=b.product_data['square'];N=b.power(B,K)
    b.amplification_data={'B':B,'K':K,'N':N,'F':F,'t':t,'R':R,'index':C,
        'local_degree_bound':E,'label_degree_bound':ell,'budget':'x',
        'horizon_minimum':horizon_minimum,'index_precision':'K','completeness_precision':'2K',
        'floor_exponent':a,'factorial_floor':Fmin,'derived_label_radix_budget':'ell*(t+1)<=2F/3<F<x=K',
        'source_bound_budget':'R<2x; x>2^32; (2x)^E<2^x=2^K',
        'strict_beta_quotient_ranges':True}
    for n in LOCAL_NAMES:
        b.divisible_binomial(encoded[n],x if n in ('u','vq') else b.add(bounds[n],ONE),N,'crt.range.'+n)
    b.divisible_binomial(C,t,N,'crt.range.index')
    # Freeze only the nine independently chosen CRT representatives.
    b.aggregate_requests=list(b.range_requests)
    iq=b.new('crt.index_quotient')
    b.eq(b.sum([C,T,ONE]),b.mul(B,iq),'crt.reciprocal_index_congruence')
    value,labels=source_and_labels(b,source,params|encoded,C)
    b.divisible_binomial(labels,b.add(t,ONE),N,'crt.range.derived_label_sum')
    b.amplification_data['derived_label_sum']=labels
    quotient=b.new('crt.nonnegative_quotient')
    b.eq(value,b.mul(N,quotient),'crt.nonnegative_evaluation')
    b.finalize_binomials();b.finalize_power_frame()
    return b,src,bc


def generate(out,syntax='cantor',horizon_minimum=16,builder=SelfRadixBuilder):
    prev_builder=h.HybridBuilder
    prev_construct,prev_names=fc.construct,fc.LOCAL_NAMES
    h.HybridBuilder=builder
    fc.construct,fc.LOCAL_NAMES=construct,LOCAL_NAMES
    try: result=fc.generate(out,syntax,horizon_minimum)
    finally:
        h.HybridBuilder=prev_builder
        fc.construct,fc.LOCAL_NAMES=prev_construct,prev_names
    result['self_sized_radix']=True
    result['amplification_budget']='R'
    h.write(Path(out)/'SUMMARY.json',result)
    return result

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True)
    p.add_argument('--syntax',choices=['cantor','xx0','xy0'],default='cantor')
    a=p.parse_args();print(json.dumps(generate(a.output,a.syntax),indent=2))
