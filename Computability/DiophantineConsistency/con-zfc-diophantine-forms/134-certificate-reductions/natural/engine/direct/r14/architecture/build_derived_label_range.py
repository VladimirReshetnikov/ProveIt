#!/usr/bin/env python3
"""Bound all source labels by one derived binomial range, not a local slack.

The aggregate representative bound EXCLUDES the derived label expression.
Its separate polynomial-degree carry bound is checked in the emitted recipe.
"""
from pathlib import Path
from math import factorial
import argparse, json
import build_factorial_carrier as fc
h, bp, ONE, TWO, const = fc.h, fc.bp, fc.ONE, fc.TWO, fc.const
LOCAL_NAMES = ('a', 'b', 'c', 'd', 'S', 'Sp', 'u', 'vq')

def source_and_labels(b, source, env, index):
    data = bp.codes(b, source, env)
    cs, I, A = data['codes'], data['I'], data['A']
    a, z, c, d = [env[s] for s in ('a', 'b', 'c', 'd')]
    add, mul, sd, sq = b.add, b.mul, b.sqdiff, b.square
    S, Sp, F = env['S'], env['Sp'], env['F']
    SpF = mul(Sp, F)
    ordinary = [sd(Sp,S)] + [sd(add(Sp,mul(SpF,code)),S) for code in cs[:-1]]
    guard = sd(mul(sd(c,a),sd(c,z)),sq(add(d,ONE)))
    bundle = add(sd(add(Sp,mul(SpF,cs[-1])),S),guard)
    def weight(v): return add(ONE,mul(v,F))
    implication, universal = I(a,z), A(a,z)
    mp = sd(mul(Sp,weight(z)),b.product([S,weight(a),weight(implication)]))
    gen = sd(mul(Sp,weight(universal)),mul(S,weight(z)))
    horn = b.product(ordinary+[bundle,mp,gen])
    den = add(mul(add(index,ONE),env['y']),ONE)
    beta = [sd(env['x'],add(S,mul(den,env['u']))),
            sd(env['x'],add(Sp,mul(add(den,env['y']),env['vq'])))]
    labels = b.sum(cs+[a,z,implication,universal,ONE])
    return b.sum([horn]+beta), labels

def majorants(source):
    b = bp.UpperBuilder(True)
    atoms = {n:b.new(n) for n in ('t','x','y','F')}
    bounds = {n:atoms['t'] if i<4 else atoms['y'] if i<6 else atoms['x']
              for i,n in enumerate(LOCAL_NAMES)}
    value, labels = source_and_labels(b,source,atoms|bounds,atoms['t'])
    out = b.sum([value,labels,atoms['t'],atoms['x'],atoms['y'],ONE])
    cert = bp.bound_certificate(b,atoms,out)
    cert['base'] = '2+t+x+y+F'
    cert['emitted_exponent'] = max(4,1 << (cert['exponent']-1).bit_length())
    cert['squared_difference_majorization'] = '(u-v)^2 <= (U+V)^2'
    # A distinct literal certificate for J on arbitrary encoded inputs.
    lb = bp.Builder(True)
    n = lb.new('n')
    dd = bp.codes(lb,source,{name:n for name in ('a','b','c','d')})
    jj = lb.sum(dd['codes']+[n,n,dd['I'](n,n),dd['A'](n,n),ONE])
    labelcert = bp.bound_certificate(lb,{'n':n},jj)
    labelcert['base'] = 'n+1'
    labelcert['emitted_exponent'] = 1 << (labelcert['exponent']-1).bit_length()
    cert['derived_label_majorant'] = labelcert
    return cert

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
    R=b.sum([TWO,t,x,y,F]);K=b.mul(TWO,R)
    B=b.moduli_product(t,F);T=b.product_data['square'];N=b.power(B,K)
    b.amplification_data={'B':B,'K':K,'N':N,'F':F,'t':t,'R':R,'index':C,
        'local_degree_bound':E,'label_degree_bound':ell,'budget':'2R',
        'horizon_minimum':horizon_minimum,'index_precision':'K','completeness_precision':'2K',
        'floor_exponent':a,'factorial_floor':Fmin,'derived_label_radix_budget':'3*ell*(t+1)<=2F<=K'}
    for n in LOCAL_NAMES:
        b.divisible_binomial(encoded[n],b.add(bounds[n],ONE),N,'crt.range.'+n)
    b.divisible_binomial(C,t,N,'crt.range.index')
    # Freeze only the nine independently chosen CRT representatives.
    b.aggregate_requests=list(b.range_requests)
    iq=b.new('crt.index_quotient')
    b.eq(b.add(C,ONE),b.add(T,b.mul(B,iq)),'crt.reciprocal_index_congruence')
    value,labels=source_and_labels(b,source,params|encoded,C)
    b.divisible_binomial(labels,b.add(t,ONE),N,'crt.range.derived_label_sum')
    b.amplification_data['derived_label_sum']=labels
    quotient=b.new('crt.nonnegative_quotient')
    b.eq(value,b.mul(N,quotient),'crt.nonnegative_evaluation')
    b.finalize_binomials();b.finalize_power_frame()
    return b,src,bc

def generate(out,syntax='cantor',horizon_minimum=16):
    # Reuse only the output/contraction routine, not its source constructor.
    old_construct,old_names=fc.construct,fc.LOCAL_NAMES
    fc.construct=construct
    fc.LOCAL_NAMES=LOCAL_NAMES
    try:
        result=fc.generate(out,syntax,horizon_minimum)
    finally:
        fc.construct,fc.LOCAL_NAMES=old_construct,old_names
    result['derived_label_range']=True
    h.write(Path(out)/'SUMMARY.json',result)
    return result

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True)
    p.add_argument('--syntax',choices=['cantor','xx0','xy0'],default='cantor')
    p.add_argument('--horizon-minimum',type=int,default=16)
    a=p.parse_args();print(json.dumps(generate(a.output,a.syntax,a.horizon_minimum),indent=2))
