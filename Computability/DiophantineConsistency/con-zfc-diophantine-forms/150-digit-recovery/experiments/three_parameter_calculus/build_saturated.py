#!/usr/bin/env python3
"""Three-parameter calculus with a modular inverse for the bundle guard.

Research constructor. All semantic changes are concentrated in this module.
Inherited arithmetic is a frozen, ordinary-proof-calibrated graph compiler.
"""
from pathlib import Path
from math import factorial
import argparse
import hashlib
import json
import sys
import os
import importlib.util

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
PARENT = Path(os.environ['PROVEIT_NATURAL_PARENT']).resolve()
pin = json.loads((HERE / 'PARENT_PIN.json').read_text())
for name, expected in pin['files'].items():
    actual = hashlib.sha256((PARENT / name).read_bytes()).hexdigest()
    if actual != expected:
        raise ValueError('Pinned inherited source differs: '+name)
sys.path.insert(0, str(PARENT / 'portable/source/custom'))
import build_strict_budget as rr
import build_modular_factorial as mf
spec = importlib.util.spec_from_file_location('inherited_natural_builder', PARENT / 'build.py')
ib = importlib.util.module_from_spec(spec)
spec.loader.exec_module(ib)
h, bp = rr.h, rr.bp
ONE, TWO, const = rr.ONE, rr.TWO, rr.const
LOCAL_NAMES = ('a','b','c','S','Sp','u','vq')

SOURCE_SPEC = {
    'schema':'three_parameter_calculus_and_modular_saturation_v1',
    'constructors':{'I':'2*(a+b)*(a+b+1)+4*b','A':'I(a,b)+2',
                    'M':'I(a,b)+1','Eq':'I(a,b)+3','Not':'I(a,1)'},
    'replacement':{'old':'((c->d)->a)->((a->c)->(b->c))',
                   'new':['a->(b->a)',
                          '(a->(b->c))->((a->b)->(a->c))',
                          '((a->b)->a)->a']},
    'local_names':list(LOCAL_NAMES),
    'bundle_guard':'c!=a and c!=b',
    'saturation':'U*D*E = U + N*q',
    'D':'(c-a)^2*(c-b)^2',
    'U':'product of squared residuals of every non-bundle branch',
    'E_domain':'natural, unbounded; no range or Pell index certificate',
}
SOURCE_BYTES=(json.dumps(SOURCE_SPEC,sort_keys=True,separators=(',',':'))+'\n').encode()

def codes(b,env):
    add,mul=b.add,b.mul
    def I(x,y):
        s=add(x,y)
        return add(mul(TWO,mul(s,add(s,ONE))),mul(const(4),y))
    def A(x,y):return add(I(x,y),TWO)
    def M(x,y):return add(I(x,y),ONE)
    def Eq(x,y):return add(I(x,y),const(3))
    def Not(x):return I(x,ONE)
    def Ex(x,y):return Not(A(x,Not(y)))
    def req(x,k,m):return A(x,I(m,Not(A(x,I(m,Not(M(x,k)))))))
    def clos(x,y,k,m):
        subset=A(k,I(M(k,x),M(k,y)))
        tail=I(subset,req(y,k,m))
        tail=Not(A(x,tail))
        tail=Not(A(x,I(m,tail)))
        return A(y,I(M(y,k),tail))
    def bundle(x,y,z):
        nks=A(z,I(clos(x,y,z,z),Not(req(y,z,z))))
        rv=I(M(x,y),A(z,M(x,y)))
        return Not(I(rv,nks))
    a,z,c=[env[k] for k in ('a','b','c')]
    base=[Ex(a,Eq(a,z)),I(A(a,I(z,c)),I(A(a,z),A(a,c))),
          I(Eq(a,z),I(M(c,a),M(c,z))),I(A(a,A(z,c)),A(z,A(a,c))),
          I(Eq(c,a),I(M(c,z),M(a,z))),I(Ex(a,A(a,z)),z),
          I(Eq(c,a),I(Eq(c,z),A(M(a,z),Eq(a,z))))]
    replacement=[I(a,I(z,a)),
                 I(I(a,I(z,c)),I(I(a,z),I(a,c))),
                 I(I(I(a,z),a),a)]
    return base+replacement+[bundle(a,z,c)],I,A

def local_source(b,env,index):
    cs,I,A=codes(b,env)
    a,z,c=[env[n] for n in ('a','b','c')]
    S,Sp,F=[env[n] for n in ('S','Sp','F')]
    add,mul,sd=b.add,b.mul,b.sqdiff
    SpF=mul(Sp,F)
    ordinary=[sd(Sp,S)]+[sd(add(Sp,mul(SpF,code)),S) for code in cs[:-1]]
    def weight(v):return add(ONE,mul(v,F))
    implication,universal=I(a,z),A(a,z)
    mp=sd(mul(Sp,weight(z)),b.product([S,weight(a),weight(implication)]))
    gen=sd(mul(Sp,weight(universal)),mul(S,weight(z)))
    U=b.product(ordinary+[mp,gen])
    V=sd(add(Sp,mul(SpF,cs[-1])),S)
    D=mul(sd(c,a),sd(c,z))
    den=add(mul(add(index,ONE),env['y']),ONE)
    beta=[sd(env['x'],add(S,mul(den,env['u']))),
          sd(env['x'],add(Sp,mul(add(den,env['y']),env['vq'])))]
    value=b.sum([mul(U,V)]+beta)
    labels=b.sum(cs+[a,z,implication,universal,ONE])
    return value,labels,U,D

def majorants():
    b=bp.UpperBuilder(True)
    atoms={n:b.new(n) for n in ('t','x','y','F')}
    bounds={n:atoms['t'] if n in ('a','b','c') else atoms['y'] if n in ('S','Sp') else atoms['x'] for n in LOCAL_NAMES}
    value,labels,U,D=local_source(b,atoms|bounds,atoms['t'])
    out=b.sum([value,labels,U,D,atoms['t'],atoms['x'],atoms['y'],ONE])
    cert=bp.bound_certificate(b,atoms,out)
    cert['base']='2+t+x+y+F'
    cert['emitted_exponent']=max(4,1 << (cert['exponent']-1).bit_length())
    cert['squared_difference_majorization']='(u-v)^2 <= (U+V)^2'
    lb=bp.Builder(True); n=lb.new('n')
    cs,I,A=codes(lb,{name:n for name in ('a','b','c')})
    jj=lb.sum(cs+[n,n,I(n,n),A(n,n),ONE])
    lc=bp.bound_certificate(lb,{'n':n},jj)
    lc['base']='n+1';lc['emitted_exponent']=1 << (lc['exponent']-1).bit_length()
    cert['derived_label_majorant']=lc
    return cert

def construct(syntax='cantor',horizon_minimum=12):
    if syntax!='cantor':raise ValueError('Only the audited Cantor constructor is supported')
    b=h.HybridBuilder(positive_powers=True)
    t=b.add(b.new('t0','outer'),const(horizon_minimum))
    x,y=[b.new(n,'outer') for n in ('x','y')]
    F=b.factorial(t)
    params={'t':t,'x':x,'y':y,'F':F}
    u0,r0,ut=[b.new('endpoint.'+n) for n in ('u0','r0','ut')]
    dt=b.add(b.mul(b.add(t,ONE),y),ONE)
    b.eq(x,b.sum([F,ONE,b.mul(b.add(y,ONE),u0)]),'endpoint.first_quotient')
    b.eq(y,b.sum([F,r0,ONE]),'endpoint.first_remainder')
    b.eq(x,b.add(ONE,b.mul(dt,ut)),'endpoint.last_quotient')
    bounds={n:t if n in ('a','b','c') else y if n in ('S','Sp') else x for n in LOCAL_NAMES}
    encoded={n:b.add(b.new('crt.encoded.'+n),ONE) for n in LOCAL_NAMES}
    C=b.add(b.new('crt.encoded_index_minus_one'),ONE)
    bc=majorants();E=bc['emitted_exponent'];ell=bc['derived_label_majorant']['emitted_exponent']
    Fmin=factorial(horizon_minimum);a=Fmin.bit_length()-1
    if not(a*E<2**a and 2*E<=2**a and 2*Fmin>=3*ell*(horizon_minimum+1)):
        raise ValueError(f'New majorants require a larger horizon: E={E}, ell={ell}, a={a}')
    R=b.sum([TWO,t,x,y,F]);K=x
    B=b.moduli_product(t,F);T=b.product_data['square'];N=b.power(B,K)
    b.amplification_data={'B':B,'K':K,'N':N,'F':F,'t':t,'R':R,'index':C,
        'local_degree_bound':E,'label_degree_bound':ell,'budget':'x',
        'horizon_minimum':horizon_minimum,'index_precision':'K','completeness_precision':'2K',
        'floor_exponent':a,'factorial_floor':Fmin,'derived_label_radix_budget':'ell*(t+1)<=2F/3<F<x=K',
        'source_bound_budget':'R<2x; x>2^32; (2x)^E<2^x=2^K',
        'strict_beta_quotient_ranges':True,'three_parameter_calculus':True}
    for n in LOCAL_NAMES:
        b.divisible_binomial(encoded[n],x if n in ('u','vq') else b.add(bounds[n],ONE),N,'crt.range.'+n)
    b.divisible_binomial(C,t,N,'crt.range.index')
    b.aggregate_requests=list(b.range_requests)
    iq=b.new('crt.index_quotient')
    b.eq(b.add(C,ONE),b.add(T,b.mul(B,iq)),'crt.reciprocal_index_congruence')
    value,labels,U,D=local_source(b,params|encoded,C)
    b.divisible_binomial(labels,b.add(t,ONE),N,'crt.range.derived_label_sum')
    b.amplification_data['derived_label_sum']=labels
    quotient=b.new('crt.nonnegative_quotient')
    b.eq(value,b.mul(N,quotient),'crt.nonnegative_evaluation')
    inverse=b.new('crt.guard_inverse');satq=b.new('crt.guard_quotient')
    b.eq(b.product([U,D,inverse]),b.add(U,b.mul(N,satq)),'crt.bundle_guard_saturation')
    b.amplification_data['saturation']={'U':U,'D':D,'inverse':inverse,'quotient':satq,
        'inverse_bounded':False,'equation':'U*D*inverse=U+N*quotient'}
    b.finalize_binomials();b.finalize_power_frame()
    b.radix_data['completeness_lift']='encoded a increased by 2*N^2 and encoded b increased by N^2; encoded c stays in (0,N^2]'
    b.radix_data['saturation_nonnegative_quotient']='these lifts force global D>=1; take the inverse representative >=1'
    return b,SOURCE_BYTES,bc

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--support-cap',type=int,default=48);ap.add_argument('--horizon',type=int,default=12)
    args=ap.parse_args()
    rr.construct=construct;mf.dl.LOCAL_NAMES=LOCAL_NAMES
    result=ib.generate(args.output,args.support_cap,'consecutive',args.horizon)
    (args.output/'source_spec.json').write_bytes(SOURCE_BYTES)
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
