#!/usr/bin/env python3
"""Odd centered factorial graph, composed with the pinned direct407 source.

This file emits literal quartics.  The unbounded new graph theorem is proved
in centered_factorial_proof.md; inherited interfaces remain explicit.
"""
from pathlib import Path
import argparse, hashlib, json, sys, importlib.util

HERE=Path(__file__).resolve().parent
UP=HERE/'ConZFC_407_888_Quartics'
sys.path.insert(0,str(UP/'code'))
import build_projected as bp
from build_equation import ONE, TWO, write_json


class CenteredBuilder(bp.AdditiveReusedRadixBuilder):
    def __init__(self, **kw):
        super().__init__(**kw)
        self.odd_halves={}
        self.centered_factorials=[]

    def factorial(self,n):
        if n in self.factorials:return self.factorials[n]
        if n not in self.odd_halves:raise ValueError('factorial input not structurally odd')
        half=self.odd_halves[n]
        tag='centered_factorial'+str(len(self.factorials))
        f=self.new(tag+'.output')
        self.factorials[n]=f
        c=self.binomial(self.add(f,n),n)
        numerator=self.power(self.sum([f,half,ONE]),n)
        r,s=[self.new(tag+'.'+name) for name in ('remainder','slack')]
        self.eq(numerator,self.add(self.mul(c,f),r),tag+'.floor')
        self.eq(c,self.sum([r,s,ONE]),tag+'.remainder_bound')
        record={'input':n,'half':half,'output':f,'binomial':c,'numerator':numerator,
                'remainder':r,'slack':s}
        self.centered_factorials.append(record)
        self.macro_log.append({'macro':'odd_centered_factorial',**record})
        return f

    def finalize_binomials(self):
        first=self.centered_factorials[0]
        self.factorial_radix={'H':first['input'],'factorial':first['output'],
            'numerator':self.sum(r['numerator'] for r in self.centered_factorials),
            'factorial_numerators':[r['numerator'] for r in self.centered_factorials],
            'method':'sum_of_odd_centered_factorial_numerators'}
        return super().finalize_binomials()


def construct():
    b=CenteredBuilder(positive_powers=True)
    src=(bp.ng.UP/'provenance/upstream/wire_eliminated_source.json').read_bytes()
    source=json.loads(src)
    params={n:b.new(n+('0' if n=='t' else ''),'outer') for n in ('t','x','y','M0')}
    t0=params['t'];params['t']=b.add(b.mul(TWO,t0),ONE)
    t,x,y,M0=[params[n] for n in ('t','x','y','M0')]
    b.odd_halves[t]=t0
    labelcert=bp.label_majorant(source)
    basepower=b.power(b.add(t,ONE),t)
    carrier=bp.ng.syn.fixed_power(b,basepower,labelcert['carrier_exponent'])
    b.eq(carrier,b.add(M0,ONE),'projected.carrier')
    u0,r0,ut=[b.new('endpoint.'+n) for n in ('u0','r0','ut')]
    dt=b.add(b.mul(b.add(t,ONE),y),ONE)
    b.eq(x,b.add(b.add(M0,TWO),b.mul(b.add(y,ONE),u0)),'endpoint.first_quotient')
    b.eq(y,b.sum([M0,r0,TWO]),'endpoint.first_remainder')
    b.eq(x,b.add(ONE,b.mul(dt,ut)),'endpoint.last_quotient')
    bounds={n:t if i<4 else y if i<6 else x for i,n in enumerate(bp.LOCAL_NAMES)}
    encoded={n:b.add(b.new('crt.encoded.'+n),ONE) for n in bp.LOCAL_NAMES}
    C=b.new('crt.encoded_index')
    boundcert=bp.local_majorant(source)
    R=b.sum([TWO,t,x,y,M0])
    Hhalf=bp.ng.syn.fixed_power(b,R,boundcert['emitted_exponent'])
    H=b.add(b.mul(TWO,Hhalf),ONE)
    b.odd_halves[H]=Hhalf
    T=b.factorial(H);B=b.moduli_product(t,T)
    for n in bp.LOCAL_NAMES:b.divisible_binomial(encoded[n],b.add(bounds[n],ONE),B,'crt.range.'+n)
    b.eq(b.add(ONE,b.mul(b.add(C,ONE),T)),B,'crt.canonical_index')
    value=bp.projected_source(b,source,params|encoded,C)
    q=b.new('crt.nonnegative_quotient')
    b.eq(value,b.mul(B,q),'crt.nonnegative_evaluation')
    b.finalize_binomials();b.finalize_power_frame()
    return b,src,labelcert,boundcert


def generate(out):
    out=Path(out);out.mkdir(parents=True,exist_ok=True)
    b,src,lc,bc=construct()
    eq,poly,metrics=b.export(hashlib.sha256(src).hexdigest(),'odd_centered_factorials',True)
    records={'equation.json':eq,'expanded_polynomial.json':poly,
        'macro_inventory.json':b.macro_log,'factorial_graphs.json':b.centered_factorials,
        'index_derivations.json':b.index_derivations,'label_majorant.json':lc,
        'local_majorant.json':bc,'radix_certificate.json':b.radix_data,
        'gate_ledger.json':{'square_difference_gates':b.sqd_ledger,
            'all_variables':b.variables,'all_rows':b.rows,'gates':b.gates}}
    records['raw_audit_input.json']={'variables':b.variables,'rows':b.rows,
        'powers':[{'base':n,'exponent':k,'output':v} for (n,k),v in b.powers.items()],
        'factorials':[{'input':n,'output':v} for n,v in b.factorials.items()],
        'factorial_graphs':b.centered_factorials,
        'binomials':[{'n':n,'k':k,'output':v} for (n,k),v in b.binomials.items()],
        'ranges':b.range_requests,'radix':b.radix_data,'scale':b.shared_parameters,
        'auxiliary':b.common_index_parameters,'discriminant':b.pell_D,
        'derivations':b.index_derivations,
        'seeds':[{'exponent':k,'pair':v} for k,v in b.seed_indices.items()],
        'indices':[{'exponent':k,'pair':v} for k,v in b.shared_indices.items()],
        'label_majorant':lc,'local_majorant':bc}
    for name,value in records.items():write_json(out/name,value)
    spec=importlib.util.spec_from_file_location('psd_contract',UP/'code/psd_contract/contract.py')
    mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
    results={'source':metrics,'power_relations':len(b.powers),
             'seed_indices':len(b.seed_indices),'distinct_bases':len({n for n,k in b.powers})}
    for cap in (16,64):
        target,cert,pp=mod.contract(eq,support_cap=cap)
        dest=out/('natural_cap'+str(cap));dest.mkdir(exist_ok=True)
        for name,value in [('equation.json',target),('elimination_certificate.json',cert),
                           ('expanded_polynomial.json',pp)]:write_json(dest/name,value)
        results[str(cap)]=target['metrics']
    write_json(out/'METRICS.json',results)
    return results

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--output',required=True,type=Path)
    a=p.parse_args();print(json.dumps(generate(a.output),indent=2))
