#!/usr/bin/env python3
"""Reproduce the cofinal-frame Pell-residue quartic and natural projection."""
from pathlib import Path
import hashlib, importlib.util, json
import argparse
import build_projected
from modular_binomial import ModularBinomialBuilder

HERE=Path(__file__).resolve().parent

def write(p,x):
    p.parent.mkdir(parents=True,exist_ok=True)
    p.write_text(json.dumps(x,sort_keys=True,separators=(',',':'))+'\n')

def load_module(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    return module

def generate(out):
    out=Path(out)
    if out.exists() and any(out.iterdir()):raise ValueError('output must be empty')
    out.mkdir(parents=True,exist_ok=True)
    build_projected.AdditiveReusedRadixBuilder=ModularBinomialBuilder
    b,src,label,local=build_projected.construct()
    equation,expanded,metrics=b.export(hashlib.sha256(src).hexdigest(),'modular_binomial_experiment',True)
    raw={'variables':b.variables,'rows':b.rows,'gates':b.gates,'square_difference_gates':b.sqd_ledger,
         'powers':[{'base':n,'exponent':k,'output':v} for (n,k),v in b.powers.items()],
         'factorials':[{'input':n,'output':v} for n,v in b.factorials.items()],
         'binomials':[{'n':n,'k':k,'output':v} for (n,k),v in b.binomials.items()],
         'ranges':b.range_requests,'radix':b.radix_data,'scale':b.shared_parameters,'lower_A':b.scale_lower,
         'auxiliary':b.common_index_parameters,'discriminant':b.pell_D,'derivations':b.index_derivations,
         'seeds':[{'exponent':k,'pair':v} for k,v in b.seed_indices.items()],
         'indices':[{'exponent':k,'pair':v} for k,v in b.shared_indices.items()],
         'label_majorant':label,'local_majorant':local}
    for n,x in [('equation.json',equation),('expanded_polynomial.json',expanded),('METRICS.json',metrics),
                ('raw_audit_input.json',raw),('radix_certificate.json',b.radix_data),('macro_inventory.json',b.macro_log),
                ('label_majorant.json',label),('local_majorant.json',local)]:write(out/'source655'/n,x)
    contractor=load_module('modular_psd_producer',HERE/'psd_contract/contract.py')
    checker=load_module('modular_psd_checker',HERE/'psd_contract/check.py')
    protected=[i for i,v in enumerate(equation['variables']) if v['name']=='shared.W']
    if len(protected)!=1:raise ValueError('one shared W required')
    target,cert,poly=contractor.contract(equation,64,protected_variables=protected)
    result,independent=checker.verify(equation,target,cert)
    if poly['terms']!=independent:raise ValueError('independent polynomial mismatch')
    for n,x in [('equation.json',target),('expanded_polynomial.json',poly),('elimination_certificate.json',cert),
                ('VERIFICATION.json',result)]:write(out/'natural395'/n,x)
    # Retain the smaller-coordinate/higher-support variant for a measured tradeoff.
    small,smallcert,smallpoly=contractor.contract(equation,64)
    sr,sp=checker.verify(equation,small,smallcert)
    if smallpoly['terms']!=sp:raise ValueError('small independent polynomial mismatch')
    for n,x in [('equation.json',small),('expanded_polynomial.json',smallpoly),('elimination_certificate.json',smallcert),
                ('VERIFICATION.json',sr)]:write(out/'natural394'/n,x)
    report={'source':metrics,'natural395':result,'natural394':sr,'exact_power_calls':len(b.powers),
            'seed_indices':len(b.seed_indices),'modular_requests':len(b.modular_requests),
            'protected_variable':'shared.W'}
    write(out/'RESULTS.json',report)
    return report

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True)
    args=p.parse_args();print(json.dumps(generate(args.output),indent=2))
