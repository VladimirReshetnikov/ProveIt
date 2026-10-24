#!/usr/bin/env python3
"""Deterministically construct the 977-integer quartic from certified domains."""
import argparse, hashlib, json
from pathlib import Path
from signed_contract import lift, contract, metrics

ROOT=Path(__file__).resolve().parent.parent
def canonical(data):return (json.dumps(data,sort_keys=True,separators=(',',':'))+'\n').encode()
def digest(data):return hashlib.sha256(canonical(data)).hexdigest()
def build():
    source=json.loads((ROOT/'equations_v3/cap64/equation.json').read_text())
    domain=json.loads((ROOT/'DOMAIN_CERTIFICATE.json').read_text())
    guards=domain['guards']
    guarded=lift(source,guards,monic=True)
    target,cert=contract(guarded,64,'first')
    met,expanded=metrics(target)
    eq={'schema':'finite_quadratic_residuals_v1','domain':'unrestricted integers',
        'polynomial':'sum(square(row) for row in residuals)',
        'variables':target['variables'],'residuals':target['residuals'],'metrics':met,
        'source_natural_equation_sha256':digest(source),
        'domain_certificate':'../DOMAIN_CERTIFICATE.json',
        'construction':'170 monic ternary guards; 28 integer polynomial contractions'}
    expanded['domain']='unrestricted integers'
    cert.update({'schema':'integer_monic_contraction_v1','source_natural_sha256':digest(source),
                 'guard_indices':guards,'guard_formula':'x-a*a-b*b-c*c-c',
                 'guarded_equation_sha256':digest(guarded),'target_equation_sha256':digest(eq),
                 'support_cap':64,'source_variables':len(guarded['variables']),
                 'source_residuals':len(guarded['residuals'])})
    return {'equation.json':eq,'expanded_polynomial.json':expanded,
            'elimination_certificate.json':cert,'METRICS.json':met}
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args();args.output.mkdir(parents=True,exist_ok=True)
    data=build()
    for name,value in data.items():(args.output/name).write_bytes(canonical(value))
    print(json.dumps(data['METRICS.json'],indent=2,sort_keys=True))
if __name__=='__main__':main()
