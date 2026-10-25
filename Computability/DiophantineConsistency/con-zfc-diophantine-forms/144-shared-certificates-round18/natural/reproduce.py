#!/usr/bin/env python3
"""Deterministic endpoint reconstruction into an explicitly separate directory."""
from pathlib import Path
import argparse,json,sys
sys.dont_write_bytecode=True
import build
HERE=Path(__file__).resolve().parent

def all_profiles(output):
    output=Path(output)
    if output.exists() and any(output.iterdir()):raise ValueError('Output must be empty')
    reports=[]
    for recipe in build.read(HERE/'PROFILE_RECIPES.json'):
        source,poly,transform=build.transform(recipe['strategy'])
        order=recipe['row_order']
        if sorted(order)!=list(range(len(source['residuals']))):raise ValueError('Not a row permutation')
        source['residuals']=[source['residuals'][i] for i in order]
        target,cert,expanded=build.pc.contract(source,support_cap=recipe['support_cap'])
        report,independent=build.check.verify(source,target,cert)
        if expanded['terms']!=independent:raise ValueError('Independent expansion differs')
        out=output/recipe['name']
        for n,o in [('source/equation.json',source),('source/transformation.json',transform),('natural/equation.json',target),('natural/elimination_certificate.json',cert),('natural/expanded_polynomial.json',expanded)]:build.write(out/n,o)
        reports.append(dict(name=recipe['name'],**report))
    return reports

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    print(json.dumps(all_profiles(a.output),indent=2))
