#!/usr/bin/env python3
"""Certified integral projection using an exact affine consequence."""
import argparse
from collections import defaultdict
from hashlib import sha256
from pathlib import Path
import json
import sys

from affine_search import run


def poly_add(p, q, scale=1):
    out = dict(p)
    for m, c in q.items():
        v = out.get(m, 0) + scale * c
        if v:
            out[m] = v
        else:
            out.pop(m, None)
    return out


def mul(p, q):
    out = defaultdict(int)
    for a, c in p.items():
        for b, d in q.items():
            out[tuple(sorted(a+b))] += c*d
    return {m:c for m,c in out.items() if c}


def aspoly(terms):
    return {tuple(m):int(c) for c,m in terms if c}


def asterms(p):
    return [[c,list(m)] for m,c in sorted(p.items()) if c]


def substitute(poly, variable, replacement):
    out = {}
    for mon, coeff in poly.items():
        term = {():coeff}
        for v in mon:
            term = mul(term, replacement if v==variable else {(v,):1})
        out = poly_add(out, term)
    return out


def renumber(poly, variable):
    return {tuple(i-(i>variable) for i in m):c for m,c in poly.items()}


def collect(equation):
    out={}
    for row in equation['residuals']:
        p=aspoly(row['terms'])
        out=poly_add(out,mul(p,p))
    return out


def metrics(equation, expanded):
    return {'variables':len(equation['variables']),
            'residuals':len(equation['residuals']),
            'degree':max(map(len,expanded),default=0),
            'collected_terms':len(expanded),
            'coefficient_height':max(map(abs,expanded.values()),default=0)}


def project(equation, relation, variable):
    affine=aspoly(relation['affine_terms'])
    content=relation['whole_content']
    affine={m:c//content for m,c in affine.items()}
    if any(len(m)>1 for m in affine):
        raise RuntimeError('Not affine')
    a=affine.pop((variable,),0)
    if abs(a)!=1:
        raise RuntimeError('Not a unit')
    replacement={m:-c//a for m,c in affine.items()}
    combo=relation['row_combination']
    omitted=next(j for c,j in combo if c)
    # The row combination is a consequence. After setting that affine
    # consequence to zero, any row with nonzero combination coefficient
    # follows from the other rows over Q. Integer witnesses are preserved.
    out=dict(equation)
    out['variables']=[v for j,v in enumerate(equation['variables']) if j!=variable]
    out['residuals']=[]
    for j,row in enumerate(equation['residuals']):
        if j==omitted:
            continue
        p=substitute(aspoly(row['terms']),variable,replacement)
        if any(len(m)>2 for m in p):
            raise RuntimeError('Unexpected degree increase')
        newrow=dict(row)
        newrow['terms']=asterms(renumber(p,variable))
        out['residuals'].append(newrow)
    out['variant']=str(equation.get('variant',''))+'; exact affine projection'
    cert={'schema':'unit-affine-projection-v1','eliminated_coordinate':variable,
          'eliminated_variable':equation['variables'][variable],
          'omitted_residual':omitted,'affine_consequence':relation,
          'restoration_terms_original_indices':asterms(replacement)}
    return out,cert


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('input',type=Path)
    ap.add_argument('--output-dir',type=Path,required=True)
    args=ap.parse_args()
    data=json.loads(args.input.read_text())
    result=run(args.input)
    args.output_dir.mkdir(parents=True,exist_ok=True)
    found=False
    for idx,rel in enumerate(result['certified_relations']):
        for var in rel['unit_variables_after_content_normalization']:
            eq,cert=project(data,rel,var)
            cert['input_sha256']=sha256(args.input.read_bytes()).hexdigest()
            cert['input_path']=str(args.input.resolve())
            exp=collect(eq);met=metrics(eq,exp)
            dest=args.output_dir/f'project_r{idx}_v{var}'
            dest.mkdir(parents=True,exist_ok=True)
            ep=dest/'equation.json'
            ep.write_text(json.dumps(eq,indent=2)+'\n')
            cert['output_sha256']=sha256(ep.read_bytes()).hexdigest()
            (dest/'projection_certificate.json').write_text(json.dumps(cert,indent=2)+'\n')
            (dest/'metrics.json').write_text(json.dumps(met,indent=2)+'\n')
            (dest/'expanded_polynomial.json').write_text(json.dumps({'schema':'sparse-polynomial-v1','terms':asterms(exp)},indent=2)+'\n')
            further=run(ep)
            (dest/'affine_search.json').write_text(json.dumps(further,indent=2)+'\n')
            print(json.dumps({'path':str(dest),'metrics':met,'remaining_affine_relations':further['certified_relations']}),flush=True)
            found=True
    if not found:
        print(json.dumps({'path':str(args.input),'no_unit_affine_projection_found':True}),flush=True)


if __name__=='__main__':
    main()

