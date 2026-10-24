#!/usr/bin/env python3
"""Append quadratic semantic-input guards; preserve the frozen natural source."""
import argparse
from collections import Counter,defaultdict
import hashlib,json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
PARENT=ROOT/'candidates/shared-crt-prime-lift/affine'
DEST=PARENT.parent/'integer'
PINS={'equation.json':'e851ff1d420a39be069e63f6f117557356c38e6d8272a481258fe38cb38dc6ea',
      'expanded_polynomial.json':'06912612d90d67209d1554f29f50e45faebead811d2ec9cf7e8f97fa900e0718'}


def need(ok,text):
    if not ok:raise RuntimeError(text)


def sha(raw):return hashlib.sha256(raw).hexdigest()


def encoded(value):return(json.dumps(value,separators=(',',':'),sort_keys=True)+'\n').encode()


def build():
    data={}
    for name,pin in PINS.items():
        raw=(PARENT/name).read_bytes();need(sha(raw)==pin,'frozen natural parent')
        data[name]=json.loads(raw)
    old=data['equation.json'];variables=list(old['variables']);rows=list(old['residuals'])
    need(set(v['kind']for v in variables)=={'outer','witness','gate'},'original variable kinds')
    semantic=[i for i,v in enumerate(variables)if v['kind']!='gate']
    need(len(variables)==3609 and len(semantic)==1670 and len(rows)==2949,'exact frozen source dimensions')
    bindings=[]
    polynomial=defaultdict(int,{tuple(m):c for c,m in data['expanded_polynomial.json']['terms']})
    for i in semantic:
        a,b,c=range(len(variables),len(variables)+3)
        for suffix in ['a','b','c']:
            variables.append(dict(name='nonnegativity.'+str(i)+'.'+suffix,kind='nonnegativity'))
        terms=[[1,[i]],[-1,[a,a]],[-1,[b,b]],[-1,[c,c]],[-1,[c]]]
        terms=sorted(terms,key=lambda t:t[1])
        row=dict(label='semantic input nonnegativity '+str(i),terms=terms)
        rows.append(row);bindings.append(dict(input=i,auxiliaries=[a,b,c]))
        for ca,ma in terms:
            for cb,mb in terms:
                polynomial[tuple(sorted(ma+mb))]+=ca*cb
    poly=[[v,list(m)]for m,v in sorted(polynomial.items())if v]
    metrics=dict(variables=len(variables),semantic_inputs_guarded=len(semantic),
                 gate_variables=1939,nonnegativity_auxiliaries=3*len(semantic),quadratic_rows=len(rows),
                 exact_degree=max(len(m)for c,m in poly),expanded_monomials=len(poly),
                 max_abs_expanded_coefficient=max(abs(c)for c,m in poly),
                 max_abs_row_coefficient=max(abs(c)for row in rows for c,m in row['terms']))
    need(metrics['variables']==8619,'complete integer dimension')
    equation=dict(schema='finite_quadratic_residuals_v1',domain='unrestricted integers',
                  polynomial='sum(square(row) for row in residuals)',variables=variables,residuals=rows,
                  natural_parent_equation_sha256=PINS['equation.json'],semantic_input_guards=bindings,metrics=metrics)
    expanded=dict(schema='sparse_integer_polynomial_v1',domain='unrestricted integers',variables=len(variables),terms=poly)
    files={'equation.json':encoded(equation),'expanded_polynomial.json':encoded(expanded)}
    receipt=dict(status='PASS',metrics=metrics,natural_parent_sha256=PINS,
                 generator_sha256=sha(Path(__file__).read_bytes()),sha256={n:sha(raw)for n,raw in files.items()},
                 scope='Exact quadratic guard addition; ordinary Legendre/nonnegative gate-restoration proof in README.md; no Lean/internal-ZFC derivation.')
    files['BUILD.json']=(json.dumps(receipt,indent=2,sort_keys=True)+'\n').encode()
    return files,receipt


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--check',action='store_true');args=ap.parse_args()
    files,receipt=build()
    if not args.check:DEST.mkdir(exist_ok=True)
    for name,raw in files.items():
        path=DEST/name
        if args.check:need(path.read_bytes()==raw,'deterministic integer '+name)
        else:path.write_bytes(raw)
    print(json.dumps(dict(status='PASS',check=args.check,metrics=receipt['metrics']),indent=2))


if __name__=='__main__':main()
