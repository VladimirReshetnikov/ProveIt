#!/usr/bin/env python3
"""Independent exact SOS/export audit. Imports no author construction code."""
from collections import Counter, defaultdict
from hashlib import sha256
from pathlib import Path
import json, sys

ROOT=Path(__file__).resolve().parents[1]
DATASET=sys.argv[1] if len(sys.argv)>1 else 'eq'
if DATASET not in ('eq','small_height'):
    raise ValueError('dataset must be eq or small_height')

def require(ok, label):
    if not ok: raise RuntimeError(label)

def digest(path):
    return sha256(path.read_bytes()).hexdigest()

equation_path=ROOT/DATASET/'equation.json'
expanded_path=ROOT/DATASET/'expanded_polynomial.json'
eq=json.loads(equation_path.read_text())
poly=json.loads(expanded_path.read_text())
build=json.loads((ROOT/DATASET/'BUILD.json').read_text())
require(eq['domain']==poly['domain']=='nonnegative integers','explicit common domain')
variables=eq['variables']; rows=eq['residuals']; count=len(variables)
require(len({v['name'] for v in variables})==count,'unique variable names')
seen=set(); coeffs=defaultdict(int); max_row=0
for row in rows:
    row_support=set()
    for c,m in row['terms']:
        require(type(c) is int and c!=0,'nonzero integral row coefficient')
        require(all(type(i) is int and 0<=i<count for i in m),'valid variable indices')
        require(m==sorted(m) and len(m)<=2,'quadratic monomial in canonical order')
        mon=tuple(m);require(mon not in row_support,'collected residual monomials')
        row_support.add(mon);seen.update(m);max_row=max(max_row,abs(c))
    for ca,ma in row['terms']:
        for cb,mb in row['terms']:
            coeffs[tuple(sorted(ma+mb))]+=ca*cb
require(seen==set(range(count)),'every declared variable occurs')
coeffs={m:c for m,c in coeffs.items() if c}
supplied={}
for c,m in poly['terms']:
    require(type(c) is int and c!=0 and m==sorted(m),'canonical expanded term')
    require(tuple(m) not in supplied,'collected expanded monomials')
    supplied[tuple(m)]=c
require(supplied==coeffs,'exact full expansion equals sum of residual squares')
require(poly['variables']==count,'expanded variable count')
metric=dict(variables=count,quadratic_rows=len(rows),exact_degree=max(map(len,coeffs)),
            expanded_monomials=len(coeffs),max_abs_row_coefficient=max_row,
            max_abs_expanded_coefficient=max(map(abs,coeffs.values())),
            variable_kinds=dict(Counter(v['kind'] for v in variables)))
for key,value in metric.items():
    require(eq['metrics'][key]==build['metrics'][key]==value,'metric '+key)
require(metric['exact_degree']==4,'exact quartic degree')
require(build['sha256']['equation.json']==digest(equation_path),'equation release hash')
require(build['sha256']['expanded_polynomial.json']==digest(expanded_path),'expanded release hash')
require(digest(ROOT/'wire_eliminated_source.json')==eq['wire_eliminated_source_sha256']==build['source_sha256'],'numerical source pin')
require(digest(ROOT/'direct_calculus.py')==build['literal_calculus_sha256'],'calculus file pin')

required_labels={'norm1','norm2','norm3','B_mod_U','T_definition','last_norm'}
blocks={}
for row in rows:
    if row['label'].startswith('pow'):
        prefix,suffix=row['label'].split('.',1)
        blocks.setdefault(prefix,Counter())[suffix]+=1
for prefix,labels in blocks.items():
    require(set(labels)==required_labels and set(labels.values())=={1},'six power constraints '+prefix)
    inputs=[v for v in variables if v['kind']=='witness' and v['name'].startswith(prefix+'.')]
    require(len(inputs)==12,'eleven power auxiliaries plus output '+prefix)
require(len(blocks)==55,'55 power blocks')

report=dict(status='PASS',dataset=DATASET,metrics=metric,power_blocks=55,
            each_power_block_auxiliaries=11,each_power_block_polynomial_constraints=6,
            all_declared_variables_occur=True,exact_expansion_verified=True,
            equation_sha256=digest(equation_path),expanded_sha256=digest(expanded_path),
            reviewed_mathlib_source_sha256=digest(ROOT/'upstream/PellMatiyasevic.lean'),
            reviewed_builder_sha256=digest(ROOT/'build_equation.py'),
            optimization=sys.flags.optimize,
            scope='Independent finite export and exact algebra audit; mathematical orientation and fixed-W proofs reviewed separately in REVIEW.md. Does not reprove inherited C222-to-ZFC calibration or CRT packing.')
suffix='_OPTIMIZED' if sys.flags.optimize else ''
prefix='CHECKS' if DATASET=='eq' else 'CHECKS_SMALL_HEIGHT'
(Path(__file__).parent/(prefix+suffix+'.json')).write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
