#!/usr/bin/env python3
"""Independent domain conversion, exact expansion, and monic-map audit.

Imports no builder or optimizer. The separate projection checker was written
by another research agent and is included locally for portability.
"""
from collections import defaultdict,Counter
from copy import deepcopy
from pathlib import Path
import hashlib
import json
import argparse
import shutil
import subprocess
import sys
import tempfile

import verify_projection

HERE=Path(__file__).resolve().parent


def require(ok,message):
    if not ok:
        raise ValueError(message)


def canonical(value):
    return (json.dumps(value,sort_keys=True,separators=(',',':'))+'\n').encode()


def digest(value):
    return hashlib.sha256(canonical(value)).hexdigest()


def poly(terms):
    result={}
    for coefficient,monomial in terms:
        require(isinstance(coefficient,int) and coefficient!=0,'nonzero integer coefficient')
        m=tuple(monomial)
        require(m==tuple(sorted(m)),'canonical sorted monomial')
        require(m not in result,'unique monomial')
        result[m]=coefficient
    return result


def verify_conversion(parent,signed,certificate):
    require(parent['domain']=='nonnegative integers','natural source domain')
    require(signed['domain']=='unrestricted integers','signed target domain')
    require(digest(parent)==certificate['parent_sha256'],'natural literal identity')
    require(digest(signed)==certificate['guarded_sha256'],'guarded literal identity')
    n=len(parent['variables']); rows=len(parent['residuals'])
    require(signed['variables'][:n]==parent['variables'],'retained original coordinate list')
    require(signed['residuals'][:rows]==parent['residuals'],'retained original residual list')
    gate_set={i for i,v in enumerate(parent['variables']) if v['kind']=='gate'}
    input_set=set(range(n))-gate_set
    definitions=certificate['gate_definitions']
    require(len(definitions)==len(gate_set),'one certificate for every gate')
    require({d['variable'] for d in definitions}==gate_set,'complete gate coverage')
    for item in definitions:
        v=item['variable']; r=poly(parent['residuals'][item['row_id']]['terms'])
        restored=poly(item['restoration'])
        require(all(c>0 and all(i<v for i in mon) for mon,c in restored.items()),
                'nonnegative triangular polynomial defining original gate')
        expected={(v,):1}
        for mon,c in restored.items():
            expected[mon]=expected.get(mon,0)-c
        expected={m:c for m,c in expected.items() if c}
        require(r==expected,'exact original gate restoration row')
    guards=certificate['guards']
    require(len(guards)==len(input_set),'one sign certificate for every nongate')
    require({g['parent_variable'] for g in guards}==input_set,'complete input guard coverage')
    require(len(signed['variables'])==n+3*len(guards),'exact guard coordinate count')
    require(len(signed['residuals'])==rows+len(guards),'exact guard row count')
    for j,g in enumerate(guards):
        v=g['parent_variable']; a,b,c=g['coordinates']
        require((a,b,c)==(n+3*j,n+3*j+1,n+3*j+2),'private disjoint guard coordinates')
        require(g['row_id']==rows+j,'guard row order')
        expected={(v,):1,(a,a):-1,(b,b):-1,(c,c):-1,(c,):-1}
        require(poly(signed['residuals'][rows+j]['terms'])==expected,
                'literal x=a^2+b^2+c(c+1) guard')
    return dict(original_variables=n,original_gates=len(gate_set),
                guarded_nongates=len(input_set),guarded_variables=len(signed['variables']),
                guarded_residuals=len(signed['residuals']),status='PASS')


def verify_expansion(equation,expanded):
    require(equation['domain']==expanded['domain']=='unrestricted integers',
            'unrestricted integer domain at final equation')
    n=len(equation['variables'])
    require(expanded['variables']==n,'expanded polynomial coordinate count')
    result=defaultdict(int);used=set();row_height=0
    for row in equation['residuals']:
        p=poly(row['terms'])
        require(p and max(map(len,p))<=2,'nonzero quadratic residual')
        require(all(0<=i<n for mon in p for i in mon),'coordinate bounds')
        used.update(i for mon in p for i in mon)
        row_height=max(row_height,max(map(abs,p.values())))
        for m1,c1 in p.items():
            for m2,c2 in p.items():
                result[tuple(sorted(m1+m2))]+=c1*c2
    result={m:c for m,c in result.items() if c}
    require(result==poly(expanded['terms']),'complete expanded coefficient dictionary')
    require(used==set(range(n)),'all displayed variables occur')
    metrics=dict(variables=n,quadratic_rows=len(equation['residuals']),
                 exact_degree=max(map(len,result)),expanded_monomials=len(result),
                 max_abs_expanded_coefficient=max(map(abs,result.values())),
                 max_abs_row_coefficient=row_height)
    for key,value in metrics.items():
        require(equation['metrics'][key]==value,'metric '+key)
    return metrics


def rebuild_and_compare():
    """Run the builder separately; its output is evidence only after comparison."""
    with tempfile.TemporaryDirectory(prefix='integer-batch-rebuild-') as tmp:
        target=Path(tmp)
        (target/'source').mkdir()
        for filename in ('build_integer.py','terminal_elimination.py','SOURCE_PINS.json',
                         'source/parent_natural.json'):
            shutil.copy2(HERE/filename,target/filename)
        subprocess.run([sys.executable,str(target/'build_integer.py')],
                       check=True,capture_output=True,text=True)
        filenames=('input/equation.json','input/domain_conversion_certificate.json',
                   'signed_output/equation.json',
                   'signed_output/terminal_elimination_certificate.json',
                   'signed_output/expanded_polynomial.json','signed_output/BUILD.json')
        for filename in filenames:
            require((target/filename).read_bytes()==(HERE/filename).read_bytes(),
                    'byte-exact rebuild: '+filename)
    return dict(status='PASS',byte_identical_files=len(filenames))


def main(directory='signed_output',rebuild=False,receipt_path=None):
    parent_bytes=(HERE/'source/parent_natural.json').read_bytes()
    pins=json.loads((HERE/'SOURCE_PINS.json').read_text())
    require(hashlib.sha256(parent_bytes).hexdigest()==pins['parent_sha256'],
            'pinned source bytes')
    parent=json.loads(parent_bytes)
    signed=json.loads((HERE/'input/equation.json').read_text())
    conversion=json.loads((HERE/'input/domain_conversion_certificate.json').read_text())
    output=HERE/directory
    child=json.loads((output/'equation.json').read_text())
    certificate=json.loads((output/'terminal_elimination_certificate.json').read_text())
    expanded=json.loads((output/'expanded_polynomial.json').read_text())
    receipt=dict(status='PASS',conversion=verify_conversion(parent,signed,conversion),
                 projection=verify_projection.verify(signed,child,certificate),
                 metrics=verify_expansion(child,expanded))
    corrupted=deepcopy(conversion)
    corrupted['guards'].pop()
    rejected=False
    try:
        verify_conversion(parent,signed,corrupted)
    except ValueError:
        rejected=True
    require(rejected,'missing input positivity guard rejected')
    receipt['missing_guard_rejected']=True
    corrupted_projection=deepcopy(certificate)
    corrupted_projection['steps'][0]['restoration'][0][0]+=1
    rejected=False
    try:
        verify_projection.verify(signed,child,corrupted_projection)
    except ValueError:
        rejected=True
    require(rejected,'corrupted polynomial restoration rejected')
    receipt['mutated_restoration_rejected']=True
    receipt['sha256']={str(path.relative_to(HERE)):hashlib.sha256(path.read_bytes()).hexdigest()
        for path in (HERE/'input/equation.json',HERE/'input/domain_conversion_certificate.json',
                     output/'equation.json',output/'terminal_elimination_certificate.json',
                     output/'expanded_polynomial.json')}
    receipt['scope']='Exact signed algebra and natural-domain conversion; universal calculus and Pell interfaces are inherited.'
    if rebuild:
        require(directory=='signed_output','rebuild audits the released signed_output')
        receipt['rebuild']=rebuild_and_compare()
    if receipt_path:
        Path(receipt_path).write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--directory',default='signed_output')
    parser.add_argument('--rebuild',action='store_true')
    parser.add_argument('--receipt',type=Path)
    args=parser.parse_args()
    main(args.directory,args.rebuild,args.receipt)
