#!/usr/bin/env python3
"""Verify finite polynomial objects without searching for solutions.

The arithmetic and logical theorems are proved in the report. This driver
authenticates dependencies, checks independent identities, restores eliminated
coordinates, and compares every expanded coefficient.
"""
from copy import deepcopy
from hashlib import sha256
from pathlib import Path
import argparse,json,subprocess,sys,tempfile

import check_affine_export as affine
import check_contraction as contraction
import check_arithmetic_parent as parent_arithmetic
import check_new_arithmetic as new_arithmetic
import render_equations
import evaluate

ROOT=Path(__file__).resolve().parents[1]
PYTHON=[sys.executable]+(['-O'] if sys.flags.optimize else [])+['-B']

def require(ok,message):
    if not ok:raise ValueError(message)

def load(path):return json.loads(path.read_text())

def run_json(script,*arguments):
    result=subprocess.run(PYTHON+[str(ROOT/'code'/script)]+list(map(str,arguments)),
                          cwd=ROOT,text=True,capture_output=True)
    if result.returncode:
        raise RuntimeError(script+' failed\n'+result.stdout+'\n'+result.stderr)
    return json.loads(result.stdout)

def verify(rebuild=False):
    pins=load(ROOT/'provenance/SOURCE_PINS.json')
    for entry in pins['copied_shared_binomial_direct']:
        file=ROOT/entry['local_path']
        require(file.is_file() and sha256(file.read_bytes()).hexdigest()==entry['sha256'],
                'changed inherited source: '+entry['local_path'])
    manifest=ROOT/'SHA256SUMS'
    manifest_count=0
    if manifest.exists():
        for line in manifest.read_text().splitlines():
            expected,name=line.split('  ',1)
            file=ROOT/name
            require(file.is_file() and sha256(file.read_bytes()).hexdigest()==expected,'manifest mismatch: '+name)
            manifest_count+=1
    source_path=ROOT/'equations/source'
    metadata=load(source_path/'semantic.json')
    raw=load(source_path/'equation.json')
    source_polynomial=load(source_path/'expanded_polynomial.json')
    arithmetic_rows=run_json('check_semantics.py',source_path/'semantic.json',
        '--parent-semantic',ROOT/'upstream/shared_binomial/direct/equation319/raw/raw_audit_input.json',
        '--negative-controls')
    affine_receipt,affine_certificate=affine.verify(metadata,raw)
    affine_receipt.update(affine.check_expansion(raw,source_polynomial))
    affine_receipt['negative_controls_rejected']=affine.negative_controls(metadata,raw,affine_certificate)
    contractions={}
    for count in (234,233):
        folder=ROOT/f'equations/natural{count}'
        target=load(folder/'equation.json');certificate=load(folder/'elimination_certificate.json')
        polynomial=load(folder/'expanded_polynomial.json')
        receipt,terms=contraction.verify(raw,target,certificate)
        require(polynomial['domain']=='nonnegative integers' and polynomial['variables']==count,
                'wrong final polynomial domain/count')
        require(polynomial['terms']==terms,'literal coefficient expansion mismatch')
        require(receipt==load(folder/'VERIFICATION.json'),'recorded contraction receipt mismatch')
        affine.validate_quadratic_equation(target,'natural'+str(count))
        altered=deepcopy(target)
        altered['residuals'][0]['terms'][0][0]+=1
        altered_certificate=deepcopy(certificate)
        altered_certificate['target_equation_sha256']=sha256(contraction.canonical(altered)).hexdigest()
        try:contraction.verify(raw,altered,altered_certificate)
        except (ValueError,KeyError,IndexError):pass
        else:raise ValueError('mutated target accepted despite updated hash')
        receipt['corruption_with_updated_hash_rejected']=True
        recipe=load(ROOT/f'equations/integer/integer{3*count}.json')
        require(recipe['parent_sha256']==sha256((folder/'equation.json').read_bytes()).hexdigest(),
                'integer substitution parent hash')
        expected=[{'parent_coordinate':i,'integer_coordinates':[3*i,3*i+1,3*i+2],
                   'polynomial_terms':[[1,[3*i,3*i]],[1,[3*i+1,3*i+1]],
                                       [1,[3*i+2,3*i+2]],[1,[3*i+2]]]}
                  for i in range(count)]
        require(recipe['substitutions']==expected and recipe['domain']=='integers' and recipe['degree']==8,
                'integer substitution recipe mismatch')
        zero=evaluate.evaluate('natural'+str(count),[0]*count)
        signed=[((i*17)%9)-4 for i in range(3*count)]
        mapped=[signed[i]**2+signed[i+1]**2+signed[i+2]*(signed[i+2]+1)
                for i in range(0,len(signed),3)]
        require(evaluate.evaluate('integer'+str(3*count),signed)['polynomial_value']==
                evaluate.evaluate('natural'+str(count),mapped)['polynomial_value'],
                'integer evaluator mismatch')
        receipt['zero_tuple_value']=zero['polynomial_value']
        contractions[str(count)]=receipt
    transcription=render_equations.run(check=True)
    arithmetic={'parent':parent_arithmetic.check(),'new':new_arithmetic.check(),
                'consecutive':run_json('check_consecutive_ordinates.py')}
    rebuilt={}
    if rebuild:
        with tempfile.TemporaryDirectory(prefix='conzfc-rebuild-') as temporary:
            for count in (234,233):
                output=Path(temporary)/str(count)
                args=['--upstream',ROOT/'upstream/shared_binomial','--output',output,
                      '--support-cap','64','--dominant','--semantic-anchor','--coordinates','consecutive']
                if count==234:args+=['--protect','index_cap.Y']
                result=run_json('build_combined.py',*args)
                for name in ('equation.json','expanded_polynomial.json','METRICS.json','semantic.json','local_majorant.json'):
                    require((output/'raw'/name).read_bytes()==(source_path/name).read_bytes(),
                            'raw reconstruction differs: '+name)
                for name in ('equation.json','expanded_polynomial.json','elimination_certificate.json','VERIFICATION.json'):
                    require((output/'natural'/name).read_bytes()==(ROOT/f'equations/natural{count}'/name).read_bytes(),
                            'final reconstruction differs: '+name)
                require((output/'SUMMARY.json').read_bytes()==(ROOT/f'equations/natural{count}/SUMMARY.json').read_bytes(),
                        'reconstruction summary differs')
                rebuilt[str(count)]={'exact_files_compared':10,'variables':result['natural']['variables']}
    return {'status':'PASS','optimized_python':bool(sys.flags.optimize),
            'scope':'finite artifact authentication, algebraic equivalences, arithmetic controls; not a full kernel proof',
            'source_commit':pins['commit'],'inherited_files_authenticated':len(pins['copied_shared_binomial_direct']),
            'manifest_files_authenticated':manifest_count,'semantic_rows':arithmetic_rows,
            'affine_export':affine_receipt,'contractions':contractions,
            'transcription':transcription,'arithmetic_controls':arithmetic,'reconstruction':rebuilt}

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--rebuild',action='store_true')
    p.add_argument('--output',type=Path,help='Optional receipt path; use an external path after packaging.')
    a=p.parse_args();result=verify(a.rebuild);body=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if a.output:a.output.write_text(body)
    print(body,end='')
