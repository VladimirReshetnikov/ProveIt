#!/usr/bin/env python3
"""Offline exact verification, including the preserved parent and two new families.

Python standard library only. This authenticates finite artifacts and their
integer algebraic transformations. It does not decide consistency or replace
the unbounded mathematical proofs by finite tests.
"""
from pathlib import Path
import argparse
import hashlib
import importlib.util
import json
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT/'code'))
import verify_growth
import verify_balanced

PYTHON = [sys.executable,'-B']+(['-O'] if sys.flags.optimize else [])
EXPECTED = {
    'equations/principal210/equation.json':'20a2108353a3756ed7d1ddfdc71695131dcf0b6d94039988d9565ac48e6e1f0a',
    'equations/balanced214/equation.json':'f351ebddacc0515984a00617a8bd7c318a24beaa48b5ad4bfff5aa99f6c383b6',
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def read(relative):
    return json.loads((ROOT/relative).read_text())


def run(relative, *args):
    path = ROOT/relative
    process = subprocess.run(PYTHON+[str(path)]+[str(arg) for arg in args],
                             cwd=path.parent, capture_output=True, text=True)
    if process.returncode:
        raise RuntimeError(str(relative)+' failed\n'+process.stdout+'\n'+process.stderr)
    return json.loads(process.stdout)


def load_module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def integrity(skip_manifest):
    for relative, digest in EXPECTED.items():
        require(hashlib.sha256((ROOT/relative).read_bytes()).hexdigest() == digest,
                'Frozen equation changed: '+relative)
    count = 0
    if not skip_manifest:
        seen = set()
        for line in (ROOT/'SHA256SUMS').read_text().splitlines():
            digest, relative = line.split('  ',1)
            path = Path(relative)
            require(not path.is_absolute() and '..' not in path.parts, 'Unsafe manifest path')
            require(relative not in seen, 'Duplicate manifest path')
            seen.add(relative)
            require(hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == digest,
                    'Manifest mismatch: '+relative)
        count = len(seen)
    return {'frozen_equations_checked':len(EXPECTED),'manifest_files_checked':count,
            'manifest_explicitly_skipped':bool(skip_manifest)}


def printed_equations():
    checker = load_module('strict_printed_equation',ROOT/'inherited/anchor/code/check_printed_equation.py')
    results = {}
    for profile in ['principal210','balanced214']:
        folder = ROOT/'equations'/profile
        metrics = json.loads((folder/'metrics.json').read_text())
        if profile == 'principal210':
            tex = (ROOT/'report/residuals.tex').read_text()
            macros = (ROOT/'report/metrics.tex').read_text()
            require(tex == (folder/'residuals.tex').read_text(), 'Report residual copy differs')
        else:
            tex = (folder/'residuals.tex').read_text()
            values = {'NV':metrics['variables'],'LastVar':metrics['variables']-1,
                      'NR':metrics['rows'],'LastRow':metrics['rows']-1,
                      'NT':metrics['monomials'],'Height':metrics['height']}
            macros = ''.join('\\newcommand{\\'+key+'}{'+str(value)+'}\n' for key,value in values.items())
        bundle = {'equation':json.loads((folder/'equation.json').read_text()),
                  'expanded':json.loads((folder/'expanded_polynomial.json').read_text()),
                  'metrics':metrics,'tex':tex,'macros':macros}
        result = checker.verify_bundle(bundle)
        result['mutation_controls'] = checker.run_mutation_controls(bundle)
        results[profile] = result
    return results


def evaluator_controls():
    evaluator = load_module('new_literal_evaluator',ROOT/'evaluate.py')
    equation = read('equations/principal210/equation.json')
    n = len(equation['variables'])
    result = evaluator.evaluate(equation,[0]*n)
    require(result['polynomial_value'] > 0 and not result['is_zero'], 'Invalid zero-tuple control')
    invalid = [None,{},[0]*(n-1),[0]*(n+1),[False]+[0]*(n-1),[0.0]+[0]*(n-1),['0']+[0]*(n-1)]
    for point in invalid:
        try:
            evaluator.evaluate(equation,point)
        except ValueError:
            pass
        else:
            raise ValueError('Noninteger or malformed tuple accepted')
    return {'zero_tuple_value':result['polynomial_value'],'invalid_inputs_rejected':len(invalid),
            'scope':'Evaluator sanity control, not a root search.'}


def sanitize(value, temporary):
    if isinstance(value,dict):
        return {key:sanitize(item,temporary) for key,item in value.items()}
    if isinstance(value,list):
        return [sanitize(item,temporary) for item in value]
    if isinstance(value,str):
        return value.replace(str(temporary),'<temporary-rebuild>').replace(str(ROOT)+'/', '')
    return value


def verify(args):
    receipt = {'status':'PASS','python_optimized':bool(sys.flags.optimize),
               'integrity':integrity(args.skip_manifest)}
    receipt['inherited_parent'] = run('inherited/anchor/verify.py')
    parent = ROOT/'inherited/anchor/source/anchor219/equation.json'
    helper = ROOT/'inherited/anchor/code/audit_projection.py'
    direct = verify_growth.check(ROOT/'stages/growth217',ROOT/'stages/source216',parent)
    direct['source_mutations'] = verify_growth.source_mutations(ROOT/'stages/growth217',parent)
    direct['projection_and_optimization'] = verify_growth.check_chain(
        ROOT/'stages/source216',ROOT/'stages/projection211',ROOT/'stages/projection210',
        ROOT/'equations/principal210',helper,True)
    receipt['principal210'] = direct
    receipt['balanced214'] = verify_balanced.check(
        ROOT/'inherited/anchor/source/anchor221/uncontracted.json',
        ROOT/'stages/balanced_source220',ROOT/'stages/balanced_projection215',
        ROOT/'stages/balanced_projection214',ROOT/'equations/balanced214',helper,True)
    receipt['printed_equations'] = printed_equations()
    pell_examples = run('code/check_pell_residue_examples.py')
    require(pell_examples == read('verification/PELL_RESIDUE_EXAMPLES.json'), 'Modular example receipt differs')
    receipt['modular_growth_examples'] = pell_examples
    receipt['compact_builder'] = run('compact11/build_constant_dilation.py','--check')
    receipt['compact11'] = run('compact11/verify_constant_dilation.py','--mutations')
    receipt['evaluator'] = evaluator_controls()
    with tempfile.TemporaryDirectory(prefix='conzfc210-replay-') as temporary:
        receipt['fresh_rebuild'] = run('code/rebuild.py','--output-dir',Path(temporary)/'rebuilt')
        receipt = sanitize(receipt,temporary)
    receipt['scope'] = ('Exact inherited/source bindings, integer projections and inverses, '
                        'literal TeX and collected coefficients, compact inverse identity and leading form, '
                        'and byte-identical fresh reconstruction. Ordinary unbounded proofs are separate; '
                        'no end-to-end proof-assistant build or consistency decision is claimed.')
    rendered = json.dumps(receipt,indent=2)+'\n'
    if args.receipt:
        args.receipt.parent.mkdir(parents=True,exist_ok=True)
        args.receipt.write_text(rendered)
    print(rendered,end='')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--receipt',type=Path)
    parser.add_argument('--skip-manifest',action='store_true',
                        help='Authoring only, before the release manifest exists; all coefficient checks still run.')
    verify(parser.parse_args())
