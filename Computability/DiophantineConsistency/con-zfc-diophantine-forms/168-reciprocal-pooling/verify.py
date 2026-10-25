#!/usr/bin/env python3
"""Read-only finite verification of the complete reciprocal-pooling package.

Python standard library only.  --receipt PATH writes the requested receipt.
--rebuild generates files exclusively under temporary directories and checks
byte-exact reproduction; it does not overwrite any delivered equation.
"""
from __future__ import annotations
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent
PARENT_SHA = 'fee84c408828aba3e7ceebe9a37f58509327063aa7fd078fd49c80adf3af4e56'
FINAL_SHA = {
    'equations/quartic218/equation.json': '878d2f427a117f35b4c211a223003978d52509acc46a5c97b829380b6e608ad8',
    'equations/decic215/equation.json': 'a335e0d1d1d82aa2cd30c2f436ed61a752fff001db134b339c23fae01d4a70b0',
}


def require(test, message):
    if not test:
        raise ValueError(message)


def read(path):
    return json.loads(Path(path).read_text(encoding='utf-8'))


def canonical_sha(value):
    payload = (json.dumps(value, sort_keys=True, separators=(',', ':')) + '\n').encode()
    return hashlib.sha256(payload).hexdigest()


def local(relative):
    """Require package-contained inputs, independent of the caller's cwd."""
    path = (ROOT / relative).resolve()
    require(path.is_relative_to(ROOT), 'input escapes the package: '+str(relative))
    return path


def python_command(script, *args):
    command = [sys.executable, '-B']
    if sys.flags.optimize:
        command.append('-O')
    return command + [str(script)] + [str(arg) for arg in args]


def run_script(script, *args, expect_json=True):
    environment = dict(os.environ)
    environment['PYTHONDONTWRITEBYTECODE'] = '1'
    completed = subprocess.run(python_command(script, *args), cwd=ROOT,
                               env=environment, capture_output=True, text=True)
    require(completed.returncode == 0,
            f'{Path(script).name} failed ({completed.returncode}):\n{completed.stdout}\n{completed.stderr}')
    if expect_json:
        try:
            return json.loads(completed.stdout)
        except json.JSONDecodeError as exc:
            raise ValueError(f'{Path(script).name} did not emit one JSON receipt: {completed.stdout}') from exc
    return {'status': 'PASS', 'stdout_sha256': hashlib.sha256(completed.stdout.encode()).hexdigest()}


def load_auditor():
    path = ROOT/'code'/'audit_transformations.py'
    spec = importlib.util.spec_from_file_location('independent_integer_audit', path)
    require(spec is not None and spec.loader is not None, 'cannot load independent auditor')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def compare_files(generated, delivered, filenames):
    receipt = []
    for name in filenames:
        actual = (generated/name).read_bytes()
        expected = (delivered/name).read_bytes()
        require(actual == expected, 'byte reproduction failed: '+str(delivered/name))
        receipt.append({'file': name, 'sha256': hashlib.sha256(actual).hexdigest(), 'bytes': len(actual)})
    return receipt


def verify(rebuild=False):
    plan = read(ROOT/'VERIFY_PLAN.json')
    require(plan['schema'] == 'conzfc-reciprocal-verification-plan-v1', 'unsupported plan schema')
    require(plan['domain'] == 'unrestricted integers', 'incorrect plan domain')
    require(plan['parent']['canonical_sha256'] == PARENT_SHA, 'parent pin in plan changed')
    parent_path = local(plan['parent']['equation'])
    parent = read(parent_path)
    require(canonical_sha(parent) == PARENT_SHA, 'pinned parent225 polynomial changed')
    parent_stage = read(ROOT/'inherited'/'parent225'/'stages'/'principal225'/'equation.json')
    require(parent == parent_stage, 'delivered parent225 differs from its verified last stage')
    require(len(parent['variables']) == 225 and len(parent['residuals']) == 162,
            'unexpected parent dimensions')
    for endpoint in plan['final_equations']:
        path = endpoint['path']
        require(path in FINAL_SHA and endpoint['canonical_sha256'] == FINAL_SHA[path],
                'final polynomial pin in plan changed')
        require(canonical_sha(read(local(path))) == FINAL_SHA[path], 'final polynomial changed: '+path)
    require({item['path'] for item in plan['final_equations']} == set(FINAL_SHA),
            'final polynomial missing from plan')

    auditor = load_auditor()
    functions = {'radical': auditor.audit_radical, 'affine': auditor.audit_affine,
                 'unit_affine': auditor.audit_unit_affine, 'rows': auditor.audit_rows,
                 'reciprocal': auditor.audit_reciprocal}
    expected_modes = ['radical', 'affine', 'unit_affine', 'rows', 'reciprocal']
    require([s['mode'] for s in plan['stages']] == expected_modes, 'verification stages changed')
    stage_receipts = []
    for stage in plan['stages']:
        source = local(stage['source']); target = local(stage['target'])
        result = functions[stage['mode']](source, target)
        stage_receipts.append({'name': stage['name'], 'mode': stage['mode'], 'result': result})
    protected = stage_receipts[-2]['result']
    require(protected.get('protected_pool_rows_unchanged') is True and
            protected.get('no_pool_row_used_as_source_or_target') is True,
            'power-pool protection was not checked')
    for endpoint, stage in zip(plan['final_equations'], stage_receipts[-2:]):
        result=stage['result']
        for plan_key, audit_key in [('variables','variables'),('residuals','rows'),
                                    ('degree','degree'),('monomials','monomials'),('height','height')]:
            require(endpoint[plan_key] == result[audit_key], 'headline metric differs: '+plan_key)

    parent_arguments = ['--rebuild'] if rebuild else []
    inherited = run_script(local(plan['parent']['inherited_verifier']), *parent_arguments)
    require(inherited.get('result') == 'passed', 'inherited verifier did not report a pass')
    frames = run_script(ROOT/'inherited'/'parent225'/'code'/'check_all_frame_atoms.py', parent_path)
    require(frames.get('each_actual_base_index_output_square_strictly_below_W') is True,
            'actual square-frame atoms were not established')
    pool_frame = run_script(ROOT/'inherited'/'parent225'/'code'/'check_pool_frame.py', '--equation', parent_path)
    lemma = run_script(ROOT/'code'/'check_reciprocal_lemma.py')
    require(lemma.get('status') == 'PASS', 'reciprocal arithmetic controls failed')

    rebuilt = {'requested': rebuild, 'files': []}
    if rebuild:
        with tempfile.TemporaryDirectory(prefix='conzfc-reciprocal-release-') as temp:
            temporary = Path(temp)
            reciprocal_dir = temporary/'reciprocal215'
            run_script(ROOT/'code'/'build_reciprocal.py', ROOT/'equations'/'quartic218'/'equation.json', reciprocal_dir)
            rebuilt['files'].append({'stage': 'reciprocal215', 'checks': compare_files(
                reciprocal_dir, ROOT/'equations'/'decic215',
                ['equation.json','certificate.json','METRICS.json','expanded_polynomial.json'])})
            lattice_dir = temporary/'lattice219'
            run_script(ROOT/'code'/'lattice_affine.py', ROOT/'stages'/'radical220'/'equation.json',
                       lattice_dir, expect_json=False)
            rebuilt['files'].append({'stage': 'integral_affine219', 'checks': compare_files(
                lattice_dir, ROOT/'stages'/'lattice219',
                ['equation.json','affine_lattice_certificate.json','metrics.json','expanded_polynomial.json'])})
        rebuilt['inherited_parent_json_files'] = inherited.get('reconstructed_json_files', 0)
        require(rebuilt['inherited_parent_json_files'] > 0, 'inherited parent rebuild produced no comparisons')

    report_path = ROOT/'code'/'check_report.py'
    printed_report = run_script(report_path) if report_path.exists() else {
        'status': 'NOT_PRESENT', 'scope': 'The optional printed-report checker was not present for this run.'}
    negative_controls = sum(len(s['result'].get('negative_controls_rejected',[])) for s in stage_receipts)
    require(negative_controls == 25, 'unexpected independent corruption-control count')
    return {
        'status': 'PASS',
        'schema': 'conzfc-reciprocal-release-verification-v1',
        'python_optimized': bool(sys.flags.optimize),
        'parent225_canonical_sha256': PARENT_SHA,
        'stage_audits': stage_receipts,
        'new_deliberate_corruptions_rejected': negative_controls,
        'inherited_parent225': inherited,
        'parent225_actual_frame_atoms': frames,
        'parent225_pool_frame': pool_frame,
        'independent_reciprocal_lemma_controls': lemma,
        'printed_report': printed_report,
        'rebuild': rebuilt,
        'scope': 'Exact finite polynomial identities, integer maps, protected row changes, complete expansions, and explicitly bounded arithmetic controls. Unbounded reciprocal-pooling and inherited consistency calibration remain ordinary proof dependencies.',
        'no_solution_search_performed': True,
        'formal_assistant_recompiled': False,
        'default_is_read_only': True,
    }


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--receipt', type=Path)
    parser.add_argument('--rebuild', action='store_true')
    args=parser.parse_args()
    try:
        result=verify(args.rebuild)
    except Exception as exc:
        result={'status':'FAIL','error_type':type(exc).__name__,'error':str(exc)}
        if args.receipt:
            args.receipt.parent.mkdir(parents=True,exist_ok=True)
            args.receipt.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n',encoding='utf-8')
        print(json.dumps(result,indent=2,sort_keys=True),file=sys.stderr)
        return 1
    text=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.receipt:
        args.receipt.parent.mkdir(parents=True,exist_ok=True)
        args.receipt.write_text(text,encoding='utf-8')
    print(text,end='')
    return 0


if __name__=='__main__':
    raise SystemExit(main())
