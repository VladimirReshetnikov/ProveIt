#!/usr/bin/env python3
"""Run all Report183 numerical certificates and tests, writing deterministic JSON."""
import argparse
import ast
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import certify_rational_circle
import certify_local
import certify_consequences
import exact_coefficients
import independent_global_check
import regenerate_polynomial
import test_local
from rigorous import require


def json_text(data):
    return json.dumps(data, indent=2, sort_keys=True)+'\n'


def run(data_dir, output_dir):
    code_dir = Path(__file__).resolve().parent
    output_dir.mkdir(parents=True, exist_ok=True)
    results = {}
    results['global'] = certify_rational_circle.run(data_dir)
    results['local'] = certify_local.run(data_dir)
    results['remainder'] = certify_consequences.remainder_certificate(results['global'], results['local'])
    results['inverse'] = certify_consequences.inverse_certificate(results['local'], results['remainder'])
    coefficients = exact_coefficients.generate(65)
    require(coefficients == json.loads((data_dir/'exact_coefficients.json').read_text()),
            'frozen exact coefficient data differs from regeneration')
    results['coefficients'] = coefficients
    results['global_independent'] = independent_global_check.run(data_dir)
    polynomial = regenerate_polynomial.run()
    require(polynomial == json.loads((data_dir/'N_H8.json').read_text()),
            'regenerated determinant polynomial differs from supplied data')
    results['polynomial_regeneration'] = {'status': 'PASS', 'height': polynomial['H'],
                                          'degree': len(polynomial['coeffs'])-1,
                                          'method': 'exact Newton interpolation with proved degree bound 239',
                                          'coefficients': polynomial['coeffs']}
    results['tests_local'] = test_local.run(data_dir)
    for name, script in [('tests_global', 'test_rational_circle.py'),
                         ('tests_coefficients', 'test_exact_coefficients.py')]:
        bootstrap = ('import runpy,sys; from pathlib import Path; '
                     'script=sys.argv.pop(1); '
                     'sys.path.insert(0,str(Path(script).resolve().parent)); '
                     'runpy.run_path(script,run_name="__main__")')
        command = [sys.executable, '-I', '-S', '-B']+(['-O'] if not __debug__ else [])+['-c', bootstrap, str(code_dir/script)]
        process = subprocess.run(command, cwd=output_dir, capture_output=True, text=True, check=False)
        require(process.returncode == 0, script+' failed:\n'+process.stderr)
        results[name] = json.loads(process.stdout)
    for path in sorted(code_dir.glob('*.py')):
        syntax = ast.parse(path.read_text())
        require(not any(isinstance(n, ast.Assert) for n in ast.walk(syntax)),
                'removable assertion in '+path.name)
    for name, result in results.items():
        (output_dir/(name+'.json')).write_text(json_text(result))
    summary = {'status': 'PASS', 'dependencies_for_replay': 'Python 3.10+ standard library only',
               'arithmetic': 'exact integers, exact fractions, and outward-rounded dyadic integer intervals',
               'files': {name+'.json': hashlib.sha256((output_dir/(name+'.json')).read_bytes()).hexdigest()
                         for name in sorted(results)},
               'code_sha256': {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                               for p in sorted(code_dir.glob('*.py'))},
               'data_sha256': {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                               for p in sorted(data_dir.glob('*.json'))},
               'scope': 'Finite executable certificates supplement the analytic proof; they do not establish worldwide priority or enumerate other poles.'}
    (output_dir/'summary.json').write_text(json_text(summary))
    return summary


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--data-dir', type=Path, default=Path(__file__).resolve().parent.parent/'data')
    parser.add_argument('--output-dir', type=Path, required=True)
    args = parser.parse_args()
    print(json_text(run(args.data_dir.resolve(), args.output_dir.resolve())), end='')


if __name__ == '__main__':
    main()
