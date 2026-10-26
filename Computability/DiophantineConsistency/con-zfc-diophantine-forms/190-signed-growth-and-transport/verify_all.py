#!/usr/bin/env python3
"""Offline finite verification. This does not prove or test Con(ZFC)."""
from collections import Counter
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise ValueError(message)


def run_script(relative, *args, cwd=None):
    script = ROOT/relative
    result = subprocess.run([sys.executable, '-B', str(script), *map(str, args)],
                            cwd=cwd or script.parent, text=True,
                            capture_output=True,
                            env=dict(os.environ, PYTHONDONTWRITEBYTECODE='1'))
    if result.returncode:
        raise RuntimeError(f'{relative} failed:\n{result.stdout}\n{result.stderr}')
    return {'script': relative, 'exit_code': result.returncode,
            'stdout_sha256': hashlib.sha256(result.stdout.encode()).hexdigest()}


def verify_printed_residuals():
    text = (ROOT/'report/quartic_residuals.tex').read_text()
    blocks = re.findall(r'% residual (\d+)\n(.*?)% end residual \1\n', text, re.S)
    rows = json.loads((ROOT/'quartic/equations/affine209_F64/equation.json').read_text())['residuals']
    require(len(blocks) == len(rows) == 149, 'Printed residual count')
    count = 0
    for expected_index, (raw_index, block) in enumerate(blocks):
        require(int(raw_index) == expected_index, 'Printed residual order')
        expression = block.split(f'R_{{{expected_index}}}=', 1)[1].split(r'\end{aligned}', 1)[0]
        expression = expression.replace(r'\\', '').replace('&', '').replace('{}', '')
        expression = re.sub(r'\s+', '', expression)
        tokens = re.findall(r'[+-]?[^+-]+', expression)
        actual = Counter()
        for token in tokens:
            sign = -1 if token.startswith('-') else 1
            body = token.lstrip('+-')
            m = re.match(r'\d+', body)
            coefficient = int(m.group()) if m else 1
            factors = body[m.end():] if m else body
            monomial = []
            while factors:
                f = re.match(r'\\xi_\{(\d+)\}(?:\^\{(\d+)\})?', factors)
                require(f is not None, f'Unparsed TeX in residual {expected_index}: {factors}')
                monomial.extend([int(f.group(1))] * int(f.group(2) or 1))
                factors = factors[f.end():]
            actual[tuple(sorted(monomial))] += sign*coefficient
        expected = Counter()
        for coefficient, monomial in rows[expected_index]['terms']:
            expected[tuple(sorted(monomial))] += coefficient
        require(dict(actual) == dict(expected), f'Printed residual {expected_index} differs')
        count += len(tokens)
    require(count == 1004, 'Printed term count')
    return {'residuals': 149, 'coefficient_monomial_terms': count, 'status': 'PASS'}


def verify_manifest():
    path = ROOT/'MANIFEST.sha256'
    if not path.exists():
        return {'status': 'NOT_SEALED'}
    count = 0
    for line in path.read_text().splitlines():
        digest, relative = line.split('  ', 1)
        target = (ROOT/relative).resolve()
        require(target.is_relative_to(ROOT.resolve()), 'Manifest path escapes package')
        require(target.is_file(), 'Missing manifest file '+relative)
        require(hashlib.sha256(target.read_bytes()).hexdigest() == digest,
                'Manifest mismatch '+relative)
        count += 1
    return {'status': 'PASS', 'files': count}


def rebuild_all():
    with tempfile.TemporaryDirectory(prefix='conzfc-rebuild-') as tmp:
        base = Path(tmp)
        run_script('quartic/code/build.py', '--output', base/'quartic')
        matched = 0
        for folder in ('affine209_F64', 'affine209_F128', 'affine209_F128_basis'):
            for p in sorted((ROOT/'quartic/equations'/folder).iterdir()):
                require(p.read_bytes() == (base/'quartic'/folder/p.name).read_bytes(),
                        'Quartic rebuild differs '+str(p))
                matched += 1
        for generated, stored in [('source210_original.json', 'equation.json'),
                                  ('source210_affine.json', 'affine_horizon_equation.json')]:
            require((base/'quartic'/generated).read_bytes() ==
                    (ROOT/'quartic/source210'/stored).read_bytes(), 'Source-stage rebuild differs')
            matched += 1
        run_script('pooling/build.py', '--output', base/'pooling')
        pooled = list((base/'pooling').rglob('*.json'))
        for p in pooled:
            require(p.read_bytes() == (ROOT/'pooling'/p.relative_to(base/'pooling')).read_bytes(),
                    'Pooling rebuild differs')
        shutil.copytree(ROOT/'compact', base/'compact',
                        ignore=shutil.ignore_patterns('__pycache__', '*.pyc'))
        result = subprocess.run([sys.executable, '-B', str(base/'compact/build.py')],
                                capture_output=True, text=True)
        require(result.returncode == 0, 'Compact rebuild failed: '+result.stderr)
        require((base/'compact/equation.json').read_bytes() ==
                (ROOT/'compact/equation.json').read_bytes(), 'Compact equation rebuild differs')
    return {'status': 'PASS', 'quartic_byte_identical_files': matched,
            'pooling_byte_identical_files': len(pooled), 'compact_byte_identical_equations': 1}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--rebuild', action='store_true', help='also rerun each producer in a temporary directory')
    parser.add_argument('--receipt', type=Path, help='optional JSON result path')
    args = parser.parse_args()
    receipts = [run_script('quartic/verify.py'), run_script('compact/verify.py'),
                run_script('pooling/verify.py')]
    answer = {'status': 'PASS',
              'scope': 'Exact finite algebra, fixed numerals, source bindings and emitted artifacts; unbounded arithmetic and logical calibration are the separate written proofs.',
              'component_checks': receipts, 'printed_equation': verify_printed_residuals()}
    if args.rebuild:
        answer['rebuild'] = rebuild_all()
    answer['manifest'] = verify_manifest()
    if args.receipt:
        args.receipt.parent.mkdir(parents=True, exist_ok=True)
        args.receipt.write_text(json.dumps(answer, indent=2)+'\n')
    print(json.dumps(answer, indent=2))


if __name__ == '__main__':
    main()
