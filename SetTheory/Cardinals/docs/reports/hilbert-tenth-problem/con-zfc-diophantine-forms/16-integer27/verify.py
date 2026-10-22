#!/usr/bin/env python3
"""Replay the finite checks. This does not decide consistency or halting."""
from pathlib import Path
import hashlib
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise ValueError(message)


def read(path):
    return json.loads((ROOT / path).read_text())


def main():
    pins = read('SOURCE_PINS.json')
    for item in pins['files']:
        actual = hashlib.sha256((ROOT / item['path']).read_bytes()).hexdigest()
        require(actual == item['sha256'], 'Changed pinned dependency: ' + item['path'])
    scripts = ['src/build_positive.py', 'src/build_integer.py',
               'src/audit_positive.py', 'compiler/pruned_t4_check.py']
    for name in scripts:
        result = subprocess.run([sys.executable, str(ROOT / name)], cwd=ROOT,
                                text=True, capture_output=True)
        require(result.returncode == 0, name + '\n' + result.stdout + result.stderr)
        require(not result.stderr, name + ' emitted warnings: ' + result.stderr)
        json.loads(result.stdout)
    expected = [
        ('data/improved_weight_polynomial13_84.json', 13, 84, [515]),
        ('data/improved_weight_system13_78.json', 13, 78, [18, 7, 2, 488]),
        ('data/integer27_weighted_root_polynomial139.json', 27, 139, [1004]),
        ('data/integer27_weighted_root_system133.json', 27, 133, [35, 13, 4, 952]),
    ]
    circuits = []
    for name, variables, operations, degrees in expected:
        obj = read(name)
        require(len(obj['witnesses']) == variables, name + ': variable count')
        require(len(obj['source']) == operations, name + ': operation count')
        known = set(obj['witnesses'] + obj['fixed_numerals'])
        for register, operation, left, right in obj['source']:
            require(register not in known, name + ': duplicate register')
            require(operation in ('+', '-', '*'), name + ': invalid operation')
            require(all(type(x) is int or x in known for x in (left, right)),
                    name + ': undefined operand')
            known.add(register)
        outputs = [obj['output']] if 'output' in obj else [x for row in obj['comparisons'] for x in row if isinstance(x, str)]
        live = set(outputs)
        for register, operation, left, right in reversed(obj['source']):
            if register in live:
                live.update(x for x in (left, right) if isinstance(x, str))
        require(all(row[0] in live for row in obj['source']), name + ': dead gate')
        require(set(obj['witnesses'] + obj['fixed_numerals']) <= live, name + ': dead port')
        stated = [obj['exact_degree']] if 'output' in obj else obj['residual_exact_degrees']
        require(stated == degrees, name + ': degree claim')
        diagnostics = obj.get('degree_diagnostics', [obj.get('audit', {})])
        require(all(x.get('degrees') == degrees for x in diagnostics), name + ': degree diagnostic')
        require(obj['coefficient_binding']['fixed_tuple'] == 'pruned_t4', name + ': coefficient binding')
        circuits.append(dict(path=name, variables=variables, operations=operations,
                             degrees=degrees, ledger=obj['ledger']))
    compiler = read('compiler/pruned_t4_receipt.json')
    positive = read('verification/positive13_independent.json')
    integer = read('verification/integer27.json')
    require(compiler['status'] == 'PASS', 'Compiler audit failed')
    require(compiler['old_count'] == 37075 and compiler['new_count'] == 5268, 'Tile census')
    require(compiler['geometry']['d'] == 5**17, 'Fixed exponent')
    require(positive['status'] == 'PASS', 'Positive algebra audit')
    require(integer['independent_full_formula_fixtures'] == 100, 'Integer algebra fixture count')
    require(integer['signed_root_inverse_fixtures'] == 216, 'Integer inverse fixture count')
    result = dict(
        status='PASS', source_commit=pins['commit'], pinned_sources=len(pins['files']),
        circuits=circuits,
        checks=dict(positive_direct_assignments=positive['direct_signed_assignments'],
                    exact_sparse_ring_identities=positive['generic']['exact_sparse_integer_ring_identities'],
                    positive_inverse_fixtures=positive['fixtures']['isolated_signed_inverse_fixtures'],
                    integer_direct_assignments=100, integer_inverse_fixtures=216,
                    new_tiles=5268, old_tiles=37075, radix_exponent=5**17,
                    control_helices=len(compiler['seams']),
                    control_windows=sum(x['windows'] for x in compiler['seams'])),
        scope='Finite algebra, circuit, provenance, and compiler checks. Unbounded equivalence is proved in report.tex and proofs/. No consistency proof or new proof-assistant build.'
    )
    (ROOT / 'verification/summary.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
