"""Reproduce the lexical kernel's finite checks and complete-source metrics."""
import gzip
import hashlib
import json
import platform
from pathlib import Path
import subprocess
import sys
import tempfile

import producer
import source_measure

ROOT = Path(__file__).resolve().parent


def run(path, payload, optimized=False):
    command = [sys.executable] + (['-O'] if optimized else []) + [str(path)]
    result = subprocess.run(command, input=payload, text=True,
                            capture_output=True, timeout=20)
    accepted = result.returncode == 0 and result.stdout.strip() == 'ACCEPT'
    protocol = accepted or (result.returncode != 0 and result.stdout.strip() == 'REJECT')
    return {'accepted': accepted, 'protocol': protocol, 'exit_status': result.returncode}


def main():
    examples = producer.cases()
    encoded = {'format': 'Four-field generated-assumption packets with lexical scope',
               'scope': 'Finite examples, not a formal verification', 'cases': examples}
    (ROOT / 'cases.json').write_text(json.dumps(encoded, indent=2) + '\n')
    malformed = [('empty_input', ''), ('broken_json', '{broken'),
                 ('root_mapping', '{}'), ('root_null', 'null'),
                 ('root_boolean', 'true'), ('root_number', '1'),
                 ('root_string', '"text"'), ('empty_certificate', '[]'),
                 ('missing_instruction', '[[0,[0]]]'),
                 ('string_goal', '["bad"]'), ('mapping_goal', '[{}]'),
                 ('nonfinite_goal', '[NaN]'), ('infinite_goal', '[Infinity]'),
                 ('extra_json_value', '[] []')]
    records = []
    for profile in ['checker.py', 'readable_checker.py']:
        for optimized in [False, True]:
            for case in examples:
                result = run(ROOT / profile, json.dumps(case['packet']), optimized)
                records.append({'profile': profile, 'case': case['name'],
                                'optimized': optimized, 'expected': case['accept'], **result,
                                'passed': result['protocol'] and result['accepted'] == case['accept']})
            for name, payload in malformed:
                result = run(ROOT / profile, payload, optimized)
                records.append({'profile': profile, 'case': name, 'optimized': optimized,
                                'expected': False, **result,
                                'passed': result['protocol'] and not result['accepted']})

    indexed = {case['name']: case for case in examples}
    source = (ROOT / 'checker.py').read_text()
    axiom = [0, 0, 0]
    fake_major = [0, [0]]
    failed_major = [[0, axiom, 0, 0],
                    [fake_major, 0, [0], [axiom, 1]], [axiom, [0]]]
    mutations = [
        ('major_proof_is_mandatory', '        c(m, g, k)\n', '', failed_major),
        ('eager_predecessor_validation', 'i([*n, t, u], d=1)', '[*n, t, u]',
         indexed['two_child_counter_constant_update']['packet']),
        ('literal_equation_progress_only', 'len(a) % 2 == m', 'm == 0',
         indexed['forbidden_compound_progress']['packet']),
        ('DI_witness_scope_before_allocation', 'k <= a < d', 'a < d',
         indexed['DI_fresh_witness_cannot_depend_on_step_parameter']['packet']),
    ]
    controls = []
    with tempfile.TemporaryDirectory() as temporary:
        for name, before, after, packet in mutations:
            if source.count(before) != 1:
                raise RuntimeError('Mutation target is not unique: ' + name)
            path = Path(temporary) / (name + '.py')
            path.write_text(source.replace(before, after))
            for optimized in [False, True]:
                payload = json.dumps(packet)
                original = run(ROOT / 'checker.py', payload, optimized)
                mutant = run(path, payload, optimized)
                controls.append({'guard': name, 'optimized': optimized,
                                 'original': original, 'mutant': mutant,
                                 'passed': original['protocol'] and mutant['protocol']
                                 and not original['accepted'] and mutant['accepted']})

    # A major premise with local parameters checks at its caller's floor.
    # Forgetting that argument rejects a valid contextual induction proof.
    with tempfile.TemporaryDirectory() as temporary:
        path = Path(temporary) / 'forgot_scope_argument.py'
        path.write_text(source.replace('c(m, g, k)', 'c(m, g)'))
        payload = json.dumps(indexed['contextual_induction_seed_congruence']['packet'])
        original, mutant = run(ROOT / 'checker.py', payload), run(path, payload)
        controls.append({'guard': 'pass_the_current_scope_to_major_premise',
                         'original': original, 'mutant': mutant,
                         'passed': original['protocol'] and mutant['protocol']
                         and original['accepted'] and not mutant['accepted']})

    rows = []
    for filename in ['checker.py', 'readable_checker.py', 'reference_global.py']:
        path = ROOT / filename
        raw = path.read_bytes()
        row = {'file': filename, **source_measure.metrics(path),
               'gzip9_raw_bytes': len(gzip.compress(raw, compresslevel=9, mtime=0))}
        rows.append(row)
    result = {
        'python': platform.python_version(),
        'implementation': platform.python_implementation(),
        'scope': 'Finite execution checks and reproducible measurements; no mechanized metatheorem is claimed.',
        'gzip_recipe': 'len(gzip.compress(raw_source, compresslevel=9, mtime=0)); default empty filename header',
        'examples': len(examples), 'positive_examples': sum(x['accept'] for x in examples),
        'certificate_and_input_runs': len(records),
        'certificate_and_input_passes': sum(x['passed'] for x in records),
        'guard_controls': controls, 'metrics': rows, 'results': records,
    }
    (ROOT / 'verification.json').write_text(json.dumps(result, indent=2) + '\n')
    (ROOT / 'metrics.json').write_text(json.dumps(rows, indent=2) + '\n')
    failed = [x for x in records + controls if not x['passed']]
    print(json.dumps({'runs': len(records), 'passed': sum(x['passed'] for x in records),
                      'controls': len(controls), 'failed': failed,
                      'compact_metrics': rows[0]}, indent=2))
    if failed:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
