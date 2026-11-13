"""Reproduce lexical neutral-major certificates and audit complete CLI programs.

No checker imports this producer or test suite.  This is finite evidence,
not a formal metatheoretic verification.
"""
import copy
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile

import inherited_verify
import producer
from protocol import translate

ROOT = Path(__file__).resolve().parents[1]


def local_cases():
    previous = producer.Emitter

    class LocalEmitter(previous):
        def emit(self, proof, context):
            saved = self.floor
            self.floor = -len(context)
            try:
                return super().emit(proof, context)
            finally:
                self.floor = saved

    producer.Emitter = LocalEmitter
    try:
        examples = inherited_verify.cases()
    finally:
        producer.Emitter = previous
    for filename in ('context_leak_counterexample.json', 'false_float_capture.json'):
        examples.append({
            'name': filename[:-5],
            'packet': translate(json.loads((ROOT / 'tests' / filename).read_text())),
            'accept': False,
            'meaning': 'The inherited concrete false-proof attack, translated to neutral majors.'
        })
    examples.append({
        'name': 'future_witness_capture',
        'packet': json.loads((ROOT / 'tests' / 'future_witness_capture.json').read_text()),
        'accept': False,
        'meaning': 'A witness must not refer to the induction eigenparameter allocated after its opening.'
    })
    return examples


def run(path, text, optimized=False):
    result = subprocess.run(
        [sys.executable] + (['-O'] if optimized else []) + [str(path)],
        input=text, text=True, capture_output=True, timeout=15)
    return result.returncode == 0 and result.stdout == 'ACCEPT\n'


def main():
    local = local_cases()
    global_cases = inherited_verify.cases()
    rows = []
    for name, examples, directory in (
        ('checker.py', local, 'code'),
        ('checker_bytes.py', local, 'code'),
        ('checker_ast.py', local, 'code'),
        ('readable_checker.py', local, 'code'),
        ('neutral_checker.py', global_cases, 'reference'),
        ('neutral_checker_bytes.py', global_cases, 'reference'),
        ('neutral_checker_joint.py', global_cases, 'reference')
    ):
        for case in examples:
            for optimized in (False, True):
                got = run(ROOT / directory / name, json.dumps(case['packet']), optimized)
                rows.append({'profile': name, 'case': case['name'], 'optimized': optimized,
                             'expected': case['accept'], 'accepted': got,
                             'ok': got == case['accept']})

    malformed = ['', '{}', 'null', 'true', '42', '"x"', '["x"]',
                 '[[0,[0]]]', '[[true,0,0,0],[0,[0]]]', '[[[0,3.0]]]',
                 '[[[],0,0,0,0],[0,[0]]]']
    for name in ('checker.py', 'checker_bytes.py', 'checker_ast.py', 'readable_checker.py'):
        for index, packet in enumerate(malformed):
            for optimized in (False, True):
                got = run(ROOT / 'code' / name, packet, optimized)
                rows.append({'profile': name, 'case': f'malformed_{index}',
                             'optimized': optimized, 'expected': False,
                             'accepted': got, 'ok': not got})

    mutations = []
    with tempfile.TemporaryDirectory() as directory:
        controls = (
            ('wrong_induction_selector', 'checker_bytes.py',
             'len(a) % 2 == u', 'len(a) % 2 == s', 'compound_source_attack'),
            ('in_place_context_leak', 'checker_ast.py',
             'g=([],)', 'g=[[]]', 'context_leak_counterexample')
        )
        for name, base, old, new, case_name in controls:
            source = (ROOT / 'code' / base).read_text()
            if source.count(old) != 1:
                raise ValueError(f'Unexpected mutation source: {name}')
            path = Path(directory) / (name + '.py')
            path.write_text(source.replace(old, new))
            packet = next(x['packet'] for x in local if x['name'] == case_name)
            for optimized in (False, True):
                got = run(path, json.dumps(packet), optimized)
                mutations.append({'mutation': name, 'case': case_name,
                                  'optimized': optimized, 'expected': True,
                                  'accepted': got, 'ok': got})

        # Moving allocation across witness opening is an unsound ordering
        # change, not a harmless reordering of independent expressions.
        source = (ROOT / 'code' / 'checker_bytes.py').read_text().splitlines()
        row = next(i for i, line in enumerate(source) if line.strip().startswith('h = '))
        if source[row + 1].strip() != 'k -= 1':
            raise ValueError('Unexpected source order for allocation mutation')
        source[row], source[row + 1] = source[row + 1], source[row]
        path = Path(directory) / 'future_witness_allocation.py'
        path.write_text('\n'.join(source) + '\n')
        packet = next(x['packet'] for x in local if x['name'] == 'future_witness_capture')
        for optimized in (False, True):
            got = run(path, json.dumps(packet), optimized)
            mutations.append({'mutation': 'allocation_before_witness_opening',
                              'case': 'future_witness_capture', 'optimized': optimized,
                              'expected': True, 'accepted': got, 'ok': got})

    all_rows = rows + mutations
    summary = {'local_cases': len(local), 'global_reference_cases': len(global_cases),
               'cli_checks': len(rows), 'mutation_checks': len(mutations),
               'mismatches': sum(not x['ok'] for x in all_rows),
               'finite_evidence_only': True}
    result = {'summary': summary, 'results': rows, 'mutation_results': mutations,
              'source_sha256': {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                                for p in sorted((ROOT / 'code').glob('*.py'))}}
    (ROOT / 'evidence' / 'validation.json').write_text(json.dumps(result, indent=2) + '\n')
    (ROOT / 'evidence' / 'local_cases.json').write_text(json.dumps(local, indent=2) + '\n')
    print(json.dumps(summary, indent=2))
    if summary['mismatches']:
        print(json.dumps([x for x in all_rows if not x['ok']], indent=2))
        raise SystemExit(1)


if __name__ == '__main__':
    main()
