"""Reproduce complete-source measurements and meaningful certificate checks."""
import ast
import hashlib
import importlib.util
import json
from pathlib import Path
import platform
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent


def run(path, payload, optimized=False):
    command = [sys.executable] + (['-O'] if optimized else []) + [str(path)]
    result = subprocess.run(command, input=payload, text=True,
                            capture_output=True, timeout=30)
    accepted = result.stdout.strip() == 'ACCEPT' and result.returncode == 0
    protocol = accepted or (result.stdout.strip() == 'REJECT' and result.returncode != 0)
    return accepted, protocol, result.returncode


def main():
    spec = importlib.util.spec_from_file_location('source_measure', ROOT / 'reference/source_measure.py')
    measure = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(measure)
    profiles = [('code/checker.py', 'witness_cases.json'),
                ('code/checker_ast.py', 'witness_cases.json'),
                ('code/checker_strict.py', 'cases.json')]
    controls = ['reference/endpoint_tokens.py', 'reference/endpoint_ast.py',
                'reference/successor_bytes.py', 'reference/neutral_control.py']
    rows = [{'file': p, **measure.metrics(ROOT / p)} for p in
            [p for p, _ in profiles] + controls]
    envelope = {'normalized_tokens': 287, 'ast_nodes': 323, 'normalized_bytes': 738}
    for row in rows[:3]:
        for key, bound in envelope.items():
            if row[key] >= bound:
                raise RuntimeError('Lost strict coordinate improvement: ' + row['file'] + '/' + key)
    records = []
    for profile, case_file in profiles:
        cases = json.loads((ROOT / 'tests' / case_file).read_text())['cases']
        for optimized in [False, True]:
            for case in cases:
                accepted, protocol, status = run(ROOT / profile, json.dumps(case['packet']), optimized)
                records.append({'profile': profile, 'case': case['name'], 'optimized': optimized,
                                'expected': case['accept'], 'accepted': accepted,
                                'exit_status': status, 'passed': protocol and accepted == case['accept']})
            for name, payload in [('empty_input', ''), ('not_json', '{broken'), ('not_packet_array', '{}')]:
                accepted, protocol, status = run(ROOT / profile, payload, optimized)
                records.append({'profile': profile, 'case': name, 'optimized': optimized,
                                'expected': False, 'accepted': accepted,
                                'exit_status': status, 'passed': protocol and not accepted})

    # Each mutation removes a specific soundness obligation. Acceptance of the
    # corresponding invalid derivation shows that the test actually reaches it.
    source = (ROOT / 'code/checker.py').read_text()
    fixtures = {c['name']: c for c in json.loads((ROOT / 'tests/witness_cases.json').read_text())['cases']}
    axiom_source = [0, 0, 0]
    fake_major = [0, [0]]
    bad_major_packet = [[0, axiom_source, 0, 0],
                        [fake_major, 0, [0], [axiom_source, 1]],
                        [axiom_source, [0]]]
    mutations = [
        ('eager_predecessor_check', 'i([*n, t, u], d=1)', '[*n, t, u]',
         fixtures['two_child_counter_constant_update']['packet']),
        ('major_proof_check', '        c(m, g)\n', '', bad_major_packet),
        ('equation_only_progress', 'len(a) % 2 == m', 'm == 0',
         fixtures['forbidden_compound_progress']['packet']),
    ]
    mutation_records = []
    with tempfile.TemporaryDirectory() as tmp:
        for name, old, new, packet in mutations:
            if source.count(old) != 1:
                raise RuntimeError('Mutation target changed: ' + name)
            modified = Path(tmp) / (name + '.py')
            modified.write_text(source.replace(old, new))
            original, original_protocol, _ = run(ROOT / 'code/checker.py', json.dumps(packet))
            mutant, mutant_protocol, _ = run(modified, json.dumps(packet))
            mutation_records.append({'guard': name, 'original_accepts': original,
                                     'mutant_accepts': mutant,
                                     'passed': original_protocol and mutant_protocol and not original and mutant})
    failed = [r for r in records + mutation_records if not r['passed']]
    report = {'python': platform.python_version(), 'implementation': platform.python_implementation(),
              'scope': 'Finite execution checks and measurements, not formal verification.',
              'coordinate_envelope': envelope, 'programs': rows,
              'certificate_and_input_runs': len(records),
              'certificate_and_input_passes': sum(r['passed'] for r in records),
              'mutation_controls': mutation_records,
              'results': records}
    (ROOT / 'evidence/verification.json').write_text(json.dumps(report, indent=2) + '\n')
    metrics = {k: report[k] for k in ['python', 'implementation', 'coordinate_envelope', 'programs']}
    (ROOT / 'evidence/metrics.json').write_text(json.dumps(metrics, indent=2) + '\n')
    print(json.dumps({'certificate_and_input_runs': len(records),
                      'passed': sum(r['passed'] for r in records),
                      'mutation_controls': mutation_records, 'failures': failed}, indent=2))
    if failed:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
