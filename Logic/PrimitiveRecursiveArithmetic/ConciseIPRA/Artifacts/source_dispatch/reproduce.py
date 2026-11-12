"""Reproduce certificates, rejection controls, source measurements and identities.

Uses the standard library. Producers are untrusted and no checker is imported.
Run from any directory: python3 /path/to/extracted/package/reproduce.py
"""
import hashlib
import importlib.util
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent
OUT = ROOT / 'evidence/reproduced'
OUT.mkdir(parents=True, exist_ok=True)
sys.path.insert(0, str(ROOT / 'tests'))
import normalizer as n
import global_producer


def run_checker(program, packet, optimized):
    command = [sys.executable] + (['-O'] if optimized else []) + [str(ROOT / program)]
    run = subprocess.run(command, input=json.dumps(packet) + '\n',
                         capture_output=True, text=True, timeout=45)
    return run.returncode == 0 and run.stdout == 'ACCEPT\n'


def main():
    identities = json.loads((ROOT / 'evidence/comparison_sources.json').read_text())
    for row in identities:
        path = ROOT / row['local_path']
        if hashlib.sha256(path.read_bytes()).hexdigest() != row['sha256']:
            raise RuntimeError('Frozen comparison source changed: ' + row['local_path'])
    spec = importlib.util.spec_from_file_location('module_metrics', ROOT / 'tools/measure.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    measurements = module.results()
    (OUT / 'measurements.json').write_text(json.dumps(measurements, indent=2) + '\n')

    local_programs = ['code/checker.py', 'code/checker_bytes.py', 'code/readable_checker.py']
    global_programs = ['code/checker_tokens.py']
    commands = [sys.executable, str(ROOT / 'tests/generate_certificates.py'),
                '--output', str(OUT / 'certificates')]
    for program in local_programs:
        commands += ['--local-checker', str(ROOT / program)]
    for program in global_programs:
        commands += ['--global-checker', str(ROOT / program)]
    subprocess.run(commands, check=True, capture_output=True, text=True, timeout=180)
    derived = json.loads((OUT / 'certificates/validation.json').read_text())

    rows = []
    # The unreduced proof remains valid in the baseline, but its old transport
    # packet is deliberately inadmissible in the new primitive interface.
    original = n.p.contextual_seed_congruence()
    for producer, programs, predecessor, dialect in (
        (n.p, local_programs, 'reference/checkers/neutral_scope/checker.py', 'local'),
        (global_producer, global_programs,
         'reference/checkers/prevalidated_elimination/checker_structure.py', 'global'),
    ):
        packet = producer.Emitter().packet(original)
        (OUT / 'certificates' / ('contextual_induction_original_' + dialect + '.json')).write_text(
            json.dumps(packet, separators=(',', ':')) + '\n')
        for program in programs + [predecessor]:
            expected = program == predecessor
            for optimized in (False, True):
                accepted = run_checker(program, packet, optimized)
                rows.append({'case': 'original_contextual_induction_' + dialect,
                             'program': program, 'optimized': optimized,
                             'expected': expected, 'accepted': accepted,
                             'pass': accepted == expected})
    for case in n.p.build_cases():
        if 'proof_tree' not in case:
            continue
        proof = n.eliminate_zero_sources(case['proof_tree'])
        audit = n.audit(n.p.expand_proof(proof))
        if audit['forbidden_zero_sources']:
            raise RuntimeError('Unremoved zero-source transport in ' + case['name'])
        for producer, programs in ((n.p, local_programs), (global_producer, global_programs)):
            packet = producer.Emitter(not case['accept']).packet(proof)
            for program in programs:
                for optimized in (False, True):
                    accepted = run_checker(program, packet, optimized)
                    rows.append({'case': case['name'], 'program': program,
                                 'optimized': optimized, 'expected': case['accept'],
                                 'accepted': accepted, 'pass': accepted == case['accept']})

    # Independent raw controls cover scope, phase separation, and unproved majors.
    controls = {
        'closed_false': [[0, [0]]],
        'unallocated_parameter': [[-1, -1]],
    }
    for filename in ('false_float_capture.json', 'future_witness_capture.json',
                     'scalar_false_sentinel_attack.json', 'phase_guard_counterexample.json'):
        controls[filename] = json.loads((ROOT / 'tests' / filename).read_text())
    for name, packet in controls.items():
        for program in local_programs + global_programs:
            for optimized in (False, True):
                accepted = run_checker(program, packet, optimized)
                rows.append({'case': name, 'program': program, 'optimized': optimized,
                             'expected': False, 'accepted': accepted, 'pass': not accepted})
    (OUT / 'checks.json').write_text(json.dumps(rows, indent=2) + '\n')
    derived_runs = sum(len(c['checks']) for e in derived['examples'] for c in e['certificates'])
    summary = {
        'frozen_comparison_modules': len(identities),
        'named_and_control_runs': len(rows),
        'named_and_control_passed': sum(r['pass'] for r in rows),
        'derived_certificate_runs': derived_runs,
        'derived_certificate_passed': sum(c['accepted'] for e in derived['examples']
                                          for p in e['certificates'] for c in p['checks']),
        'total_runs': len(rows) + derived_runs,
        'all_passed': all(r['pass'] for r in rows) and derived['all_requested_checks_passed'],
        'baseline_minima': measurements['baseline_minima'],
        'selected_minima': measurements['selected_minima'],
        'proof_status': 'Written universal proof; finite executable certificates; no new Lean/Rocq formalization.',
    }
    (OUT / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps(summary, indent=2))
    if not summary['all_passed']:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
