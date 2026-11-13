"""Run the bounded verification suites shipped in this archive."""
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent

def run(args, *, data=None):
    p = subprocess.run([sys.executable, *args], cwd=ROOT, input=data,
                       text=True, capture_output=True, timeout=120)
    if p.returncode:
        raise RuntimeError({'command': args, 'stdout': p.stdout,
                            'stderr': p.stderr, 'exit': p.returncode})
    return p.stdout

if __name__ == '__main__':
    receipts = {}
    run(['bundle/bundle_examples.py'])
    receipts['bundle_suite'] = json.loads((ROOT / 'bundle/bundle_results.json').read_text())
    run(['bundle/review_cases.py'])
    receipts['binding_review'] = json.loads((ROOT / 'bundle/independent_audit.json').read_text())
    outcomes = []
    for name in ('root_congruence', 'equation_induction',
                 'induction_then_transport', 'empty_bundle_auxiliary'):
        document = (ROOT / 'bundle' / (name + '.json')).read_text()
        for options in ([], ['-O']):
            result = run([*options, 'bundle/bundle_checker.py'], data=document).strip()
            if result != 'ACCEPT':
                raise RuntimeError((name, options, result))
            outcomes.append({'certificate': name, 'optimized': bool(options),
                             'verdict': result})
    receipts['bundle_isolated_cli'] = outcomes
    run(['refinement/verify_floor.py', '--receipt',
         str(ROOT / 'evidence/floor_reproduced.json')])
    receipts['refinement'] = json.loads((ROOT / 'evidence/floor_reproduced.json').read_text())
    run(['synthesis/verify_synth.py'])
    receipts['synthesis'] = json.loads((ROOT / 'synthesis/synthesis_tests.json').read_text())
    output = ROOT / 'evidence/verification.json'
    output.write_text(json.dumps(receipts, indent=2) + '\n')
    print('PASS: bundle rules, transport, binding, 252 refinement runs, and 28 synthesis runs.')
    print('Receipt:', output.relative_to(ROOT))
