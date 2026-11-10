"""Complete-program proof-packet tests and three targeted guard mutations.

These are finite implementation checks, not a proof-assistant verification.
No checker imports this runner or the producer.
"""
import hashlib
import json
from pathlib import Path
import platform
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]

def run(program, packet, optimized=False):
    command = [sys.executable, '-I'] + (['-O'] if optimized else []) + [str(program)]
    result = subprocess.run(command, input=json.dumps(packet), text=True,
                            capture_output=True, timeout=10)
    if result.returncode == 0 and result.stdout.strip() == 'ACCEPT':
        return True
    if result.returncode != 0 and result.stdout.strip() == 'REJECT':
        return False
    raise AssertionError(dict(command=command, exit=result.returncode,
                              stdout=result.stdout, stderr=result.stderr[-1500:]))

def main():
    cases = json.loads((ROOT / 'tests/cases.json').read_text())['cases']
    programs = ['checker.py', 'checker_bytes.py', 'checker_ast.py', 'readable_checker.py']
    failures = []
    count = 0
    for program in programs:
        for optimized in (False, True):
            for case in cases:
                accepted = run(ROOT / 'code' / program, case['packet'], optimized)
                count += 1
                if accepted != case['accept']:
                    failures.append(dict(program=program, optimized=optimized,
                                         case=case['name'], accepted=accepted))
    mutations = [
        ('constructed_successor', 'u and [n]', 'u and n',
         'false_annotated_counter_equation', 'False R(0,0;0)=0 becomes an inserted hypothesis.'),
        ('literal_equation_induction', 'm or len(a) % 2 == m', 'm or m == 0',
         'compound_progress_forbidden', 'A compound induction hypothesis is improperly supplied.'),
        ('allocated_parameter_scope', 'k <= a < d', 'a < d',
         'forged_parameter_reflexivity', 'An unallocated numerical parameter becomes usable.')]
    controls = []
    original = (ROOT / 'code/checker.py').read_text()
    by_name = {case['name']: case for case in cases}
    with tempfile.TemporaryDirectory(prefix='ipra-guard-controls-') as directory:
        for name, before, after, case_name, reason in mutations:
            if original.count(before) != 1:
                raise AssertionError('Mutation target changed: ' + name)
            mutant = Path(directory) / (name + '.py')
            mutant.write_text(original.replace(before, after))
            packet = by_name[case_name]['packet']
            for optimized in (False, True):
                accepted = run(mutant, packet, optimized)
                controls.append(dict(name=name, optimized=optimized,
                                     accepted=accepted, expected=True, reason=reason))
                if not accepted:
                    failures.append(dict(mutant=name, optimized=optimized,
                                         reason='Targeted guard mutation was not detected'))
    result = dict(status='PASS' if not failures else 'FAIL', python=platform.python_version(),
                  proof_packets=len(cases), positive=sum(c['accept'] for c in cases),
                  negative=sum(not c['accept'] for c in cases),
                  complete_program_runs=count, mutation_runs=len(controls),
                  programs={name: hashlib.sha256((ROOT/'code'/name).read_bytes()).hexdigest()
                            for name in programs}, mutations=controls, failures=failures,
                  scope='Finite standalone process checks, ordinary and optimized Python; '
                        'not a formal proof of soundness, completeness, or bi-interpretability.')
    if '--record' in sys.argv:
        (ROOT/'evidence/checker_validation.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))
    if failures:
        raise SystemExit(1)

if __name__ == '__main__':
    main()
