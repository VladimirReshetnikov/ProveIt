"""Execute actual deterministic-witness checkers and focused rule controls."""
import copy
import json
import subprocess
import sys
import tempfile
from pathlib import Path

import witness_normalizer as w

ROOT = Path(__file__).resolve().parent


def run(program, packet, optimized=False):
    command = [sys.executable] + (['-O'] if optimized else []) + [str(program)]
    result = subprocess.run(command, input=json.dumps(packet), text=True,
                            capture_output=True, timeout=20)
    return result.returncode == 0 and result.stdout == 'ACCEPT\n'


def main():
    cases = w.build_positive_cases()
    controls = []
    for name, proof in w.supplementary_proofs():
        old = w.p.Emitter().packet(proof)
        controls.append({'name': name + '_untranslated', 'accept': False,
                         'packet': w.marker_normalize(old)})
    forged = copy.deepcopy(w.p.forbidden_compound_progress())
    forged['witness'] = 0  # the witness coordinate is unused in this matrix
    emitter = w.Emitter(allow_forbidden_compound_progress=True)
    controls.append({'name': 'compound_progress_at_zero', 'accept': False,
                     'packet': emitter.packet(forged)})
    controls.extend([
        {'name': 'closed_false', 'accept': False,
         'packet': [[[], 0, [0], 0], [0, [0]]]},
        {'name': 'future_parameter', 'accept': False,
         'packet': [[[], 0, [0], 0], [-1, -1]]},
    ])
    results = []
    programs = ['checker.py', 'checker_explicit_type.py',
                'checker_explicit_list.py', 'readable_checker.py']
    for case in cases + controls:
        for program in programs:
            for optimized in (False, True):
                accepted = run(ROOT.parent / 'code' / program, case['packet'], optimized)
                results.append({'case': case['name'], 'program': program,
                                'optimized': optimized,
                                'expected': case['accept'], 'accepted': accepted,
                                'match': accepted == case['accept']})
    source = (ROOT.parent / 'code/checker.py').read_text()
    mutation = source.replace('(m or t == len(a) % 2 == 0) and k',
                              '(m or t == 0) and k')
    if mutation == source:
        raise ValueError('Guard mutation failed')
    temporary = tempfile.TemporaryDirectory(prefix='ipra-guard-control-')
    mutant = Path(temporary.name) / 'mutant.py'
    mutant.write_text(mutation)
    mutation_results = []
    for optimized in (False, True):
        accepted = run(mutant, controls[2]['packet'], optimized)
        mutation_results.append({'mutation': 'remove_literal_equation_restriction',
                                 'case': controls[2]['name'], 'optimized': optimized,
                                 'accepted': accepted, 'expected': True,
                                 'match': accepted is True})
    receipt = {'cases': len(cases) + len(controls),
               'positive_cases': len(cases), 'negative_cases': len(controls),
               'executions': len(results), 'results': results,
               'mutation_results': mutation_results}
    temporary.cleanup()
    if '--write' in sys.argv:
        (ROOT.parent / 'evidence/witness_verification.json').write_text(json.dumps(receipt, indent=2) + '\n')
    mismatches = [row for row in results + mutation_results if not row['match']]
    print(json.dumps({'executions': len(results),
                      'mutation_controls': len(mutation_results),
                      'mismatches': mismatches}))
    if mismatches:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
