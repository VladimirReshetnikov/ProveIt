"""Reproduce the complete checker measurements and the scope regression.

This is untrusted support code. The standalone checkers import none of it.
"""
import json
import runpy
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def main():
    runpy.run_path(str(ROOT / 'tests/reproduce_checkers.py'))['reproduce']()
    payload = (ROOT / 'tests/list_context_leak.json').read_bytes()
    correct = ROOT / 'code/checker_tokens.py'
    text = correct.read_text()
    old = 'g += (i(h, (m or len(a) == 2) and k),)'
    new = 'g += [i(h, (m or len(a) == 2) and k)]'
    if text.count(old) != 1 or text.count('c(q(), ())') != 1:
        raise ValueError('The regression mutant no longer matches the audited source')
    mutant_text = text.replace(old, new).replace('c(q(), ())', 'c(q(), [])')
    controls = []
    with tempfile.TemporaryDirectory(prefix='ipra-scope-control-') as temporary:
        mutant = Path(temporary) / 'deliberately_unsound_list_mutant.py'
        mutant.write_text(mutant_text)
        for optimized in (False, True):
            for label, path, expected in (
                ('correct_tuple_checker', correct, False),
                ('deliberately_unsound_list_mutant', mutant, True),
            ):
                command = [sys.executable]
                if optimized:
                    command.append('-O')
                command.append(str(path))
                result = subprocess.run(command, input=payload, capture_output=True,
                                        timeout=20)
                accepted = result.returncode == 0 and result.stdout == b'ACCEPT\n'
                row = {'program': label, 'optimized': optimized,
                       'expected_acceptance': expected, 'accepted': accepted,
                       'exit_code': result.returncode}
                controls.append(row)
                if accepted != expected:
                    raise ValueError('Scope-control mismatch: ' + json.dumps(row))
    baseline = json.loads((ROOT / 'evidence/checker_validation.json').read_text())
    summary = {
        'candidate_control_comparisons': baseline['comparisons'],
        'candidate_control_processes': baseline['process_executions'],
        'scope_control_processes': len(controls),
        'total_process_executions': baseline['process_executions'] + len(controls),
        'mismatches': 0,
        'scope_controls': controls,
        'limitation': 'Finite process checks plus written preservation proofs; '
                      'no new Lean/Rocq verification.',
    }
    (ROOT / 'evidence/reproduction_summary.json').write_text(
        json.dumps(summary, indent=2) + '\n')
    (ROOT / 'evidence/verification_summary.tex').write_text(
        'The final reproduction run completed \\textbf{'
        + str(baseline['comparisons'])
        + ' candidate/control comparisons} ('
        + str(baseline['process_executions'])
        + ' Python processes) and four additional scope-control executions: '
        + '\\textbf{'
        + str(summary['total_process_executions'])
        + ' processes in total, with zero discrepancies from their prescribed '
          'outcomes}. The correct checker rejects the scope attack in both '
          'modes; the deliberate mutable-list mutant accepts it in both.\n')
    print(json.dumps({k: v for k, v in summary.items() if k != 'scope_controls'}))


if __name__ == '__main__':
    main()
