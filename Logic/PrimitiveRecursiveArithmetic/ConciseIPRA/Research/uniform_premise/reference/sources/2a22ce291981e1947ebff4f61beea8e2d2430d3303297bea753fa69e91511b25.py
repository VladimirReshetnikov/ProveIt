"""Replay independently emitted proof packets through the complete CLI."""

import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent


def run(checker, packet, optimize=False):
    command = [sys.executable]
    if optimize:
        command.append('-O')
    command.append(str(checker))
    result = subprocess.run(command, input=json.dumps(packet), text=True,
                            capture_output=True, timeout=5)
    return {
        'returncode': result.returncode,
        'stdout': result.stdout.strip(),
        'stderr_last_line': result.stderr.strip().splitlines()[-1:]
    }


def main():
    subprocess.run([sys.executable, str(ROOT / 'producer.py')], check=True,
                   capture_output=True, text=True)
    cases = json.loads((ROOT / 'cases.json').read_text())['cases']
    results = []
    packaged = ROOT.parent / 'code'
    checkers = ([packaged / 'checker.py', packaged / 'checker_direct.py', packaged / 'checker_ast.py']
                if packaged.is_dir() else
                [ROOT / 'checker_expr.py', ROOT / 'checker.py', ROOT / 'checker_ast.py'])
    for checker in checkers:
        profile = 'iterable' if checker.name == 'checker_ast.py' else 'list'
        for optimize in [False, True]:
            for case in cases:
                observed = run(checker, case['packet'], optimize)
                expected = case.get('accept_by_profile', {}).get(profile, case['accept'])
                passed = (observed['returncode'] == 0 and observed['stdout'] == 'ACCEPT'
                          if expected else
                          observed['returncode'] != 0 and observed['stdout'] == 'REJECT')
                results.append({'checker': checker.name, 'profile': profile, 'optimize': optimize,
                                'case': case['name'], 'expected_accept': expected,
                                'passed': passed, **observed})
    # Each unsafe mutation has a specific certificate rejected by the real
    # checker and accepted after the guard/semantics is changed. This checks
    # that rejection fixtures exercise the intended obligations.
    mutations = [
        ('omit_major_proof', '        c(m, g)\n', '        pass\n',
         'failed_major_does_not_fall_through'),
        ('permit_compound_progress', 'k if m or len(a) % 2 == m else 0',
         'k if m or m == 0 else 0', 'forbidden_compound_progress'),
        ('omit_recursive_image_validation', 'i(u, i([*n, t, u], d=1), 1)',
         'i(u, [*n, t, u], 1)', 'two_child_counter_constant_update'),
        ('restore_wrong_I0_semantics', 'if n else [t]', 'if n else t',
         'old_I0_equation_is_false_for_J'),
    ]
    mutation_results = []
    by_name = {case['name']: case for case in cases}
    with tempfile.TemporaryDirectory(prefix='j_checker_mutations_') as directory:
        for checker in checkers:
            source = checker.read_text()
            for name, old, new, case_name in mutations:
                if source.count(old) != 1:
                    raise AssertionError('Mutation no longer matches exactly once: ' + name)
                mutated = source.replace(old, new)
                path = Path(directory) / (checker.stem + '_' + name + '.py')
                path.write_text(mutated)
                for optimize in [False, True]:
                    observed = run(path, by_name[case_name]['packet'], optimize)
                    passed = observed['returncode'] == 0 and observed['stdout'] == 'ACCEPT'
                    mutation_results.append({'checker': checker.name, 'mutation': name,
                                             'case': case_name, 'optimize': optimize,
                                             'expected_mutant_accept': True, 'passed': passed,
                                             **observed})
    output = {
        'scope': 'Finite CLI verification of complete checkers; not a formal soundness theorem or a certificate of the full arithmetic bootstrap.',
        'python': sys.version,
        'checker_sha256': {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in checkers},
        'case_count': len(cases),
        'canonical_case_count': sum(not c.get('alias_boundary') for c in cases),
        'positive_cases': sum(c['accept'] for c in cases if not c.get('alias_boundary')),
        'negative_cases': sum(not c['accept'] for c in cases if not c.get('alias_boundary')),
        'alias_boundary_cases': sum(bool(c.get('alias_boundary')) for c in cases),
        'cli_runs': len(results),
        'passed_runs': sum(r['passed'] for r in results),
        'failed_runs': [r for r in results if not r['passed']],
        'mutation_controls': mutation_results,
        'mutation_runs': len(mutation_results),
        'passed_mutation_runs': sum(r['passed'] for r in mutation_results),
        'failed_mutation_runs': [r for r in mutation_results if not r['passed']],
        'results': results,
    }
    (ROOT / 'test_summary.json').write_text(json.dumps(output, indent=2) + '\n')
    lines = [
        'SUCCESSOR-SEEDED J COMPLETE-CHECKER RECEIPT',
        '=========================================',
        '',
        output['scope'],
        '',
        'Python: ' + sys.version.replace('\n', ' '),
        'Distinct fixtures: ' + str(output['case_count']),
        'Common fixtures: %s (%s accepted; %s rejected)' %
        (output['canonical_case_count'], output['positive_cases'], output['negative_cases']),
        'Profile-boundary aliases: ' + str(output['alias_boundary_cases']),
        'Complete CLI runs passed: %s / %s' % (output['passed_runs'], output['cli_runs']),
        'Targeted mutation controls passed: %s / %s' %
        (output['passed_mutation_runs'], output['mutation_runs']),
        '',
        'Exact source SHA-256 hashes:',
    ]
    lines.extend('  ' + name + '  ' + digest
                 for name, digest in output['checker_sha256'].items())
    lines.extend(['', 'For every checker, both ordinary Python and -O were run.',
                  'The three alias fixtures are rejected by list dispatch and accepted',
                  'by iterable dispatch. Their decoded numerical equations are true.',
                  'All remaining fixtures have identical expectations across profiles.',
                  '', 'Any source change requires a fresh run and new hashes.'])
    if output['failed_runs'] or output['failed_mutation_runs']:
        lines.extend(['', 'FAILURES PRESENT: inspect test_summary.json.'])
    (ROOT / 'test_summary.txt').write_text('\n'.join(lines) + '\n')
    print(json.dumps({k: output[k] for k in ('case_count', 'canonical_case_count', 'alias_boundary_cases', 'positive_cases',
                                           'negative_cases', 'cli_runs', 'passed_runs',
                                           'failed_runs', 'mutation_runs',
                                           'passed_mutation_runs', 'failed_mutation_runs')}, indent=2))
    if output['failed_runs'] or output['failed_mutation_runs']:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
