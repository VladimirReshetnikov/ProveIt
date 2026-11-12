"""Run the two self-contained suites and replay the independent adversaries."""
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def main():
    for relative in ('raw/verify.py', 'zero/verify.py', 'measure.py'):
        result = subprocess.run([sys.executable, str(ROOT / relative)],
                                cwd=ROOT, text=True, capture_output=True)
        if result.returncode:
            raise RuntimeError(relative + '\n' + result.stdout + result.stderr)
        print(relative + ': passed')
    independent = []
    for kind, program in [('raw', 'raw/checker.py'), ('zero', 'zero/code/checker.py')]:
        folder = ROOT / 'validation' / ('independent_' + kind)
        old = json.loads((folder / 'results.json').read_text())
        cases = {}
        for item in old['results']:
            cases[item['case']] = item['expected_accept']
        for case, expected in cases.items():
            certificate = (folder / (case + '.json')).read_text()
            for optimized in (False, True):
                command = [sys.executable] + (['-O'] if optimized else []) + [str(ROOT / program)]
                run = subprocess.run(command, input=certificate, text=True, capture_output=True)
                observed = run.returncode == 0 and run.stdout.strip() == 'ACCEPT'
                if observed != expected:
                    raise RuntimeError(f'Independent {kind}/{case}, optimized={optimized}')
                independent.append({'system': kind, 'case': case,
                                    'optimized': optimized, 'accepted': observed})
    result = {'status': 'all passed', 'independent_cli_checks': len(independent),
              'independent_results': independent,
              'raw': json.loads((ROOT / 'raw/evidence/verification.json').read_text()),
              'zero': json.loads((ROOT / 'zero/evidence/verification.json').read_text())}
    (ROOT / 'evidence/reproduction.json').write_text(json.dumps(result, indent=2) + '\n')
    print(f'Independent replay: {len(independent)} expected CLI outcomes passed')
    print('ALL CHECKS PASSED')


if __name__ == '__main__':
    main()
