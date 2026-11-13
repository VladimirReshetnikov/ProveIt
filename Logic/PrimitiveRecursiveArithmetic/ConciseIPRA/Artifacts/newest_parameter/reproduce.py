"""Run all mathematical artifact checks; no third-party Python packages."""
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def main():
    summaries = {}
    for name in ('verify_native', 'verify_guarded', 'verify_arithmetic', 'measure'):
        run = subprocess.run([sys.executable, str(ROOT / 'code' / (name + '.py'))],
                             cwd=ROOT, capture_output=True, text=True)
        if run.returncode:
            print(run.stdout)
            print(run.stderr, file=sys.stderr)
            raise SystemExit(run.returncode)
        print(name + ': PASS')
        summaries[name] = dict(status='PASS', returncode=run.returncode)
    native = ROOT / 'code' / 'checker_native.py'
    examples = sorted((ROOT / 'examples' / 'native').glob('*.json'))
    for path in examples:
        run = subprocess.run([sys.executable, str(native)], input=path.read_text(),
                             cwd=ROOT, capture_output=True, text=True)
        assert run.returncode == 0 and run.stdout.strip() == 'ACCEPT', path.name
    summaries['native_cli'] = dict(status='PASS', certificates=len(examples))
    report = dict(status='PASS', python=sys.version.split()[0], results=summaries,
                  limitations='The universal equivalence and full predecessor theorem are written '
                              'proofs. Finite and symbolic tests do not replace their formalization.')
    (ROOT / 'evidence' / 'reproduction.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
