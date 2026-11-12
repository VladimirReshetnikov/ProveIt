"""Run the packaged evidence without network or repository access."""
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def run(script, output=None):
    result = subprocess.run([sys.executable, str(ROOT / 'code' / script)],
                            cwd=ROOT, check=True, stdout=subprocess.PIPE, text=True)
    if output:
        parsed = json.loads(result.stdout)
        (ROOT / 'evidence' / output).write_text(json.dumps(parsed, indent=2) + '\n')
        print(script + ': ' + str(parsed.get('total', parsed.get('checks', 'complete'))) + ' checks')
    else:
        print(result.stdout.strip())


if __name__ == '__main__':
    run('verify_head.py')
    run('check_weak_head_laws.py', 'weak_head_checks.json')
    run('check_colour_lemmas.py', 'colour_checks.json')
    if (ROOT / 'code' / 'verify_compact477.py').exists():
        run('verify_compact477.py')
    run('measure.py')
