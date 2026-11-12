"""Compare the exact 479-byte refactor with its 487-byte control."""
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import json
import platform
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
CONTROL = ROOT / 'controls/checker_487.py'
CANDIDATE = ROOT / 'code/checker_479.py'
FILES = sorted((ROOT / 'tests/byte').rglob('*.json'))
FILES.append(ROOT / 'tests/scope/future_scope_attack.json')


def check(task):
    path, optimized = task
    command = [sys.executable, '-I', '-S', '-B'] + (['-O'] if optimized else [])
    def run(program):
        result = subprocess.run(command + [str(program)], input=path.read_bytes(),
                                capture_output=True, timeout=20)
        return result.returncode == 0 and result.stdout == b'ACCEPT\n'
    return {'fixture': str(path.relative_to(ROOT)), 'optimized': optimized,
            'control': run(CONTROL), 'candidate': run(CANDIDATE)}


def main():
    with ThreadPoolExecutor(max_workers=8) as pool:
        rows = list(pool.map(check, [(p, mode) for p in FILES for mode in (False, True)]))
    mismatch = [r for r in rows if r['candidate'] != r['control']]
    bad_scope = [r for r in rows if r['fixture'].startswith('tests/scope/')
                 and (r['candidate'] or r['control'])]
    if mismatch or bad_scope:
        raise AssertionError({'mismatches': mismatch, 'accepted_scope_attack': bad_scope})
    report = {'python': platform.python_version(), 'fixtures': len(FILES),
              'process_executions': 2 * len(rows), 'mismatches': [],
              'scope_attack_rejected': True, 'results': rows}
    (ROOT / 'evidence/byte_validation.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items() if k != 'results'}, indent=2))


if __name__ == '__main__':
    main()
