#!/usr/bin/env python3
"""Run copied rebase controls with copied parent-pair tools; no project replay."""
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
RESEARCH = HERE.parent.parent / 'research'
FILES = {
    'fresh-project-rebase': ('prepare.py', 'test_prepare.py', 'test_real_prepare.py'),
    'fresh-project-closure': ('rebuild.py', 'compare.py', 'run_pair.py'),
}

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    before = {f'{directory}/{name}': sha(RESEARCH / directory / name)
              for directory, names in FILES.items() for name in names}
    saved = HERE / 'inputs'
    saved.mkdir(exist_ok=False)
    for directory, names in FILES.items():
        target = saved / directory; target.mkdir()
        for name in names:
            shutil.copyfile(RESEARCH / directory / name, target / name)
            assert sha(target / name) == before[f'{directory}/{name}']
    runs = []
    for name in ('test_prepare.py', 'test_real_prepare.py'):
        cmd = [sys.executable, str(saved / 'fresh-project-rebase' / name)]
        p = subprocess.run(cmd, capture_output=True, text=True, timeout=300)
        assert p.returncode == 0, (name, p.returncode, p.stdout, p.stderr)
        runs.append({'script': name, 'exit_code': p.returncode, 'stdout': p.stdout, 'stderr': p.stderr})
    assert before == {f'{directory}/{name}': sha(RESEARCH / directory / name)
                      for directory, names in FILES.items() for name in names}
    result = {'status': 'PASS_INDEPENDENT_REBASE_CONTROLS', 'source_sha256': before, 'runs': runs,
              'scope': 'Toy graph and real Lean toy pair only; this is not a full project '
                       'parent-pair acceptance, successor preparation, rebuild or package/dynamic provenance audit.'}
    out = HERE / 'receipt.json'
    with out.open('x') as f:
        json.dump(result, f, indent=2, sort_keys=True); f.write('\n')
    print(result['status'], sha(out), flush=True)

if __name__ == '__main__':
    main()
