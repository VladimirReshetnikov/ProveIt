#!/usr/bin/env python3
"""Independently rerun copied selective successor builder/comparator controls."""
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
RESEARCH = HERE.parent.parent / 'research'
FILES = {
    'fresh-project-rebase': ('prepare.py', 'rebuild.py', 'compare.py', 'run_pair.py',
                             'test_prepare.py', 'test_real_prepare.py'),
    'fresh-project-closure': ('rebuild.py', 'compare.py', 'run_pair.py'),
}

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    before = {f'{directory}/{name}': sha(RESEARCH / directory / name)
              for directory, names in FILES.items() for name in names}
    saved = HERE / 'inputs'; saved.mkdir(exist_ok=False)
    for directory, names in FILES.items():
        dest = saved / directory; dest.mkdir()
        for name in names:
            shutil.copyfile(RESEARCH / directory / name, dest / name)
            assert sha(dest / name) == before[f'{directory}/{name}']
    runs = []
    for name in ('test_prepare.py', 'test_real_prepare.py'):
        p = subprocess.run([sys.executable, str(saved / 'fresh-project-rebase' / name)],
                           capture_output=True, text=True, timeout=300)
        assert p.returncode == 0, (name, p.returncode, p.stdout, p.stderr)
        runs.append({'script': name, 'exit_code': p.returncode, 'stdout': p.stdout, 'stderr': p.stderr})
    assert before == {f'{directory}/{name}': sha(RESEARCH / directory / name)
                      for directory, names in FILES.items() for name in names}
    result = {'status': 'PASS_INDEPENDENT_SELECTIVE_REBUILD_CONTROLS',
              'source_sha256': before, 'runs': runs,
              'scope': 'Copied source, toy project and real Lean toy parent/successor pairs only; '
                       'not a full project successor replay or transitive package/dynamic provenance audit.'}
    out = HERE / 'receipt.json'
    with out.open('x') as stream:
        json.dump(result, stream, indent=2, sort_keys=True); stream.write('\n')
    print(result['status'], sha(out), flush=True)

if __name__ == '__main__':
    main()
