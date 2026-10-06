#!/usr/bin/env python3
"""Build Gowers modules in dependency order, with exactly one Lean worker.

Uses the installed toolchain and Lake's package caches. Does not download or
modify dependencies. Run from any directory; default target is GowersSzemeredi.
"""
from pathlib import Path
import fcntl
import os
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[3]
SOURCE = ROOT / 'Combinatorics/Ramsey/Lean'
OUTPUT = ROOT / '.lake/build/lib/lean'


def main():
    OUTPUT.mkdir(parents=True, exist_ok=True)
    # Separate invocations must not compile into the same cache concurrently.
    lock = (OUTPUT / '.gowers-build.lock').open('w')
    fcntl.flock(lock, fcntl.LOCK_EX)
    env = dict(os.environ)
    paths = [OUTPUT] + sorted((ROOT / '.lake/packages').glob('*/.lake/build/lib/lean'))
    env['LEAN_PATH'] = os.pathsep.join(map(str, paths))
    done = set()

    def build(module):
        if module in done:
            return
        source = SOURCE / (module.replace('.', '/') + '.lean')
        if not source.exists():
            raise SystemExit(f'Missing source: {source}')
        dependencies = re.findall(r'^import\s+(\S+)', source.read_text(), re.M)
        local = [d for d in dependencies if d.startswith('GowersSzemeredi')]
        for dependency in local:
            build(dependency)
        target = OUTPUT / (module.replace('.', '/') + '.olean')
        inputs = [source, ROOT / 'lean-toolchain', ROOT / 'lake-manifest.json']
        inputs += [OUTPUT / (d.replace('.', '/') + '.olean') for d in local]
        if target.exists() and all(p.stat().st_mtime < target.stat().st_mtime for p in inputs):
            done.add(module)
            return
        target.parent.mkdir(parents=True, exist_ok=True)
        print(f'Checking {module}', flush=True)
        subprocess.run(['lean', '-o', str(target), str(source)], cwd=ROOT, env=env, check=True)
        done.add(module)

    for module in sys.argv[1:] or ['GowersSzemeredi']:
        build(module)
    print(f'Checked {len(done)} modules (including up-to-date dependencies).', flush=True)


if __name__ == '__main__':
    main()
