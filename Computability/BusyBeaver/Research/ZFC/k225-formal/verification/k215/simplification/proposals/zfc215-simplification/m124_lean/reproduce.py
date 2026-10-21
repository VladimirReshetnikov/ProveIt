#!/usr/bin/env python3
"""Rebuild the exact-table Lean proof in a fresh private directory."""
from pathlib import Path
import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parent

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--lean', default='lean')
    ap.add_argument('--baseline', type=Path,
                    default=ROOT.parent / 'm124_rocq' / 'k215.native.tm')
    ap.add_argument('--output', type=Path)
    args = ap.parse_args()
    lean = shutil.which(args.lean)
    if not lean:
        raise SystemExit('Lean compiler not found: ' + args.lean)
    out = args.output.resolve() if args.output else Path(tempfile.mkdtemp(prefix='m124-lean-'))
    if args.output:
        out.mkdir(parents=True, exist_ok=False)
    p = subprocess.run([sys.executable, str(ROOT / 'generate_data.py'),
                        str(args.baseline), '--output', str(ROOT / 'Marker124Data.lean'),
                        '--check'], capture_output=True, text=True)
    (out / 'input-check.log').write_text(p.stdout + p.stderr)
    p.check_returncode()
    version = subprocess.run([lean, '--version'], text=True, capture_output=True, check=True).stdout.strip()
    sources = {}
    env = dict(os.environ)
    env['LEAN_PATH'] = str(out)
    modules = []
    for name in ['Marker124Data', 'Marker124']:
        src = ROOT / (name + '.lean')
        shutil.copyfile(src, out / src.name)
        sources[src.name] = hashlib.sha256(src.read_bytes()).hexdigest()
        start = time.monotonic()
        command = [lean, '-j1', '-M3000', '-o', name + '.olean', name + '.lean']
        result = subprocess.run(command, cwd=out, env=env, capture_output=True, text=True)
        log = result.stdout + result.stderr
        (out / (name + '.log')).write_text(log)
        modules.append({'module': name, 'exit_code': result.returncode,
                        'seconds': time.monotonic() - start, 'command': command})
        result.check_returncode()
        if 'sorryAx' in log or 'error:' in log or 'warning:' in log:
            raise RuntimeError('Unexpected admission, compiler error, or warning: ' + name)
        if name == 'Marker124':
            expected = '[propext, Classical.choice, Quot.sound]'
            assert log.count(expected) == 2
    receipt = {
        'status': 'PASS_LEAN_KERNEL', 'version': version,
        'source_sha256': sources, 'modules': modules,
        'axioms': ['propext', 'Classical.choice', 'Quot.sound'],
        'scope': 'Exact native-table all-tape equivalence and counted-state reachability; '
                 'the existing ZFC endpoint model bridge is not integrated.'
    }
    (out / 'build-receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({'output': str(out), **receipt}, indent=2))

if __name__ == '__main__':
    main()
