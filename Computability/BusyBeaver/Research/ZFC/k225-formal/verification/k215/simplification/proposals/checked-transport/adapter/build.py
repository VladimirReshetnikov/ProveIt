#!/usr/bin/env python3
"""Fresh minimal adapter build; excludes the complete-ZFC integration client.

Usage: python3 build.py --native-dir /path/to/transport --out /fresh/directory
Requires Coq 8.18.0 or a compatible Rocq toolchain with coqc/coqchk commands.
"""
import argparse
import fcntl
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import time

ROOT = Path(__file__).resolve().parent


def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--native-dir', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--lock', type=Path)
    args = parser.parse_args()
    out = args.out.resolve()
    if out.exists() and any(out.iterdir()):
        raise SystemExit('Use an empty output directory for a fresh build.')
    out.mkdir(parents=True, exist_ok=True)
    (out/'logs').mkdir()
    files = [
        'BusyCoq/LibTactics.v', 'BusyCoq/Helper.v', 'BusyCoq/TM.v',
        'K215F/Table230.v', 'K215F/TM230.v',
        'NativeContext.v', 'LiteralBindings.v', 'NativeSparseAdapter.v', 'ContextSparse.v', 'ContextLiteralSparse.v',
    ]
    for name in files:
        source = args.native_dir/name if name in ('NativeContext.v','LiteralBindings.v') else ROOT/name
        target = out/name
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, target)
    options = ['-Q', 'BusyCoq', 'BusyCoq', '-Q', 'K215F', 'K215F']
    receipt = {
        'toolchain': subprocess.check_output(['coqc','--version'], text=True),
        'inputs': {name:digest(out/name) for name in files},
        'checks': [],
        'excluded': {'ContextZFCClient.v': 'Requires the full maintained K215 ZFC dependency closure, not rebuilt by this minimal driver.'},
    }
    lock = args.lock or out.parent/'context-adapter-compiler.lock'
    with lock.open('w') as handle:
        fcntl.flock(handle, fcntl.LOCK_EX)
        for name in files:
            command = ['coqc',*options,name]
            t = time.monotonic()
            proc = subprocess.run(command, cwd=out, capture_output=True, text=True)
            log = out/'logs'/(name.replace('/','_')+'.log')
            log.write_text(proc.stdout+proc.stderr)
            receipt['checks'].append({'source':name,'command':command,'exit':proc.returncode,
                                     'seconds':time.monotonic()-t,'log_sha256':digest(log)})
            print(name, proc.returncode, flush=True)
            if proc.returncode:
                receipt['status'] = 'FAILED'
                (out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
                raise SystemExit(proc.stdout+proc.stderr)
        command = ['coqchk','-silent',*options,'ContextLiteralSparse']
        t = time.monotonic()
        proc = subprocess.run(command,cwd=out,capture_output=True,text=True)
        log=out/'logs/coqchk.log';log.write_text(proc.stdout+proc.stderr)
        receipt['checks'].append({'command':command,'exit':proc.returncode,
                                 'seconds':time.monotonic()-t,'log_sha256':digest(log)})
        receipt['status'] = 'PASS' if proc.returncode == 0 else 'FAILED'
        receipt['objects'] = {str(p.relative_to(out)):digest(p) for p in sorted(out.rglob('*.vo'))}
        (out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
        print('coqchk',proc.returncode,flush=True)
        if proc.returncode:
            raise SystemExit(proc.stdout+proc.stderr)


if __name__ == '__main__':
    main()
