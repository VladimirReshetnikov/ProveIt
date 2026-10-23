#!/usr/bin/env python3
"""Fresh, serial component build; writes an honest source/object/log receipt."""
import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", type=Path, help="Optional checkout; otherwise use pinned vendor sources")
    ap.add_argument("--lean", required=True, type=Path)
    ap.add_argument("--out", required=True, type=Path)
    ap.add_argument("--target", default="BusyBeaver.ZFC.KLeftFrame215")
    ap.add_argument("--lock", type=Path, default=Path('/tmp/proveit-proof-compiler.lock'))
    args = ap.parse_args()
    own = Path(__file__).parent
    upstream = args.repo / "Computability/BusyBeaver/Lean" if args.repo else own / "vendor"
    root = args.out.resolve()
    if root.exists():
        raise SystemExit("Use a fresh output directory")
    root.mkdir(parents=True)
    sources = {}
    order = []

    def visit(name):
        if name in sources:
            return
        rel = Path(*name.split('.')).with_suffix('.lean')
        src = own / rel
        if not src.exists():
            src = upstream / rel
        if not src.exists():
            raise RuntimeError(f"Missing project source {name}")
        imports = re.findall(r'^import\s+([\w.]+)', src.read_text(), re.M)
        project_imports = [x for x in imports if x.startswith('BusyBeaver.')]
        sources[name] = {'origin':str(src), 'sha256':sha(src), 'imports':imports,
                         'project_imports': project_imports, 'rel':str(rel)}
        for imp in project_imports:
            visit(imp)
        order.append(name)

    visit(args.target)
    for name in order:
        rel = Path(sources[name]['rel'])
        dst = root / rel
        dst.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(sources[name]['origin'], dst)
    version = subprocess.check_output([str(args.lean),'--version'],text=True).strip()
    records = []
    env = dict(os.environ, LEAN_PATH=str(root))
    (root/'logs').mkdir()
    for name in order:
        rel = Path(sources[name]['rel'])
        obj = rel.with_suffix('.olean')
        command = [str(args.lean), '-o', str(obj), str(rel)]
        log = root/'logs'/f'{name}.log'
        started = time.monotonic()
        args.lock.parent.mkdir(parents=True, exist_ok=True)
        with args.lock.open('a') as lock, log.open('w') as stream:
            fcntl.flock(lock, fcntl.LOCK_EX)
            p = subprocess.run(command,cwd=root,env=env,stdout=stream,stderr=subprocess.STDOUT)
        record = {'module':name,'source':sources[name], 'command':command,
                  'cwd':str(root),'returncode':p.returncode,
                  'elapsed_seconds':round(time.monotonic()-started,6),
                  'log_sha256':sha(log), 'object_sha256':sha(root/obj) if (root/obj).exists() else None,
                  'import_objects':{x:sha(root/Path(*x.split('.')).with_suffix('.olean'))
                    for x in sources[name]['project_imports']}}
        records.append(record)
        receipt = {'status':'PASS' if p.returncode==0 and name==order[-1] else 'IN_PROGRESS' if p.returncode==0 else 'FAIL',
                   'toolchain':version,'target':args.target,'records':records,
                   'full_zfc_endpoint_rebuilt':False,
                   'scope':'Append-frame component and literal template contracts only'}
        (root/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
        print(name,p.returncode,record['elapsed_seconds'],flush=True)
        if p.returncode:
            print(log.read_text(),flush=True)
            raise SystemExit(p.returncode)


if __name__ == '__main__':
    main()
