#!/usr/bin/env python3
"""Compile and recursively check the standalone prototype, recording exact inputs.

Use a normal Coq installation, or set COQLIB/OCAMLFIND_CONF for a local one.
This does not build or modify the ProveIt K215 endpoint.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import shutil
import subprocess
import time

HERE = Path(__file__).resolve().parent
FILES = ['OracleFootprint.v', 'Support215217.v']

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--coqc', default='coqc')
    ap.add_argument('--coqchk', default=None)
    args = ap.parse_args()
    compiler = Path(shutil.which(args.coqc) or args.coqc).resolve()
    checker = Path(args.coqchk).resolve() if args.coqchk else compiler.with_name('coqchk')
    version = subprocess.check_output([str(compiler), '--version'], text=True)
    records = []
    commands = [[str(compiler), name] for name in FILES]
    commands.append([str(checker), '-silent', '-o', 'OracleFootprint', 'Support215217'])
    for i, command in enumerate(commands):
        start = time.monotonic()
        result = subprocess.run(command, cwd=HERE, text=True, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, timeout=120)
        log = HERE / f'check-{i+1}.txt'
        log.write_text(result.stdout)
        records.append({'command': command, 'exit_code': result.returncode,
                        'elapsed_seconds': round(time.monotonic()-start, 6),
                        'log': log.name, 'log_sha256': sha(log),
                        'closed_reports': result.stdout.count('Closed under the global context')})
        if result.returncode:
            raise SystemExit(result.stdout)
    evidence = {'scope': 'Standalone generic transport and finite literal-table witness only; not the K215 endpoint',
                'compiler_version': version.strip(),
                'environment': {k:os.environ.get(k) for k in ['COQLIB', 'OCAMLFIND_CONF']},
                'sources': {name:sha(HERE/name) for name in FILES},
                'driver_sha256': sha(Path(__file__).resolve()), 'records':records,
                'status':'PASS_STANDALONE_COQ_KERNEL'}
    (HERE / 'verification.json').write_text(json.dumps(evidence, indent=2)+'\n')
    print(json.dumps({'status':evidence['status'],'compiler':evidence['compiler_version'],
                      'closed_reports':sum(r['closed_reports'] for r in records)},indent=2))

if __name__ == '__main__':
    main()
