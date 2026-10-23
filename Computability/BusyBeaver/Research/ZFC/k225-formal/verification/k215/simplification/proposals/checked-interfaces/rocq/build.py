#!/usr/bin/env python3
"""Fresh focused Coq build of lookup-parametric normalized K215 source proof.

This is not a build of the binary-machine/ZFC endpoint. The default lane is
the installed Coq 8.18 compiler; Rocq 9.1 keeps the unmodified dependency.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import shutil
import subprocess
import time

ROOT = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--out', type=Path, required=True)
    ap.add_argument('--coqc', default='coqc')
    ap.add_argument('--coqchk', default='coqchk')
    ap.add_argument('--baseline', action='store_true')
    ap.add_argument('--recursive', action='store_true')
    args = ap.parse_args()
    out = args.out.resolve()
    if out.exists() and any(out.iterdir()):
        raise SystemExit('Output must be new or empty.')
    work, logs = out/'work', out/'logs'
    work.mkdir(parents=True)
    logs.mkdir()
    coqc = shutil.which(args.coqc)
    coqchk = shutil.which(args.coqchk)
    if coqc is None or (args.recursive and coqchk is None):
        raise SystemExit('Requested compiler/auditor was not found.')
    version = subprocess.check_output([coqc, '--version'], text=True).strip()
    compat = 'version 8.18.' in version
    if not compat and 'version 9.1.' not in version:
        raise SystemExit('Use Coq 8.18 or the untested production Rocq 9.1 lane.')
    order = (['Compat818.v'] if compat else []) + [
        'deps/K230/RM.v', 'deps/K230/RMEquiv.v', 'deps/K230/Prog230.v',
        'deps/K230P/Bisim230.v', 'deps/K215F/Prog215.v',
        'deps/K215F/DagPerm.v', 'deps/K215F/PathCodec.v',
        'deps/K215F/NormalizedCert215.v']
    if args.baseline:
        order += ['deps/K215F/NormalizedBisim.v', 'BaselineSource215.v']
    order += ['PathEq.v', 'LookupNormalized.v', 'CheckedTree.v', 'BoundaryCases.v',
              'Source215Direct.v', 'deps/K215F/Source215.v', 'SourceClient.v']
    flags = ['-Q', 'deps/K230', 'K230', '-Q', 'deps/K230P', 'K230P',
             '-Q', 'deps/K215F', 'K215F']
    receipt = {
        'schema': 'k215-checked-lookup-v1',
        'scope': 'Exact all-register source equivalence; not binary-machine/ZFC endpoint',
        'toolchain': version, 'compiler_sha256': sha(coqc),
        'fresh': True, 'complete': False,
        'compatibility_import': compat, 'sources': [], 'checks': [],
        'driver_sha256': sha(__file__)}

    def save():
        (out/'result.json').write_text(json.dumps(receipt, indent=2)+'\n')

    for rel in order:
        src = ROOT/rel
        if rel == 'deps/K230/RMEquiv.v':
            src = ROOT/'deps/K230/RMEquiv.rocq91.v'
        elif rel == 'BaselineSource215.v':
            src = ROOT/'deps/K215F/Source215.v'
        elif rel == 'deps/K215F/Source215.v':
            src = ROOT/'Source215.v'
        data = src.read_bytes()
        if rel == 'deps/K230/RMEquiv.v' and compat:
            needle = b'From K230 Require Import RM.'
            if data.count(needle) != 1:
                raise SystemExit('Unexpected compatibility import site.')
            data = data.replace(needle, needle+b'\nRequire Import Compat818.')
        dst = work/rel
        dst.parent.mkdir(parents=True, exist_ok=True)
        dst.write_bytes(data)
        receipt['sources'].append({
            'module': rel, 'delivered': str(src.relative_to(ROOT)),
            'delivered_sha256': sha(src), 'compiled_sha256': sha(dst)})
    save()

    def run(name, cmd):
        print('CHECK '+name, flush=True)
        log = logs/(name.replace('/', '_')+'.log')
        start = time.monotonic()
        with log.open('w') as stream:
            proc = subprocess.Popen(cmd, cwd=work, stdout=stream,
                                    stderr=subprocess.STDOUT)
            _, status, usage = os.wait4(proc.pid, 0)
            proc.returncode = os.waitstatus_to_exitcode(status)
        content = log.read_text()
        row = {'name': name, 'argv': cmd, 'exit_code': proc.returncode,
               'seconds': round(time.monotonic()-start, 3),
               'max_rss_kib': usage.ru_maxrss,
               'closed_reports': content.count('Closed under the global context'),
               'log_sha256': sha(log)}
        if name.endswith('.v') and proc.returncode == 0:
            row['object_sha256'] = sha((work/name).with_suffix('.vo'))
        receipt['checks'].append(row)
        save()
        print(json.dumps(row), flush=True)
        if proc.returncode:
            print(content)
            raise SystemExit(proc.returncode)
        return content

    expected = {'LookupNormalized.v': 1, 'CheckedTree.v': 2,
                'Source215Direct.v': 2, 'deps/K215F/Source215.v': 1,
                'SourceClient.v': 1, 'BaselineSource215.v': 1, 'BoundaryCases.v': 3}
    for rel in order:
        text = run(rel, [coqc, *flags, rel])
        if rel in expected and (text.count('Closed under the global context')
                                != expected[rel] or 'Axioms:' in text):
            raise SystemExit('Unexpected assumption report: '+rel)
    if args.recursive:
        run('recursive_SourceClient', [coqchk, *flags, '-silent', 'SourceClient'])
    receipt['complete'] = True
    receipt['recursive_audit'] = 'passed' if args.recursive else 'not run'
    save()
    print('PASS_EXACT_SOURCE_CHECKED_LOOKUP', flush=True)


if __name__ == '__main__':
    main()
