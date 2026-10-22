#!/usr/bin/env python3
"""Fresh focused original/candidate kernel checks; never edits a repository.

Sources are decoded as text with CRLF normalized to LF. The optional
compatibility transformation is From Stdlib -> From Coq for Coq 8.18.
All input and compiled source bytes are hashed separately.
"""
import argparse
import fcntl
import hashlib
import json
import shutil
import subprocess
import time
from pathlib import Path


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--coqc', default='coqc')
    ap.add_argument('--coqchk', default='coqchk')
    ap.add_argument('--out', type=Path, required=True)
    ap.add_argument('--compat-818', action='store_true')
    ap.add_argument('--lock-file', type=Path,
                    default=Path('/tmp/proveit-k215-proof-build.lock'))
    a = ap.parse_args()
    root = Path(__file__).resolve().parent
    out = a.out.resolve()
    if out.exists():
        raise SystemExit('Output must be new: refusing reuse of proof objects.')
    out.mkdir(parents=True)
    coqc, coqchk = shutil.which(a.coqc), shutil.which(a.coqchk)
    if not coqc or not coqchk:
        raise SystemExit('Both coqc and coqchk are required.')
    result = {'scope': 'focused calculus; not the K215 machine endpoint',
              'compat_818': a.compat_818,
              'coqc_version': subprocess.check_output([coqc, '--version'], text=True),
              'coqc': coqc, 'coqchk': coqchk, 'lanes': {}}
    base_order = ['K230S/KCode230.v', 'K230L/Codes230.v',
                  'K215F/Codes222.v', 'K215F/Thm222.v',
                  'K215F/DomRho8.v', 'K215F/ThmDom.v',
                  'K215F/CD222.v', 'K215F/ExactTypes.v']
    for lane in ['baseline', 'candidate']:
        dst = out / lane
        dst.mkdir()
        order = base_order[:]
        if lane == 'candidate':
            order.insert(4, 'K215F/DominatedImplication.v')
        paths, transformations, newlines = {}, {}, {}
        for relative in order:
            inp = root / 'inputs' / relative
            if relative.endswith('/ExactTypes.v') or (
                    lane == 'candidate' and (root / 'candidate' / relative).exists()):
                inp = root / 'candidate' / relative
            data = inp.read_text()
            newlines[relative] = inp.read_bytes().count(b'\r\n')
            transformations[relative] = data.count('From Stdlib') if a.compat_818 else 0
            if a.compat_818:
                data = data.replace('From Stdlib', 'From Coq')
            target = dst / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(data)
            paths[relative] = {'input': str(inp.relative_to(root)),
                               'input_sha256': sha(inp), 'compiled_source_sha256': sha(target)}
        flags = sum((['-Q', str(dst / ns), ns] for ns in ['K230S', 'K230L', 'K215F']), [])
        records = []
        for relative in order:
            command = [coqc, *flags, str(dst / relative)]
            with a.lock_file.open('a') as lock:
                fcntl.flock(lock, fcntl.LOCK_EX)
                start = time.monotonic()
                run = subprocess.run(command, cwd=dst, capture_output=True, text=True)
                seconds = time.monotonic() - start
            log = dst / (Path(relative).stem + '.log')
            log.write_text(run.stdout + run.stderr)
            records.append({'module': relative, 'command': command,
                            'exit_code': run.returncode, 'seconds': seconds,
                            'log': str(log.relative_to(out)), 'log_sha256': sha(log),
                            'closed_reports': run.stdout.count('Closed under the global context')})
            print(lane, relative, run.returncode, round(seconds, 3), flush=True)
            if run.returncode:
                print(run.stdout + run.stderr)
                result['failure'] = records[-1]
                (out / 'result.json').write_text(json.dumps(result, indent=2) + '\n')
                raise SystemExit(run.returncode)
        command = [coqchk, '-silent', *flags, 'K215F.ExactTypes']
        with a.lock_file.open('a') as lock:
            fcntl.flock(lock, fcntl.LOCK_EX)
            start = time.monotonic()
            run = subprocess.run(command, cwd=dst, capture_output=True, text=True)
            seconds = time.monotonic() - start
        log = dst / 'coqchk.log'
        log.write_text(run.stdout + run.stderr)
        kernel = {'command': command, 'exit_code': run.returncode,
                  'seconds': seconds, 'log': str(log.relative_to(out)), 'log_sha256': sha(log)}
        result['lanes'][lane] = {'files': paths, 'namespace_replacements': transformations,
                                 'crlf_to_lf_replacements': newlines,
                                 'compile': records, 'recursive_coqchk': kernel}
        (out / 'result.json').write_text(json.dumps(result, indent=2) + '\n')
        if run.returncode:
            print(run.stdout + run.stderr)
            raise SystemExit(run.returncode)
        audit = records[-1]
        if audit['closed_reports'] != 9:
            raise SystemExit('Expected nine closed exact-interface reports.')
        print(lane, 'recursive coqchk PASS', round(seconds, 3), flush=True)
    result['status'] = 'PASS_FOCUSED_BASELINE_AND_CANDIDATE'
    (out / 'result.json').write_text(json.dumps(result, indent=2) + '\n')
    print(result['status'])


if __name__ == '__main__':
    main()
