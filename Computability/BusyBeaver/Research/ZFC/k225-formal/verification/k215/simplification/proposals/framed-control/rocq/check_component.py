#!/usr/bin/env python3
"""Regenerate and kernel-check the standalone Coq/Rocq frame component.

This does not compile K215LeftFrame.v against production Rocq9.1 dependencies.
Installed compiler usage:
    python3 check_component.py --coqc coqc --coqchk coqchk
Private extracted Ubuntu runtime usage:
    python3 check_component.py --private-prefix toolchain/root
"""
from pathlib import Path
import argparse
import datetime
import hashlib
import json
import os
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent

def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--coqc', default='coqc')
    ap.add_argument('--coqchk', default='coqchk')
    ap.add_argument('--private-prefix', type=Path)
    args = ap.parse_args()
    env = os.environ.copy()
    if args.private_prefix:
        prefix = args.private_prefix.resolve()
        args.coqc = str(prefix / 'usr/bin/coqc')
        args.coqchk = str(prefix / 'usr/bin/coqchk')
        ocaml = prefix / 'usr/lib/ocaml'
        env['COQLIB'] = str(ocaml / 'coq')
        env['OCAMLPATH'] = str(ocaml)
        env['CAML_LD_LIBRARY_PATH'] = str(ocaml / 'stublibs')
    logs = ROOT / 'evidence'
    logs.mkdir(exist_ok=True)
    records = []
    def run(name, cmd):
        start = time.perf_counter()
        cp = subprocess.run(cmd, cwd=ROOT, env=env, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, text=True)
        path = logs / f'{name}.log'
        path.write_text(cp.stdout)
        records.append({'name': name, 'command': cmd, 'exit_code': cp.returncode,
                        'elapsed_seconds': time.perf_counter() - start,
                        'log': str(path.relative_to(ROOT)), 'log_sha256': sha(path)})
        if cp.returncode:
            print(cp.stdout)
            raise RuntimeError(f'{name} failed; see {path}')
        return cp.stdout
    run('regenerate', [sys.executable, str(ROOT / 'prepare_rocq.py')])
    version = run('compiler-version', [args.coqc, '--version'])
    core = run('K215FrameStandalone', [args.coqc, '-q', 'K215FrameStandalone.v'])
    templates = run('K215FrameTemplates', [args.coqc, '-q', 'K215FrameTemplates.v'])
    kernel = run('coqchk', [args.coqchk, '-silent', '-o', 'K215FrameTemplates'])
    if core.count('Closed under the global context') != 5:
        raise RuntimeError('Expected five closed generic theorem reports')
    if templates.count('Closed under the global context') != 20:
        raise RuntimeError('Expected twenty closed template theorem reports')
    if '* Axioms: <none>' not in kernel:
        raise RuntimeError('Recursive kernel checker did not report axiom-free context')
    files = ['FrameProofBody.v.inc', 'K215FrameStandalone.v', 'K215FrameTemplates.v',
             'K215LeftFrame.v', 'prepare_rocq.py', 'check_component.py',
             'EXTRACTION.json', 'K215FrameStandalone.vo', 'K215FrameTemplates.vo']
    toolpaths = [shutil.which(args.coqc) or args.coqc,
                 shutil.which(args.coqchk) or args.coqchk]
    result = {
        'status': 'PASS', 'scope': 'Standalone exact-definition Coq compatibility component',
        'compiled_at_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'compiler_version': version.strip(),
        'compiler_binaries': [{'path': p, 'sha256': sha(p)} for p in toolpaths],
        'source_files': {p: {'sha256': sha(ROOT / p), 'bytes': (ROOT / p).stat().st_size} for p in files},
        'records': records,
        'closed_assumption_reports': {'generic': 5, 'templates': 20},
        'coqchk_axioms': [],
        'production_rocq_9_1_endpoint_rebuilt': False,
        'production_import_adapter_compiled': False,
        'concrete_tape_semantic_client_instantiated': False,
        'timing_note': 'Single local run, not a comparison benchmark or endpoint build timing.',
    }
    (logs / 'CHECKED.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: result[k] for k in ['status', 'scope', 'compiler_version',
         'closed_assumption_reports', 'coqchk_axioms', 'production_rocq_9_1_endpoint_rebuilt']}, indent=2))

if __name__ == '__main__':
    main()
