#!/usr/bin/env python3
"""Reproduce this isolated Rocq/Coq proof-core check; never builds the TM endpoint.

Usage: python3 build.py --coqc /path/to/coqc --coqchk /path/to/coqchk --out /tmp/core-check
Coq 8 uses only namespace re-export shims for unchanged sources importing Stdlib.
Rocq 9 uses its real Stdlib directly. Source files are copied, never edited.
"""
from pathlib import Path
import argparse
import contextlib
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


@contextlib.contextmanager
def locked(path):
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open('a+b') as stream:
        if os.name == 'posix':
            import fcntl
            fcntl.flock(stream, fcntl.LOCK_EX)
        else:
            import msvcrt
            stream.seek(0)
            if not stream.read(1):
                stream.write(b'0')
                stream.flush()
            stream.seek(0)
            msvcrt.locking(stream.fileno(), msvcrt.LK_LOCK, 1)
        try:
            yield
        finally:
            if os.name == 'posix':
                fcntl.flock(stream, fcntl.LOCK_UN)
            else:
                stream.seek(0)
                msvcrt.locking(stream.fileno(), msvcrt.LK_UNLCK, 1)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--coqc', default=shutil.which('coqc'))
    parser.add_argument('--coqchk')
    parser.add_argument('--out', type=Path, default=ROOT / '.build')
    parser.add_argument('--lock', type=Path,
                        default=Path(tempfile.gettempdir()) / 'proveit-k215-proof-build.lock')
    args = parser.parse_args()
    if not args.coqc:
        parser.error('provide --coqc')
    compiler = Path(shutil.which(args.coqc) or args.coqc).resolve()
    checker = Path(args.coqchk).resolve() if args.coqchk else compiler.with_name(
        'coqchk.exe' if os.name == 'nt' else 'coqchk')
    if not checker.is_file():
        parser.error('provide the matching --coqchk')
    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=True)
    receipt = {'status': 'RUNNING', 'scope': 'isolated implication core, numeric adapter, and unchanged ThmDom',
               'full_machine_endpoint_rebuilt': False, 'commands': [], 'source_sha256': {}}
    start = time.perf_counter()

    def run(label, command):
        began = time.perf_counter()
        process = subprocess.run(list(map(str, command)), text=True,
                                 stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        log = out / (label + '.log')
        log.write_text(process.stdout, encoding='utf-8')
        item = {'label': label, 'command': list(map(str, command)), 'exit_code': process.returncode,
                'seconds': time.perf_counter() - began, 'log': log.name, 'log_sha256': sha(log),
                'closed_reports': process.stdout.count('Closed under the global context')}
        receipt['commands'].append(item)
        bad_axioms = any('Axioms:' in line and line.split('Axioms:', 1)[1].strip() != '<none>'
                         for line in process.stdout.splitlines())
        if process.returncode or bad_axioms:
            raise RuntimeError(label + ' failed; see ' + str(log))
        return process.stdout

    try:
        with locked(args.lock):
            version = run('compiler-version', [compiler, '--version'])
            receipt['compiler_version'] = version.strip()
            match = re.search(r'version (\d+)\.(\d+)', version)
            if not match:
                raise RuntimeError('unrecognized compiler version')
            old_coq = int(match[1]) < 9
            receipt['stdlib_namespace_shims'] = old_coq
            work = Path(tempfile.mkdtemp(prefix='source-', dir=out))
            for namespace in ['K230S', 'K230L', 'K215F']:
                shutil.copytree(ROOT / 'reference' / namespace, work / namespace)
            for name in ['DominatedImplication', 'DomRho8']:
                shutil.copyfile(ROOT / 'coq' / (name + '.v'), work / 'K215F' / (name + '.v'))
            (work / 'Baseline').mkdir()
            shutil.copyfile(ROOT / 'reference/original_DomRho8.v', work / 'Baseline/DomRho8.v')

            generator = ROOT / 'generator/generate_domrho8_cd.py'
            core_input = ROOT / 'generator/derivation_core.txt'
            run('generate-core', [sys.executable, generator, '--derivation', core_input,
                '--core-rocq', work / 'generated.v', '--core', work / 'generated.lean'])
            if (work / 'generated.v').read_bytes() != (ROOT / 'coq/DominatedImplication.v').read_bytes():
                raise RuntimeError('Rocq core differs from deterministic regeneration')
            if (work / 'generated.lean').read_bytes() != (ROOT / 'reference/DominatedImplication.lean').read_bytes():
                raise RuntimeError('existing Lean core changed')
            receipt['current_lean_core_reproduced_byte_for_byte'] = True

            nat_input = ROOT / 'generator/derivation.txt'
            for label, gen in [('old', ROOT / 'reference/original_generator.py'), ('new', generator)]:
                run('generate-nat-' + label, [sys.executable, gen, '--derivation', nat_input,
                    '--lean', work / (label + '.lean'), '--rocq', work / (label + '.v')])
            for suffix in ['lean', 'v']:
                if (work / ('old.' + suffix)).read_bytes() != (work / ('new.' + suffix)).read_bytes():
                    raise RuntimeError('existing Nat generator output changed')
            receipt['legacy_nat_renderings_unchanged'] = True

            flags = []
            for namespace in ['K230S', 'K230L', 'K215F', 'Baseline']:
                flags += ['-Q', work / namespace, namespace]
            if old_coq:
                shutil.copytree(ROOT / 'reference/compat', work / 'compat')
                flags += ['-Q', work / 'compat', 'Stdlib']
                for name in ['Arith', 'Lia', 'List', 'Bool', 'NArith']:
                    run('shim-' + name, [compiler, *flags, work / 'compat' / (name + '.v')])

            modules = ['K230S/KCode230', 'K230L/Codes230', 'K215F/Codes222', 'K215F/Thm222',
                       'K215F/DominatedImplication', 'K215F/DomRho8', 'K215F/ThmDom', 'Baseline/DomRho8']
            for module in modules:
                source = work / (module + '.v')
                receipt['source_sha256'][module + '.v'] = sha(source)
                run(module.replace('/', '-'), [compiler, *flags, source])
            run('coqchk-new-client', [checker, '-silent', '-o', *flags, 'K215F.ThmDom'])
            receipt['compiled_client_byte_identical_to_baseline'] = (
                sha(work / 'K215F/ThmDom.v') == sha(ROOT / 'reference/K215F/ThmDom.v'))
            receipt['status'] = 'PASS_CLOSED_ISOLATED_KERNEL'
            receipt['source_snapshot_directory'] = work.name
            receipt['metrics'] = {}
            for label, paths in [('baseline', [ROOT / 'reference/original_DomRho8.v']),
                                 ('core_plus_adapter', [ROOT / 'coq/DominatedImplication.v', ROOT / 'coq/DomRho8.v'])]:
                receipt['metrics'][label] = {
                    'bytes': sum(p.stat().st_size for p in paths),
                    'lines': sum(len(p.read_text().splitlines()) for p in paths)}
    except Exception as exc:
        receipt['status'] = 'FAILED'
        receipt['error'] = str(exc)
        raise
    finally:
        receipt['seconds'] = time.perf_counter() - start
        (out / 'verification.json').write_text(json.dumps(receipt, indent=2) + '\n', encoding='utf-8')
    print(json.dumps({'status': receipt['status'], 'receipt': str(out / 'verification.json'),
                      'full_machine_endpoint_rebuilt': False, 'metrics': receipt['metrics']}, indent=2))


if __name__ == '__main__':
    main()
