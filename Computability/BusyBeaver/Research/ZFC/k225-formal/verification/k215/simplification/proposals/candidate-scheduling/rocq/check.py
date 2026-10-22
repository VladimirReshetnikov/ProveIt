#!/usr/bin/env python3
"""Fresh, offline check of the bundled Rocq component and typed audit client.

Uses only Python's standard library and a complete Coq/Rocq installation.
No repository checkout, downloaded dependencies, or precompiled project files
are required. For Coq 8.x, the only source compatibility change is the explicit
replacement of `From Stdlib ` with `From Coq ` in disposable build copies.
"""
from datetime import datetime, timezone
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import time

HERE = Path(__file__).resolve().parent
sha = lambda data: hashlib.sha256(data).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--coqc', default='coqc', help='Compiler executable')
    parser.add_argument('--coqchk', default='coqchk', help='Kernel checker executable')
    parser.add_argument('--out', required=True, type=Path, help='New build directory')
    args = parser.parse_args()
    out = args.out.resolve()
    if out.exists():
        raise SystemExit('--out must not exist: ' + str(out))
    executables = {}
    for name in ('coqc', 'coqchk'):
        resolved = shutil.which(getattr(args, name))
        if not resolved:
            raise SystemExit('Executable not found: ' + getattr(args, name))
        executables[name] = Path(resolved).resolve()
    manifest_bytes = (HERE / 'source_provenance.json').read_bytes()
    manifest = json.loads(manifest_bytes)
    modules = manifest['modules']
    paths = {m['path'] for m in modules}
    names = {m['module'] for m in modules}
    if len(names) != len(modules) or len(paths) != len(modules):
        raise SystemExit('Duplicate module or path in source manifest')
    actual_paths = {p.relative_to(HERE).as_posix() for p in (HERE / 'src').rglob('*.v')}
    if actual_paths != paths:
        raise SystemExit('Bundled source set does not match the manifest')
    if any((HERE / 'src').rglob('*.vo')) or any((HERE / 'src').rglob('*.vos')):
        raise SystemExit('Bundled source directory must contain no project objects')
    for item in modules:
        source = (HERE / item['path']).resolve()
        if not source.is_relative_to(HERE / 'src'):
            raise SystemExit('Source manifest path leaves src/: ' + item['path'])
        if sha(source.read_bytes()) != item['source_sha256']:
            raise SystemExit('Source hash mismatch: ' + item['module'])
    env = dict(os.environ)
    # Explicit -Q entries below provide the only project libraries. The
    # installed standard library and its plugins still use the toolchain env.
    env['COQPATH'] = ''
    version = subprocess.check_output([str(executables['coqc']), '--version'], env=env, text=True)
    compat = re.search(r'\bversion 8\.', version) is not None
    out.mkdir(parents=True)
    (out / 'logs').mkdir()
    receipt = {
        'schema_version': 1, 'base_commit': manifest['base_commit'],
        'scope': manifest['scope'], 'version': version,
        'started_utc': datetime.now(timezone.utc).isoformat(),
        'compiler_binary_sha256': sha(executables['coqc'].read_bytes()),
        'kernel_checker_binary_sha256': sha(executables['coqchk'].read_bytes()),
        'driver_sha256': sha(Path(__file__).read_bytes()),
        'source_provenance_sha256': sha(manifest_bytes),
        'stdlib_namespace_compatibility': compat,
        'project_objects_reused': False, 'network_required': False,
        'repository_required': False, 'sources': [], 'checks': [],
        'full_tm_endpoint_rebuilt': False, 'status': 'RUNNING',
    }
    for item in modules:
        data = (HERE / item['path']).read_bytes()
        compiled = data.replace(b'From Stdlib ', b'From Coq ') if compat else data
        rel = Path(item['module'].replace('.', '/') + '.v')
        dest = out / rel
        dest.parent.mkdir(exist_ok=True, parents=True)
        dest.write_bytes(compiled)
        receipt['sources'].append({
            'module': item['module'], 'source': item['path'],
            'sha256': item['source_sha256'], 'compiled_sha256': sha(compiled),
            'namespace_alias_count': data.count(b'From Stdlib ') if compat else 0,
        })
    flags = ['-Q', 'K230S', 'K230S', '-Q', 'K230L', 'K230L', '-Q', 'K215F', 'K215F']

    def save():
        (out / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')

    def run(name, command):
        started = time.monotonic()
        result = subprocess.run(command, cwd=out, env=env,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        log = 'logs/' + name + '.log'
        (out / log).write_bytes(result.stdout)
        receipt['checks'].append({
            'name': name, 'command': ['COQC' if command[0] == str(executables['coqc']) else 'COQCHK', *command[1:]],
            'exit_code': result.returncode, 'seconds': time.monotonic() - started,
            'log': log, 'log_sha256': sha(result.stdout),
        })
        print(name, result.returncode, flush=True)
        if result.returncode:
            receipt['status'] = 'FAIL'
            save()
            print(result.stdout.decode(errors='replace'))
            raise SystemExit(result.returncode)
        save()
        return result.stdout.decode(errors='replace')

    save()
    for item in modules:
        rel = item['module'].replace('.', '/') + '.v'
        output = run(item['module'], [str(executables['coqc']), '-q', *flags, rel])
        if item['module'] == 'Client':
            count = output.count('Closed under the global context')
            receipt['closed_client_assumption_reports'] = count
            if count != manifest['expected_closed_assumption_reports'] or 'Axioms:' in output:
                receipt['status'] = 'FAIL'
                save()
                raise SystemExit('Unexpected assumption report in Client')
    run('coqchk', [str(executables['coqchk']), *flags, *manifest['recursive_check_roots']])
    receipt['status'] = 'PASS'
    receipt['completed_utc'] = datetime.now(timezone.utc).isoformat()
    save()
    print('PASS:', len(modules), 'fresh source files; recursive kernel check; no repository or network')


if __name__ == '__main__':
    main()
