#!/usr/bin/env python3
"""Fresh, serial kernel compilation of KEndpoint215 and explicit closed clients.

No repository .olean files or third-party project cache are used. Resume is allowed only
when the source, direct dependency objects, compiler identity, and all companions match.
"""
from pathlib import Path
import argparse
import fcntl
import hashlib
import json
import os
import re
import signal
import subprocess
import time

TARGET = 'BusyBeaver.ZFC.KEndpoint215'
ROOTS = ('Computability/BusyBeaver/Lean', 'Logic/FirstOrder/Lean',
         'SetTheory/ZF/Lean', 'SetTheory/BoundedConsistency/Lean')
HERE = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def save(path, data):
    tmp = path.with_suffix(path.suffix + '.tmp')
    tmp.write_text(json.dumps(data, indent=2) + '\n')
    os.replace(tmp, path)


def without_comments_strings(text):
    out, i, depth = [], 0, 0
    while i < len(text):
        if text[i:i + 2] == '/-':
            depth += 1
            i += 2
        elif depth and text[i:i + 2] == '-/':
            depth -= 1
            i += 2
        elif depth:
            # Preserve line breaks for the import parser.
            if text[i] == '\n':
                out.append('\n')
            i += 1
        elif text[i:i + 2] == '--':
            j = text.find('\n', i)
            i = len(text) if j < 0 else j
        elif text[i] == '"':
            i += 1
            while i < len(text):
                if text[i] == '\\':
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
        else:
            out.append(text[i])
            i += 1
    assert depth == 0, 'Unclosed Lean comment'
    return ''.join(out)


def inventory(repo):
    rows, seen, active = [], set(), set()
    external = {'Init'}

    def visit(module):
        if module in seen:
            return
        assert module not in active, ('Import cycle', module)
        candidates = [repo / r / (module.replace('.', '/') + '.lean') for r in ROOTS]
        found = [p for p in candidates if p.is_file()]
        if not found:
            assert module == 'Init' or module.startswith('Init.'), ('Unbound import', module)
            external.add(module)
            return
        assert len(found) == 1, ('Ambiguous source', module, found)
        source = found[0]
        clean = without_comments_strings(source.read_text())
        imports = [m for line in re.findall(r'(?m)^\s*(?:public\s+)?import\s+([^\n]+)', clean)
                   for m in line.split()]
        active.add(module)
        for parent in imports:
            visit(parent)
        active.remove(module)
        seen.add(module)
        rows.append({'module': module, 'source': str(source), 'source_sha256': sha(source),
                     'imports': imports})

    visit(TARGET)
    return {'target': TARGET, 'modules': rows, 'external_imports': sorted(external)}


def run_locked(command, cwd, env, lock_path, log, timeout, row, record):
    """Kill the entire dedicated compiler group before unlocking on timeout/interruption."""
    row['status'] = 'WAITING_SHARED_LOCK'
    save(record, row)
    start_wait = time.monotonic()
    with lock_path.open('a+') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        row['lock_wait_seconds'] = time.monotonic() - start_wait
        row['status'] = 'COMPILING'
        save(record, row)
        started = time.monotonic()
        with log.open('wb') as stream:
            proc = subprocess.Popen(command, cwd=cwd, env=env, stdout=stream,
                                    stderr=subprocess.STDOUT, start_new_session=True)
            row['process_group'] = proc.pid
            interrupted = None
            try:
                code = proc.wait(timeout=timeout)
                timed_out = False
            except subprocess.TimeoutExpired:
                try:
                    os.killpg(proc.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                proc.wait()
                code, timed_out = proc.returncode, True
            except BaseException as exc:
                try:
                    os.killpg(proc.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                proc.wait()
                code, timed_out, interrupted = proc.returncode, False, exc
        row.update(exit_code=code, timed_out=timed_out,
                   status='PASS' if code == 0 and interrupted is None else 'FAIL',
                   seconds=time.monotonic() - started, log_sha256=sha(log))
        save(record, row)
        # The context closes the lock only after the compiler group has been terminated.
    if interrupted is not None:
        raise interrupted
    return code == 0


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path)
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--lock', type=Path, default=Path('/tmp/proveit-k215-proof-build.lock'))
    parser.add_argument('--timeout', type=float, default=900)
    parser.add_argument('--audit-timeout', type=float, default=120)
    parser.add_argument('--memory-mib', type=int, default=12288)
    args = parser.parse_args()
    repo = args.repo.resolve() if args.repo else next(
        p for p in HERE.parents if (p / 'lean-toolchain').is_file())
    assert args.timeout > 0 and args.audit_timeout > 0 and args.memory_mib > 0
    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=True)
    owner = {'repo': str(repo), 'target': TARGET,
             'toolchain': (repo / 'lean-toolchain').read_text(),
             'driver_sha256': sha(Path(__file__))}
    owner_path = out / 'owner.json'
    if owner_path.exists():
        assert json.loads(owner_path.read_text()) == owner, 'Output belongs to another build'
    else:
        assert not list(out.iterdir()), 'Use a new empty output directory'
        save(owner_path, owner)
    # Prevent two drivers from mutating the same record/cache, independently of global serialization.
    with (out / 'output.lock').open('a+') as output_lock:
        fcntl.flock(output_lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        workspace = out / 'workspace'
        workspace.mkdir(exist_ok=True)
        (workspace / 'lean-toolchain').write_text(owner['toolchain'])
        (workspace / 'lakefile.toml').write_text('name = "K215KernelCheck"\n\n[[lean_lib]]\nname = "K215KernelCheck"\n')
        cache = workspace / '.lake/build/lib/lean'
        cache.mkdir(parents=True, exist_ok=True)
        env = os.environ.copy()
        env.pop('LEAN_PATH', None)
        env['LEAN_NUM_THREADS'] = '1'
        inv = inventory(repo)
        sessions = out / 'sessions'
        sessions.mkdir(exist_ok=True)
        session = sessions / f'{1 + len(list(sessions.iterdir())):04d}'
        session.mkdir()
        save(session / 'inventory.json', inv)
        save(out / 'inventory.json', inv)
        completed_path = out / 'completed.json'
        completed = json.loads(completed_path.read_text()) if completed_path.exists() else {}
        attempts = out / 'attempts'
        attempts.mkdir(exist_ok=True)

        def execute(name, source, source_root, dependencies, timeout, is_audit=False):
            source = Path(source)
            before = sha(source)
            obj = cache / (name.replace('.', '/') + '.olean')
            previous = completed.get(name)
            if (previous and previous['source_sha256'] == before
                    and previous['dependencies'] == dependencies
                    and obj.is_file() and previous['object_sha256'] == sha(obj)
                    and Path(previous['log']).is_file()
                    and sha(previous['log']) == previous['log_sha256']
                    and previous['companions']
                    and all(Path(p).is_file() and sha(p) == h
                            for p, h in previous['companions'].items())):
                return previous
            index = 1 + len(list(attempts.iterdir()))
            attempt = attempts / f'{index:04d}-{name}'
            attempt.mkdir()
            (attempt / source.name).write_bytes(source.read_bytes())
            obj.parent.mkdir(parents=True, exist_ok=True)
            command = ['lake', 'env', 'lean', '-j1', f'-M{args.memory_mib}',
                       '--root=' + str(source_root), '-o', str(obj), str(source)]
            row = {'module': name, 'source': str(source), 'source_sha256': before,
                   'dependencies': dependencies, 'command': command, 'cwd': str(workspace),
                   'timeout_seconds': timeout, 'memory_mebibytes': args.memory_mib,
                   'audit': is_audit, 'log': str(attempt / 'compiler.log')}
            print('CHECK', name, flush=True)
            ok = run_locked(command, workspace, env, args.lock, attempt / 'compiler.log',
                            timeout, row, attempt / 'record.json')
            row['source_unchanged'] = sha(source) == before
            assert row['source_unchanged'], ('Changed source during compilation', source)
            if ok:
                assert obj.is_file(), ('Missing object', obj)
                row['companions'] = {str(p): sha(p) for p in sorted(obj.parent.glob(obj.stem + '.olean*'))}
                row['object_sha256'] = sha(obj)
                completed[name] = row
                save(completed_path, completed)
            save(attempt / 'record.json', row)
            print(row['status'], name, round(row['seconds'], 3), flush=True)
            if not ok:
                raise SystemExit('Compiler failed; original log and source snapshot retained: ' + str(attempt))
            return row

        # Bind toolchain identity before any cache reuse. Queries also obey the global lock.
        identities = {}
        for suffix, flag in [('version', '--version'), ('prefix', '--print-prefix')]:
            log = session / ('toolchain-' + suffix + '.log')
            row = {'command': ['lake', 'env', 'lean', flag], 'timeout_seconds': 30}
            assert run_locked(row['command'], workspace, env, args.lock, log, 30,
                              row, session / ('toolchain-' + suffix + '.json'))
            identities[suffix] = log.read_text().strip()
        prefix = Path(identities['prefix'])
        identities['lean_sha256'] = sha(prefix / 'bin/lean')
        identities['lake_sha256'] = sha(prefix / 'bin/lake')
        identities['Init_olean_sha256'] = sha(prefix / 'lib/lean/Init.olean')
        identity_path = out / 'toolchain.json'
        if identity_path.exists():
            assert json.loads(identity_path.read_text()) == identities, 'Compiler identity changed'
        else:
            save(identity_path, identities)

        project_names = {entry['module'] for entry in inv['modules']}
        for entry in inv['modules']:
            source = Path(entry['source'])
            assert sha(source) == entry['source_sha256'], source
            module = entry['module']
            root = str(source)[:-len(module.replace('.', '/') + '.lean')].rstrip('/')
            direct_projects = set(entry['imports']) & project_names
            assert direct_projects <= completed.keys(), ('Missing dependency', module)
            dependencies = {m: completed[m]['object_sha256'] for m in sorted(direct_projects)}
            execute(module, source, root, dependencies, args.timeout)
        all_dependencies = {row['module']: completed[row['module']]['object_sha256'] for row in inv['modules']}
        for name in ('EndpointAudit215', 'K215Audit'):
            row = execute(name, HERE / (name + '.lean'), HERE, all_dependencies,
                          args.audit_timeout, is_audit=True)
            log = Path(row['log']).read_text()
            axioms = {word.strip() for block in re.findall(r'depends on axioms: \[(.*?)\]', log, re.S)
                      for word in block.split(',') if word.strip()}
            assert axioms <= {'propext', 'Classical.choice', 'Quot.sound'}, axioms
            expected = 2 if name == 'EndpointAudit215' else 8
            assert log.count('depends on axioms:') + log.count('does not depend on any axioms') == expected
        for entry in inv['modules']:
            assert sha(entry['source']) == entry['source_sha256'], entry['source']
            expected = {m: completed[m]['object_sha256'] for m in entry['imports'] if m in project_names}
            assert completed[entry['module']]['dependencies'] == expected, entry['module']
        assert set(completed) == project_names | {'EndpointAudit215', 'K215Audit'}, 'Unexpected object set'
        for row in completed.values():
            assert all(sha(p) == h for p, h in row['companions'].items())
        save(out / 'verification.json', {'status': 'PASS', 'target': TARGET,
             'project_modules': len(inv['modules']), 'typed_audits': 2,
             'external_imports': inv['external_imports'], 'toolchain': identities,
             'inventory_sha256': sha(out / 'inventory.json'),
             'completed_sha256': sha(completed_path), 'compiler_lock': str(args.lock),
             'scope': 'Fresh current-source project closure and exact dense215/ZFC endpoint clients.'})
        print('COMPLETE', len(inv['modules']), 'project modules and two typed audits', flush=True)


if __name__ == '__main__':
    def interrupt(signum, frame):
        raise KeyboardInterrupt(f'Signal {signum}')
    signal.signal(signal.SIGTERM, interrupt)
    main()
