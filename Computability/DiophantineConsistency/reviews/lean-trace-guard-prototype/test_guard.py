#!/usr/bin/env python3
"""Adversarial synthetic controls and real syscall-traced Lean/plugin smoke tests."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

import trace_guard as guard

HERE = Path(__file__).resolve().parent
LEAN = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')

def hx(s):
    return ''.join('\\x%02x' % b for b in os.fsencode(str(s)))

def line(path, target, dirfd='AT_FDCWD', *, relative=False):
    name = str(path) if not relative else path.name
    return f'42 openat({dirfd}, "{hx(name)}", O_RDONLY|O_CLOEXEC) = 3<{hx(target)}>\n'

def rejects(raw, policy, expected):
    try:
        guard.analyze(raw, policy)
    except (guard.TraceError, FileNotFoundError) as exc:
        if expected not in str(exc):
            raise AssertionError((expected, str(exc)))
    else:
        raise AssertionError(('unexpected acceptance', expected))

def traced(command, logfile, env=None):
    cmd = ['strace', '-f', '-qq', '-yy', '-xx', '-s', '4096',
           '-e', 'trace=open,openat,openat2,execve,execveat', '-o', str(logfile), *command]
    result = subprocess.run(cmd, capture_output=True, text=True, env=env, timeout=120)
    assert result.returncode == 0, (result.returncode, result.stdout, result.stderr)
    return logfile.read_text()

def main():
    controls = []
    with tempfile.TemporaryDirectory(prefix='lean-trace-guard-control-') as td:
        tmp = Path(td); good = tmp / 'good'; good.mkdir(); bad = tmp / 'bad'; bad.mkdir()
        f = good / 'source.olean'; f.write_bytes(b'example object')
        outside = bad / 'foreign.so'; outside.write_bytes(b'foreign plugin')
        policy = {'roots': [{'path': str(good), 'role': 'approved'}]}
        events = guard.analyze(line(f, f), policy)
        assert len(events) == 1 and events[0]['resolved'] == str(f) and events[0]['role'] == 'approved'
        controls.append('allowed_absolute')
        rejects(line(f, f), {'roots': [{'path': '/', 'role': 'accidentally-broad'}]}, 'filesystem root policy')
        controls.append('filesystem_root_requires_explicit_override')
        relative = line(f, f, f'AT_FDCWD<{hx(good)}>', relative=True)
        assert guard.analyze(relative, policy)[0]['resolved'] == str(f)
        controls.append('resolved_relative')
        rejects(line(f, f, 'AT_FDCWD', relative=True), policy, 'unresolved dirfd')
        controls.append('unresolved_dirfd_rejected')
        rejects(f'42 open("{hx(f.name)}", O_RDONLY) = 3<{hx(f)}>\n', policy, 'relative path without proven directory')
        controls.append('unresolved_relative_rejected')
        rejects(line(f, outside), policy, 'opened fd path disagrees')
        controls.append('wrong_fd_annotation_rejected')
        alias = good / 'escape.olean'; alias.symlink_to(outside)
        rejects(line(alias, outside), policy, 'outside allowed resolved roots')
        controls.append('symlink_escape_rejected')
        rejects(line(outside, outside), policy, 'outside allowed resolved roots')
        controls.append('unexpected_plugin_rejected')
        two = {'roots': [{'path': str(good), 'role': 'project'}, {'path': str(bad), 'role': 'plugin'}]}
        assert guard.analyze(line(outside, outside), two)[0]['role'] == 'plugin'
        controls.append('explicit_plugin_classified')
        broken = f'42 openat(AT_FDCWD, "{hx(f)}", O_RDONLY <unfinished ...>\n'
        rejects(broken, policy, 'unfinished calls')
        controls.append('unfinished_trace_rejected')
        joined = (f'42 openat(AT_FDCWD, "{hx(f)}", O_RDONLY <unfinished ...>\n'
                  f'42 <... openat resumed>) = 3<{hx(f)}>\n')
        assert guard.analyze(joined, policy)[0]['resolved'] == str(f)
        controls.append('unfinished_resume_matched')
        rejects('42 openat(AT_FDCWD, "abc"..., O_RDONLY) = 3\n', policy, 'not -xx encoded')
        controls.append('unsupported_or_truncated_path_rejected')
        # A broad root is deliberately used only to exercise the real tracer;
        # the receipt does not claim this is a useful security policy.
        broad = {'roots': [{'path': '/', 'role': 'inherited-smoke-only'}],
                 'allow_broad_root_for_smoke': True,
                 'special_paths': ['/dev/urandom']}
        src = tmp / 'Smoke.lean'; src.write_text('#check Nat\n')
        env = dict(os.environ); env.pop('LEAN_PATH', None); env.pop('LEAN_SRC_PATH', None)
        raw = traced([str(LEAN), str(src)], tmp / 'lean.trace', env)
        real = guard.analyze(raw, broad)
        assert any(e['resolved'].endswith('.olean') for e in real)
        assert any('.so' in e['resolved'] for e in real)
        controls.append('real_lean_import_and_shared_libraries_observed')
        plugin = bad / 'loaded.so'
        cc = subprocess.run(['cc', '-shared', '-fPIC', '-x', 'c', '-', '-o', str(plugin)],
                            input='int plugin_value(void) { return 7; }\n', text=True,
                            capture_output=True, timeout=30)
        assert cc.returncode == 0, cc.stderr
        raw_plugin = traced([sys.executable, '-c', 'import ctypes,sys; ctypes.CDLL(sys.argv[1])', str(plugin)],
                            tmp / 'plugin.trace')
        plugin_line = next(s for s in raw_plugin.splitlines()
                           if hx(plugin) in s and 'openat(' in s and ') = -1 ' not in s)
        assert guard.analyze(plugin_line + '\n', two)[0]['resolved'] == str(plugin)
        rejects(plugin_line + '\n', policy, 'outside allowed resolved roots')
        controls.append('real_ctypes_dynamic_plugin_observed_and_rejected')
    receipt = {'status': 'PASS_TRACE_GUARD_CONTROLS', 'controls': controls,
               'lean_sha256': hashlib.sha256(LEAN.read_bytes()).hexdigest(),
               'guard_sha256': hashlib.sha256((HERE / 'trace_guard.py').read_bytes()).hexdigest(),
               'test_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
               'scope': 'Prototype and controlled smoke tests only; no proof replay traced or complete '
                        'dynamic dependency provenance established.'}
    out = HERE / 'test-receipt.json'
    with out.open('x') as f:
        json.dump(receipt, f, indent=2, sort_keys=True); f.write('\n')
    print(receipt['status'], len(controls), hashlib.sha256(out.read_bytes()).hexdigest())

if __name__ == '__main__':
    main()
