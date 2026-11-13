#!/usr/bin/env python3
"""Audit a failed split diagnostic and its successfully compiled prefix."""
import hashlib
import json
import os
import subprocess
import sys
from pathlib import Path

assert sys.flags.isolated and sys.flags.no_site
root = Path(__file__).resolve().parents[2]
packet = root / 'research/nine-sharing-sign25-endpoint-diagnostic-check'
attempt = packet / 'attempt01'
output = Path('/tmp/nine-sharing-sign25-endpoint-diagnostic-20261109')
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
outer = json.loads((attempt / 'outer-result.json').read_text())
assert outer['outer_session_id'] == 13406 and outer['outer_exit_code'] == 1
state_path = attempt / 'state.json'
assert digest(state_path) == digest(output / 'state.json')
state = json.loads(state_path.read_text())
assert state['status'] == 'FAILED' and state['failure'] == "RuntimeError('compile failed Sign25DiagExpression')"
assert state['runner_sha256'] == digest(packet / 'run.py') == '213c1ca053ba8a44e8af4378e1bbb92e22967f1f96745f957919cf26f4eae7cf'
assert len(state['rows']) == 2
manifest = json.loads((packet / 'source-manifest.json').read_text())['rows']
assert [r['module'] for r in state['rows']] == ['Sign25DiagImport', 'Sign25DiagExpression']
guard_count = 0
for index, row in enumerate(state['rows']):
    name = row['module']
    source = packet / 'src/DiophantineConsistency' / (name + '.lean')
    assert digest(source) == row['source_sha256'] == manifest[index]['source_sha256']
    assert digest(source) == digest(output / 'src/DiophantineConsistency' / (name + '.lean'))
    assert row['deps']['exit'] == 0 and row['compile']['exit'] == (0 if index == 0 else -6)
    for phase in ('deps', 'compile'):
        stage = row[phase]
        assert stage['stop_reason'] is None and not stage['monitor_errors'] and not stage['observed_descendant_pids']
        assert stage['rss_limit_bytes'] == 4 * 1024**3 and stage['timeout_seconds'] == 120
        log = name + '-' + phase + '.txt'
        assert digest(attempt / log) == digest(output / log) == stage['log_sha256']
    for path, observation in row['direct_guard'].items():
        candidate = Path(path)
        if observation is None: assert not os.path.lexists(candidate)
        else:
            assert candidate.is_file() and str(candidate.resolve()) == observation['realpath']
            assert digest(candidate) == observation['sha256']
        guard_count += 1
    for mod in manifest[index]['imports']:
        dep = row['dependencies'][mod]
        assert row['direct_guard'][dep['path']] == {'sha256': dep['sha256'], 'realpath': dep['realpath']}
        if index == 1: assert dep['sha256'] == state['rows'][0]['object_sha256']
        else: assert dep['sha256'] == 'b662728032c262f52f1bda8a52d9b29401129c6279a3f9d4e6f8e2924980f1ea'
first_obj = output / 'lib/DiophantineConsistency/Sign25DiagImport.olean'
assert digest(first_obj) == state['rows'][0]['object_sha256'] == 'd19db48e807bbc306a0bf3a7fa6e4f36e03a7c246fba3e5fad1b6fcfb82ed50f'
assert not (attempt / 'Sign25DiagImport-compile.txt').read_text()
assert 'memory_exception' in (attempt / 'Sign25DiagExpression-compile.txt').read_text()
assert "'interpreter'" in (attempt / 'Sign25DiagExpression-compile.txt').read_text()
for name in ('Sign25DiagExpression', 'Sign25DiagBridge', 'Sign25DiagAxioms'):
    assert not (output / 'lib/DiophantineConsistency' / (name + '.olean')).exists()
for path, target in state['overlay_links'].items():
    assert Path(path).is_symlink() and str(Path(path).resolve()) == target
upstream = root / 'reviews/nine-sharing-sign25-concrete-polynomial-bridge-terminal-frontier-independent/check.py'
assert digest(upstream) == 'e355b74413e5748d74a78f1a365f9378fe04c5d7ba2e52668ccba96fa7e2c5bd'
subprocess.run([sys.executable, '-I', '-S', '-B', str(upstream)], check=True, capture_output=True, timeout=120)
print(json.dumps({'status': 'PASS_FAILURE_AUDIT', 'author_session': 13406, 'author_outer_exit': 1,
                  'import_compile_exit': 0, 'alias_compile_exit': -6, 'guard_count': guard_count,
                  'overlay_links': len(state['overlay_links']), 'state_sha256': digest(state_path),
                  'scope': 'diagnostic prefix and failure only; no endpoint or final postflight'}, sort_keys=True, indent=2))
