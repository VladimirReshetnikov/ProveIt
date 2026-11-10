#!/usr/bin/env python3
"""Independent audit of the failed sign25 endpoint attempt; never calls Lean."""
import hashlib
import json
import os
import subprocess
import sys
from pathlib import Path

assert sys.flags.isolated and sys.flags.no_site
root = Path(__file__).resolve().parents[2]
packet = root / 'research/nine-sharing-sign25-endpoint-no-alias-retry-check'
attempt = packet / 'attempt01'
output = Path('/tmp/nine-sharing-sign25-endpoint-no-alias-retry-20261109')
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
outer = json.loads((attempt / 'outer-result.json').read_text())
assert outer['outer_session_id'] == 12392 and outer['outer_exit_code'] == 1
state_path = attempt / 'state.json'
assert digest(state_path) == digest(output / 'state.json')
state = json.loads(state_path.read_text())
assert state['status'] == 'FAILED' and state['failure'] == "RuntimeError('compile failed Sign25DirectNoAliasNative')"
assert state['runner_sha256'] == digest(packet / 'run.py') == '18fb7d0eaeee2e3fa1fe918fa17fe611cf1155ff03869faa18fb2b68a5fe2bee'
assert 'sign25' in state['scope']
assert len(state['rows']) == 1
row, = state['rows']
name = 'Sign25DirectNoAliasNative'
assert row['module'] == name
manifest = json.loads((packet / 'source-manifest.json').read_text())['rows']
assert [r['module'] for r in manifest] == ['DiophantineConsistency.' + n for n in
       ('Sign25DirectNoAliasNative', 'Sign25DirectNoAliasStandard', 'Sign25DirectNoAliasTranslated')]
source = packet / 'src/DiophantineConsistency' / (name + '.lean')
assert digest(source) == row['source_sha256'] == manifest[0]['source_sha256']
assert digest(source) == digest(root / 'research/nine-sharing-sign25-endpoint-no-alias-check/src/DiophantineConsistency/Sign25DirectNoAliasNative.lean')
assert digest(source) == digest(output / 'src/DiophantineConsistency' / (name + '.lean'))
assert row['deps']['exit'] == 0 and row['compile']['exit'] == -6
for phase in ('deps', 'compile'):
    stage = row[phase]
    assert stage['stop_reason'] is None and not stage['monitor_errors'] and not stage['observed_descendant_pids']
    assert stage['rss_limit_bytes'] == 4 * 1024**3 and stage['timeout_seconds'] == 120
    log = name + '-' + phase + '.txt'
    assert digest(attempt / log) == digest(output / log) == stage['log_sha256']
assert 'memory_exception' in (attempt / (name + '-compile.txt')).read_text()
assert "'interpreter'" in (attempt / (name + '-compile.txt')).read_text()
assert "'-M2800'" in (packet / 'run.py').read_text()
assert not (output / 'lib/DiophantineConsistency/Sign25DirectNoAliasNative.olean').exists()
for later in ('Sign25DirectNoAliasNative', 'Sign25DirectNoAliasStandard', 'Sign25DirectNoAliasTranslated'):
    assert not (output / 'lib/DiophantineConsistency' / (later + '.olean')).exists()
for path, observation in row['direct_guard'].items():
    candidate = Path(path)
    if observation is None: assert not os.path.lexists(candidate)
    else:
        assert candidate.is_file() and str(candidate.resolve()) == observation['realpath']
        assert digest(candidate) == observation['sha256']
for path, target in state['overlay_links'].items():
    assert Path(path).is_symlink() and str(Path(path).resolve()) == target
upstream = root / 'reviews/nine-sharing-sign25-concrete-polynomial-bridge-terminal-frontier-independent/check.py'
assert digest(upstream) == 'e355b74413e5748d74a78f1a365f9378fe04c5d7ba2e52668ccba96fa7e2c5bd'
subprocess.run([sys.executable, '-I', '-S', '-B', str(upstream)], check=True, capture_output=True, timeout=120)
print(json.dumps({'status': 'PASS_FAILURE_AUDIT', 'author_session': 12392, 'author_outer_exit': 1,
                  'first_deps_exit': 0, 'first_compile_exit': -6, 'later_stages': 'not attempted',
                  'state_sha256': digest(state_path), 'runner_sha256': digest(packet / 'run.py'),
                  'guard_count': len(row['direct_guard']), 'overlay_links': len(state['overlay_links']),
                  'scope': 'failed retry only; earlier successful native child unchanged'}, sort_keys=True, indent=2))
