#!/usr/bin/env python3
"""Audit one completed project replay; never execute or modify Lean artifacts.

Rate-limited hashing and idle-I/O invocation avoid monopolizing the disk while
the independent peer is compiling. This is not a proof replay or a claim
about unobserved package-transitive or dynamic inputs.
"""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PAIR = Path('/tmp/ipra-aq29-fresh-project-pair')
AUTHOR = PAIR / 'author'
STATE = AUTHOR / 'state.json'
SAVED = ROOT / 'reviews/fresh-project-pair-author'
MANIFEST_PIN = '63b846158674d41beeaa99843d92008465f8e0fe5c45bb9e1fed4b78e1a2ab48'
PROVIDER_PIN = '7cbd49b6d84497c46520e908fc8c4dc105d7a0070fd1323c6c28e26bf4cf00f6'
STATE_PIN = 'b9ab036bf00296c9491ef6f06eb44aca805b51ab36f0d48e090d5620a55f6153'
SUFFIXES = ('.olean', '.olean.private', '.olean.server', '.ir', '.ilean',
            '.olean.hash', '.olean.private.hash', '.olean.server.hash',
            '.ir.hash', '.ilean.hash')
EXPECTED = [
    'DiophantineConsistency.AdaptiveAQ29.current_no_zero_iff',
    'DiophantineConsistency.IPRAAQ29Native.sameNoZero',
    'DiophantineConsistency.IPRAAQ29Native.bridge29',
    'DiophantineConsistency.IPRAAQ29Native.literal_equivalence',
]
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
REPORT = re.compile(r"^'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", re.M)
HASH_RATE = 8 * 1024 * 1024
started = time.monotonic()
hashed_bytes = 0
cache = {}


def digest(path):
    """Hash each unchanged real file once; reject observed mutation."""
    global hashed_bytes
    path = Path(path)
    real = path.resolve(strict=True)
    before = real.stat()
    key = (str(real), before.st_dev, before.st_ino, before.st_size, before.st_mtime_ns, before.st_ctime_ns)
    if key in cache:
        return cache[key]
    h = hashlib.sha256()
    with real.open('rb') as f:
        while chunk := f.read(1024 * 1024):
            h.update(chunk)
            hashed_bytes += len(chunk)
            wait = hashed_bytes / HASH_RATE - (time.monotonic() - started)
            if wait > 0:
                time.sleep(wait)
    after = real.stat()
    assert (after.st_dev, after.st_ino, after.st_size, after.st_mtime_ns, after.st_ctime_ns) == key[1:], ('mutation', str(real))
    cache[key] = h.hexdigest()
    return cache[key]


def guard(items):
    for name, entry in items.items():
        q = Path(name)
        if entry is None:
            assert not os.path.lexists(q), ('unexpected companion', name)
        else:
            assert q.is_file() and str(q.resolve()) == entry['realpath'], ('guard path', name)
            assert digest(q) == entry['sha256'], ('guard hash', name)


def coverage(order, rows, outputs):
    assert len(order) == 1210 and len(set(order)) == len(order)
    assert [row['module'] for row in rows] == order
    assert set(outputs) == set(order)
    assert order[-1] == 'DiophantineConsistency.IPRAAQ29NativeChecks'


def reports_ok(text, target=False):
    reports = REPORT.findall(text)
    if target:
        assert [x[0] for x in reports] == EXPECTED, ('target report names', reports)
    for _, values in reports:
        assert set(x.strip() for x in values.split(',') if x.strip()) <= ALLOWED, ('axioms', values)
    return [x[1] for x in reports]


def git_verify(commit, rows, manifest):
    requests = [(r['workspace_path'], r['sha256']) for r in rows.values()]
    requests.extend([('lakefile.toml', manifest['lakefile_sha256']), ('lean-toolchain', manifest['lean_toolchain_sha256'])])
    proc = subprocess.Popen(['git', 'cat-file', '--batch'], cwd=ROOT.parent.parent,
                            stdin=subprocess.PIPE, stdout=subprocess.PIPE)
    assert proc.stdin and proc.stdout
    for path, expected in requests:
        proc.stdin.write((commit + ':' + path + '\n').encode())
        proc.stdin.flush()
        header = proc.stdout.readline().decode().strip().split()
        assert len(header) == 3 and header[1] == 'blob', ('git source missing', path, header)
        data = proc.stdout.read(int(header[2])); assert proc.stdout.read(1) == b'\n'
        assert hashlib.sha256(data).hexdigest() == expected, ('git source mismatch', path)
    proc.stdin.close(); assert proc.wait() == 0
    return len(requests)


def main():
    receipt = HERE / 'receipt.json'
    assert not receipt.exists(), 'refusing to overwrite receipt'
    obs = json.loads((SAVED / 'observation.json').read_text())
    assert obs['observed_coordinator_stdout_chunk'] == 'author exit 0\n'
    assert obs['coordinator_terminal_exit'] == 'not yet observed'
    assert obs['author_state_sha256'] == STATE_PIN
    assert digest(STATE) == digest(SAVED / 'state.json') == STATE_PIN
    assert digest(PAIR / 'author-process.log') == digest(SAVED / 'process.log') == obs['author_process_log_sha256']
    s = json.loads(STATE.read_text()); assert s['status'] == 'PASS' and s['phase'] == 'complete'
    assert s['manifest_sha256'] == MANIFEST_PIN and s['provider_receipt_sha256'] == PROVIDER_PIN
    snap = Path(s['snapshot']); mp = snap / 'manifest.json'; pp = Path(s['provider'])
    assert digest(mp) == MANIFEST_PIN and digest(pp) == PROVIDER_PIN
    assert digest(s['foundation_input_path']) == s['foundation_input_sha256']
    assert digest(s['lean_path']) == s['lean_sha256']
    assert digest(ROOT / 'research/fresh-project-closure/rebuild.py') == s['driver_sha256']
    m = json.loads(mp.read_text()); p = json.loads(pp.read_text())
    assert m['head'] == '74f797792c2ef3f81bc9d9e8eb14a58664a3aded'
    assert p['status'] == 'BUILT' and p['exit_code'] == 0 and p['manifest_sha256'] == s['foundation_input_sha256']
    assert s['source_status'] == 'HISTORICAL_SNAPSHOT' and len(s['workspace_source_drift']) == 15
    assert s['workspace_source_drift'] == obs['workspace_source_drift']
    order, rows, outputs, sources = m['order'], s['records'], s['outputs'], m['sources']
    coverage(order, rows, outputs); assert s['expected_axiom_reports'] == len(EXPECTED)
    # Exercise controls against the actual records without changing evidence.
    try: coverage(order, rows[:-1], outputs)
    except AssertionError: pass
    else: raise AssertionError('dropped-record mutation accepted')
    try: reports_ok("'bad' depends on axioms: [sorryAx]", target=True)
    except AssertionError: pass
    else: raise AssertionError('forged-target mutation accepted')
    assert len(sources) == len(order) and set(sources) == set(order)
    git_rows = git_verify(m['head'], sources, m)
    lib = AUTHOR / 'lib'; pkg = Path(s['package_overlay']); tool = Path(s['lean_path']).parent.parent / 'lib/lean'
    foundation = Path(p['root']) / '.lake/build/lib/lean/Foundation'
    assert (pkg / 'Foundation').resolve() == foundation.resolve()
    seen = set(); direct_count = 0; log_reports = 0
    for i, row in enumerate(rows):
        name = row['module']; spec = sources[name]
        rel = Path(*name.split('.')); source = snap / 'src' / rel.with_suffix('.lean')
        assert str(source.relative_to(snap)) == spec['snapshot_path'] and not source.is_symlink() and digest(source) == spec['sha256'] == row['source_sha256']
        assert row['exit'] == 0
        obj = lib / rel.with_suffix('.olean'); assert not obj.is_symlink()
        output = outputs[name]; expected_paths = {str(lib / rel) + suffix for suffix in SUFFIXES}
        assert set(output) == expected_paths and output[str(obj)]['sha256'] == row['object_sha256'] == digest(obj)
        log = AUTHOR / 'logs' / (f'{i:04d}-' + name.replace('.', '_') + '.log')
        assert str(log) == row['log'] and digest(log) == row['log_sha256']
        text = log.read_text(); assert not re.search(r'(?m)^.*(?:error:|error\([^)]*\):)|\bsorryAx\b|\bsorry\b', text)
        observed_reports = reports_ok(text, target=name == order[-1]); log_reports += len(observed_reports)
        assert observed_reports == row['axiom_reports']
        declared, actual = set(spec['imports']), set(row['direct_inputs'])
        assert declared <= actual and actual - declared <= {'Init'}, ('direct coverage', name)
        for module, inp in row['direct_inputs'].items():
            q = Path(inp['path']); entry = s['guarded_companions'].get(str(q)); direct_count += 1
            assert entry and entry['sha256'] == inp['sha256'] == digest(q)
            path = Path(*module.split('.')).with_suffix('.olean')
            if module in sources:
                assert module in seen and inp['kind'] == 'project' and q == lib / path
            else:
                base = {'package': pkg, 'toolchain': tool}.get(inp['kind']); assert base and q == base / path
                if module.startswith('Foundation.'):
                    assert inp['kind'] == 'package' and q.resolve().is_relative_to(foundation.resolve())
        seen.add(name)
    guard(s['guarded_companions'])
    for g in outputs.values(): guard(g)
    # Inventory every fresh object and companion, rejecting unrecorded files.
    expected_files = {k for g in outputs.values() for k, v in g.items() if v is not None}
    actual_files = {str(q) for q in lib.rglob('*') if q.is_file() or q.is_symlink()}
    assert actual_files == expected_files
    guard(p['declared_external_guard'])
    expected_foundation = p['foundation_artifacts']
    actual_foundation = {str(q.relative_to(foundation)) for q in foundation.rglob('*') if q.is_file() or q.is_symlink()}
    assert actual_foundation == set(expected_foundation)
    for name, expected in expected_foundation.items():
        q = foundation / name; assert not q.is_symlink() and digest(q) == expected
    assert digest(STATE) == STATE_PIN and digest(mp) == MANIFEST_PIN and digest(pp) == PROVIDER_PIN
    result = {
        'status': 'PASS_INDEPENDENT_AUTHOR_ARTIFACT_AUDIT', 'author_state_sha256': STATE_PIN,
        'manifest_sha256': MANIFEST_PIN, 'foundation_provider_receipt_sha256': PROVIDER_PIN,
        'author_rows': len(rows), 'direct_input_occurrences': direct_count,
        'guarded_companion_paths': len(s['guarded_companions']), 'output_modules': len(outputs),
        'fresh_output_files': len(actual_files), 'foundation_artifacts': len(expected_foundation),
        'all_lean_log_axiom_reports': log_reports, 'endpoint_declarations': EXPECTED,
        'git_blob_checks': git_rows, 'source_commit': m['head'],
        'author_recorded_workspace_drifts': s['workspace_source_drift'],
        'observed_author_stdout': obs['observed_coordinator_stdout_chunk'],
        'foundation_outer_exit': 'not observed', 'peer_and_coordinator_terminal': 'not yet observed at author observation',
        'hash_bytes_read': hashed_bytes, 'elapsed_seconds': round(time.monotonic() - started, 2),
        'script_sha256': digest(Path(__file__)),
        'scope': 'Independent author-only artifact and recorded-input audit; no Lean replay or matched peer claim. '
                 'Unobserved package-transitive/dynamic ancestry and between-observation mutation are not authenticated.',
    }
    receipt.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(result['status'], len(rows), 'rows;', direct_count, 'direct inputs;', hashlib.sha256(receipt.read_bytes()).hexdigest(), flush=True)


if __name__ == '__main__':
    main()
