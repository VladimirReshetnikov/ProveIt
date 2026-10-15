"""Supplemental source protection layered on the immutable merged-source guard."""
from pathlib import Path
import functools, hashlib, json, re
BASE = Path('/tmp/gowers-merged-native-tools')
SNAPSHOT = Path('/tmp/gowers-merged-supplemental-native-tools/snapshot.json')
SNAPSHOT_SHA = 'e50b42fe6a8f6eea6ae537385183a2c5e806dca38464cce74b2b4111d5c69ebc'
BASE_GUARD_SHA = '59675ea063b9809e2f9db1bf541698bc67a3b75493d85ace82b3c92fc52d692f'
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(BASE / 'guard.py') == BASE_GUARD_SHA
base = {'__file__': str(BASE / 'guard.py'), '__name__': 'merged_supplemental_base_library'}
exec(compile((BASE / 'guard.py').read_bytes(), str(BASE / 'guard.py'), 'exec'), base)
ROOT = base['ROOT']; CHECKER = base['CHECKER']
for name in ('head', 'stamp', 'when', 'worker_check', 'freeze_check', 'artifact_snapshot', 'error_diagnostic'):
    globals()[name] = base[name]
def guard():
    assert sha(SNAPSHOT) == SNAPSHOT_SHA; snap = json.loads(SNAPSHOT.read_text())
    prior = base['guard'](snap['source_commit'], 'shared')
    baseline = json.loads(Path(snap['base_snapshot']['path']).read_text())
    assert sha(snap['base_snapshot']['path']) == snap['base_snapshot']['sha256'] == base['SNAPSHOT_SHA']
    assert sha(snap['coverage_analysis']['path']) == snap['coverage_analysis']['sha256']
    analysis = json.loads(Path(snap['coverage_analysis']['path']).read_text())
    assert snap['source_commit'] == analysis['source_commit'] and snap['roots'] == analysis['additional_roots_excluding_facades']
    assert snap['protected_source_hashes'] == {**baseline['protected_source_hashes'], **snap['extra_source_hashes']}
    base['committed'](snap['source_commit'], snap['extra_source_hashes'])
    for path, h in snap['extra_source_hashes'].items(): assert sha(ROOT / path) == h
    @functools.lru_cache(None)
    def closure(m): return frozenset({m}).union(*(closure(d) for d in snap['graph'][m] if d.split('.')[0] in ('GowersSzemeredi', 'OAI')))
    modules = set().union(*(closure(m) for m in snap['roots'])); selected = set(baseline['modes']['shared']['modules'])
    assert sorted(modules) == snap['modules'] and len(modules) == snap['module_count'] == 437
    assert snap['input_count'] == len(modules) + len(baseline['configs'])
    assert sorted(selected) == snap['prior_selected_modules'] and sorted(modules | selected) == snap['combined_modules']
    assert len(modules | selected) == snap['combined_module_count'] == 1962
    assert sorted(modules - selected) == snap['extra_modules'] == sorted(analysis['extra_modules'])
    assert set(snap['extra_source_hashes']) == {base['module_path'](m) for m in modules - selected}
    assert set(snap['covered_affected_outside_selected']) == set(analysis['affected_outside_selected']) - set(snap['excluded_aggregate_facades'])
    assert set(snap['covered_affected_outside_selected']) <= modules
    for m, imports in snap['graph'].items():
        assert re.findall(r'^import\s+(\S+)', (ROOT / base['module_path'](m)).read_text(), re.M) == imports
    assert sum(len((ROOT / base['module_path'](m)).read_bytes().splitlines()) for m in modules) == snap['source_lines']
    assert sum(len((ROOT / base['module_path'](m)).read_bytes().splitlines()) for m in modules | selected) == snap['combined_source_lines']
    source = {**prior['source_freeze'], **{str(ROOT / p): stamp(ROOT / p) for p in snap['extra_source_hashes']}}
    evidence = {**prior['evidence_freeze'], str(SNAPSHOT): stamp(SNAPSHOT), snap['coverage_analysis']['path']: stamp(snap['coverage_analysis']['path'])}
    assert len(source) == len(snap['protected_source_hashes']) == 1969
    return {'snapshot_sha256': SNAPSHOT_SHA, 'source_commit': snap['source_commit'], 'mode': 'supplemental', 'source_freeze': source, 'evidence_freeze': evidence, 'protected_paths': len(source), 'native_source_repairs': 1}
