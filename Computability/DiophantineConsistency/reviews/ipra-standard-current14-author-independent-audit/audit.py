#!/usr/bin/env python3
"""Independent point-in-time artifact audit; this does not replay Lean."""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
TASK = ROOT / 'Computability/DiophantineConsistency'
TRIAL = Path('/tmp/ipra-standard-current14-author-trial')
PACKET = TASK / 'reviews/ipra-standard-current14-author-trial'
PARENT = Path('/tmp/ipra-aq29-fresh-project-pair/author')
PARENT_AUDIT = TASK / 'reviews/fresh-project-author-independent-audit/receipt.json'
DRIVER = TASK / 'research/author-only-extension/run.py'
MANIFEST = TASK / 'research/ipra-standard-current14/author-additions.json'
RATE = 8 * 1024 * 1024
started = time.monotonic()
read_bytes = 0
cache = {}

def digest(path):
    global read_bytes
    p = Path(path)
    st = p.stat()
    key = (st.st_dev, st.st_ino, st.st_size, st.st_mtime_ns, st.st_ctime_ns)
    if key not in cache:
        h = hashlib.sha256()
        with p.open('rb') as f:
            while chunk := f.read(1024 * 1024):
                h.update(chunk)
                read_bytes += len(chunk)
                delay = read_bytes / RATE - (time.monotonic() - started)
                if delay > 0:
                    time.sleep(delay)
        after = p.stat()
        assert (after.st_dev, after.st_ino, after.st_size, after.st_mtime_ns,
                after.st_ctime_ns) == key, ('changed while reading', str(p))
        cache[key] = h.hexdigest()
    return cache[key]

def guard(entries, *, links=None):
    present = 0
    for name, expected in entries.items():
        p = Path(name)
        if expected is None:
            assert not os.path.lexists(p), ('unexpected companion', name)
        else:
            assert p.is_file() and str(p.resolve()) == expected['realpath'], ('missing or redirected', name)
            if links is not None:
                assert p.is_symlink() == links, ('unexpected symlink', name)
            assert digest(p) == expected['sha256'], ('changed bytes', name)
            present += 1
    return present

def main():
    state_path = TRIAL / 'state.json'
    assert digest(state_path) == 'bd643e25b07538400b7f7cc397ff64af6ddc6d73f1e563d69fb5c6aed863da61'
    assert digest(PACKET/'state.json') == digest(state_path)
    t = json.loads(state_path.read_text())
    obs = json.loads((PACKET/'terminal-observation.json').read_text())
    assert t['status'] == obs['status'] == 'AUTHOR_ONLY_PASS'
    assert obs['tool_session'] == 18849 and obs['observed_exit_code'] == 0
    assert obs['observed_stdout'] == 'STANDARD_CURRENT14_AUTHOR_TRIAL_EXIT=0\n'
    assert obs['state_sha256'] == digest(state_path)
    assert digest(DRIVER) == t['driver_sha256'] == obs['driver_sha256']
    assert digest(MANIFEST) == t['manifest_sha256'] == obs['manifest_sha256']
    assert digest(PACKET/'author-additions.json') == digest(MANIFEST)
    assert digest(PACKET/'process.log') == digest('/tmp/ipra-standard-current14-author-trial.process.log') == obs['process_log_sha256']
    manifest = json.loads(MANIFEST.read_text())
    names = manifest['order']
    assert len(names) == len(set(names)) == 16 and [x['module'] for x in t['rows']] == names
    expected_names = [
        'DiophantineConsistency.IPRAStandardTheory.leibniz',
        'DiophantineConsistency.IPRAStandardTheory.provable_iff',
        'DiophantineConsistency.IPRAStandardCurrentEndpoint.ipra_current_iff_consistency',
        'DiophantineConsistency.IPRAStandardCurrentEndpoint.ipra_current_iff_translated_consistency',
    ]
    assert manifest['axiom_reports'] == {names[-1]: expected_names}
    process_lines = (PACKET/'process.log').read_text().splitlines()
    assert process_lines == [f'PASS {i} 16 {n}' for i,n in enumerate(names,1)] + ['AUTHOR_ONLY_PASS 16']

    audit = json.loads(PARENT_AUDIT.read_text())
    assert digest(PARENT_AUDIT) == t['author_audit_sha256'] == obs['parent_independent_audit_sha256']
    assert audit['status'] == 'PASS_INDEPENDENT_AUTHOR_ARTIFACT_AUDIT'
    parent = json.loads((PARENT/'state.json').read_text())
    assert digest(PARENT/'state.json') == t['parent_state_sha256'] == obs['parent_state_sha256'] == audit['author_state_sha256']
    assert parent['status'] == 'PASS' and len(parent['records']) == 1210
    assert len(parent['workspace_source_drift']) == 15 and parent['source_status'] == 'HISTORICAL_SNAPSHOT'
    snap = Path(parent['snapshot'])
    assert digest(snap/'manifest.json') == parent['manifest_sha256'] == audit['manifest_sha256']
    pm = json.loads((snap/'manifest.json').read_text())
    assert [r['module'] for r in parent['records']] == pm['order'] and set(parent['outputs']) == set(pm['order'])
    assert len(pm['order']) == 1210
    provider_path = Path(parent['provider'])
    assert digest(provider_path) == parent['provider_receipt_sha256'] == audit['foundation_provider_receipt_sha256']
    provider = json.loads(provider_path.read_text())
    assert provider['status'] == 'BUILT' and provider['exit_code'] == 0
    assert digest(parent['foundation_input_path']) == parent['foundation_input_sha256']
    assert digest(parent['lean_path']) == parent['lean_sha256']
    parent_lib = PARENT/'lib'
    trial_lib = TRIAL/'lib'
    assert not set(names) & set(pm['order'])
    assert not any(dep in names for row in parent['records'] for dep in row['direct_inputs'])
    parent_files = 0
    expected_overlay = {}
    for record in parent['records']:
        name = record['module']; row = pm['sources'][name]
        source = snap / row['snapshot_path']
        assert source.is_file() and not source.is_symlink() and digest(source) == row['sha256'] == record['source_sha256']
        assert record['exit'] == 0 and digest(record['log']) == record['log_sha256']
        g = parent['outputs'][name]; obj = parent_lib.joinpath(*name.split('.')).with_suffix('.olean')
        assert str(obj) in g and g[str(obj)] is not None and g[str(obj)]['sha256'] == record['object_sha256']
        parent_files += guard(g, links=False)
        for path, entry in g.items():
            rel = Path(path).relative_to(parent_lib); dest = trial_lib / rel
            expected_overlay[str(dest)] = None if entry is None else {'realpath': str(Path(path).resolve()), 'sha256': entry['sha256']}
    assert parent_files == 1210 and expected_overlay == t['overlay_guards']
    overlay_present = guard(t['overlay_guards'], links=True)
    assert overlay_present == 1210
    parent_guard_count = len(parent['guarded_companions'])
    assert parent_guard_count == audit['guarded_companion_paths'] == 13150
    guard(parent['guarded_companions']); guard(provider['declared_external_guard'])
    foundation = Path(provider['root'])/'.lake/build/lib/lean/Foundation'
    observed = {str(p.relative_to(foundation)) for p in foundation.rglob('*') if p.is_file() or p.is_symlink()}
    assert observed == set(provider['foundation_artifacts']) and len(observed) == 1540
    foundation_count = len(observed)
    for rel, sha in provider['foundation_artifacts'].items():
        p = foundation/rel
        assert p.is_file() and not p.is_symlink() and digest(p) == sha

    seen = set(pm['order']); trial_reports = []
    for i, (name, rec) in enumerate(zip(names,t['rows'])):
        row = manifest['sources'][name]
        src = TRIAL/'src'/Path(*name.split('.')).with_suffix('.lean')
        copied = PACKET/'src'/Path(*name.split('.')).with_suffix('.lean')
        blob = subprocess.run(['git','show',manifest['source_commit']+':'+row['workspace_path']],cwd=ROOT,check=True,capture_output=True).stdout
        assert hashlib.sha256(blob).hexdigest() == row['sha256'] == rec['source_sha256'] == digest(src) == digest(copied)
        imports = re.findall(r'^import\s+([A-Za-z_][A-Za-z0-9_.\']*)\s*$',blob.decode(),re.M)
        assert len(set(imports)) == len(imports) and set(imports) == set(row['imports'])
        assert all(dep not in names or dep in seen for dep in imports)
        observed = rec['imports']; assert set(imports) <= set(observed) and set(observed)-set(imports) <= {'Init'}
        for dep, item in observed.items():
            p = Path(item['path']); assert p.is_file() and str(p.resolve()) == item['realpath'] and digest(p) == item['sha256']
            if dep in pm['order']:
                assert p.is_symlink() and p.resolve() == (parent_lib/Path(*dep.split('.')).with_suffix('.olean')).resolve()
            elif dep in names:
                assert dep in seen and not p.is_symlink() and p.is_relative_to(trial_lib)
            else:
                assert str(p) in parent['guarded_companions'] and parent['guarded_companions'][str(p)] is not None
                assert parent['guarded_companions'][str(p)]['sha256'] == item['sha256']
        logname = f'{i:03d}-'+name.replace('.','_')+'.log'
        log = TRIAL/'logs'/logname; copied_log = PACKET/'logs'/logname
        assert rec['exit'] == 0 and digest(log) == digest(copied_log) == rec['log_sha256']
        text = log.read_text()
        assert not re.search(r'(?m)^.*(?:error:|error\([^)]*\):)|\bsorryAx\b|\bsorry\b',text)
        reports = re.findall(r"^'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",text,re.M|re.S)
        assert [list(x) for x in reports] == rec['axiom_reports']
        assert [x[0] for x in reports] == manifest['axiom_reports'].get(name,[])
        for declaration, values in reports:
            assert {x.strip() for x in values.split(',') if x.strip()} <= {'propext','Classical.choice','Quot.sound'}
            trial_reports.append(declaration)
        obj = trial_lib/Path(*name.split('.')).with_suffix('.olean')
        g = t['new_output_guards'][name]
        assert str(obj) in g and g[str(obj)] is not None and g[str(obj)]['sha256'] == rec['object_sha256']
        assert not obj.is_symlink() and obj.stat().st_nlink == 1 and digest(obj) == rec['object_sha256']
        guard(g,links=False); seen.add(name)
    assert trial_reports == expected_names and set(t['new_output_guards']) == set(names)
    actual = {str(p) for p in trial_lib.rglob('*') if p.is_file() or p.is_symlink()}
    expected = {p for p,v in t['overlay_guards'].items() if v is not None}
    expected.update(p for g in t['new_output_guards'].values() for p,v in g.items() if v is not None)
    assert actual == expected
    assert digest(state_path) == obs['state_sha256'] and digest(PARENT/'state.json') == t['parent_state_sha256']
    result = {'status':'PASS_INDEPENDENT_STANDARD14_AUTHOR_ARTIFACT_AUDIT',
              'trial_state_sha256':digest(state_path), 'terminal_observation_sha256':digest(PACKET/'terminal-observation.json'),
              'author_audit_sha256':digest(PARENT_AUDIT), 'parent_state_sha256':digest(PARENT/'state.json'),
              'manifest_sha256':digest(MANIFEST), 'driver_sha256':digest(DRIVER), 'script_sha256':digest(__file__),
              'added_modules':len(names), 'added_names':names, 'exact_diagnostic_names':trial_reports,
              'parent_source_log_rows':len(parent['records']), 'parent_present_outputs':parent_files,
              'overlay_guard_paths':len(t['overlay_guards']), 'overlay_present_links':overlay_present,
              'parent_direct_guard_paths':parent_guard_count, 'foundation_artifacts':foundation_count,
              'recorded_workspace_drift':parent['workspace_source_drift'], 'hash_bytes_read':read_bytes,
              'elapsed_seconds':round(time.monotonic()-started,2),
              'scope':'Independent current artifact and recorded-input audit; not a Lean replay, peer match, current-source claim, source-to-object proof for inherited packages, dynamic-load trace, or authentication against transient mutation. Foundation build wrapper outer exit remains unobserved.'}
    out = HERE/'receipt.json'; assert not out.exists(); out.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(result['status'],digest(out),flush=True)

if __name__ == '__main__': main()
