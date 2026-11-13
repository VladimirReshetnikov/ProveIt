#!/usr/bin/env python3
"""Independent guarded direct14 author artifact audit; this does not replay Lean."""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time

if not __debug__:
    raise RuntimeError('This audit requires assertions; do not run Python with -O or -OO')

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
TASK = ROOT / 'Computability/DiophantineConsistency'
TRIAL = Path('/tmp/ipra-standard-direct14-guarded-author-20261101')
PACKET = TASK / 'reviews/ipra-standard-direct14-guarded-author'
PARENT = Path('/tmp/ipra-aq29-fresh-project-pair/author')
PARENT_AUDIT = TASK / 'reviews/fresh-project-author-independent-audit/receipt.json'
DRIVER = TASK / 'research/author-only-extension/run.py'
MANIFEST = TASK / 'research/ipra-standard-direct14/author-additions.json'
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
    script_sha = digest(__file__)
    state_path = TRIAL / 'state.json'
    assert digest(state_path) == '37092f477544b888ba861fb2e4eb7093d0fa592ef0fa0185f724d3127656d0bd'
    assert digest(PACKET/'state.json') == digest(state_path)
    t = json.loads(state_path.read_text())
    obs = json.loads((PACKET/'terminal-observation.json').read_text())
    assert t['status'] == 'AUTHOR_ONLY_PASS' and obs['observed_exit_code'] == 0 and obs['tool_session']==50269
    assert obs['state_sha256']==digest(state_path) and obs['manifest_sha256']==t['manifest_sha256']
    assert obs['stdout_sha256']==digest(PACKET/'process.log') and obs['last_stdout_line']=='AUTHOR_ONLY_PASS 5'
    assert digest(DRIVER) == digest(PACKET/'runner.py') == t['driver_sha256']
    assert digest(MANIFEST) == t['manifest_sha256']
    assert digest(PACKET/'author-additions.json') == digest(MANIFEST)
    manifest = json.loads(MANIFEST.read_text())
    assert manifest['source_commit'] == '777716daef4825d6b3023446b457f12d83aca67f'
    names = manifest['order']
    assert len(names) == len(set(names)) == 5 and [x['module'] for x in t['rows']] == names
    assert names==['DiophantineConsistency.'+n for n in (
        'IPRASuccessorInduction','IPRAAddOneGeneral','IPRASuccessorInductionConverse',
        'IPRAStandardTheory','IPRAStandardDirect14')]
    expected_names = [declaration for name in names for declaration in manifest['axiom_reports'].get(name,[])]
    assert len(expected_names) == 8 and len(set(expected_names)) == 8
    assert manifest['axiom_reports'][names[-1]] == [
        'DiophantineConsistency.IPRASquareWitnessDirect14Native.sameZero13',
        'DiophantineConsistency.IPRASquareWitnessDirect14Native.bridge13',
        'DiophantineConsistency.IPRASquareWitnessDirect14Native.sameNoZero14',
        'DiophantineConsistency.IPRASquareWitnessDirect14Native.bridge14',
        'DiophantineConsistency.IPRASquareWitnessDirect14Native.literal_equivalence',
        'DiophantineConsistency.IPRAStandardDirect14.literal_equivalence',
        'DiophantineConsistency.IPRAStandardDirect14.selected_foundation_consistency',
        'DiophantineConsistency.IPRAStandardDirect14.literal_iff_translated_consistency',
    ]
    process_lines = (PACKET/'process.log').read_text().splitlines()
    assert process_lines == [f'PASS {i} 5 {n}' for i,n in enumerate(names,1)] + ['AUTHOR_ONLY_PASS 5']

    audit = json.loads(PARENT_AUDIT.read_text())
    assert digest(PARENT_AUDIT) == t['author_audit_sha256']
    assert audit['status'] == 'PASS_INDEPENDENT_AUTHOR_ARTIFACT_AUDIT'
    parent = json.loads((PARENT/'state.json').read_text())
    assert digest(PARENT/'state.json') == t['parent_state_sha256'] == audit['author_state_sha256']
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
    # The direct-square native module was compiled in both audited parent siblings.
    pair_audit=TASK/'reviews/fresh-project-pair-independent-audit'
    pair_receipt=json.loads((pair_audit/'receipt.json').read_text())
    pair_terminal=json.loads((pair_audit/'terminal-observation.json').read_text())
    assert pair_terminal['exit_code']==0 and pair_terminal['receipt_sha256']==digest(pair_audit/'receipt.json')
    assert pair_receipt['status']=='PASS_INDEPENDENT_PAIRED_ARTIFACT_AUDIT'
    assert pair_receipt['author_state_sha256']==digest(PARENT/'state.json')
    peer_path=PARENT.parent/'peer/state.json';peer=json.loads(peer_path.read_text())
    assert digest(peer_path)==pair_receipt['peer_state_sha256']
    native='DiophantineConsistency.IPRASquareWitnessDirect14Native'
    ar=next(r for r in parent['records'] if r['module']==native)
    br=next(r for r in peer['records'] if r['module']==native)
    assert ar['exit']==br['exit']==0 and ar['source_sha256']==br['source_sha256'] and ar['object_sha256']==br['object_sha256']
    assert digest(ar['log'])==ar['log_sha256']==br['log_sha256']==digest(br['log'])
    for label,row in [('author',ar),('peer',br)]:
        obj=PARENT.parent/label/'lib'/Path(*native.split('.')).with_suffix('.olean')
        assert not obj.is_symlink() and digest(obj)==row['object_sha256']
    parent_lib = PARENT/'lib'
    trial_lib = TRIAL/'lib'
    assert not set(names) & set(pm['order'])
    assert not any(dep in names for row in parent['records'] for dep in row['direct_inputs'])
    print("Checking 1210 parent rows and provider overlay", flush=True)
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

    print("Checking 5 direct14 extension modules", flush=True)
    seen = set(pm['order']); trial_reports = []
    for i, (name, rec) in enumerate(zip(names,t['rows'])):
        row = manifest['sources'][name]
        src = TRIAL/'src'/Path(*name.split('.')).with_suffix('.lean')
        copied = PACKET/'src'/Path(*name.split('.')).with_suffix('.lean')
        blob = subprocess.run(['git','show',manifest['source_commit']+':'+row['workspace_path']],cwd=ROOT,check=True,capture_output=True).stdout
        assert hashlib.sha256(blob).hexdigest() == row['sha256'] == rec['source_sha256'] == digest(src) == digest(copied)
        imports = re.findall(r'^import\s+([A-Za-z_][A-Za-z0-9_.\']*)\s*$',blob.decode(),re.M)
        assert len(set(imports)) == len(imports) and set(imports) == set(row['imports'])
        directives = re.findall(r'^\s*#print\s+axioms\s+([^\s]+)\s*$',blob.decode(),re.M)
        assert len(directives) == len(manifest['axiom_reports'].get(name,[])), ('diagnostic directive count',name)
        if name == 'DiophantineConsistency.IPRAStandardTheory':
            assert 'theorem provable_iff (φ : Sentenceᵢ language) : standardTheory ⊢ φ ↔ nativeTheory ⊢ φ :=' in blob.decode()
        if name == 'DiophantineConsistency.IPRAStandardDirect14':
            text = blob.decode()
            assert 'import DiophantineConsistency.IPRASquareWitnessDirect14Native' in text
            assert 'theorem literal_equivalence : standardTheory ⊢ IPRAExpressionNative.nativeNoZero\n    (positiveShift (AdaptiveSquareWitnessDirect14.literal CurrentWindowCarry2011.ports)) 🡘\n      ∼mappedNativeRefutation embedding :=' in text
            assert 'theorem selected_foundation_consistency : standardTheory ⊢\n    (Semiformula.lMap embedding FoundationZFCConsistencyNat.sourceSentence)ᴺ 🡘\n      ∼mappedNativeRefutation embedding :=' in text
            assert 'theorem literal_iff_translated_consistency : standardTheory ⊢\n    IPRAExpressionNative.nativeNoZero\n      (positiveShift (AdaptiveSquareWitnessDirect14.literal CurrentWindowCarry2011.ports)) 🡘\n        (Semiformula.lMap embedding FoundationZFCConsistencyNat.sourceSentence)ᴺ :=' in text
        assert all(dep not in names or dep in seen for dep in imports)
        observed = rec['imports']; assert set(imports) <= set(observed) and set(observed)-set(imports) <= {'Init'}
        for dep, item in observed.items():
            p = Path(item['path']); assert p.is_file() and str(p.resolve()) == item['realpath'] and digest(p) == item['sha256']
            if dep in pm['order']:
                assert p.is_symlink() and p.resolve() == (parent_lib/Path(*dep.split('.')).with_suffix('.olean')).resolve()
            elif dep in names:
                assert dep in seen and not p.is_symlink()
                assert p == trial_lib/Path(*dep.split('.')).with_suffix('.olean')
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
    assert sum(len(row['imports']) for row in t['rows']) == 16
    actual = {str(p) for p in trial_lib.rglob('*') if p.is_file() or p.is_symlink()}
    expected = {p for p,v in t['overlay_guards'].items() if v is not None}
    expected.update(p for g in t['new_output_guards'].values() for p,v in g.items() if v is not None)
    assert actual == expected
    assert digest(state_path) == '37092f477544b888ba861fb2e4eb7093d0fa592ef0fa0185f724d3127656d0bd' and digest(PARENT/'state.json') == t['parent_state_sha256']
    assert digest(__file__) == script_sha and digest(DRIVER) == t['driver_sha256']
    assert digest(MANIFEST) == t['manifest_sha256'] and digest(PACKET/'process.log') == obs['stdout_sha256']
    print("Rechecking guarded artifacts", flush=True)
    for record in parent['records']:
        name=record['module']; source=snap/pm['sources'][name]['snapshot_path']
        assert source.is_file() and not source.is_symlink() and digest(source) == record['source_sha256']
        assert digest(record['log']) == record['log_sha256']
        guard(parent['outputs'][name],links=False)
    for i, (name,rec) in enumerate(zip(names,t['rows'])):
        src=TRIAL/'src'/Path(*name.split('.')).with_suffix('.lean')
        copied=PACKET/'src'/Path(*name.split('.')).with_suffix('.lean')
        logname=f'{i:03d}-'+name.replace('.','_')+'.log'
        assert digest(src)==digest(copied)==rec['source_sha256']
        assert digest(TRIAL/'logs'/logname)==digest(PACKET/'logs'/logname)==rec['log_sha256']
        guard(t['new_output_guards'][name],links=False)
    guard(t['overlay_guards'],links=True); guard(parent['guarded_companions'])
    result = {'status':'PASS_INDEPENDENT_DIRECT14_AUTHOR_ARTIFACT_AUDIT',
              'trial_state_sha256':digest(state_path), 'terminal_exit_sha256':digest(PACKET/'terminal-observation.json'),
              'author_audit_sha256':digest(PARENT_AUDIT), 'parent_state_sha256':digest(PARENT/'state.json'),
              'manifest_sha256':digest(MANIFEST), 'driver_sha256':digest(DRIVER), 'script_sha256':script_sha,
              'added_modules':len(names), 'added_names':names, 'exact_diagnostic_names':trial_reports,
              'added_direct_import_edges':sum(len(row['imports']) for row in t['rows']),
              'parent_source_log_rows':len(parent['records']), 'parent_present_outputs':parent_files,
              'overlay_guard_paths':len(t['overlay_guards']), 'overlay_present_links':overlay_present,
              'parent_direct_guard_paths':parent_guard_count, 'foundation_artifacts':foundation_count,
              'recorded_workspace_drift':parent['workspace_source_drift'], 'hash_bytes_read':read_bytes,
              'elapsed_seconds':round(time.monotonic()-started,2),
              'scope':'Independent point-in-time audit of historical combined native and standard direct14 author artifacts; not a Lean replay, peer match, current-source or PDF claim, source-to-object proof for inherited packages, dynamic-load trace, or authentication against transient mutation. Foundation build wrapper outer exit remains unobserved.'}
    out = HERE/'receipt.json'; assert not out.exists(); out.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(result['status'],digest(out),flush=True)

if __name__ == '__main__': main()
