"""Independent read of actual phase16 compiler records; runs no proof compiler."""
from pathlib import Path
import hashlib, json, re

S = Path(__file__).resolve().parent
D = Path('/tmp/k215-phase16-check')
B = Path('/tmp/k215-phase15-check')
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
read = lambda p: json.loads(Path(p).read_text())
normal = lambda rs: [(n, sorted(x.strip() for x in a.split(',') if x.strip())) for n, a in rs]
report = re.compile(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)")

old, old_done = {}, {}
for name in ['compatibility-run1', 'primary-run3']:
    p = B / name
    result, inventory, completed = [read(p / n) for n in ['result.json', 'inventory.json', 'completed.json']]
    assert result['status'] == 'PASS'
    assert sha(p / 'inventory.json') == result['inventory_sha256']
    assert sha(p / 'completed.json') == result['completed_sha256']
    old.update({r['module']: r for r in inventory['modules']})
    old_done.update(completed)
assert len(old) == 211

scopes, current, actual_clients = {}, {}, {}
for name in ['primary-run1', 'compatibility-run1']:
    p = D / name
    result, inventory, completed = [read(p / n) for n in ['result.json', 'inventory.json', 'completed.json']]
    assert result['status'] == 'PASS'
    assert sha(p / 'inventory.json') == result['inventory_sha256']
    assert sha(p / 'completed.json') == result['completed_sha256']
    rows = {r['module']: r for r in inventory['modules']}
    assert len(rows) == len(inventory['modules']) and set(rows) == set(completed)
    changed = {m for m, r in rows.items() if m not in old or
               (r['source_sha256'], r['imports']) != (old[m]['source_sha256'], old[m]['imports'])}
    forced = set(changed)
    while True:
        expanded = forced | {m for m, r in rows.items() if set(r['imports']) & forced}
        if expanded == forced:
            break
        forced = expanded
    assert sorted(changed) == result['source_changed_modules']
    assert sorted(forced) == result['force_basis_rebuild_modules']
    for m, row in rows.items():
        rec = completed[m]
        assert rec['status'] == 'PASS' and rec.get('exit_code', 0) == 0
        assert not rec.get('timed_out', False)
        assert sha(row['source']) == row['source_sha256'] == rec['source_sha256']
        assert rec['dependencies'] == {d: completed[d]['object_sha256'] for d in row['imports'] if d != 'Init'}
        assert sha(p / 'objects' / (m.replace('.', '/') + '.olean')) == rec['object_sha256']
        assert sha(rec['log']) == rec['log_sha256']
        log = Path(rec['log']).read_text()
        assert 'error:' not in log and 'sorryAx' not in log
        reports = normal(report.findall(log))
        assert all(set(a) <= {'propext', 'Classical.choice', 'Quot.sound'} for _, a in reports)
        if m in forced:
            if name == 'primary-run1':
                assert rec['origin'] == 'candidate_fresh'
            else:
                assert rec['origin'] in {'candidate_fresh', 'secondary_checked'}
        if rec['origin'] == 'candidate_fresh':
            assert sha(rec['source']) == row['source_sha256']
            assert '-j1' in rec['command'] and '-M12288' in rec['command']
            assert rec['timeout_seconds'] == (900 if 'KSites215Batch' in m else 120)
        if not m.startswith(('BusyBeaver.', 'FirstOrder.', 'ZF.', 'BoundedZFCConsistency.')):
            assert 'warning:' not in log
            if m in old_done:
                assert reports == normal(old_done[m]['reports'])
            actual_clients[m] = reports
        if m in current:
            assert current[m] == (row['source_sha256'], row['imports'], rec['object_sha256'])
        current[m] = (row['source_sha256'], row['imports'], rec['object_sha256'])
    audits = result.get('audits', [])
    if name == 'primary-run1':
        prior = {r['module']: r for r in read(B / 'primary-run3/result.json')['audits']}
        assert {r['module'] for r in audits} == set(prior)
        for rec in audits:
            assert rec['status'] == 'PASS' and rec['exit_code'] == 0 and not rec['timed_out']
            assert sha(rec['source']) == rec['source_sha256'] == prior[rec['module']]['source_sha256']
            assert sha(rec['log']) == rec['log_sha256']
            log = Path(rec['log']).read_text()
            assert 'warning:' not in log and 'sorryAx' not in log and 'error:' not in log
            assert normal(report.findall(log)) == normal(prior[rec['module']]['named_reports'])
    scopes[name] = {'providers': len(rows), 'changed': sorted(changed), 'forced': sorted(forced),
                    'fresh': [m for m, r in completed.items() if r['origin'] == 'candidate_fresh'],
                    'result_sha256': sha(p / 'result.json'), 'endpoint_audits': len(audits)}

projects = set(current) - set(actual_clients)
assert len(projects) == 199 and len(actual_clients) == 13
assert len(scopes['primary-run1']['fresh']) == 27
assert len(scopes['compatibility-run1']['fresh']) == 4
assert not any('KSites215Batch' in m for s in scopes.values() for m in s['fresh'])
receipt = {'status': 'PASS_INDEPENDENT_ACTUAL_RECORD_REVIEW', 'scopes': scopes,
           'project_union': len(projects), 'typed_clients': actual_clients,
           'all_nine_site_batches_inherited': True,
           'scope': 'Actual successful compiler records, objects, sources, imports and logs; no compiler or producer rerun.'}
(S / 'actual-review.json').write_text(json.dumps(receipt, indent=2) + '\n')
print(receipt['status'], len(projects), 'project modules;', len(actual_clients), 'typed clients')
