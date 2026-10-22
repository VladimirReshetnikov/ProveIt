"""Phase16 source-transitive record validation. This module executes no proof tools."""
from pathlib import Path
import hashlib, json, re
ROOT = '/home/codex/.codex/worktrees/ec20/Proofs'
PREP = '/tmp/k215-phase16-check'
RUNS = [PREP + '/' + n for n in ['primary-run1', 'compatibility-run1']]
OLD = ['/tmp/k215-phase15-check/' + n for n in ['primary-run3', 'compatibility-run1']]
Q = '/tmp/k215-phase16-quotient'
INTEGRATION = ROOT + '/Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/phase16/integration'
DRIVER = 'ed37105fce68f31ea45f2bc674541b260e5ae312846700f0f08bbaf6dae559ff'
FREEZE = '1bc88ebfbccbc105bf461fe7461621aa5d0604a692dfd38b8882881ed557affa'
SOURCE_FREEZE = 'd6905d22aeba74d7481922267f84b1c31d7590c63907a24a26039bf10ad9d085'
CLIENTS = ['GenericShared13Api','NumericCD52Api','LukasShared13Api','DerivedRows14Api','ThmKDerived14Api','KEindDerived14Api','ProfileTC14Api','BasicInterfaces15Api','TransRec15Api','QuotientSharing15Api','QuotientUnified16Api','WFModelCompat12','ZFNativeCompat12']
NEW_NAMES = ['QuotientUnified16Api.' + n for n in ['legacy_carrier','legacy_constructor','weak_carrier','weak_constructor','weak_membership','cp_gic_supplies_weak','weak_native_gic','strong_cp_gic']]
digest = lambda b: hashlib.sha256(b).hexdigest()
sha = lambda p: digest(Path(p).read_bytes())
dump = lambda x: (json.dumps(x, indent=2) + '\n').encode()

def closure(rows, roots):
    seen = set()
    def visit(m):
        if m == 'Init' or m in seen: return
        seen.add(m)
        for d in rows[m]['imports']: visit(d)
    for m in roots: visit(m)
    return seen

def compatible(rows, prior, m):
    return all(d in prior and (rows[d]['source_sha256'], rows[d]['imports']) ==
               (prior[d]['source_sha256'], prior[d]['imports']) for d in closure(rows, [m]))

def bind_source(row, override, old):
    if override is not None: assert all(row[key] == override[key] for key in ['source','source_sha256','imports'])
    else: assert (row['source_sha256'], row['imports']) == (old['source_sha256'], old['imports'])

def outer_gate(outer, argv):
    assert outer['status'] == 'PASS_OUTER_EXIT_ZERO' and outer['exit_code'] == 0 and not outer['timed_out']
    assert outer['argv'] == argv and outer['freeze_sha256'] == FREEZE and outer['frozen_files_unchanged']

def absence_gate(actual, old, retired):
    assert len(actual) == 5 and set(actual) == set(old) | {ROOT + '/' + retired}

def validate(members, prior, h, current_repo=None):
    assert members['config.json'] == members['review/config.json']
    cfg = json.loads(members['config.json']); routes = json.loads(members['path-map.json'])
    resolved = {}
    for path, r in routes.items():
        assert Path(path).is_absolute() and r['storage'] in {'packet', 'phase15'}
        b = (members if r['storage'] == 'packet' else prior)[r['key']]
        assert (digest(b), len(b)) == (r['sha256'], r['bytes']); resolved[path] = b
    at = lambda p: resolved[str(p)]
    read = lambda p: json.loads(at(p))
    for path, pin in cfg['context'].items(): assert digest(at(path)) == pin
    assert cfg['status'] == 'FROZEN_TERMINAL_PHASE16_INPUTS'
    assert digest(at(PREP + '/freeze.json')) == FREEZE
    f = read(PREP + '/freeze.json')
    for p, pin in f['files'].items(): assert digest(at(PREP + '/' + p)) == pin
    for p, pin in f['external_source_packet_inputs'].items(): assert digest(at(p)) == pin
    assert digest(at(Q + '/final-source-freeze.json')) == SOURCE_FREEZE
    for r in read(Q + '/final-source-freeze.json')['files']: assert digest(at(r['path'])) == r['sha256']
    oldrows, olddone, oldorigin, object_pins = {}, {}, {}, {}
    def records(root):
        result, inv, done = [read(root + '/' + n) for n in ['result.json','inventory.json','completed.json']]
        assert result['status'] == 'PASS'
        assert digest(at(root + '/inventory.json')) == result['inventory_sha256']
        assert digest(at(root + '/completed.json')) == result['completed_sha256']
        rows = {r['module']: r for r in inv['modules']}
        assert len(rows) == len(inv['modules']) and set(rows) == set(done)
        for m, rec in done.items(): object_pins[root + '/objects/' + m.replace('.', '/') + '.olean'] = rec['object_sha256']
        return result, inv, rows, done
    for root, origin in [(OLD[1], 'phase15_compatibility_checked'), (OLD[0], 'phase15_primary_checked')]:
        _, _, rows, done = records(root)
        for n in ['result.json','inventory.json','completed.json','toolchain.json']: assert at(root + '/' + n) == prior['path:' + root + '/' + n]
        oldrows.update(rows); olddone.update(done); oldorigin.update({m: origin for m in rows})
    assert len(oldrows) == 211
    ancestry = read('/tmp/k215-proof-phase8/lean-run1/result.json')
    assert digest(at('/tmp/k215-proof-phase8/lean-run1/result.json')) == '6d1eed6ad824218ab297ce8bc1b573adc520bf72f645bf546dc5618928bb1c5f'
    for name, pin in ancestry['exact_machine_pins'].items(): assert digest(at(ROOT + '/Computability/BusyBeaver/Research/ZFC/candidate-k215/' + name)) == pin
    toolchain = read(OLD[0] + '/toolchain.json')
    binary_pins = {v['path']: v['sha256'] for v in toolchain.values() if isinstance(v, dict) and 'path' in v}
    reference = json.loads(members['review/basis-reference.json'])
    parent_pins = {ROOT + '/' + reference['repository_relative_directory'] + '/' + n: r['sha256'] for n, r in reference['files'].items()}
    union, scopes, allreports, accepted = {}, {}, {}, []
    previous_rows, previous_done = {}, {}
    for k, root in enumerate(RUNS):
        result, inv, rows, done = records(root); accepted.append((root, rows, done, result))
        before = read(root + '/before.json')
        outer = read('/tmp/k215-phase16-execution/' + ('primary' if k == 0 else 'compatibility') + '-run1-outer.json')
        outer_gate(outer, read(PREP + '/commands.json')['primary' if k == 0 else 'compatibility'])
        for key in ['stdout','stderr']: assert digest(at(outer[key])) == outer[key + '_sha256']
        map_path = PREP + ('/primary-map.json' if k == 0 else '/compatibility-final-map.json')
        plan = read(map_path); overrides = {r['module']: r for r in plan['modules']}
        assert result['runner_sha256'] == before['runner_sha256'] == DRIVER == digest(at(PREP + '/build.py'))
        assert result['map_sha256'] == before['map_sha256'] == digest(at(map_path))
        assert read(root + '/toolchain.json') == toolchain
        boundary = read(PREP + '/producer-boundary.json')
        assert result['producer_boundary_sha256'] == digest(at(PREP + '/producer-boundary.json'))
        assert result['basis_result_sha256'] == digest(at(OLD[0] + '/result.json'))
        assert result['compatibility_basis_result_sha256'] == digest(at(OLD[1] + '/result.json'))
        assert before['absent_inputs'] == boundary['absent_inputs'] and before['audit_endpoint'] == (k == 0)
        assert inv['modules'] == before['rows'] and inv['targets'] == before['targets'] == result['targets']
        assert list(rows) == plan['expected']['modules'] and closure(rows, inv['targets']) == set(rows)
        seen = {'Init'}
        for m, row in rows.items(): assert set(row['imports']) <= seen; seen.add(m)
        assert inv['external_imports'] == sorted({d for row in rows.values() for d in row['imports']} - set(rows))
        assert set(inv['external_imports']) <= {'Init'}
        changed = {m for m, r in rows.items() if m not in oldrows or (r['source_sha256'], r['imports']) != (oldrows[m]['source_sha256'], oldrows[m]['imports'])}
        forced = {m for m in rows if closure(rows, [m]) & changed}
        assert sorted(changed) == result['source_changed_modules'] == plan['expected']['changed'] == before['changed_sources']
        assert sorted(forced) == result['force_basis_rebuild_modules'] == plan['expected']['forced'] == before['force_basis_rebuild']
        counts, warnings = {}, {'fresh': 0, 'reused': 0}
        for m, row in rows.items():
            rec = done[m]; origin = rec['origin']; counts[origin] = counts.get(origin, 0) + 1
            bind_source(row, overrides.get(m), oldrows.get(m))
            assert rec['status'] == 'PASS' and rec.get('exit_code', 0) == 0 and not rec.get('timed_out', False)
            assert digest(at(row['source'])) == row['source_sha256'] == rec['source_sha256'] == digest(members['sources/' + m.replace('.', '/') + '.lean'])
            assert rec['dependencies'] == {d: done[d]['object_sha256'] for d in row['imports'] if d != 'Init'}
            log = at(rec['log']); assert digest(log) == rec['log_sha256']; reports = h.reports(log)
            if 'reports' in rec: assert h.profiles(reports) == h.profiles(rec['reports'])
            if origin == 'candidate_fresh':
                assert read(str(Path(rec['log']).with_name('record.json'))) == rec
                assert digest(at(rec['source'])) == row['source_sha256']
                expected = [toolchain['lean']['path'], '-j1', '-M12288', '--root=' + root + '/workspace', '-o', root + '/objects/' + m.replace('.', '/') + '.olean', root + '/workspace/' + m.replace('.', '/') + '.lean']
                assert rec['command'] == expected and rec['timeout_seconds'] == 120 and rec['memory_mebibytes'] == 12288
                assert rec['compiler_sha256'] == toolchain['lean']['sha256']
            elif origin == 'secondary_checked':
                assert k == 1 and compatible(rows, previous_rows, m) and rec == {**previous_done[m], 'origin': origin}
            else:
                assert origin == oldorigin[m] and m not in forced and compatible(rows, oldrows, m)
                assert rec == {**olddone[m], 'origin': origin}
            if m in overrides and 'reports' in overrides[m]:
                p = overrides[m]; h.named_reports(log, p['reports'], p.get('report_axioms'))
            if m in CLIENTS:
                assert b'warning:' not in log
                if m in olddone: assert h.profiles(reports) == h.profiles(h.reports(at(olddone[m]['log'])))
                else: h.named_reports(log, NEW_NAMES, [h.STANDARD] * 8)
                allreports[m] = reports
            warnings['fresh' if origin == 'candidate_fresh' else 'reused'] += log.count(b'warning:')
            binding = [row['source_sha256'], row['imports'], rec['object_sha256']]
            if m in union: assert union[m] == binding
            union[m] = binding
        expected_counts = ({'candidate_fresh': 27, 'phase15_primary_checked': 168} if k == 0 else {'candidate_fresh': 4, 'secondary_checked': 61, 'phase15_compatibility_checked': 13})
        assert counts == expected_counts
        for field, origin in [('fresh_modules','candidate_fresh'),('phase15_primary_reused_modules','phase15_primary_checked'),('phase15_compatibility_reused_modules','phase15_compatibility_checked'),('secondary_reused_modules','secondary_checked')]:
            assert result[field] == [m for m, rec in done.items() if rec['origin'] == origin]
        audits = result['audits']; oldaudits = read(OLD[0] + '/result.json')['audits']
        assert len(audits) == (0 if k else 2)
        for rec, old in zip(audits, oldaudits):
            name = rec['module']; assert name == old['module']
            assert rec['status'] == 'PASS' and rec['exit_code'] == 0 and not rec['timed_out']
            assert digest(at(rec['source'])) == rec['source_sha256'] == old['source_sha256']
            assert digest(at(rec['log'])) == rec['log_sha256']
            reports = h.named_reports(at(rec['log']), h.AUDIT_NAMES[name])
            assert h.profiles(reports) == h.profiles(old['named_reports']) == h.profiles(rec['named_reports'])
            assert rec['dependencies'] == {m: r['object_sha256'] for m, r in done.items()}
            adir = root + '/audit-' + name
            assert rec['command'] == [toolchain['lean']['path'], '-j1', '-M12288', '--root=' + adir, '-o', adir + '/' + name + '.olean', adir + '/' + name + '.lean']
            assert rec['timeout_seconds'] == 120 and rec['memory_mebibytes'] == 12288
            assert read(adir + '/' + name + '.json') == rec
        scopes[root] = {'providers': len(rows), 'origins': counts, 'warnings': warnings, 'result_sha256': digest(at(root + '/result.json'))}
        previous_rows, previous_done = rows, done
    final = read(PREP + '/compatibility-final-map.json'); ledger = final.pop('reuse_ledger')
    assert final == read(PREP + '/compatibility-template.json')
    assert ledger == {'directory': RUNS[0], **{n: digest(at(RUNS[0] + '/' + n)) for n in ['result.json','inventory.json','completed.json']}}
    for root, rows, done, result in accepted:
        for p, pin in read(root + '/before.json')['inputs'].items():
            assert ({**object_pins, **binary_pins, **parent_pins}.get(p) if p in object_pins or p in binary_pins or p in parent_pins else digest(at(p))) == pin
    adoption = read(INTEGRATION + '/adoption.json'); current = read(INTEGRATION + '/current-review.json')
    assert adoption['status'] == 'ADOPTED_EXACT_CHECKED_PHASE16_QUOTIENT_SUCCESSOR'
    assert adoption['source_freeze_sha256'] == SOURCE_FREEZE and len(adoption['files']) == 14
    planned = read(PREP + '/sources.json'); retired = read(Q + '/retirement.json')
    writes = {r['target']: r for r in planned}
    assert {r['path'] for r in adoption['files']} == set(writes) | {retired['path']}
    for row in adoption['files']:
        assert digest(at(ROOT + '/' + row['before_snapshot'])) == row['before_sha256']
        if row['path'] in writes:
            p = writes[row['path']]; assert row['action'] == 'write' and row['candidate'] == p['source']
            assert (row['before_sha256'], row['after_sha256']) == (p['before_sha256'], p['source_sha256'])
        else: assert row['action'] == 'retire' and row['after_sha256'] is None and row['before_sha256'] == retired['before_sha256']
    assert len(union) == 212 and len(allreports) == 13 and len(set(union) - set(CLIENTS)) == 199
    assert current['status'] == 'PASS_CURRENT_PHASE16_ADOPTION' and current['adoption_sha256'] == digest(at(INTEGRATION + '/adoption.json'))
    assert set(current['sources']) == set(union) - set(CLIENTS)
    absence_gate(current['retained_absences'], read(PREP + '/producer-boundary.json')['absent_inputs'], retired['path'])
    for m, row in current['sources'].items():
        assert row['sha256'] == union[m][0]
        if current_repo is not None: assert sha(Path(current_repo) / Path(row['current']).relative_to(ROOT)) == row['sha256']
    if current_repo is not None:
        for p in current['retained_absences']: h.absent(Path(current_repo) / Path(p).relative_to(ROOT))
    return {'status': 'PASS_PHASE16_RECORDS', 'scopes': scopes, 'project_union': 199, 'source_copies': 212, 'typed_clients': allreports, 'endpoint_reports': 10, 'current_sources_checked': current_repo is not None}, accepted, object_pins, binary_pins
