"""Audit saved phase-two evidence without executing Lean or archived code.

Default scope is the historical executed source checkpoint. --repo additionally
requires every checkpoint source to remain current. No live object claim.
"""
from pathlib import Path, PurePosixPath
import argparse
import hashlib
import json
import re
import tarfile


def digest(data):
    return hashlib.sha256(data).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--packet', type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument('--repo', type=Path)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    assert not args.output.exists(), 'Refusing to overwrite a receipt'
    packet = args.packet.resolve()
    summary = json.loads((packet / 'result.json').read_text())
    index = json.loads((packet / 'index.json').read_text())
    archive = packet / 'execution.tar.gz'
    assert digest(archive.read_bytes()) == summary['execution_archive_sha256']
    members = {}
    with tarfile.open(archive, 'r:gz') as tar:
        for entry in tar:
            path = PurePosixPath(entry.name)
            assert entry.isfile() and not path.is_absolute() and '..' not in path.parts
            assert entry.name not in members
            assert path.suffix not in {'.olean', '.ilean', '.vo', '.vos', '.vok', '.glob'}
            data = tar.extractfile(entry).read()
            assert index[entry.name] == {'sha256': digest(data), 'bytes': len(data)}
            members[entry.name] = data
    assert set(members) == set(index) and len(index) == summary['archive_members']

    def read(name):
        return json.loads(members[name])

    result = read('execution/result.json')
    owner = read('execution/owner.json')
    inv = read('execution/inventory.json')
    done = read('execution/completed.json')
    phase1 = read('execution/phase1-result.json')
    old = read('execution/phase1-completed.json')
    basis = read('execution/basis-objects.json')
    toolchain = read('execution/toolchain.json')
    for key, value in result.items():
        assert summary[key] == value, key
    assert result['status'] == 'PASS' and result['external_imports'] == ['Init']
    assert digest(members['execution/inventory.json']) == result['inventory_sha256']
    assert digest(members['execution/completed.json']) == result['completed_sha256']
    for name, key in [('phase1-result.json', 'phase1_result_sha256'),
                      ('phase1-completed.json', 'phase1_completed_sha256'),
                      ('toolchain.json', 'toolchain_boundary_sha256'),
                      ('reviewed-driver.py', 'helper_sha256')]:
        assert digest(members['execution/' + name]) == owner[key]
    assert digest(members['review/build.py']) == owner['script_sha256']
    assert owner['compiler_sha256'] == phase1['compiler_sha256'] == toolchain['lean']['sha256']
    assert digest(members['review/live-review.json']) == summary['live_review_sha256']
    live = read('review/live-review.json')
    assert live['status'] == 'PASS_LIVE_POST_AUDIT_REVIEW'
    assert live['result_sha256'] == digest(members['execution/result.json'])
    assert live['reviewer_sha256'] == digest(members['review/review.py'])
    assert live['all185_objects_rehashed_after_audits'] and live['all215_phase1_objects_unchanged']
    assert (packet / 'live-review.json').read_bytes() == members['review/live-review.json']
    assert (packet / 'review_saved.py').read_bytes() == members['review/review_saved.py']

    modules = {e['module']: e for e in inv['modules']}
    assert len(modules) == len(inv['modules']) == len(done) == 185
    assert set(done) == set(modules) and inv['external_imports'] == ['Init']
    prior = {e['module']: e for e in phase1['module_evidence']}
    assert len(prior) == len(old) == len(basis) == 215 and set(prior) == set(old) == set(basis)
    assert all(basis[m] == old[m]['object_sha256'] == prior[m]['object_sha256'] for m in basis)
    seen = set()
    for entry in inv['modules']:
        assert set(entry['imports']) <= seen | {'Init'}
        seen.add(entry['module'])
    closure = set()

    def visit(module):
        if module in closure:
            return
        closure.add(module)
        for dep in modules[module]['imports']:
            if dep in modules:
                visit(dep)

    visit(inv['target'])
    assert closure == set(modules)
    run = PurePosixPath(result['audits'][0]['log']).parent.parent
    old_repo = PurePosixPath(owner['repo'])

    def saved_path(original):
        return 'execution/' + str(PurePosixPath(original).relative_to(run))

    def log_gate(data):
        text = data.decode()
        assert 'error:' not in text and 'sorryAx' not in text and "declaration uses 'sorry'" not in text
        return text

    fresh = warnings = 0
    for module, entry in modules.items():
        row = done[module]
        assert row['status'] == 'PASS' and row['source_sha256'] == entry['source_sha256']
        assert row['dependencies'] == {d: done[d]['object_sha256'] for d in entry['imports'] if d in done}
        assert re.fullmatch('[0-9a-f]{64}', row['object_sha256'])
        if args.repo:
            current = args.repo / str(PurePosixPath(entry['source']).relative_to(old_repo))
            assert digest(current.read_bytes()) == entry['source_sha256'], module
        if row['origin'] == 'phase2_fresh':
            fresh += 1
            log = saved_path(row['log'])
            folder = str(PurePosixPath(log).parent)
            assert read(folder + '/record.json') == row
            assert digest(members[folder + '/' + PurePosixPath(entry['source']).name]) == row['source_sha256']
            assert digest(members[log]) == row['log_sha256']
            root = entry['source'][:-len(module.replace('.', '/') + '.lean')].rstrip('/')
            assert row['command'] == [toolchain['lean']['path'], '-j1', '-M12288', '--root=' + root,
                                      '-o', str(run / 'objects' / (module.replace('.', '/') + '.olean')),
                                      entry['source']]
            assert row['compiler_sha256'] == owner['compiler_sha256']
            assert row['exit_code'] == 0 and not row['timed_out']
            assert row['source_unchanged'] and row['dependencies_unchanged']
            assert row['timeout_seconds'] == 900 and row['memory_mebibytes'] == 12288
            text = log_gate(members[log])
            assert text.count('warning:') == row['warnings']
        else:
            assert row['origin'] == 'phase1_hash_bound'
            for key in ['source_sha256', 'object_sha256', 'dependencies', 'log_sha256']:
                assert row[key] == prior[module][key] == old[module][key]
            log = 'execution/reused-logs/' + module + '.log'
            assert digest(members[log]) == row['log_sha256']
            text = log_gate(members[log])
            assert text.count('warning:') == prior[module]['warnings']
        warnings += text.count('warning:')
    assert fresh == result['fresh_modules'] and 185 - fresh == result['reused_modules']
    assert warnings == summary['project_warnings'] == live['project_warnings']
    assert len(result['audits']) == 2 and result['typed_audits'] == 2
    report_count = 0
    for row, name, count in zip(result['audits'], ['EndpointAudit215', 'K215Audit'], [2, 8]):
        assert row['module'] == name and row['expected_reports'] == count
        log = saved_path(row['log'])
        folder = str(PurePosixPath(log).parent)
        assert read(folder + '/' + name + '.json') == row
        assert row['dependencies'] == {m: done[m]['object_sha256'] for m in done}
        assert digest(members[folder + '/' + name + '.lean']) == row['source_sha256']
        assert digest(members[log]) == row['log_sha256']
        assert row['status'] == 'PASS' and row['exit_code'] == 0 and not row['timed_out']
        assert row['compiler_sha256'] == owner['compiler_sha256'] and row['timeout_seconds'] == 120
        auditdir = PurePosixPath(row['log']).parent
        assert row['command'] == [toolchain['lean']['path'], '-j1', '-M12288', '--root=' + str(auditdir),
                                  '-o', str(auditdir / (name + '.olean')), str(auditdir / (name + '.lean'))]
        text = log_gate(members[log])
        assert 'warning:' not in text
        reports = re.findall(r'depends on axioms: \[([^]]*)\]', text)
        assert len(reports) + text.count('does not depend on any axioms') == count
        assert reports == row['reports']
        assert all(set(x.strip() for x in report.split(',')) <=
                   {'propext', 'Classical.choice', 'Quot.sound'} for report in reports)
        report_count += count
    assert report_count == result['axiom_reports'] == 10
    receipt = {'status': 'PASS_SAVED_EVIDENCE_REVIEW', 'project_modules': 185,
               'fresh_modules': fresh, 'reused_modules': 185 - fresh,
               'typed_clients': 2, 'axiom_reports': 10, 'project_warnings': warnings,
               'audit_warnings': 0, 'compiled_objects_in_archive': False,
               'archive_members': len(index), 'archive_sha256': digest(archive.read_bytes()),
               'result_sha256': digest((packet / 'result.json').read_bytes()),
               'reviewer_sha256': digest(Path(__file__).read_bytes()),
               'current_checkpoint_sources_checked': args.repo is not None,
               'scope': 'Saved source/dependency/object hash records and raw logs only; no compiler rerun or live-object verification. Historical checkpoint is not rewritten by later source addenda.'}
    args.output.write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()
