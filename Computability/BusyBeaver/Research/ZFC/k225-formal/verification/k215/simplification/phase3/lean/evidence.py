"""Read-only validation shared by the live and saved phase-three reviewers.

Only JSON, source text and log bytes are interpreted. No archived code is run.
"""
from pathlib import Path, PurePosixPath
import hashlib
import json
import re

ROOTS = ('Computability/BusyBeaver/Lean', 'Logic/FirstOrder/Lean',
         'SetTheory/ZF/Lean', 'SetTheory/BoundedConsistency/Lean')
TARGET = 'BusyBeaver.ZFC.KEndpoint215'
AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
BINARY_SUFFIXES = {'.olean', '.ilean', '.o', '.so', '.a', '.vo', '.vos', '.vok', '.glob', '.pyc', '.pyo'}


def binary_name(path):
    # Lean also uses .olean.server/.olean.private companions.
    return any(suffix in BINARY_SUFFIXES for suffix in PurePosixPath(path).suffixes)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def sha(path):
    return digest(Path(path).read_bytes())


def save(path, value):
    with Path(path).open('x') as stream:
        json.dump(value, stream, indent=2)
        stream.write('\n')


def manifest(members):
    return {name: {'sha256': digest(data), 'bytes': len(data)}
            for name, data in sorted(members.items())}


def manifest_hash(members):
    return digest(json.dumps(manifest(members), sort_keys=True, separators=(',', ':')).encode())


def imports(data):
    """Strip nested Lean comments and strings, then read import commands."""
    text = data.decode()
    out, index, depth = [], 0, 0
    while index < len(text):
        pair = text[index:index + 2]
        if pair == '/-':
            depth += 1
            index += 2
        elif depth and pair == '-/':
            depth -= 1
            index += 2
        elif depth:
            if text[index] == '\n':
                out.append('\n')
            index += 1
        elif pair == '--':
            end = text.find('\n', index)
            index = len(text) if end < 0 else end
        elif text[index] == '"':
            index += 1
            while index < len(text):
                if text[index] == '\\':
                    index += 2
                elif text[index] == '"':
                    index += 1
                    break
                else:
                    index += 1
        else:
            out.append(text[index])
            index += 1
    assert depth == 0, 'Unclosed Lean comment'
    return [module for line in re.findall(r'(?m)^\s*(?:public\s+)?import\s+([^\n]+)', ''.join(out))
            for module in line.split()]


def log_text(data):
    text = data.decode()
    assert 'error:' not in text and 'sorryAx' not in text
    assert "declaration uses 'sorry'" not in text
    return text


def hash_string(value):
    assert isinstance(value, str) and re.fullmatch('[0-9a-f]{64}', value)


def validate(members, repo=None):
    read = lambda name: json.loads(members[name])
    result = read('execution/result.json')
    owner = read('execution/owner.json')
    inv = read('execution/inventory.json')
    done = read('execution/completed.json')
    old = read('basis/completed.json')
    old_inv = read('basis/inventory.json')
    old_owner = read('basis/owner.json')
    old_result = read('basis/result.json')
    old_review = read('basis/live-review.json')
    toolchain = read('execution/toolchain.json')
    prior = read('basis/phase1-completed.json')
    phase1 = read('basis/phase1-result.json')
    phase1_rows = {row['module']: row for row in phase1['module_evidence']}
    assert result['status'] == old_result['status'] == 'PASS'
    assert phase1['status'] == 'PASS_INCREMENTAL_KERNEL'
    assert result['primary_project_modules'] == old_result['primary_project_modules'] == 185
    assert result['external_imports'] == old_result['external_imports'] == ['Init']
    assert result['basis_unchanged'] and result['all_private_objects_logs_and_toolchain_rechecked_after_audits']
    for name, key in [('inventory.json', 'inventory_sha256'), ('completed.json', 'completed_sha256')]:
        assert digest(members['execution/' + name]) == result[key]
        assert digest(members['basis/' + name]) == old_result[key]
    for name in ('result', 'completed', 'inventory', 'toolchain'):
        assert digest(members['basis/' + name + '.json']) == owner['basis_' + name + '_sha256']
    assert members['execution/basis-completed.json'] == members['basis/completed.json']
    assert members['execution/basis-inventory.json'] == members['basis/inventory.json']
    assert members['execution/toolchain.json'] == members['basis/toolchain.json']
    assert digest(members['execution/reviewed-driver.py']) == owner['helper_sha256']
    assert digest(members['review/build.py']) == owner['script_sha256']
    for name, key in [('phase1-result.json', 'phase1_result_sha256'),
                      ('phase1-completed.json', 'phase1_completed_sha256'),
                      ('toolchain.json', 'toolchain_boundary_sha256'),
                      ('reviewed-driver.py', 'helper_sha256')]:
        assert digest(members['basis/' + name]) == old_owner[key]
    assert digest(members['basis/build.py']) == old_owner['script_sha256']
    assert old_review['status'] == 'PASS_LIVE_POST_AUDIT_REVIEW'
    assert old_review['result_sha256'] == digest(members['basis/result.json'])
    assert old_review['reviewer_sha256'] == digest(members['basis/review.py'])
    assert old_review['all185_objects_rehashed_after_audits']
    assert old_review['all215_phase1_objects_unchanged']
    assert owner['compiler_sha256'] == old_owner['compiler_sha256'] == phase1['compiler_sha256']
    assert owner['compiler_sha256'] == toolchain['lean']['sha256']
    for key in ('lean', 'lake', 'Init.olean', 'project_toolchain'):
        hash_string(toolchain[key]['sha256'])

    modules = {row['module']: row for row in inv['modules']}
    old_modules = {row['module']: row for row in old_inv['modules']}
    assert len(modules) == len(inv['modules']) == len(done) == len(old) == len(old_modules) == 185
    assert set(done) == set(modules) == set(old) == set(old_modules)
    assert inv['target'] == old_inv['target'] == TARGET
    assert inv['external_imports'] == old_inv['external_imports'] == ['Init']
    basis_objects = read('basis/basis-objects.json')
    assert set(prior) == set(phase1_rows) == set(basis_objects) and len(prior) == 215
    assert all(basis_objects[m] == prior[m]['object_sha256'] == phase1_rows[m]['object_sha256'] for m in prior)

    def check_graph(inventory, rows):
        seen = set()
        for entry in inventory['modules']:
            assert set(entry['imports']) <= seen | {'Init'}, entry['module']
            seen.add(entry['module'])
        reached = set()

        def visit(module):
            if module in reached:
                return
            reached.add(module)
            for dep in rows[module]['imports']:
                if dep in rows:
                    visit(dep)
        visit(inventory['target'])
        assert reached == set(rows)

    check_graph(inv, modules)
    check_graph(old_inv, old_modules)
    run = PurePosixPath(result['audits'][0]['log']).parent.parent
    old_run = PurePosixPath(old_result['audits'][0]['log']).parent.parent
    old_repo = PurePosixPath(owner['repo'])
    assert owner['repo'] == old_owner['repo']
    basis_logs = read('execution/basis-logs.json')
    assert set(basis_logs) == set(old)
    basis_warnings = basis_fresh = 0
    for module, row in old.items():
        entry = old_modules[module]
        assert row['status'] == 'PASS' and row['source_sha256'] == entry['source_sha256']
        assert row['dependencies'] == {d: old[d]['object_sha256'] for d in entry['imports'] if d in old}
        assert digest(members['basis/logs/' + module + '.log']) == row['log_sha256']
        text = log_text(members['basis/logs/' + module + '.log'])
        if row['origin'] == 'phase2_fresh':
            basis_fresh += 1
            assert row['exit_code'] == 0 and not row['timed_out']
            assert row['source_unchanged'] and row['dependencies_unchanged']
            assert row['compiler_sha256'] == old_owner['compiler_sha256']
            assert row['timeout_seconds'] == 900 and row['memory_mebibytes'] == 12288
            root = entry['source'][:-len(module.replace('.', '/') + '.lean')].rstrip('/')
            assert row['command'] == [toolchain['lean']['path'], '-j1', '-M12288', '--root=' + root,
                                      '-o', str(old_run / 'objects' / (module.replace('.', '/') + '.olean')), entry['source']]
            assert basis_logs[module] == row['log']
            assert text.count('warning:') == row['warnings']
        else:
            assert row['origin'] == 'phase1_hash_bound'
            for key in ('source_sha256', 'dependencies', 'object_sha256', 'log_sha256'):
                assert row[key] == prior[module][key] == phase1_rows[module][key]
            assert text.count('warning:') == phase1_rows[module]['warnings']
            if 'log' in prior[module]:
                assert basis_logs[module] == prior[module]['log']
        basis_warnings += text.count('warning:')
    assert basis_fresh == old_result['fresh_modules'] and 185 - basis_fresh == old_result['reused_modules']
    assert basis_warnings == old_review['project_warnings']

    fresh = warnings = 0
    for module, entry in modules.items():
        row = done[module]
        source = members['execution/sources/' + module.replace('.', '/') + '.lean']
        assert row['status'] == 'PASS' and digest(source) == row['source_sha256'] == entry['source_sha256']
        assert imports(source) == entry['imports'], module
        assert row['dependencies'] == {d: done[d]['object_sha256'] for d in entry['imports'] if d in done}
        hash_string(row['object_sha256'])
        expected_sources = [old_repo / root / (module.replace('.', '/') + '.lean') for root in ROOTS]
        assert PurePosixPath(entry['source']) in expected_sources
        if repo is not None:
            choices = [Path(repo) / str(path.relative_to(old_repo)) for path in expected_sources]
            found = [path for path in choices if path.is_file()]
            current = Path(repo) / str(PurePosixPath(entry['source']).relative_to(old_repo))
            assert found == [current] and digest(current.read_bytes()) == entry['source_sha256'], module
        text = log_text(members['execution/logs/' + module + '.log'])
        assert digest(members['execution/logs/' + module + '.log']) == row['log_sha256']
        if row['origin'] == 'phase3_fresh':
            fresh += 1
            relative = PurePosixPath(row['log']).relative_to(run)
            folder = 'execution/' + str(relative.parent)
            assert read(folder + '/record.json') == row
            assert members[folder + '/' + PurePosixPath(entry['source']).name] == source
            assert members['execution/' + str(relative)] == members['execution/logs/' + module + '.log']
            root = entry['source'][:-len(module.replace('.', '/') + '.lean')].rstrip('/')
            assert row['command'] == [toolchain['lean']['path'], '-j1', '-M12288', '--root=' + root,
                                      '-o', str(run / 'objects' / (module.replace('.', '/') + '.olean')), entry['source']]
            assert row['compiler_sha256'] == owner['compiler_sha256']
            assert row['exit_code'] == 0 and not row['timed_out']
            assert row['source_unchanged'] and row['dependencies_unchanged']
            assert row['timeout_seconds'] == 900 and row['memory_mebibytes'] == 12288
            assert row['seconds'] >= 0 and row['lock_wait_seconds'] >= 0
            assert text.count('warning:') == row['warnings']
        else:
            assert row['origin'] == 'phase2_hash_bound'
            for key in ('source_sha256', 'dependencies', 'object_sha256', 'log_sha256'):
                assert row[key] == old[module][key]
            assert row['log'] == basis_logs[module]
            assert members['execution/logs/' + module + '.log'] == members['basis/logs/' + module + '.log']
        warnings += text.count('warning:')
    assert fresh == result['fresh_modules'] and 185 - fresh == result['reused_modules']
    assert warnings == result['project_linter_warnings']
    assert len(result['audits']) == result['typed_audits'] == 2
    basis_audits = {row['module']: row for row in old_result['audits']}
    assert set(basis_audits) == {'EndpointAudit215', 'K215Audit'}
    reports_total = 0
    for row, name, expected in zip(result['audits'], ('EndpointAudit215', 'K215Audit'), (2, 8)):
        assert row['module'] == name and row['expected_reports'] == expected
        assert row['source_sha256'] == basis_audits[name]['source_sha256']
        assert basis_audits[name]['expected_reports'] == expected
        folder = 'execution/' + str(PurePosixPath(row['log']).parent.relative_to(run))
        assert read(folder + '/' + name + '.json') == row
        source = members[folder + '/' + name + '.lean']
        log = members[folder + '/' + name + '.log']
        assert digest(source) == row['source_sha256'] and digest(log) == row['log_sha256']
        assert row['status'] == 'PASS' and row['exit_code'] == 0 and not row['timed_out']
        assert row['dependencies'] == {m: done[m]['object_sha256'] for m in done}
        assert row['project_modules'] == 185
        assert row['compiler_sha256'] == owner['compiler_sha256'] and row['timeout_seconds'] == 120
        assert row['seconds'] >= 0 and row['lock_wait_seconds'] >= 0
        hash_string(row['object_sha256'])
        auditdir = PurePosixPath(row['log']).parent
        assert row['command'] == [toolchain['lean']['path'], '-j1', '-M12288', '--root=' + str(auditdir),
                                  '-o', str(auditdir / (name + '.olean')), str(auditdir / (name + '.lean'))]
        text = log_text(log)
        assert 'warning:' not in text
        reports = re.findall(r'depends on axioms: \[([^]]*)\]', text)
        assert len(reports) + text.count('does not depend on any axioms') == expected
        assert reports == row['reports']
        assert all({item.strip() for item in report.split(',') if item.strip()} <= AXIOMS for report in reports)
        if repo is not None:
            current = Path(repo) / str(PurePosixPath(row['source']).relative_to(old_repo))
            assert sha(current) == row['source_sha256']
        reports_total += expected
    assert reports_total == result['axiom_reports'] == 10
    return {'project_modules': 185, 'fresh_modules': fresh, 'reused_modules': 185 - fresh,
            'typed_clients': 2, 'axiom_reports': 10, 'project_warnings': warnings,
            'audit_warnings': 0, 'basis_fresh_modules': basis_fresh,
            'basis_reused_modules': 185 - basis_fresh,
            'exact_source_imports_and_dependency_sets': True,
            'compiler_sha256': owner['compiler_sha256'],
            'result_sha256': digest(members['execution/result.json']),
            'basis_result_sha256': digest(members['basis/result.json'])}
