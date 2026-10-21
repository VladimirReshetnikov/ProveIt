"""Read-only validation shared by the live and saved phase-five reviewers.

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


import io
import tarfile
import phase4_evidence

PHASE4_VALIDATOR_SHA256 = 'b4ab585495b0cd412bc4f57b76052c83b5ff64074b028da8cab0fb4bfa33fdfc'


def read_archive(data, index):
    members = {}
    with tarfile.open(fileobj=io.BytesIO(data), mode='r:gz') as stream:
        for entry in stream:
            path = PurePosixPath(entry.name)
            assert entry.isfile() and not path.is_absolute() and '..' not in path.parts
            assert not binary_name(path) and entry.name not in members
            value = stream.extractfile(entry).read()
            assert index[entry.name] == {'sha256': digest(value), 'bytes': len(value)}
            members[entry.name] = value
    assert set(members) == set(index)
    return members


def validate_basis(members):
    # This is a trusted sibling validator, never code loaded from the archive.
    assert sha(Path(__file__).with_name('phase4_evidence.py')) == PHASE4_VALIDATOR_SHA256
    assert digest(members['review/phase4_evidence.py']) == PHASE4_VALIDATOR_SHA256
    # The predecessor validator imports its own exact, pinned phase3 sibling.
    assert sha(Path(__file__).with_name('phase3_evidence.py')) == phase4_evidence.PHASE3_VALIDATOR_SHA256
    assert digest(members['review/phase3_evidence.py']) == phase4_evidence.PHASE3_VALIDATOR_SHA256
    read = lambda name: json.loads(members['basis-checkpoint/' + name])
    summary, index = read('result.json'), read('index.json')
    archive = members['basis-checkpoint/execution.tar.gz']
    assert digest(archive) == summary['execution_archive_sha256']
    prior = read_archive(archive, index)
    assert len(prior) == summary['archive_members']
    raw = json.loads(prior['execution/result.json'])
    assert all(summary[key] == value for key, value in raw.items())
    live_bytes = prior.pop('review/live-review.json')
    live = json.loads(live_bytes)
    assert live_bytes == members['basis-checkpoint/live-review.json']
    assert digest(live_bytes) == summary['live_review_sha256']
    assert live['status'] == 'PASS_LIVE_POST_AUDIT_REVIEW'
    for name, key in [('review.py', 'reviewer_sha256'), ('evidence.py', 'validator_sha256'),
                      ('capture.py', 'capture_sha256')]:
        assert digest(prior['review/' + name]) == live[key]
    assert digest(prior['review/evidence.py']) == PHASE4_VALIDATOR_SHA256
    assert manifest_hash(prior) == live['evidence_manifest_sha256']
    assert live['all185_objects_rehashed_after_audits']
    assert live['all185_basis_objects_and_logs_unchanged']
    assert live['current_inventory_exact'] and live['toolchain_and_compiler_rehashed']
    checked = phase4_evidence.validate(prior)
    assert all(live[key] == value for key, value in checked.items())
    assert summary['compiled_objects_in_archive'] is False
    assert summary['audit_warnings'] == 0
    assert summary['project_warnings'] == checked['project_warnings']
    return prior, checked


def validate_context(members, inv, old_inv, owner, repo):
    """Bind adoption/generation receipts without promoting their historical claims."""
    read = lambda name: json.loads(members[name])
    context = read('review/context.json')
    names = set()
    for row in context['files']:
        name = row['member']
        assert name.startswith('adoption/') and '..' not in PurePosixPath(name).parts
        assert not binary_name(name) and name not in names
        names.add(name)
        assert digest(members[name]) == row['sha256'] and len(members[name]) == row['bytes']
    assert names == {name for name in members if name.startswith('adoption/')}
    adopted = read('adoption/adoption.json')
    assert adopted['status'] == 'ADOPTED_PENDING_COMBINED_CHECK'  # Preserve the original chronology.
    assert adopted['primary_modules_expected'] == 184 and adopted['basis_modules'] == 185
    assert adopted['removed_primary_dependency'] == 'BusyBeaver.ZFC.RMOffsetBisim'
    assert adopted['ordinary_certificate_entries'] == 2240
    assert len(adopted['sources']) == 25
    root = PurePosixPath(owner['repo'])
    by_path = {str(PurePosixPath(e['source']).relative_to(root)): e for e in inv['modules']}
    old_by_path = {str(PurePosixPath(e['source']).relative_to(root)): e for e in old_inv['modules']}
    destinations = set()
    for row in adopted['sources']:
        path = row['destination']
        assert path not in destinations and not PurePosixPath(path).is_absolute() and '..' not in PurePosixPath(path).parts
        destinations.add(path)
        if path.endswith('.lean'):
            entry = by_path[path]
            data = members['execution/sources/' + entry['module'].replace('.', '/') + '.lean']
            assert row['before_sha256'] == old_by_path[path]['source_sha256']
            assert row['after_sha256'] == entry['source_sha256'] == digest(data)
        else:
            assert PurePosixPath(path).name in {'generate_source215_lean.py', 'partition_source215_lean.py', 'prepare_k215.py'}
            assert path == 'Computability/BusyBeaver/Research/ZFC/k225-formal/' + PurePosixPath(path).name
            data = members['adoption/producers/' + PurePosixPath(path).name]
            assert row['after_sha256'] == digest(data)
        if repo is not None:
            assert sha(Path(repo) / path) == row['after_sha256']
    regeneration = read('adoption/generation/result.json')
    assert regeneration['status'] == 'PASS_EXACT_ORDINARY_SOURCE_REGENERATION'
    assert regeneration['all_inputs_unchanged'] and regeneration['prepare_executable_ast_unchanged']
    expected = {'KSource215.lean', 'KSource215Data.lean'} | {f'KSource215FwdCheck{i:02d}.lean' for i in range(16)}
    assert set(regeneration['files']) == expected and regeneration['generated_modules'] == 18
    for name, expected_hash in regeneration['files'].items():
        assert digest(members['execution/sources/BusyBeaver/ZFC/' + name]) == expected_hash
    for path, expected_hash in regeneration['inputs'].items():
        relative = PurePosixPath(path).relative_to(root)
        if relative.name.endswith('.py'):
            assert digest(members['adoption/producers/' + relative.name]) == expected_hash
        if repo is not None:
            assert sha(Path(repo) / str(relative)) == expected_hash
    # The storage report concerns other scratch caches; retain, do not rerun it.
    storage = read('adoption/storage-deduplication.json')
    assert storage['status'] == 'PASS_EXACT_BYTE_SCRATCH_CACHE_DEDUPLICATION'
    assert storage['all_paths_types_sizes_hashes_preserved'] and storage['immutable_primary_and_predecessor_caches_untouched']
    return {'adoption_source_pins': 25, 'regenerated_modules_bound': 18,
            'retained_context_files': len(names), 'storage_receipt_retained_without_reexecution': True}


def validate(members, repo=None):
    prior_members, prior_checked = validate_basis(members)
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
    assert result['status'] == old_result['status'] == 'PASS'
    assert result['primary_project_modules'] == 184
    assert result['basis_project_modules'] == old_result['primary_project_modules'] == 185
    assert result['external_imports'] == old_result['external_imports'] == ['Init']
    assert result['basis_unchanged'] and result['all_private_objects_logs_and_toolchain_rechecked_after_audits']
    for name, key in [('inventory.json', 'inventory_sha256'), ('completed.json', 'completed_sha256')]:
        assert digest(members['execution/' + name]) == result[key]
        assert digest(members['basis/' + name]) == old_result[key]
    for name in ('owner', 'result', 'completed', 'inventory', 'toolchain', 'reviewed-driver'):
        suffix = '.py' if name == 'reviewed-driver' else '.json'
        assert members['basis/' + name + suffix] == prior_members['execution/' + name + suffix]
    assert members['basis/build.py'] == prior_members['review/build.py']
    assert members['basis/review.py'] == prior_members['review/review.py']
    assert members['basis/live-review.json'] == members['basis-checkpoint/live-review.json']
    for name in ('result', 'completed', 'inventory', 'toolchain'):
        assert digest(members['basis/' + name + '.json']) == owner['basis_' + name + '_sha256']
    assert members['execution/basis-completed.json'] == members['basis/completed.json']
    assert members['execution/basis-inventory.json'] == members['basis/inventory.json']
    assert members['execution/toolchain.json'] == members['basis/toolchain.json']
    assert digest(members['execution/reviewed-driver.py']) == owner['helper_sha256']
    assert digest(members['review/build.py']) == owner['script_sha256']
    assert owner['compiler_sha256'] == old_owner['compiler_sha256'] == toolchain['lean']['sha256']
    for key in ('lean', 'lake', 'Init.olean', 'project_toolchain'):
        hash_string(toolchain[key]['sha256'])
    modules = {row['module']: row for row in inv['modules']}
    old_modules = {row['module']: row for row in old_inv['modules']}
    assert len(modules) == len(inv['modules']) == len(done) == 184
    assert len(old) == len(old_modules) == len(old_inv['modules']) == 185
    assert set(done) == set(modules)
    assert set(old) == set(old_modules)
    assert set(modules) <= set(old_modules)
    assert set(old_modules) - set(modules) == {'BusyBeaver.ZFC.RMOffsetBisim'}
    assert inv['target'] == old_inv['target'] == TARGET
    assert inv['external_imports'] == old_inv['external_imports'] == ['Init']
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
    context_checked = validate_context(members, inv, old_inv, owner, repo)
    run = PurePosixPath(result['audits'][0]['log']).parent.parent
    old_run = PurePosixPath(old_result['audits'][0]['log']).parent.parent
    old_repo = PurePosixPath(owner['repo'])
    assert owner['repo'] == old_owner['repo']
    basis_logs = read('execution/basis-logs.json')
    assert set(basis_logs) == set(old)
    for module, row in old.items():
        assert members['basis/logs/' + module + '.log'] == prior_members['execution/logs/' + module + '.log']
        assert basis_logs[module] == row['log']
    basis_fresh = prior_checked['fresh_modules']
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
        if row['origin'] == 'phase5_fresh':
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
            assert row['origin'] == 'phase4_hash_bound'
            for key in ('source_sha256', 'dependencies', 'object_sha256', 'log_sha256'):
                assert row[key] == old[module][key]
            assert row['log'] == basis_logs[module]
            assert members['execution/logs/' + module + '.log'] == members['basis/logs/' + module + '.log']
        warnings += text.count('warning:')
    assert fresh == result['fresh_modules'] and 184 - fresh == result['reused_modules']
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
        assert row['project_modules'] == 184
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
    return {**context_checked, 'project_modules': 184, 'basis_project_modules': 185,
            'removed_module': 'BusyBeaver.ZFC.RMOffsetBisim',
            'fresh_modules': fresh, 'reused_modules': 184 - fresh,
            'typed_clients': 2, 'axiom_reports': 10, 'project_warnings': warnings,
            'audit_warnings': 0, 'basis_fresh_modules': basis_fresh,
            'basis_reused_modules': 185 - basis_fresh,
            'exact_source_imports_and_dependency_sets': True,
            'compiler_sha256': owner['compiler_sha256'],
            'result_sha256': digest(members['execution/result.json']),
            'basis_result_sha256': digest(members['basis/result.json'])}
