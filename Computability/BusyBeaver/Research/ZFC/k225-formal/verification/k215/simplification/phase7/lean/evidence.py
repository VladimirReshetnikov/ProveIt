"""Read-only validation shared by the live and saved phase-seven reviewers.

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


import basis_reference

DOM = 'BusyBeaver.ZFC.DomRho8'
AFFECTED = {'BusyBeaver.ZFC.' + n for n in ('DomRho8', 'EnumPerm', 'KCodeDom',
    'KEndpoint215', 'L2AxiomsPerm', 'L2RootPerm', 'SeedPerm')}
DRIVER_SHA256 = '54fd4bac94adefb4a447690926aa743ac3f71fd94e815996ad7b44a8356ff036'
GATES_SHA256 = '01915961e11abaae7bbe7cdeedfbc90ee294e627612d631c90399d1780f583b8'
SOURCE_SHA256 = '987a8b573a50bc72c0796e9c783595534289eae96dfbe9278107629bcc92bae9'
PRODUCER_SHA256 = 'b5421e8289a29109e80c618db61c05a7fb79c481b5cf97c0deaba5aded46e56d'
CONTEXT_SHA256 = '6a38217c918d6d01740b3a9cfb0fe9a0be2fbf8744c78eed1003fd0de6944bfd'
ADOPTION_SHA256 = 'c49e134152eedb097bdfc7fd259ebbdb5f2c838720b01c56c712bbcd1c9d1dc8'
AUDIT_SOURCES = {
    'EndpointAudit215': 'd13596021774c5b26937b13cf6cca58342af99f59626b9205ff10b9df1e6fc7d',
    'K215Audit': '9144acc6c597c4a53928fc62be00d5e25d9f32f519797d17a5058d03b5460986',
}
REPORT_NAMES = {
    'EndpointAudit215': [
        'EndpointAudit215.blank_halts_exactly_when_zfc_has_a_finite_refutation',
        'EndpointAudit215.nonhalting_exactly_when_zfc_is_consistent'],
    'K215Audit': [
        'SetTheory.BusyBeaver.ZFC.KEndpoint215.blank_halts_iff_zfc_refutation',
        'SetTheory.BusyBeaver.ZFC.KEndpoint215.nonhalting_iff_zfc_consistency',
        'SetTheory.BusyBeaver.ZFC.KDense215.commutes',
        'SetTheory.BusyBeaver.ZFC.KBoot215.boot',
        'SetTheory.BusyBeaver.ZFC.KSites215.covered',
        'SetTheory.BusyBeaver.ZFC.KEndpoint215.p215_boot_iff',
        'K215Audit.blank_halts_exact', 'K215Audit.nonhalting_exact'],
}
MACHINE_PINS = {
    'k215.tm': 'fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090',
    'k215.native.tm': '9683d6ed9628e6ce407c315b08f5da3d063da94e92706f275ca0f33e8272e4b2',
    'sites215.json': '17af207195179b2508bf91154cd00739374f8862207ca21b9a3cb9098aa6f5ba',
}


def named_reports(text, client):
    reports = re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)", text)
    assert [theorem for theorem, _ in reports] == REPORT_NAMES[client]
    assert all({item.strip() for item in ax.split(',') if item.strip()} <= AXIOMS for _, ax in reports)
    return reports


def validate_basis(members, basis_repo):
    return basis_reference.validate(basis_repo, members['review/basis-reference.json'])


def validate_context(members, inv, old_inv, owner, repo):
    """Bind two adopted files, isolated proof/generation history and source peers."""
    read = lambda name: json.loads(members[name])
    assert digest(members['review/context.json']) == CONTEXT_SHA256
    context = read('review/context.json'); names = set()
    for row in context['files']:
        name = row['member']
        assert name.startswith('context/') and '..' not in PurePosixPath(name).parts
        assert not binary_name(name) and name not in names
        names.add(name)
        assert digest(members[name]) == row['sha256'] and len(members[name]) == row['bytes']
    assert names == {n for n in members if n.startswith('context/')}
    assert digest(members['context/adoption.json']) == ADOPTION_SHA256
    adopted = read('context/adoption.json')
    assert adopted['status'] == 'ADOPTED_FOR_COMBINED_CHECK_NOT_YET_VERIFIED'
    assert adopted['primary_module_count'] == 187 and adopted['no_machine_change']
    assert adopted['driver_sha256'] == DRIVER_SHA256 == owner['script_sha256']
    assert len(adopted['files']) == 2
    old = {e['module']:e for e in old_inv['modules']}
    current = {e['module']:e for e in inv['modules']}
    assert current.keys() == old.keys()
    assert {m for m in current if current[m]['source_sha256'] != old[m]['source_sha256']} == {DOM}
    assert all(current[m]['source'] == old[m]['source'] and current[m]['imports'] == old[m]['imports'] for m in current)
    assert [e['module'] for e in inv['modules']] == [e['module'] for e in old_inv['modules']]
    affected={DOM}
    while True:
        more=affected|{m for m,e in current.items() if set(e['imports'])&affected}
        if more==affected:break
        affected=more
    scope={'changed_sources':[DOM],'potentially_affected_modules':sorted(AFFECTED)}
    assert affected == AFFECTED and owner['source_change_scope'] == scope
    assert read('execution/result.json')['source_change_scope'] == scope
    assert current[DOM]['source_sha256'] == SOURCE_SHA256
    prefix='context/pointwise/'
    for row,name,pin in zip(adopted['files'],('DomRho8.lean','generate_domrho8_lean.py'),(SOURCE_SHA256,PRODUCER_SHA256)):
        expected = ('Computability/BusyBeaver/Lean/BusyBeaver/ZFC/' if name.endswith('.lean') else 'Computability/BusyBeaver/Research/ZFC/k225-formal/')+name
        assert row['destination'] == expected and row['sha256'] == pin
        assert digest(members[prefix+name]) == pin and len(members[prefix+name]) == row['bytes']
        assert digest(members[prefix+name+'.before']) == row['before_sha256']
        assert len(members[prefix+name+'.before']) == row['before_bytes']
        if repo is not None:assert sha(Path(repo)/expected) == pin
    assert adopted['files'][0]['before_sha256'] == old[DOM]['source_sha256']
    assert members['execution/sources/BusyBeaver/ZFC/DomRho8.lean'] == members[prefix+'DomRho8.lean']
    assert members['execution/generate_domrho8_lean.py'] == members[prefix+'generate_domrho8_lean.py']
    assert owner['producer_sha256'] == read('execution/result.json')['producer_sha256'] == PRODUCER_SHA256
    assert adopted['pointwise_peer_sha256'] == digest(members['context/math-peer/review.json'])
    assert adopted['driver_peer_sha256'] == digest(members['context/driver-peer/review.json'])
    isolated=read(prefix+'run1/result.json')
    assert isolated['status']=='PASS' and isolated['exit_code']==0 and not isolated['timed_out']
    assert isolated['candidate_sha256']==SOURCE_SHA256 and isolated['warnings']==0
    assert all(isolated[k] for k in ('basis_unchanged','inputs_unchanged','source_unchanged'))
    src=members[prefix+'run1/workspace/BusyBeaver/ZFC/DomRho8.lean']
    assert src==members[prefix+'DomRho8.lean']+members[prefix+'Audit.lean']
    assert digest(src)==isolated['source_sha256']
    assert digest(members[prefix+'Audit.lean'])==isolated['audit_sha256']
    assert digest(members[prefix+'run.py'])==isolated['runner_sha256']
    log=members[prefix+'run1/compiler.log'];assert digest(log)==isolated['log_sha256']
    reports=re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)",log_text(log))
    expected=['SetTheory.BusyBeaver.ZFC.DomRho8.'+n for n in ('rho8_all','composition','lift_right')]+['DomPointwiseAudit.same_row','DomPointwiseAudit.same_lift']
    assert [n for n,_ in reports]==expected and [list(r) for r in reports]==isolated['axiom_reports']
    assert all({x.strip()for x in ax.split(',')if x.strip()} <= AXIOMS for _,ax in reports)
    generation=read(prefix+'generation/result.json')
    assert generation['status']=='PASS_SOURCE_GENERATION_ONLY' and generation['inputs_unchanged']
    assert generation['inputs_before']==generation['inputs_after']
    assert generation['producer_sha256']==PRODUCER_SHA256 and generation['candidate_sha256']==SOURCE_SHA256
    labels=['explicit-lf','explicit-crlf','default-path-lf','reject-template-byte','reject-template-mixed-eol','reject-certificate-byte','reject-conflicting-route']
    assert [r['label']for r in generation['jobs']]==labels
    for index,row in enumerate(generation['jobs']):
        assert digest(members[prefix+'generation/'+row['label']+'.log'])==row['log_sha256']
        assert row['expected_success']==(index<3) and row['output_exists']==(index<3)
        assert (row['exit_code']==0)==(index<3)
        if index<3:assert digest(members[prefix+'generation/'+row['label']+'.lean'])==row['output_sha256']==SOURCE_SHA256
    return {'adoption_source_pins':2,'unchanged_project_source_pins':186,
            'retained_context_files':len(names),'isolated_named_reports':5,
            'generation_positive_controls':3,'generation_negative_controls':4}


def expand_references(members, prior):
    """Resolve small basis ledgers and reused logs in memory, never archive them."""
    expanded=dict(members)
    def put(name,data):
        assert name not in expanded, ('Duplicated predecessor payload',name)
        expanded[name]=data
    for name in ('owner','result','completed','inventory','toolchain','reviewed-driver'):
        suffix='.py'if name=='reviewed-driver'else'.json'
        put('basis/'+name+suffix,prior['execution/'+name+suffix])
    put('basis/live-review.json',prior['review/live-review.json'])
    old=json.loads(expanded['basis/completed.json']);done=json.loads(members['execution/completed.json'])
    origins=json.loads(members['execution/reused-log-origins.json'])
    assert set(origins)=={m for m,r in done.items()if r['origin']=='phase6_hash_bound'}
    for m,row in old.items():
        name='execution/logs/'+m+'.log';data=prior[name]
        put('basis/logs/'+m+'.log',data)
        if m in origins:
            assert origins[m]=={'basis_member':name,'sha256':row['log_sha256']}
            assert digest(data)==row['log_sha256']
            put(name,data)
    return expanded


def validate(members, repo=None, basis_repo=None):
    prior_members, prior_checked, prior_files = validate_basis(members, basis_repo or repo)
    members = expand_references(members, prior_members)
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
    assert result['primary_project_modules'] == 187
    assert result['basis_project_modules'] == old_result['primary_project_modules'] == 187
    assert result['external_imports'] == old_result['external_imports'] == ['Init']
    assert result['basis_unchanged'] and result['all_private_objects_logs_and_toolchain_rechecked_after_audits']
    for name, key in [('inventory.json', 'inventory_sha256'), ('completed.json', 'completed_sha256')]:
        assert digest(members['execution/' + name]) == result[key]
        assert digest(members['basis/' + name]) == old_result[key]
    for name in ('owner', 'result', 'completed', 'inventory', 'toolchain', 'reviewed-driver'):
        suffix = '.py' if name == 'reviewed-driver' else '.json'
        assert members['basis/' + name + suffix] == prior_members['execution/' + name + suffix]
    assert members['basis/live-review.json'] == prior_files['live-review.json']
    for name in ('result', 'completed', 'inventory', 'toolchain'):
        assert digest(members['basis/' + name + '.json']) == owner['basis_' + name + '_sha256']
    assert members['execution/basis-completed.json'] == members['basis/completed.json']
    assert members['execution/basis-inventory.json'] == members['basis/inventory.json']
    assert members['execution/toolchain.json'] == members['basis/toolchain.json']
    assert digest(members['execution/reviewed-driver.py']) == owner['helper_sha256']
    assert digest(members['review/build.py']) == owner['script_sha256'] == DRIVER_SHA256
    assert members['execution/build.py'] == members['review/build.py']
    assert digest(members['execution/gates.py']) == owner['gates_sha256'] == GATES_SHA256
    assert members['execution/basis-reference.json'] == members['review/basis-reference.json']
    assert owner['basis_reference_sha256'] == result['basis_reference_sha256'] == basis_reference.REFERENCE_SHA256
    assert owner['machine_pins'] == result['exact_machine_pins'] == MACHINE_PINS
    assert owner['compiler_sha256'] == old_owner['compiler_sha256'] == toolchain['lean']['sha256']
    for key in ('lean', 'lake', 'Init.olean', 'project_toolchain'):
        hash_string(toolchain[key]['sha256'])
    modules = {row['module']: row for row in inv['modules']}
    old_modules = {row['module']: row for row in old_inv['modules']}
    assert len(modules) == len(inv['modules']) == len(done) == 187
    assert len(old) == len(old_modules) == len(old_inv['modules']) == 187
    assert set(done) == set(modules)
    assert set(old) == set(old_modules)
    assert set(old_modules) == set(modules)
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
        if row['origin'] == 'phase7_fresh':
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
            assert row['origin'] == 'phase6_hash_bound'
            for key in ('source_sha256', 'dependencies', 'object_sha256', 'log_sha256'):
                assert row[key] == old[module][key]
            assert row['log'] == basis_logs[module]
            assert members['execution/logs/' + module + '.log'] == members['basis/logs/' + module + '.log']
        warnings += text.count('warning:')
    assert fresh == result['fresh_modules'] and 187 - fresh == result['reused_modules']
    assert warnings == result['project_linter_warnings']
    assert len(result['audits']) == result['typed_audits'] == 2
    basis_audits = {row['module']: row for row in old_result['audits']}
    assert set(basis_audits) == {'EndpointAudit215', 'K215Audit'}
    reports_total = 0
    for row, name, expected in zip(result['audits'], ('EndpointAudit215', 'K215Audit'), (2, 8)):
        assert row['module'] == name and row['expected_reports'] == expected
        assert row['source_sha256'] == basis_audits[name]['source_sha256'] == AUDIT_SOURCES[name]
        assert basis_audits[name]['expected_reports'] == expected
        folder = 'execution/' + str(PurePosixPath(row['log']).parent.relative_to(run))
        assert read(folder + '/' + name + '.json') == row
        source = members[folder + '/' + name + '.lean']
        log = members[folder + '/' + name + '.log']
        assert digest(source) == row['source_sha256'] and digest(log) == row['log_sha256']
        assert row['status'] == 'PASS' and row['exit_code'] == 0 and not row['timed_out']
        assert row['dependencies'] == {m: done[m]['object_sha256'] for m in done}
        assert row['project_modules'] == 187
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
        assert [list(r) for r in named_reports(text, name)] == row['named_reports']
        assert all({item.strip() for item in report.split(',') if item.strip()} <= AXIOMS for report in reports)
        if repo is not None:
            current = Path(repo) / str(PurePosixPath(row['source']).relative_to(old_repo))
            assert sha(current) == row['source_sha256']
        reports_total += expected
    assert reports_total == result['axiom_reports'] == 10
    if repo is not None:
        for name, pin in MACHINE_PINS.items():
            assert sha(Path(repo) / 'Computability/BusyBeaver/Research/ZFC/candidate-k215' / name) == pin
    return {**context_checked, 'project_modules': 187, 'basis_project_modules': 187,
            'added_modules': [],
            'fresh_modules': fresh, 'reused_modules': 187 - fresh,
            'typed_clients': 2, 'axiom_reports': 10, 'project_warnings': warnings,
            'audit_warnings': 0, 'basis_fresh_modules': basis_fresh,
            'basis_reused_modules': 187 - basis_fresh,
            'exact_source_imports_and_dependency_sets': True,
            'compiler_sha256': owner['compiler_sha256'],
            'result_sha256': digest(members['execution/result.json']),
            'basis_result_sha256': digest(members['basis/result.json'])}
