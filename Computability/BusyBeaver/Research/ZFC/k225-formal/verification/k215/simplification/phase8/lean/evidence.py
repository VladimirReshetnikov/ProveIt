"""Read-only validation shared by the live and saved phase-eight reviewers.

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

NEW_MODULE = 'BusyBeaver.ZFC.DominatedImplication'
REGISTERED_MODULES = {'BusyBeaver.ZFC.'+n for n in ('DominatedImplication','DomRho8','KSeed222','KSeedModel222')}
FORMAL = 'Computability/BusyBeaver/Research/ZFC/k225-formal/'
PRODUCTION_PATHS = {FORMAL+n:kind for n,kind in (
    ('generate_domrho8_lean.py','producer'),('generate_dominated_implication_lean.py','producer'),
    ('dominated_implication_templates/core-prefix.txt','producer_input'),
    ('dominated_implication_templates/core-suffix.txt','producer_input'),
    ('dominated_implication_templates/adapter.txt','producer_input'))}
DRIVER_SHA256 = 'ced6fb8ac5000387273e00932cecf781c1e62d6f6995dd8b8cd587968a2c99e9'
GATES_SHA256 = 'b2dcfb0f69372e25b14ed479382739966bad1488dc05289b3e5fc4ed7bdc1475'
REGISTRATION_SHA256 = '031eba1dcc033110d5913efef92d5b00cbf042008bda71d4deb0e38dc120f7c7'
CONTEXT_SHA256 = '51a940eac6e820e64517f55d01cfeabe041cc733152f57a0f1a0bcef6c9bddf5'
ADOPTION_SHA256 = '3941c1647198a818b8f0d7782e7684a01fd3b432f3ce6de68b1b6110d15dfec8'
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
    """Bind the exact registered sources, producer inputs and isolated provenance."""
    read=lambda name:json.loads(members[name])
    assert digest(members['review/context.json']) == CONTEXT_SHA256
    context=read('review/context.json');names=set()
    for row in context['files']:
        name=row['member'];path=PurePosixPath(name)
        assert name.startswith('context/') and '..' not in path.parts
        assert not binary_name(name) and name not in names
        names.add(name)
        assert digest(members[name])==row['sha256'] and len(members[name])==row['bytes']
    assert names=={n for n in members if n.startswith('context/')}
    registration=read('execution/registered-adoption.json')
    assert digest(members['execution/registered-adoption.json'])==REGISTRATION_SHA256
    assert members['execution/registered-adoption.json']==members['context/driver/registered-adoption.json']
    assert registration['status']=='REGISTERED_FOR_COMBINED_CHECK_NOT_YET_VERIFIED'
    assert registration['basis_result_sha256']==basis_reference.reference()['raw_result_sha256']
    assert registration['primary_project_modules']==188 and registration['basis_project_modules']==187
    assert owner['adoption_sha256']==read('execution/result.json')['adoption_sha256']==REGISTRATION_SHA256
    assert digest(members['context/driver/adoption.json'])==ADOPTION_SHA256
    adopted=read('context/driver/adoption.json')
    assert adopted['status']=='ADOPTED_FOR_COMBINED_CHECK_NOT_YET_VERIFIED'
    assert adopted['registration_sha256']==REGISTRATION_SHA256 and adopted['files']==registration['files']
    old={e['module']:e for e in old_inv['modules']};current={e['module']:e for e in inv['modules']}
    assert len(old)==187 and len(current)==188 and set(current)-set(old)=={NEW_MODULE}
    assert set(old)<set(current)
    lean={};producers={};destinations=set()
    for row in registration['files']:
        dest=row['destination'];path=PurePosixPath(dest)
        assert not path.is_absolute() and '..'not in path.parts and dest not in destinations
        destinations.add(dest)
        data=members['execution/adopted-sources/'+dest]
        assert digest(data)==row['sha256'] and len(data)==row['bytes']
        if row['kind']=='lean':
            module=row['module'];assert module in REGISTERED_MODULES and module not in lean
            assert dest=='Computability/BusyBeaver/Lean/'+module.replace('.','/')+'.lean'
            assert current[module]['source']==str(PurePosixPath(owner['repo'])/dest)
            assert current[module]['source_sha256']==row['sha256']
            assert current[module]['imports']==row['imports']==imports(data)
            assert row['before_sha256']==(old[module]['source_sha256']if module in old else None)
            assert members['execution/sources/'+module.replace('.','/')+'.lean']==data
            lean[module]=row
        else:
            assert dest in PRODUCTION_PATHS and row['kind']==PRODUCTION_PATHS[dest]
            assert 'module'not in row and 'imports'not in row
            producers[dest]=row['sha256']
        if repo is not None:assert sha(Path(repo)/dest)==row['sha256']
    assert set(lean)==REGISTERED_MODULES and set(producers)==set(PRODUCTION_PATHS) and len(destinations)==9
    assert {n for n in members if n.startswith('execution/adopted-sources/')}=={'execution/adopted-sources/'+n for n in destinations}
    for module in old:
        assert old[module]['source']==current[module]['source']
        if module not in REGISTERED_MODULES:assert old[module]==current[module],module
        else:assert old[module]['source_sha256']!=current[module]['source_sha256']
    for module in ('BusyBeaver.ZFC.KSeed222','BusyBeaver.ZFC.KSeedModel222'):
        assert old[module]['imports']==current[module]['imports']
    affected=set(REGISTERED_MODULES)
    while True:
        more=affected|{m for m,e in current.items()if set(e['imports'])&affected}
        if more==affected:break
        affected=more
    scope={'changed_sources':sorted(REGISTERED_MODULES),'added_modules':[NEW_MODULE],
           'unchanged_source_count':184,'potentially_affected_modules':sorted(affected),'producer_pins':producers}
    assert owner['source_change_scope']==read('execution/result.json')['source_change_scope']==scope
    assert owner['producer_pins']==read('execution/result.json')['producer_pins']==producers
    assert owner['script_sha256']==DRIVER_SHA256
    # Peer receipts remain source-only; do not promote them to kernel outcomes.
    for key,name in (('implication_math_producer_peer_sha256','math-peer'),('seed_peer_sha256','seed-peer')):
        assert adopted[key]==digest(members['context/'+name+'/review.json'])
    peer=read('context/driver-peer/review.json')
    assert peer['driver_sha256']==DRIVER_SHA256 and peer['gates_sha256']==GATES_SHA256
    assert peer['registration_sha256']==REGISTRATION_SHA256 and peer['findings']==[]
    # Root's isolated check is separate from the complete endpoint check.
    prefix='context/implication/isolated-run2/'
    isolated=read(prefix+'summary.json')
    assert adopted['isolated_summary_sha256']==digest(members[prefix+'summary.json'])
    assert isolated['status']=='PASS' and isolated['inputs_unchanged'] and isolated['all_187_basis_objects_unchanged']
    assert isolated['warnings']==0 and isolated['reports']==17
    assert isolated['runner_sha256']==digest(members['context/implication/run_isolated.py'])
    qualified='SetTheory.BusyBeaver.ZFC.'
    expected={
        'BusyBeaver.ZFC.DominatedImplication':[qualified+'DominatedImplication.'+n for n in ('rho8_all','composition','lift_right')],
        'BusyBeaver.ZFC.DomRho8':[qualified+'DomRho8.'+n for n in ('rho8_all','composition','lift_right','rho8_all_of_restricted')],
        'BusyBeaver.ZFC.KSeed222':[qualified+'KSeed222.BundleSemantics.bundle_iff_seed',qualified+'KSeed222.bundle_of_seed'],
        'BusyBeaver.ZFC.KSeedModel222':[qualified+'KSeed222.seed_of_bundle',qualified+'KSeed222.seed_eqFree'],
        'DomApi':['DomPointwiseAudit.same_row','DomPointwiseAudit.same_lift'],
        'SeedApi':[qualified+'SeedSharingApi.'+n for n in ('forward','reverse','equalityFreeSeed','namedBundle')]}
    assert [row['module']for row in isolated['rows']]==list(expected)
    for row in isolated['rows']:
        module=row['module'];name=module.rsplit('.',1)[-1]
        assert row==read(prefix+name+'.json')
        source=members[prefix+'workspace/'+module.replace('.','/')+'.lean']
        log=members[prefix+name+'.log'];text=log_text(log)
        assert digest(source)==row['candidate_sha256']==row['source_sha256']
        assert digest(log)==row['log_sha256'] and row['warnings']==0 and 'warning:'not in text
        assert row['status']=='PASS'and row['exit_code']==0 and not row['timed_out']
        assert row['compiler_sha256']==owner['compiler_sha256'] and row['helper_sha256']==owner['helper_sha256']
        assert row['timeout_seconds']==120 and row['memory_mebibytes']==12288
        assert row['seconds']>=0 and row['lock_wait_seconds']>=0
        work=PurePosixPath(row['source']);obj=work.parent
        # Match the precise original isolated workspace/output command.
        isolated_dir=PurePosixPath(row['log']).parent
        target=isolated_dir/'workspace'/(module.replace('.','/')+'.lean')
        assert work==target
        assert row['command']==[read('execution/toolchain.json')['lean']['path'],'-j1','-M12288',
            '--root='+str(isolated_dir/'workspace'),'-o',str(isolated_dir/'objects'/(module.replace('.','/')+'.olean')),str(target)]
        reports=re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)",text)
        assert [n for n,_ in reports]==expected[module] and [list(r)for r in reports]==row['axiom_reports']
        assert all({x.strip()for x in ax.split(',')if x.strip()}<=AXIOMS for _,ax in reports)
        if module in lean:assert digest(source)==lean[module]['sha256']
        else:
            loc='context/implication/DomApi.lean'if module=='DomApi'else'context/seed/SeedApi.lean'
            assert source==members[loc]
    # These producer controls are separately attributed to Drop; they invoke no proof tools.
    math=read('context/math-peer/review.json');controls=read('context/math-peer/controls.json')
    assert digest(members['context/math-peer/controls.json'])==math['controls_sha256']
    assert controls['status']=='ALL_PRODUCER_METADATA_CONTROLS_PASS'and not controls['kernel_or_compiler_invoked']
    assert not controls['candidate_inputs_modified']
    assert math['checks']['positive_producer_controls']==5 and math['checks']['negative_producer_controls']==13
    assert len(controls['controls'])==18
    assert sum(r['status']=='PASS'for r in controls['controls'])==5
    assert sum(r['status']=='EXPECTED_REJECTION'for r in controls['controls'])==13
    assert controls['script_sha256']==math['controls_script_sha256']==digest(members['context/math-peer/check_controls.py'])
    producer=producers[FORMAL+'generate_dominated_implication_lean.py']
    assert controls['producer_sha256']==producer
    generation=read('context/implication/generation.json')
    assert members['context/implication/generation.json']==members['context/implication/generation-check.json']==members['context/driver/canonical-generation-check.json']
    assert generation['generic_sha256']==lean[NEW_MODULE]['sha256']
    assert generation['adapter_sha256']==lean['BusyBeaver.ZFC.DomRho8']['sha256']
    for name,pin in generation['input_raw_sha256'].items():assert digest(members['context/raw-inputs/'+name])==pin
    for name,pin in generation['template_raw_sha256'].items():assert producers[FORMAL+'dominated_implication_templates/'+name]==pin
    return {'adoption_source_pins':9,'unchanged_project_source_pins':184,
        'retained_context_files':len(names),'isolated_named_reports':17,
        'generation_positive_controls':5,'generation_negative_controls':13}


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
    assert set(origins)=={m for m,r in done.items()if r['origin']=='phase7_hash_bound'}
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
    assert result['primary_project_modules'] == 188
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
    assert len(modules) == len(inv['modules']) == len(done) == 188
    assert len(old) == len(old_modules) == len(old_inv['modules']) == 187
    assert set(done) == set(modules)
    assert set(old) == set(old_modules)
    assert set(modules) - set(old_modules) == {NEW_MODULE} and set(old_modules) < set(modules)
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
        if row['origin'] == 'phase8_fresh':
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
            assert row['origin'] == 'phase7_hash_bound'
            for key in ('source_sha256', 'dependencies', 'object_sha256', 'log_sha256'):
                assert row[key] == old[module][key]
            assert row['log'] == basis_logs[module]
            assert members['execution/logs/' + module + '.log'] == members['basis/logs/' + module + '.log']
        warnings += text.count('warning:')
    assert fresh == result['fresh_modules'] and 188 - fresh == result['reused_modules']
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
        assert row['project_modules'] == 188
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
    return {**context_checked, 'project_modules': 188, 'basis_project_modules': 187,
            'added_modules': [NEW_MODULE],
            'fresh_modules': fresh, 'reused_modules': 188 - fresh,
            'typed_clients': 2, 'axiom_reports': 10, 'project_warnings': warnings,
            'audit_warnings': 0, 'basis_fresh_modules': basis_fresh,
            'basis_reused_modules': 187 - basis_fresh,
            'exact_source_imports_and_dependency_sets': True,
            'compiler_sha256': owner['compiler_sha256'],
            'result_sha256': digest(members['execution/result.json']),
            'basis_result_sha256': digest(members['basis/result.json'])}
