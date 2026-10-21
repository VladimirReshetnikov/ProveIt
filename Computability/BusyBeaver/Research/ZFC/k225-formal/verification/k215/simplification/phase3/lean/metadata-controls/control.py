"""Synthetic metadata controls only. No Lean proof or compiler is executed.

Fixtures deliberately use /fixture paths and synthetic object hashes. They test
acceptance/rejection of evidence structure, not mathematical correctness.
"""
from pathlib import Path
import copy
import gzip
import io
import json
import sys
import tarfile
import tempfile
from unittest.mock import patch
from evidence import digest, manifest, manifest_hash, save, validate
import review_saved

HERE = Path(__file__).resolve().parent


def fixture():
    members = {}
    encode = lambda value: (json.dumps(value, indent=2) + '\n').encode()
    put = lambda name, value: members.__setitem__(name, encode(value))
    hashof = lambda value: digest(value.encode())
    repo, run, basis = '/fixture/Proofs', '/fixture/phase3/run', '/fixture/phase2/run'
    compiler = '/fixture/toolchain/lean'
    names = [f'BusyBeaver.Fixture.M{i:03d}' for i in range(184)] + ['BusyBeaver.ZFC.KEndpoint215']
    sources = {m: (('import ' + names[i - 1] + '\n') if i else '') + '-- Synthetic source only.\n'
               for i, m in enumerate(names)}
    sourcepath = lambda m: repo + '/Computability/BusyBeaver/Lean/' + m.replace('.', '/') + '.lean'
    old_inv = {'target': names[-1], 'external_imports': ['Init'], 'modules': [
        {'module': m, 'source': sourcepath(m), 'source_sha256': hashof(sources[m]),
         'imports': [names[i - 1]] if i else []} for i, m in enumerate(names)]}
    toolchain = {key: {'path': '/fixture/toolchain/' + key, 'sha256': hashof(key)}
                 for key in ('lean', 'lake', 'Init.olean', 'project_toolchain')}
    prior = {}
    for i, m in enumerate(names + [f'BusyBeaver.Fixture.Extra{i:03d}' for i in range(30)]):
        prior[m] = {'module': m, 'status': 'PASS', 'source_sha256': hashof(sources.get(m, 'extra')),
                    'object_sha256': hashof('object:' + m), 'log_sha256': hashof(''), 'warnings': 0,
                    'dependencies': {names[i - 1]: hashof('object:' + names[i - 1])} if 0 < i < 185 else {},
                    'log': '/fixture/phase1/' + m + '.log', 'compilation_origin': 'execution.tar.gz/fixture/' + m}
    phase1 = {'status': 'PASS_INCREMENTAL_KERNEL', 'compiler_sha256': hashof('lean'),
              'module_evidence': list(prior.values())}
    old = {m: {key: prior[m][key] for key in ('module', 'status', 'source_sha256', 'object_sha256', 'log_sha256', 'dependencies')}
           for m in names}
    for row in old.values():
        row['origin'] = 'phase1_hash_bound'
    last = names[-1]

    def fresh_row(m, base, source_sha, obj, origin, deps):
        return {'module': m, 'status': 'PASS', 'origin': origin, 'source': sourcepath(m),
                'source_sha256': source_sha, 'object_sha256': obj, 'log_sha256': hashof(''),
                'log': base + '/attempts/001-' + m + '/compiler.log', 'dependencies': deps,
                'compiler_sha256': hashof('lean'), 'exit_code': 0, 'timed_out': False,
                'source_unchanged': True, 'dependencies_unchanged': True,
                'seconds': 1.0, 'lock_wait_seconds': 0.0, 'warnings': 0,
                'timeout_seconds': 900, 'memory_mebibytes': 12288,
                'command': [compiler, '-j1', '-M12288', '--root=' + repo + '/Computability/BusyBeaver/Lean',
                            '-o', base + '/objects/' + m.replace('.', '/') + '.olean', sourcepath(m)]}
    old[last] = fresh_row(last, basis, prior[last]['source_sha256'], prior[last]['object_sha256'],
                          'phase2_fresh', prior[last]['dependencies'])
    basis_logs = {m: old[m].get('log', prior[m]['log']) for m in names}
    put('basis/phase1-result.json', phase1)
    put('basis/phase1-completed.json', prior)
    put('basis/basis-objects.json', {m: row['object_sha256'] for m, row in prior.items()})
    put('basis/inventory.json', old_inv)
    put('basis/completed.json', old)
    put('basis/toolchain.json', toolchain)
    members['basis/reviewed-driver.py'] = b'# Synthetic helper identity.\n'
    members['basis/build.py'] = b'# Synthetic build identity.\n'
    members['basis/review.py'] = b'# Synthetic basis reviewer identity.\n'
    old_owner = {'repo': repo, 'compiler_sha256': hashof('lean'),
                 'script_sha256': digest(members['basis/build.py'])}
    for name, key in [('phase1-result.json', 'phase1_result_sha256'), ('phase1-completed.json', 'phase1_completed_sha256'),
                      ('toolchain.json', 'toolchain_boundary_sha256'), ('reviewed-driver.py', 'helper_sha256')]:
        old_owner[key] = digest(members['basis/' + name])
    put('basis/owner.json', old_owner)
    old_result = {'status': 'PASS', 'primary_project_modules': 185, 'external_imports': ['Init'],
                  'fresh_modules': 1, 'reused_modules': 184,
                  'inventory_sha256': digest(members['basis/inventory.json']),
                  'completed_sha256': digest(members['basis/completed.json']),
                  'audits': [{'log': basis + '/audit-001/EndpointAudit215.log'}]}
    put('basis/result.json', old_result)
    put('basis/live-review.json', {'status': 'PASS_LIVE_POST_AUDIT_REVIEW',
                                  'result_sha256': digest(members['basis/result.json']),
                                  'reviewer_sha256': digest(members['basis/review.py']),
                                  'all185_objects_rehashed_after_audits': True,
                                  'all215_phase1_objects_unchanged': True, 'project_warnings': 0})
    inv = copy.deepcopy(old_inv)
    sources[last] += '-- Synthetic successor.\n'
    inv['modules'][-1]['source_sha256'] = hashof(sources[last])
    done = copy.deepcopy(old)
    for m, row in done.items():
        row['origin'] = 'phase2_hash_bound'
        row['log'] = basis_logs[m]
    done[last] = fresh_row(last, run, hashof(sources[last]), hashof('newobject:' + last),
                           'phase3_fresh', prior[last]['dependencies'])
    put('execution/inventory.json', inv)
    put('execution/completed.json', done)
    put('execution/basis-logs.json', basis_logs)
    for name in ('completed', 'inventory'):
        members['execution/basis-' + name + '.json'] = members['basis/' + name + '.json']
    members['execution/toolchain.json'] = members['basis/toolchain.json']
    members['execution/reviewed-driver.py'] = b'# Synthetic current helper.\n'
    members['review/build.py'] = b'# Synthetic phase3 driver.\n'
    for name in ('evidence.py', 'capture.py', 'review.py', 'review_saved.py', 'publish.py'):
        members['review/' + name] = (HERE / name).read_bytes()
    owner = {'repo': repo, 'compiler_sha256': hashof('lean'),
             'script_sha256': digest(members['review/build.py']),
             'helper_sha256': digest(members['execution/reviewed-driver.py'])}
    for name in ('result', 'completed', 'inventory', 'toolchain'):
        owner['basis_' + name + '_sha256'] = digest(members['basis/' + name + '.json'])
    put('execution/owner.json', owner)
    for m in names:
        members['execution/sources/' + m.replace('.', '/') + '.lean'] = sources[m].encode()
        members['execution/logs/' + m + '.log'] = b''
        members['basis/logs/' + m + '.log'] = b''
    folder = 'execution/attempts/001-' + last
    members[folder + '/compiler.log'] = b''
    members[folder + '/KEndpoint215.lean'] = sources[last].encode()
    put(folder + '/record.json', done[last])
    audits = []
    for name, count in [('EndpointAudit215', 2), ('K215Audit', 8)]:
        folder = 'execution/audit-001/'
        data = b'-- Synthetic typed-client stand-in, not compiled.\n'
        log = ('synthetic depends on axioms: [propext]\n' * count).encode()
        row = {'module': name, 'expected_reports': count, 'source_sha256': digest(data),
               'source': repo + '/audit/' + name + '.lean', 'object_sha256': hashof('audit:' + name),
               'status': 'PASS', 'exit_code': 0, 'timed_out': False, 'project_modules': 185,
               'compiler_sha256': hashof('lean'), 'timeout_seconds': 120, 'seconds': 1, 'lock_wait_seconds': 0,
               'dependencies': {m: d['object_sha256'] for m, d in done.items()},
               'log': run + '/audit-001/' + name + '.log', 'log_sha256': digest(log),
               'reports': ['propext'] * count,
               'command': [compiler, '-j1', '-M12288', '--root=' + run + '/audit-001', '-o',
                           run + '/audit-001/' + name + '.olean', run + '/audit-001/' + name + '.lean']}
        members[folder + name + '.lean'] = data
        members[folder + name + '.log'] = log
        put(folder + name + '.json', row)
        audits.append(row)
    old_result['audits'] = [{'module': row['module'], 'source_sha256': row['source_sha256'],
                             'expected_reports': row['expected_reports'],
                             'log': basis + '/audit-001/' + row['module'] + '.log'} for row in audits]
    put('basis/result.json', old_result)
    basis_review = json.loads(members['basis/live-review.json'])
    basis_review['result_sha256'] = digest(members['basis/result.json'])
    put('basis/live-review.json', basis_review)
    owner['basis_result_sha256'] = digest(members['basis/result.json'])
    put('execution/owner.json', owner)
    put('execution/result.json', {'status': 'PASS', 'primary_project_modules': 185, 'external_imports': ['Init'],
                                  'basis_unchanged': True,
                                  'all_private_objects_logs_and_toolchain_rechecked_after_audits': True,
                                  'inventory_sha256': digest(members['execution/inventory.json']),
                                  'completed_sha256': digest(members['execution/completed.json']),
                                  'fresh_modules': 1, 'reused_modules': 184, 'project_linter_warnings': 0,
                                  'typed_audits': 2, 'axiom_reports': 10, 'audits': audits})
    return members


def main():
    parser = __import__('argparse').ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    args.out.mkdir(exist_ok=False)
    good = fixture()
    result = validate(good)
    checks = [{'control': 'positive synthetic metadata', 'status': 'PASS'}]
    cases = [
        ('source tamper', 'execution/sources/BusyBeaver/Fixture/M000.lean', b'import Init\n'),
        ('selected log tamper', 'execution/logs/BusyBeaver.Fixture.M000.log', b'warning: synthetic\n'),
        ('basis log tamper', 'basis/logs/BusyBeaver.Fixture.M000.log', b'changed'),
        ('fresh compiler log error', 'execution/attempts/001-BusyBeaver.ZFC.KEndpoint215/compiler.log', b'error: synthetic\n'),
        ('audit warning', 'execution/audit-001/EndpointAudit215.log', b'warning: synthetic\n'),
        ('new axiom', 'execution/audit-001/K215Audit.log', b'depends on axioms: [sorryAx]\n'),
        ('driver identity', 'review/build.py', b'changed'),
        ('basis owner identity', 'basis/reviewed-driver.py', b'changed'),
    ]
    for label, name, data in cases:
        altered = dict(good)
        altered[name] = data
        try:
            validate(altered)
        except (AssertionError, KeyError, ValueError):
            checks.append({'control': label, 'status': 'REJECTED_AS_EXPECTED'})
        else:
            raise AssertionError('Accepted negative control: ' + label)
    for label, action in [
        ('wrong direct dependency', lambda x: x['BusyBeaver.Fixture.M001']['dependencies'].clear()),
        ('missing provider', lambda x: x.pop('BusyBeaver.Fixture.M000')),
        ('false inherited origin', lambda x: x['BusyBeaver.Fixture.M000'].update(origin='phase3_fresh')),
    ]:
        altered = dict(good)
        done = json.loads(altered['execution/completed.json'])
        action(done)
        altered['execution/completed.json'] = (json.dumps(done, indent=2) + '\n').encode()
        raw = json.loads(altered['execution/result.json'])
        raw['completed_sha256'] = digest(altered['execution/completed.json'])
        altered['execution/result.json'] = (json.dumps(raw, indent=2) + '\n').encode()
        try:
            validate(altered)
        except (AssertionError, KeyError, ValueError):
            checks.append({'control': label, 'status': 'REJECTED_AS_EXPECTED'})
        else:
            raise AssertionError('Accepted negative control: ' + label)
    changed_client = dict(good)
    name = 'execution/audit-001/EndpointAudit215.lean'
    changed_client[name] += b'-- Changed client, still self-consistently recorded.\n'
    raw = json.loads(changed_client['execution/result.json'])
    raw['audits'][0]['source_sha256'] = digest(changed_client[name])
    changed_client['execution/result.json'] = (json.dumps(raw, indent=2) + '\n').encode()
    changed_client['execution/audit-001/EndpointAudit215.json'] = (json.dumps(raw['audits'][0], indent=2) + '\n').encode()
    try:
        validate(changed_client)
    except AssertionError:
        checks.append({'control': 'typed client differs from immutable basis', 'status': 'REJECTED_AS_EXPECTED'})
    else:
        raise AssertionError('Accepted a changed typed client')
    # The portable saved-reader positive and archive-only rejection controls.
    live = {'status': 'PASS_LIVE_POST_AUDIT_REVIEW', **result,
            'evidence_manifest_sha256': manifest_hash(good),
            'reviewer_sha256': digest(good['review/review.py']),
            'validator_sha256': digest(good['review/evidence.py']),
            'capture_sha256': digest(good['review/capture.py']),
            'all185_objects_rehashed_after_audits': True,
            'all185_basis_objects_and_logs_unchanged': True,
            'current_inventory_exact': True, 'toolchain_and_compiler_rehashed': True}
    good['review/live-review.json'] = (json.dumps(live, indent=2) + '\n').encode()

    def packet(path, entries):
        path.mkdir()
        index = manifest(entries)
        with gzip.open(path / 'execution.tar.gz', 'wb') as raw:
            with tarfile.open(fileobj=raw, mode='w') as archive:
                for name, data in entries.items():
                    info = tarfile.TarInfo(name)
                    info.size = len(data)
                    archive.addfile(info, io.BytesIO(data))
        summary = {**json.loads(entries['execution/result.json']), 'archive_members': len(index),
                   'execution_archive_sha256': digest((path / 'execution.tar.gz').read_bytes()),
                   'live_review_sha256': digest(entries['review/live-review.json']),
                   'project_warnings': 0, 'audit_warnings': 0, 'compiled_objects_in_archive': False}
        for name, value in [('index.json', index), ('result.json', summary)]:
            save(path / name, value)
        for name in ('evidence.py', 'review_saved.py', 'live-review.json'):
            (path / name).write_bytes(entries['review/' + name])
    for label, extra in [('positive saved metadata', None), ('binary archive member', 'synthetic.olean'),
                          ('binary companion archive member', 'synthetic.olean.server'),
                          ('Python bytecode archive member', 'synthetic.pyc'),
                          ('traversal archive member', '../synthetic.log')]:
        entries = dict(good)
        if extra:
            entries[extra] = b'synthetic'
        folder = args.out / label.replace(' ', '-')
        packet(folder, entries)
        try:
            with patch.object(sys, 'argv', ['review_saved.py', '--packet', str(folder),
                                           '--output', str(folder / 'SYNTHETIC-METADATA-ONLY.json')]), patch('sys.stdout', io.StringIO()):
                review_saved.main()
        except (AssertionError, KeyError, ValueError):
            assert extra is not None
            checks.append({'control': label, 'status': 'REJECTED_AS_EXPECTED'})
        else:
            assert extra is None
            checks.append({'control': label, 'status': 'PASS'})
    receipt = {'status': 'PASS_SYNTHETIC_METADATA_CONTROLS', 'checks': checks,
               'proof_execution': False, 'compiler_execution': False,
               'scope': 'Synthetic /fixture paths and object hashes test reviewer structure only. '
                        'No fixture is evidence of a Lean compilation.',
               'source_sha256': digest(Path(__file__).read_bytes()),
               'scripts': {p.name: digest(p.read_bytes()) for p in HERE.glob('*.py')}}
    save(args.out / 'result.json', receipt)
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()
