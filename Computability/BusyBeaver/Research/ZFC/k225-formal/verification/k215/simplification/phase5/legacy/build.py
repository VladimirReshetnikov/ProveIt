"""Refresh retained legacy interfaces against a completed phase-five closure.

The union is discovered from imports, not fixed by a module-count assumption.
Primary providers are immutable symlinks; only the extra modules are compiled.
The completed basis and its independent live review are mandatory.
"""
from pathlib import Path
import argparse
import hashlib
import importlib.util
import json
import os
import re
import shutil
import signal

REPO = Path('/home/codex/.codex/worktrees/ec20/Proofs')
FORMAL = REPO / 'Computability/BusyBeaver/Research/ZFC/k225-formal'
HELPER = FORMAL / 'verification/k215/lean/build.py'
HELPER_SHA = 'a3cf7cc38004bca5e2a2df10c607fe5353896c0454069b4ff24d6b5176c32fbd'
PHASE1 = FORMAL / 'verification/k215/simplification/lean/result.json'
LOCK = Path('/tmp/proveit-k215-proof-build.lock')
NAMES = ('Enum222', 'L2Axioms222', 'L2Root222', 'Seed222', 'Dag219Equiv',
         'L2Lib219', 'L2Macros219', 'L2Control219', 'L2Axioms219', 'L2Root219',
         'L2Dom', 'EnumDom', 'L2AxiomsDom', 'L2RootDom', 'RMOffsetBisim')
TARGETS = {'BusyBeaver.ZFC.' + name for name in NAMES}
AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def read(path):
    return json.loads(Path(path).read_text())


def save(path, value):
    Path(path).write_text(json.dumps(value, indent=2) + '\n')


def union_inventory(driver):
    primary = driver.inventory(REPO)
    assert primary['external_imports'] == ['Init']
    rows = {row['module']: row for row in primary['modules']}
    order = list(rows)
    target = driver.TARGET
    try:
        for name in NAMES:
            driver.TARGET = 'BusyBeaver.ZFC.' + name
            extra = driver.inventory(REPO)
            assert extra['external_imports'] == ['Init']
            for row in extra['modules']:
                module = row['module']
                if module in rows:
                    assert rows[module] == row
                else:
                    rows[module] = row
                    order.append(module)
    finally:
        driver.TARGET = target
    seen = set()
    for module in order:
        assert set(rows[module]['imports']) <= seen | {'Init'}
        seen.add(module)
    return primary, {'modules': [rows[m] for m in order], 'external_imports': ['Init'],
                     'primary_target': target, 'legacy_targets': sorted(TARGETS)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--basis', type=Path, required=True)
    parser.add_argument('--basis-review', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    basis, out = args.basis.resolve(), args.out.resolve()
    assert not out.exists(), 'Use a new output directory; failed attempts are retained'
    assert sha(HELPER) == HELPER_SHA
    spec = importlib.util.spec_from_file_location('reviewed_lean_driver', HELPER)
    driver = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(driver)
    primary, inventory = union_inventory(driver)
    assert read(Path(__file__).with_name('prepared-inventory.json')) == {'primary': primary, 'union': inventory}
    extras = {r['module'] for r in inventory['modules']} - {r['module'] for r in primary['modules']}
    baseline, old = read(basis / 'result.json'), read(basis / 'completed.json')
    live_review = read(args.basis_review) if args.basis_review else None
    assert baseline['status'] == 'PASS' and baseline['primary_project_modules'] == len(primary['modules'])
    assert baseline['all_private_objects_logs_and_toolchain_rechecked_after_audits']
    assert baseline['basis_unchanged'] and baseline['typed_audits'] == 2 and baseline['axiom_reports'] == 10
    if live_review is not None:
        assert live_review['status'] == 'PASS_LIVE_POST_AUDIT_REVIEW'
        assert live_review['result_sha256'] == sha(basis / 'result.json')
        assert live_review[f'all{len(primary["modules"])}_objects_rehashed_after_audits']
    assert read(basis / 'inventory.json') == primary
    assert sha(basis / 'inventory.json') == baseline['inventory_sha256']
    assert sha(basis / 'completed.json') == baseline['completed_sha256']
    assert set(old) == {row['module'] for row in primary['modules']}
    phase1 = read(PHASE1)
    assert phase1['status'] == 'PASS_INCREMENTAL_KERNEL'
    prior = {row['module']: row for row in phase1['module_evidence']}
    assert TARGETS - {'BusyBeaver.ZFC.RMOffsetBisim'} <= set(prior)
    toolchain = read(basis / 'toolchain.json')
    compiler = Path(toolchain['lean']['path'])
    assert phase1['compiler_sha256'] == toolchain['lean']['sha256']
    inputs = {str(path): sha(path) for path in
              [Path(__file__), Path(__file__).with_name('prepared-inventory.json'), HELPER, PHASE1,
               Path(__file__).with_name('LegacyAudit.lean'),
               *[basis / name for name in ('result.json', 'completed.json', 'inventory.json', 'toolchain.json')]]}
    if args.basis_review:
        inputs[str(args.basis_review)] = sha(args.basis_review)
    for row in inventory['modules']:
        inputs[row['source']] = row['source_sha256']
    for key in ('lean', 'lake', 'Init.olean', 'project_toolchain'):
        entry = toolchain[key]
        assert sha(entry['path']) == entry['sha256']
        inputs[entry['path']] = entry['sha256']
    for row in primary['modules']:
        module, record = row['module'], old[row['module']]
        assert record['status'] == 'PASS' and record['source_sha256'] == row['source_sha256']
        assert record['dependencies'] == {dep: old[dep]['object_sha256'] for dep in row['imports'] if dep in old}
        obj = basis / 'objects' / (module.replace('.', '/') + '.olean')
        assert sha(obj) == record['object_sha256'] and sha(record['log']) == record['log_sha256']
        inputs[str(obj)] = record['object_sha256']
        inputs[record['log']] = record['log_sha256']

    out.mkdir(parents=True)
    save(out / 'before.json', inputs)
    save(out / 'inventory.json', inventory)
    save(out / 'basis-completed.json', old)
    save(out / 'basis-result.json', baseline)
    if live_review is not None:
        save(out / 'basis-review.json', live_review)
    save(out / 'phase1-extra-origins.json', {m: prior[m] for m in sorted(extras & set(prior))})
    save(out / 'toolchain.json', toolchain)
    shutil.copyfile(HELPER, out / 'supervisor.py')
    cache = out / 'objects'
    done = {}
    for module, record in old.items():
        obj = cache / (module.replace('.', '/') + '.olean')
        obj.parent.mkdir(parents=True, exist_ok=True)
        obj.symlink_to(basis / 'objects' / (module.replace('.', '/') + '.olean'))
        done[module] = {**record, 'origin': 'phase5_primary_hash_bound'}
    save(out / 'completed.json', done)
    env = os.environ.copy()
    env['LEAN_PATH'], env['LEAN_NUM_THREADS'] = str(cache), '1'
    attempts = out / 'attempts'
    attempts.mkdir()
    for entry in inventory['modules']:
        module = entry['module']
        if module not in extras:
            continue
        source = Path(entry['source'])
        assert sha(source) == entry['source_sha256']
        deps = {dep: done[dep]['object_sha256'] for dep in entry['imports'] if dep in done}
        for dep, value in deps.items():
            assert sha(cache / (dep.replace('.', '/') + '.olean')) == value
        attempt = attempts / f'{1 + len(list(attempts.iterdir())):02d}-{module}'
        attempt.mkdir()
        shutil.copyfile(source, attempt / source.name)
        obj = cache / (module.replace('.', '/') + '.olean')
        obj.parent.mkdir(parents=True, exist_ok=True)
        # Never let the compiler write through a provider symlink.
        assert not obj.exists() and not obj.is_symlink()
        obj.unlink(missing_ok=True)
        root = str(source)[:-len(module.replace('.', '/') + '.lean')].rstrip('/')
        command = [str(compiler), '-j1', '-M12288', '--root=' + root, '-o', str(obj), str(source)]
        record = {'module': module, 'source': str(source), 'source_sha256': sha(source),
                  'dependencies': deps, 'command': command, 'compiler_sha256': sha(compiler),
                  'timeout_seconds': 120, 'memory_mebibytes': 12288,
                  'log': str(attempt / 'compiler.log'), 'origin': 'legacy_fresh'}
        print('CHECK', module, flush=True)
        ok = driver.run_locked(command, REPO, env, LOCK, Path(record['log']), 120,
                               record, attempt / 'record.json')
        text = Path(record['log']).read_text()
        record['source_unchanged'] = sha(source) == record['source_sha256']
        record['dependencies_unchanged'] = all(
            sha(cache / (dep.replace('.', '/') + '.olean')) == value for dep, value in deps.items())
        record['warnings'] = text.count('warning:')
        ok = ok and record['source_unchanged'] and record['dependencies_unchanged']
        ok = ok and 'sorryAx' not in text and "declaration uses 'sorry'" not in text and 'error:' not in text
        record['status'] = 'PASS' if ok else 'FAIL'
        if ok:
            record['object_sha256'] = sha(obj)
        save(attempt / 'record.json', record)
        print(record['status'], module, round(record['seconds'], 3), flush=True)
        if not ok:
            print(text[-10000:], flush=True)
            raise SystemExit(1)
        done[module] = record
        save(out / 'completed.json', done)

    def postcheck():
        assert union_inventory(driver) == (primary, inventory)
        assert all(sha(path) == value for path, value in inputs.items())
        assert set(done) == {row['module'] for row in inventory['modules']}
        expected = {m.replace('.', '/') + '.olean' for m in done}
        assert all(not p.is_symlink() or p.is_file() for p in cache.rglob('*'))
        for module in done:
            obj = cache / (module.replace('.', '/') + '.olean')
            if module in extras:
                assert not obj.is_symlink()
            else:
                provider = basis / 'objects' / (module.replace('.', '/') + '.olean')
                assert obj.is_symlink() and obj.resolve(strict=True) == provider.resolve(strict=True)
        assert {p.relative_to(cache).as_posix() for p in cache.rglob('*') if p.is_file()} == expected
        for entry in inventory['modules']:
            module, record = entry['module'], done[entry['module']]
            assert record['status'] == 'PASS' and record['source_sha256'] == sha(entry['source'])
            assert record['object_sha256'] == sha(cache / (module.replace('.', '/') + '.olean'))
            assert record['log_sha256'] == sha(record['log'])
            assert record['dependencies'] == {dep: done[dep]['object_sha256'] for dep in entry['imports'] if dep in done}

    postcheck()
    auditdir = out / 'audit'
    auditdir.mkdir()
    source = auditdir / 'LegacyAudit.lean'
    shutil.copyfile(Path(__file__).with_name(source.name), source)
    obj = auditdir / 'LegacyAudit.olean'
    command = [str(compiler), '-j1', '-M12288', '--root=' + str(auditdir), '-o', str(obj), str(source)]
    audit = {'module': 'LegacyAudit', 'source_sha256': sha(source), 'command': command,
             'dependencies': {m: row['object_sha256'] for m, row in done.items()},
             'compiler_sha256': sha(compiler), 'timeout_seconds': 120, 'memory_mebibytes': 12288,
             'log': str(auditdir / 'compiler.log'), 'expected_axiom_reports': 5}
    ok = driver.run_locked(command, REPO, env, LOCK, Path(audit['log']), 120, audit, auditdir / 'record.json')
    text = Path(audit['log']).read_text()
    reports = re.findall(r'depends on axioms: \[([^]]*)\]', text)
    audit['reports'], audit['warnings'] = reports, text.count('warning:')
    ok = ok and not audit['warnings'] and 'error:' not in text and 'sorryAx' not in text
    ok = ok and len(reports) + text.count('does not depend on any axioms') == 5
    ok = ok and all({x.strip() for x in report.split(',') if x.strip()} <= AXIOMS for report in reports)
    ok = ok and sha(source) == audit['source_sha256']
    audit['status'] = 'PASS' if ok else 'FAIL'
    if ok:
        audit['object_sha256'] = sha(obj)
    save(auditdir / 'record.json', audit)
    postcheck()
    result = {'status': 'PASS' if ok else 'FAIL', 'project_modules': len(inventory['modules']),
              'reused_primary_modules': len(primary['modules']), 'fresh_legacy_modules': len(extras),
              'external_imports': ['Init'], 'audit': audit,
              'basis_unchanged': True, 'all_inputs_objects_logs_rechecked_after_audit': True,
              'inventory_sha256': sha(out / 'inventory.json'),
              'completed_sha256': sha(out / 'completed.json'),
              'scope': 'Dynamically discovered legacy modules freshly compiled against the completed phase5 primary; '
                       'Five typed clients: four root iter_iff interfaces plus the retained arbitrary-program offset checker. Primary objects reused by exact read-only symlinks; '
                       'no fresh full-union claim.'}
    save(out / 'result.json', result)
    print('TERMINAL', result['status'], flush=True)
    if not ok:
        print(text, flush=True)
        raise SystemExit(1)


if __name__ == '__main__':
    signal.signal(signal.SIGTERM, lambda *_: (_ for _ in ()).throw(KeyboardInterrupt('SIGTERM')))
    main()
