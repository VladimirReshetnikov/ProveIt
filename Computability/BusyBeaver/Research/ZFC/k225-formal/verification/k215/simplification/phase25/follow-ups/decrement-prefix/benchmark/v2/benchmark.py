#!/usr/bin/env python3
"""UNEXECUTED owned two-arm/three-block diagnostic; no production acceptance."""
import argparse, fcntl, hashlib, importlib.util, json, os, re, shutil, signal, sys
from pathlib import Path

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
PLAN_SHA = 'a9b1431126c25f9e031db0c09f7236053a03f1eb3d34b08976215560a4132310'
STD = {'propext', 'Classical.choice', 'Quot.sound'}
PATTERN = r"'([^\r\n]+?)'\s+(?:depends on axioms:\s*\[([^]]*)\]|does not depend on any axioms)"
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
read = lambda p: json.loads(Path(p).read_text())

def save(path, value):
    temp = path.with_suffix(path.suffix + '.tmp')
    temp.write_text(json.dumps(value, indent=2) + '\n')
    os.replace(temp, path)

def profiles(text):
    found = [[name, sorted({x.strip() for x in axioms.split(',') if x.strip()})]
             for name, axioms in re.findall(PATTERN, text)]
    assert len(found) == text.count('depends on axioms:') + text.count('does not depend on any axioms')
    assert all(set(ax) <= STD for _, ax in found)
    return found

def norm(reports):
    return [[name, sorted({x.strip() for x in (ax.split(',') if isinstance(ax, str) else ax) if x.strip()})]
            for name, ax in reports]

def terminate(*_):
    raise KeyboardInterrupt('SIGTERM')

def main():
    signal.signal(signal.SIGTERM, terminate)
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    plan_path, freeze_path = HERE / 'plan.json', HERE / 'freeze.json'
    assert sha(plan_path) == PLAN_SHA
    plan, freeze = read(plan_path), read(freeze_path)
    assert freeze['files'][str(Path(__file__).resolve())] == sha(__file__)
    inputs = {**plan['inputs'], str(plan_path): PLAN_SHA, str(freeze_path): sha(freeze_path),
              str(Path(__file__).resolve()): sha(__file__)}
    for path, pin in freeze['files'].items():
        assert sha(path) == pin
        inputs[path] = pin
    def check_inputs():
        for path, pin in inputs.items():
            assert sha(path) == pin, path
    check_inputs()
    assert plan['limits'] == {'ordinary_seconds': 120, 'benchmark_seconds': 900, 'memory_mebibytes': 12288, 'workers': 1}
    assert plan['global_lock'] == '/tmp/proveit-k215-proof-build.lock'
    spec = importlib.util.spec_from_file_location('owned_p24_supervisor', plan['supervisor'])
    supervisor = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(supervisor)
    basis = Path(plan['basis']['directory'])
    result, inventory, old = read(basis / 'result.json'), read(basis / 'inventory.json'), read(basis / 'completed.json')
    assert result['status'] == 'PASS' and sha(basis / 'result.json') == plan['basis']['result_sha256']
    assert sha(basis / 'inventory.json') == result['inventory_sha256'] and sha(basis / 'completed.json') == result['completed_sha256']
    assert len(old) == len(inventory['modules']) == 230
    accepted = {r['module']: r for r in inventory['modules']}
    rows = {r['module']: r for r in plan['modules']}
    fresh, reuse = set(plan['fresh_modules']), set(plan['reused_modules'])
    assert fresh == {'BusyBeaver.ZFC.KSim', 'BusyBeaver.ZFC.KFastSites215'}
    assert len(rows) == 19 and len(reuse) == 17 and reuse == set(rows) - fresh
    seen, order = set(), []
    def visit(module):
        if module == 'Init' or module in seen:
            return
        assert module in rows
        seen.add(module)
        for dep in rows[module]['imports']:
            visit(dep)
        order.append(module)
    for module in plan['benchmark_imports']:
        visit(module)
    assert order == plan['exact_dependency_order'] == [r['module'] for r in plan['modules']]
    raw_absent, source_pins = [], {}
    for module, row in rows.items():
        assert row['source_sha256'] == accepted[module]['source_sha256'] == old[module]['source_sha256'] == sha(row['source'])
        assert row['imports'] == accepted[module]['imports']
        if module not in reuse:
            continue
        assert set(row['imports']) - {'Init'} <= reuse
        record = old[module]
        assert record['status'] == 'PASS' and record.get('exit_code', 0) == 0 and not record.get('timed_out', False)
        assert record['dependencies'] == {d: old[d]['object_sha256'] for d in row['imports'] if d != 'Init'}
        log = Path(record['log']).read_text()
        assert sha(record['log']) == record['log_sha256'] and 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log
        assert profiles(log) == row['expected_reports']
        if 'reports' in record:
            assert norm(record['reports']) == profiles(log)
        raw = Path(record['log']).with_name('record.json')
        if raw.is_file():
            original = read(raw)
            for key in ['module', 'source_sha256', 'dependencies', 'log_sha256', 'status']:
                assert original[key] == record[key]
            assert original['exit_code'] == 0 and not original['timed_out']
            for key in ['command', 'exit_code', 'timed_out', 'object_sha256']:
                if key in original and key in record:
                    assert original[key] == record[key]
            assert original['command'][:3] == [plan['compiler']['path'], '-j1', '-M12288']
            if 'reports' in original:
                assert norm(original['reports']) == profiles(log)
        else:
            assert not raw.exists() and not raw.is_symlink()
            raw_absent.append(module)
    assert raw_absent == plan['missing_adjacent_basis_raw_records']
    out = args.out.resolve()
    assert not out.exists() and not out.is_symlink(), 'Use a NEW output; no resuming benchmark objects.'
    out.mkdir(parents=True)
    with (out / 'output.lock').open('a') as owner_lock:
        fcntl.flock(owner_lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        save(out / 'before.json', {'inputs': inputs, 'plan_sha256': PLAN_SHA, 'missing_basis_raw_records': raw_absent})
        arms, attempts = {}, []
        def cache_check():
            for arm in arms.values():
                cache = arm['objects']
                assert {str(p) for p in cache.rglob('*') if p.is_file()} == set(arm['object_pins'])
                for path, pin in arm['object_pins'].items():
                    assert not Path(path).is_symlink() and sha(path) == pin
            for path, pin in source_pins.items():
                assert sha(path) == pin
        def imports(path):
            text = supervisor.without_comments_strings(Path(path).read_text())
            return [m for line in re.findall(r'(?m)^\s*(?:public\s+)?import\s+([^\n]+)', text) for m in line.split()]
        try:
            for definition in plan['arms']:
                name = definition['name']
                workspace, cache = out / name / 'workspace', out / name / 'objects'
                workspace.mkdir(parents=True); cache.mkdir()
                arm = arms[name] = {'workspace': workspace, 'objects': cache, 'object_pins': {}, 'records': {}}
                for module in order:
                    row = rows[module]
                    source = definition['KSim_source'] if module.endswith('.KSim') else plan['fresh_KFastSites215_source'] if module.endswith('.KFastSites215') else row['source']
                    dest = workspace / (module.replace('.', '/') + '.lean')
                    dest.parent.mkdir(parents=True, exist_ok=True); shutil.copyfile(source, dest)
                    assert sha(dest) == inputs[source] and imports(dest) == row['imports']
                    source_pins[str(dest)] = sha(dest)
                    if module in reuse:
                        obj = basis / 'objects' / (module.replace('.', '/') + '.olean')
                        assert sha(obj) == old[module]['object_sha256']
                        for companion in sorted(obj.parent.glob(obj.stem + '.olean*')):
                            target = cache / companion.relative_to(basis / 'objects')
                            target.parent.mkdir(parents=True, exist_ok=True); shutil.copyfile(companion, target)
                            assert sha(target) == inputs[str(companion)]
                            arm['object_pins'][str(target)] = sha(target)
                        arm['records'][module] = old[module]
                probe = workspace / (plan['benchmark_module'] + '.lean')
                shutil.copyfile(plan['benchmark_source'], probe)
                assert sha(probe) == inputs[plan['benchmark_source']] and imports(probe) == plan['benchmark_imports']
                assert all(probe.read_text().count(b['declaration_text']) == 1 for b in plan['blocks'])
                source_pins[str(probe)] = sha(probe)
            cache_check()
            def execute(arm_name, module, expected):
                arm = arms[arm_name]; workspace, cache = arm['workspace'], arm['objects']
                source = workspace / (module.replace('.', '/') + '.lean')
                obj = cache / (module.replace('.', '/') + '.olean')
                assert not obj.exists() and not list(obj.parent.glob(obj.stem + '.olean*'))
                check_inputs(); cache_check()
                declared_imports = imports(source)
                dependencies = {d: arm['records'][d]['object_sha256'] for d in declared_imports if d != 'Init'}
                attempt = out / 'attempts' / (str(len(attempts) + 1).zfill(2) + '-' + arm_name + '-' + module)
                attempt.mkdir(parents=True); shutil.copyfile(source, attempt / source.name)
                obj.parent.mkdir(parents=True, exist_ok=True)
                command = [plan['compiler']['path'], '-j1', '-M12288', '--root=' + str(workspace), '-o', str(obj), str(source)]
                timeout = 900 if module == plan['benchmark_module'] else 120
                row = {'arm': arm_name, 'module': module, 'source': str(source), 'source_sha256': sha(source), 'snapshot': str(attempt / source.name), 'imports': declared_imports, 'dependencies': dependencies, 'command': command, 'cwd': str(workspace), 'environment': {'LEAN_PATH': str(cache), 'LEAN_NUM_THREADS': '1'}, 'compiler_sha256': plan['compiler']['sha256'], 'supervisor_sha256': inputs[plan['supervisor']], 'timeout_seconds': timeout, 'memory_mebibytes': 12288, 'log': str(attempt / 'compiler.log')}
                attempts.append(row); record = attempt / 'record.json'
                env = {k: v for k, v in os.environ.items() if not k.startswith('LEAN_')}
                env.update(LEAN_PATH=str(cache), LEAN_NUM_THREADS='1')
                print('CHECK', arm_name, module, flush=True)
                try:
                    assert supervisor.run_locked(command, workspace, env, Path(plan['global_lock']), Path(row['log']), timeout, row, record)
                    assert row['exit_code'] == 0 and not row['timed_out']
                    text = Path(row['log']).read_text()
                    assert 'warning:' not in text and 'error:' not in text and 'sorryAx' not in text
                    row['warnings'] = 0
                    row['reports'] = profiles(text)
                    if expected is None:
                        assert [n for n, _ in row['reports']] == plan['expected_benchmark_report_names']
                    else:
                        assert row['reports'] == expected
                    assert sha(source) == sha(attempt / source.name) == row['source_sha256'] and sha(row['log']) == row['log_sha256']
                    row['companions'] = {str(p): sha(p) for p in obj.parent.glob(obj.stem + '.olean*')}
                    assert str(obj) in row['companions']
                    arm['object_pins'].update(row['companions']); row['object_sha256'] = sha(obj)
                    arm['records'][module] = row; row['validation_status'] = 'PASS'
                finally:
                    save(record, row)
                check_inputs(); cache_check()
                print('PASS', arm_name, module, row['seconds'], flush=True)
                return row
            for name in ['baseline', 'prefix']:
                for module in plan['fresh_modules']:
                    execute(name, module, rows[module]['expected_reports'])
            first = execute('baseline', plan['benchmark_module'], None)
            second = execute('prefix', plan['benchmark_module'], first['reports'])
            check_inputs(); cache_check()
            save(out / 'result.json', {'status': 'PASS_DIAGNOSTIC_IDENTICAL_THREE_BLOCK_COMPARISON_ONLY', 'plan_sha256': PLAN_SHA, 'inputs': inputs, 'staged_source_pins': source_pins, 'object_pins': {name: arm['object_pins'] for name, arm in arms.items()}, 'attempts': attempts, 'baseline_benchmark_seconds': first['seconds'], 'prefix_benchmark_seconds': second['seconds'], 'reports_identical': True, 'missing_inherited_basis_raw_records': raw_absent, 'scope': 'One ordered sample per arm, blocks0/5/10 only; not full coverage, adoption or a general speed claim.'})
        except BaseException as exc:
            save(out / 'result.json', {'status': 'FAIL_DIAGNOSTIC', 'plan_sha256': PLAN_SHA, 'inputs': inputs, 'attempts': attempts, 'exception': type(exc).__name__ + ': ' + str(exc)})
            raise

if __name__ == '__main__':
    main()
