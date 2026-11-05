#!/usr/bin/env python3
"""Pure temporary-file controls for runner inventory and namespace guards; no Lean."""
import importlib.util
import json
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('base_only_runner', HERE / 'runner.py')
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)
guards = runner.load('extension_guards', runner.DRIVER_DIR / 'guards.py')

def rejected(f):
    try:
        f()
    except ValueError:
        return
    raise AssertionError('expected rejection')

good_reports = "'X' does not depend on any axioms\n'Y' depends on axioms: [Classical.choice, Quot.sound]\n"
runner.reports(good_reports, ['X', 'Y'])
rejected(lambda: runner.reports(good_reports, ['Y', 'X']))
rejected(lambda: runner.reports("'X' depends on axioms: [Untrusted.axiom]\n", ['X']))
rejected(lambda: runner.reports("'X' depends on axioms: [sorryAx]\n", ['X']))
rejected(lambda: runner.reports("warning: fixture\n" + good_reports, ['X', 'Y']))
rejected(lambda: runner.reports("error: fixture\n" + good_reports, ['X', 'Y']))

with tempfile.TemporaryDirectory(prefix='base-inventory-control-') as tmp:
    root = Path(tmp) / 'lib'
    root.mkdir()
    target = root / 'Project' / 'A.olean'
    target.parent.mkdir()
    target.write_text('recorded object')
    outputs = {'Project.A': {str(target): {'sha256': 'fixture'}, str(target)+'.private': None}}
    runner.check_base_inventory(root, outputs)
    guards.reject_project_fallbacks((root,), {'Mathlib', 'Foundation', 'Init', 'Lean'})
    (root / 'Mathlib').mkdir()
    rejected(lambda: guards.reject_project_fallbacks((root,), {'Mathlib', 'Foundation', 'Init', 'Lean'}))
    (root / 'Mathlib').rmdir()
    shadow = root / 'Mathlib' / 'Injected.olean'
    shadow.parent.mkdir()
    shadow.write_text('shadow')
    rejected(lambda: runner.check_base_inventory(root, outputs))
    shadow.unlink()
    shadow.parent.rmdir()
    target.unlink()
    rejected(lambda: runner.check_base_inventory(root, outputs))
    target.write_text('recorded object')
    link = root / 'Foundation'
    link.symlink_to(target.parent, target_is_directory=True)
    rejected(lambda: runner.check_base_inventory(root, outputs))
    link.unlink()
    runner.check_base_inventory(root, outputs)
    original_walk = runner.os.walk
    def denied_walk(path, *, followlinks, onerror):
        onerror(PermissionError('injected inventory read error'))
        yield
    try:
        runner.os.walk = denied_walk
        try:
            runner.check_base_inventory(root, outputs)
        except PermissionError:
            pass
        else:
            raise AssertionError('inventory read error was suppressed')
    finally:
        runner.os.walk = original_walk
    local = Path(tmp) / 'local'
    local.mkdir()
    tops = {'Project', 'Mathlib', 'Foundation', 'Init'}
    guards.reject_project_fallbacks((local,), tops)
    for top in sorted(tops):
        shadow = local / top
        shadow.mkdir()
        rejected(lambda: guards.reject_project_fallbacks((local,), tops))
        shadow.rmdir()
    (local / 'Init.olean').write_text('shadow')
    rejected(lambda: guards.reject_project_fallbacks((local,), tops))
print(json.dumps({'status': 'PASS', 'scope': 'synthetic inventory, namespace shadow, and axiom-report controls; no Lean'}, sort_keys=True))
