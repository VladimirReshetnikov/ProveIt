#!/usr/bin/env python3
"""Independent synthetic build and read-only postflight fault injection."""
import contextlib
import copy
import hashlib
import io
import json
import os
from pathlib import Path
import runpy
import shutil
import subprocess
import sys

C = Path('/workspace/shared/report69-tool-review-candidate-v5')
BASE = Path('/workspace/shared/report69-independent-release-tool-review-20261004')
O = BASE / 'build-probes'
O.mkdir(mode=0o700)
RESULTS = []
PINS = '38b3f7a8a3bb1f837ace42df35edffd8d7627d3af476f4869106903e31824e4c'
LOCK = '62d196ba3a660790910afa4ac4eb83f1410b8b64e6a401ad52d1388ee812f3f5'

def sha(data):
    return hashlib.sha256(data).hexdigest()

def enc(data):
    return (json.dumps(data, sort_keys=True, indent=2) + '\n').encode()

def run(label, root, tool, args, success=True, env=None, expected=None):
    p = subprocess.run([sys.executable, '-I', '-S', '-B', str(root / 'tools' / tool), *args],
                       cwd=O, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=300)
    (O / (label + '.stdout')).write_bytes(p.stdout)
    assert (p.returncode == 0) == success, (label, p.stdout[-5000:])
    assert expected is None or expected.encode() in p.stdout, (label, expected, p.stdout[-5000:])
    RESULTS.append({'test': label, 'status': 'PASS', 'exit_status': p.returncode})

def build_args(out, pin=PINS, lock=LOCK):
    return ['--pins-sha', pin, '--dependency-lock-sha', lock, '--output-dir', str(out), '--require-packaged-match']

def fault(label, kind):
    # Import only the previously inspected builder. System files are never mutated.
    module = runpy.run_path(str(C / 'tools/build_report69.py'), run_name='independent_fault_injection')
    namespace = module['main'].__globals__
    original_loader = namespace['load_helper']
    real_run = subprocess.run
    phase = {'value': 'start', 'compile_count': 0, 'injections': 0}
    dependency_lock = json.loads((C / 'tools/BUILD_DEPENDENCIES_LOCK.json').read_bytes())
    latex = next(name for name in dependency_lock['system_inputs'] if name.endswith('/latex.ltx'))
    binary = dependency_lock['executables']['pdfinfo']['resolved']
    def load_instrumented_helper():
        h = original_loader()
        original_read = h.read
        def observed_read(path):
            data = original_read(path)
            inject = ((kind == 'system' and phase['value'] == 'compile-3-done' and str(path) == latex) or
                      (kind == 'binary' and phase['value'] == 'render-done' and str(path) == binary))
            if inject:
                phase['injections'] += 1
                return data + b'\nINDEPENDENT SIMULATED CHANGE\n'
            return data
        h.read = observed_read
        return h
    def observed_run(argv, **kwargs):
        result = real_run(argv, **kwargs)
        if argv[0] == '/usr/bin/pdflatex':
            phase['compile_count'] += 1
            phase['value'] = 'compile-' + str(phase['compile_count']) + '-done'
        elif argv[0] == '/usr/bin/pdftoppm':
            phase['value'] = 'render-done'
        return result
    namespace['load_helper'] = load_instrumented_helper
    out = O / label
    old_argv = sys.argv
    stream = io.StringIO()
    try:
        sys.argv = ['build_report69.py', *build_args(out)]
        subprocess.run = observed_run
        with contextlib.redirect_stdout(stream), contextlib.redirect_stderr(stream):
            try:
                module['main']()
            except ValueError as error:
                message = str(error)
            else:
                raise AssertionError('Postflight fault did not refuse')
    finally:
        subprocess.run = real_run
        sys.argv = old_argv
    (O / (label + '.stdout')).write_text(stream.getvalue() + message + '\n')
    expected = 'System input changed during build' if kind == 'system' else 'Executable post-build mismatch'
    assert expected in message and phase['injections'] > 0, (phase, message)
    failure = json.loads((out / 'BUILD_FAILURE.json').read_bytes())
    assert failure['status'] == 'FAIL' and failure['release_preserved'] is True
    assert not (out / 'BUILD_RECEIPT.json').exists()
    RESULTS.append({'test': label, 'status': 'PASS', 'injection_kind': 'read-only test double; no system bytes modified', 'injections': phase['injections'], 'expected_refusal': message, 'preservation': True})

def main():
    for label, pin, lock in [('bad-manuscript-pin', '0' * 64, LOCK), ('bad-lock-pin', PINS, '0' * 64)]:
        out = O / (label + '-out')
        run(label, C, 'build_report69.py', build_args(out, pin, lock), success=False)
        assert not out.exists()
    fixture = O / 'preflight-fixture'
    shutil.copytree(C, fixture, copy_function=shutil.copy2)
    original_lock = (fixture / 'tools/BUILD_DEPENDENCIES_LOCK.json').read_bytes()
    lock = json.loads(original_lock)
    lock['executables']['python']['sha256'] = '0' * 64
    changed = enc(lock); (fixture / 'tools/BUILD_DEPENDENCIES_LOCK.json').write_bytes(changed)
    out = O / 'stale-executable-out'
    run('stale-executable-preflight', fixture, 'build_report69.py', build_args(out, lock=sha(changed)), success=False, expected='Executable preflight mismatch')
    assert not out.exists()
    lock = json.loads(original_lock)
    first = next(iter(lock['system_inputs']))
    lock['system_inputs'][first]['sha256'] = '0' * 64
    changed = enc(lock); (fixture / 'tools/BUILD_DEPENDENCIES_LOCK.json').write_bytes(changed)
    out = O / 'stale-system-out'
    run('stale-system-preflight', fixture, 'build_report69.py', build_args(out, lock=sha(changed)), success=False, expected='System-input preflight mismatch')
    assert not out.exists()
    (fixture / 'tools/BUILD_DEPENDENCIES_LOCK.json').write_bytes(original_lock)
    helper = fixture / 'tools/release69.py'
    helper.write_bytes(helper.read_bytes() + b'\n# Inert independent helper hash-tamper probe.\n')
    out = O / 'changed-helper-out'
    run('changed-helper-refused-before-import', fixture, 'build_report69.py', build_args(out), success=False, expected='Release helper differs from inspected source')
    assert not out.exists()
    # Separate synthetic manuscript: calc is read only on the first TeX pass.
    synthetic = O / 'synthetic'
    shutil.copytree(C, synthetic, copy_function=shutil.copy2)
    modules = ['tensor.tex', 'one-witness.tex', 'classification.tex', 'costs.tex', 'power.tex', 'scope.tex']
    text = ('\\documentclass{article}\n\\pdftrailerid{}\n'
            '\\IfFileExists{Report69.aux}{}{\\usepackage{calc}}\n'
            '\\begin{document}Independent presentation-only fixture.\n' +
            ''.join('\\input{manuscript/' + name + '}\n' for name in modules) + '\\end{document}\n')
    (synthetic / 'manuscript/Report69.tex').write_text(text)
    for name in modules:
        (synthetic / 'manuscript' / name).write_text('% Inert synthetic module ' + name + '\n')
    prepared = O / 'prepared'
    run('independent-synthetic-prepare', synthetic, 'release69.py', ['prepare', '--output-dir', str(prepared)])
    shutil.copy2(prepared / 'Report69.tex', synthetic / 'Report69.tex')
    shutil.copy2(prepared / 'MANUSCRIPT_PINS.json', synthetic / 'manuscript/MANUSCRIPT_PINS.json')
    pin = sha((prepared / 'MANUSCRIPT_PINS.json').read_bytes())
    boot = O / 'synthetic-bootstrap'
    env = os.environ.copy()
    env.update(HOME=str(synthetic / 'science'), TMPDIR=str(synthetic / 'science'),
               TEXINPUTS='/definitely-not-the-toolchain', TEXFORMATS='/definitely-not-the-format',
               TEXMFHOME=str(synthetic / 'science'), shell_escape='t')
    run('independent-hostile-environment-bootstrap', synthetic, 'build_report69.py', ['--pins-sha', pin, '--bootstrap', '--output-dir', str(boot)], env=env)
    receipt = json.loads((boot / 'BUILD_RECEIPT.json').read_bytes())
    assert receipt['status'] == 'BOOTSTRAP' and receipt['dependency_lock_verified'] is False and receipt['shell_escape'] is False
    union = json.loads((boot / 'RECORDER_INPUT_UNION.json').read_bytes())
    first_only = set(union['passes'][1]['system_inputs']) - set(union['passes'][2]['system_inputs']) - set(union['passes'][3]['system_inputs'])
    calc = next(name for name in first_only if name.endswith('/calc.sty'))
    assert calc in union['union']
    RESULTS.append({'test': 'independent-calc-first-pass-only-union', 'status': 'PASS', 'path': calc})
    lock_data = (boot / 'BUILD_DEPENDENCIES.json').read_bytes()
    (synthetic / 'tools/BUILD_DEPENDENCIES_LOCK.json').write_bytes(lock_data)
    shutil.copy2(boot / 'Report69.pdf', synthetic / 'Report69.pdf')
    run('independent-synthetic-locked-build', synthetic, 'build_report69.py', build_args(O / 'synthetic-locked', pin=pin, lock=sha(lock_data)))
    lock = json.loads(lock_data); del lock['system_inputs'][calc]
    omitted = enc(lock); (synthetic / 'tools/BUILD_DEPENDENCIES_LOCK.json').write_bytes(omitted)
    run('independent-omitted-first-pass-refusal', synthetic, 'build_report69.py', build_args(O / 'omitted-first-pass', pin=pin, lock=sha(omitted)), success=False, expected='Unpinned or changed executed TeX input')
    failure = json.loads((O / 'omitted-first-pass/BUILD_FAILURE.json').read_bytes())
    assert failure['release_preserved'] is True
    fault('fault-injected-system-postflight', 'system')
    fault('fault-injected-executable-postflight', 'binary')
    result = {'status': 'PASS', 'test_count': len(RESULTS), 'scope': 'Presentation-only independent fixtures and instrumented guard checks; system toolchain unmodified; no scientific executable', 'tests': RESULTS}
    (BASE / 'BUILD_PROBES_RECEIPT.json').write_bytes(enc(result))
    print(enc(result).decode())

if __name__ == '__main__':
    main()
