#!/usr/bin/env python3
"""Exercise compiled-header reachability and fail-closed object guards."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile

import closure

HERE = Path(__file__).resolve().parent

def reject(thunk, expected):
    try:
        thunk()
    except RuntimeError as exc:
        if expected not in str(exc):
            raise AssertionError((expected, str(exc)))
    else:
        raise AssertionError(('accepted invalid input', expected))

def compile_file(root, name, text):
    path = root.joinpath(*name.split('.')).with_suffix('.lean')
    obj = path.with_suffix('.olean')
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text)
    env = dict(os.environ, LEAN_PATH=str(root), LEAN_NUM_THREADS='1')
    p = subprocess.run([str(closure.LEAN), '-j1', '--root=' + str(root), str(path), '-o', str(obj)],
                       env=env, capture_output=True, text=True, timeout=120)
    assert p.returncode == 0, (p.stdout, p.stderr)
    return obj

def main():
    controls = []
    with tempfile.TemporaryDirectory(prefix='compiled-header-control-') as td:
        tmp = Path(td); full = tmp / 'full'; full.mkdir(); partial = tmp / 'partial'; partial.mkdir()
        a = compile_file(full, 'Probe.A', 'prelude\naxiom p : Prop\n')
        b = compile_file(full, 'Probe.B', 'prelude\nimport Probe.A\naxiom q : p\n')
        policy = {'roots': [{'path': str(full), 'role': 'test'}]}
        result = closure.collect(['Probe.B'], policy, max_modules=5)
        assert set(result['modules']) == {'Probe.A', 'Probe.B'}
        assert result['modules']['Probe.B']['imports'] == ['Probe.A']
        assert result['artifacts'][str(a)]['sha256'] == closure.digest(a)
        assert result['artifacts'][str(b)]['sha256'] == closure.digest(b)
        controls.append('compiled_transitive_header_reached')
        compile_file(partial, 'Probe.A', 'prelude\naxiom p : Prop\n')
        wrong_order = {'roots': [{'path': str(partial), 'role': 'partial'},
                                  {'path': str(full), 'role': 'complete'}]}
        reject(lambda: closure.collect(['Probe.B'], wrong_order, max_modules=5), 'selected namespace lacks object')
        controls.append('earlier_namespace_shadows_later_module')
        reject(lambda: closure.collect(['Probe.B'], policy, max_modules=1), 'module limit reached')
        controls.append('module_limit_fails_closed')
        reject(lambda: closure.collect(['Probe.Unknown'], policy), 'selected namespace lacks object')
        controls.append('missing_object_fails_closed')
        reject(lambda: closure.collect(['Probe/B'], policy), 'unsupported module name')
        controls.append('unsupported_name_fails_closed')
        saved = a.read_bytes(); a.write_bytes(saved + b'changed')
        reject(lambda: closure.check_guard(result['artifacts']), 'observed artifact changed')
        a.write_bytes(saved); controls.append('object_mutation_rejected')
        ir = a.with_suffix('.ir')
        assert not os.path.lexists(ir)
        ir.write_bytes(b'unexpected companion')
        reject(lambda: closure.check_guard(result['artifacts']), 'observed artifact changed')
        ir.unlink(); controls.append('new_companion_rejected')
        fixture = Path('/home/codex/src/Proofs/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Data/Nat/Pairing.olean')
        ir_fixture = fixture.with_suffix('.ir')
        env = dict(os.environ); env.pop('LEAN_PATH', None); env.pop('LEAN_SRC_PATH', None)
        headers = closure.read_batch([fixture, ir_fixture], env)
        assert all('Mathlib.Data.Nat.Sqrt' in row['imports'] for row in headers)
        controls.append('real_mathlib_olean_and_ir_headers')
    result = {'status': 'PASS_COMPILED_HEADER_CONTROLS', 'controls': controls,
              'reader_sha256': closure.digest(HERE / 'read_imports.lean'),
              'driver_sha256': closure.digest(HERE / 'closure.py'),
              'test_sha256': closure.digest(Path(__file__)), 'lean_sha256': closure.digest(closure.LEAN),
              'scope': 'Compiled-header traversal and controlled guards only; '
                       'no source-to-object or dynamic-runtime provenance established.'}
    out = HERE / 'test-receipt.json'
    with out.open('x') as stream:
        json.dump(result, stream, indent=2, sort_keys=True); stream.write('\n')
    print(result['status'], len(controls), closure.digest(out), flush=True)

if __name__ == '__main__':
    main()
