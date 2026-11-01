#!/usr/bin/env python3
"""Demonstrate that direct guards/axiom reports do not detect a mixed import.

This intentionally derives False in a disposable inconsistent Lean environment.
It does not modify the toolchain, package provider, or project source tree.
"""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
LEAN = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
SOURCES = {
    'old/A.lean': 'def p : Prop := True\n',
    'old/B.lean': 'import A\ntheorem valid : p := trivial\n',
    'new/A.lean': 'def p : Prop := False\n',
    'new/C.lean': 'import B\ntheorem contradiction : False := valid\n#print axioms contradiction\n#print p\n',
    'new/B.lean': 'import A\ntheorem valid : p := trivial\n',
}

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def run(roots, root, source, *, deps=False):
    env = dict(os.environ, LEAN_PATH=':'.join(map(str, roots)), LEAN_NUM_THREADS='1')
    env.pop('LEAN_SRC_PATH', None)
    args = [str(LEAN)] + (['--deps', str(source)] if deps else
           ['--root=' + str(root), str(source), '-o', str(source.with_suffix('.olean'))])
    result = subprocess.run(args, env=env, text=True, capture_output=True, timeout=120)
    return {'exit': result.returncode, 'stdout': result.stdout, 'stderr': result.stderr}

def experiment():
    with tempfile.TemporaryDirectory(prefix='lean-mixed-provider-') as td:
        root = Path(td)
        for name, source in SOURCES.items():
            path = root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(source)
        old, new = root / 'old', root / 'new'
        steps = {}
        steps['old_a'] = run([old], old, old / 'A.lean')
        steps['old_b'] = run([old], old, old / 'B.lean')
        steps['new_a'] = run([new], new, new / 'A.lean')
        assert all(steps[k]['exit'] == 0 and not steps[k]['stderr'] for k in ('old_a', 'old_b', 'new_a')), steps
        old_hash, new_hash = digest(old / 'A.olean'), digest(new / 'A.olean')
        assert old_hash != new_hash
        # With the original A, the attempted False proof must fail.
        steps['old_control'] = run([old], new, new / 'C.lean')
        assert steps['old_control']['exit'] != 0 and 'error:' in steps['old_control']['stdout'], steps
        assert not (new / 'C.olean').exists()
        # Direct dependency reporting names B but omits B's transitive import A.
        steps['mixed_deps'] = run([new, old], new, new / 'C.lean', deps=True)
        assert steps['mixed_deps']['exit'] == 0 and not steps['mixed_deps']['stderr']
        dependencies = steps['mixed_deps']['stdout'].splitlines()
        assert str(old / 'B.olean') in dependencies and str(new / 'A.olean') not in dependencies
        # Fresh A and historical B yield an apparent axiom-free contradiction.
        steps['mixed'] = run([new, old], new, new / 'C.lean')
        mixed = steps['mixed']
        assert mixed['exit'] == 0 and not mixed['stderr'] and 'error:' not in mixed['stdout'], mixed
        assert "'contradiction' does not depend on any axioms" in mixed['stdout']
        assert 'def p : Prop :=\nFalse' in mixed['stdout']
        assert (new / 'C.olean').is_file()
        # Rebuilding B against fresh A fails, closing the mixed-provider route.
        steps['new_b_control'] = run([new], new, new / 'B.lean')
        assert steps['new_b_control']['exit'] != 0 and 'error:' in steps['new_b_control']['stdout']
        assert not (new / 'B.olean').exists()
        def normalized(s):
            return s.replace(str(root), '<probe>')
        return {'old_a_olean_sha256': old_hash, 'new_a_olean_sha256': new_hash,
                'old_b_olean_sha256': digest(old / 'B.olean'),
                'mixed_c_olean_sha256': digest(new / 'C.olean'),
                'steps': {k: {f: normalized(v) if isinstance(v, str) else v
                              for f, v in step.items()} for k, step in steps.items()}}

def main():
    runs = [experiment(), experiment()]
    for name in runs[0]['steps']:
        assert runs[0]['steps'][name] == runs[1]['steps'][name], name
    result = {'status': 'PASS_MIXED_IMPORT_COUNTEREXAMPLE',
              'lean_executable': str(LEAN), 'lean_sha256': digest(LEAN),
              'lean_version': subprocess.check_output([str(LEAN), '--version'], text=True).strip(),
              'source_sha256': {k: hashlib.sha256(v.encode()).hexdigest() for k, v in SOURCES.items()},
              'runs': runs,
              'scope': 'Controlled incompatible providers demonstrate lack of a general '
                       'compatibility guarantee; no claim that actual project objects prove False.'}
    output = HERE / 'receipt.json'
    if output.exists():
        raise RuntimeError('refusing to overwrite receipt')
    output.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(result['status'], digest(output))

if __name__ == '__main__':
    main()
