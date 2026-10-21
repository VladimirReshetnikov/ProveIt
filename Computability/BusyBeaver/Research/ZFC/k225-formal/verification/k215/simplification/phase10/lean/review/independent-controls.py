"""Pure metadata controls extracted from reviewed local helper syntax; no compiler."""
import ast
import hashlib
import json
from pathlib import Path, PurePosixPath

ROOT = Path('/tmp/k215-phase10-publication')
OUT = Path('/tmp/k215-phase10-publication-peer')
raw = (ROOT / 'packet.py').read_bytes()
assert hashlib.sha256(raw).hexdigest() == 'b9192219c63400ac6d15992dad5ff4dd19e01c74611b5400ce6f42f109d9a9be'
tree = ast.parse(raw)
safe = next(n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name == 'safe')
binary = next(n for n in tree.body if isinstance(n, ast.Assign) and any(isinstance(t, ast.Name) and t.id == 'BINARY' for t in n.targets))
guard = next(n for n in ast.walk(tree) if isinstance(n, ast.If) and any(isinstance(t, ast.Assign) and any(isinstance(x, ast.Name) and x.id == 'expected_axioms' for x in t.targets) for t in n.body))
profile_nodes = guard.body[-2:]
env = {'PurePosixPath': PurePosixPath}
exec(compile(ast.fix_missing_locations(ast.Module(body=[binary, safe], type_ignores=[])), '<reviewed-safe-metadata>', 'exec'), env)
profile = compile(ast.fix_missing_locations(ast.Module(body=profile_nodes, type_ignores=[])), '<reviewed-axiom-profile>', 'exec')
checks = []
def case(label, want, fn):
    try:
        fn()
        got = True
    except AssertionError:
        got = False
    assert got == want, (label, want, got)
    checks.append({'label': label, 'expected_accept': want, 'actual_accept': got})

case('relative source', True, lambda: env['safe']('execution/fresh/Core/source.lean'))
case('relative raw log', True, lambda: env['safe']('execution/logs/compiler.log'))
for name in ['/absolute', 'a/../b', 'a/./b', 'x.olean', 'x.olean.private', 'x.olean.server', 'x.pyo', 'x.vo', 'x.tar.gz', 'x.zip']:
    case('reject '+name, False, lambda name=name: env['safe'](name))

def profile_check(module, axioms):
    data = {'m': module, 'CORE': 'BusyBeaver.ZFC.DominatedImplication', 'reports': [('exact.named.report', axioms)]}
    exec(profile, data)

case('generic core empty axioms', True, lambda: profile_check('BusyBeaver.ZFC.DominatedImplication', ''))
case('generic client empty axioms', True, lambda: profile_check('GenericCD52Api', ''))
case('numeric exact two axioms', True, lambda: profile_check('NumericCD52Api', 'propext, Quot.sound'))
case('reject generic choice', False, lambda: profile_check('GenericCD52Api', 'Classical.choice'))
case('reject generic propext', False, lambda: profile_check('BusyBeaver.ZFC.DominatedImplication', 'propext'))
case('reject numeric choice', False, lambda: profile_check('NumericCD52Api', 'propext, Quot.sound, Classical.choice'))
case('reject numeric missing report axiom', False, lambda: profile_check('NumericCD52Api', 'propext'))
result = {
    'status': 'PASS_PURE_METADATA_CONTROLS',
    'source_sha256': hashlib.sha256(raw).hexdigest(),
    'positive': sum(r['expected_accept'] for r in checks),
    'negative': sum(not r['expected_accept'] for r in checks),
    'checks': checks,
    'scope': 'Only AST-extracted local filename and isolated axiom-profile guards. No packet collection, live-object audit, proof compiler or supplied producer invocation.',
}
(OUT / 'controls.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({'status': result['status'], 'positive': result['positive'], 'negative': result['negative']}))
