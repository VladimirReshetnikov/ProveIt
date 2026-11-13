#!/usr/bin/env python3
"""Read-only audit of the retained P64 captured-provider replay."""
import hashlib
import json
from pathlib import Path

if not __debug__:
    raise SystemExit('refusing optimized Python')
HERE = Path(__file__).resolve().parent
OUT = Path('/tmp/p64-independent-captured-replay')

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

records = json.loads((HERE / 'results.json').read_text())
result = json.loads((HERE / 'result.json').read_text())
names = ['P64Graph', 'P64Root', 'P64Norm', 'P64Early', 'P64Facts',
         'P64ConvZero', 'P64Converse', 'IPRAPositive64']
assert result['status'] == 'PASS' and result['modules'] == len(records) == 8
assert (OUT / 'results.json').read_bytes() == (HERE / 'results.json').read_bytes()
assert (OUT / 'result.json').read_bytes() == (HERE / 'result.json').read_bytes()
assert [r['module'] for r in records] == names
for r in records:
    assert r['exit'] == 0
    source, shim, obj, log = (Path(r[k]) for k in ('source', 'shim', 'object', 'log'))
    assert sha(source) == r['source_sha256'] and sha(shim) == r['shim_sha256']
    assert obj.exists() and not obj.is_symlink() and sha(obj) == r['object_sha256']
    assert sha(log) == r['log_sha256']
    assert sha(HERE / 'logs' / log.name) == r['log_sha256']
    assert not any(s in log.read_text() for s in ('sorryAx', 'error:', 'warning:'))
    for module, dep in r['imports'].items():
        assert sha(Path(dep['path'])) == dep['sha256'], module
    original = source.read_text()
    if r['module'] == 'P64Graph':
        old = 'import DiophantineConsistency.Compact44.FreeJSumSquares\n'
        assert original.startswith(old)
        assert shim.read_text() == 'import P65GraphShim\n' + original[len(old):]
    else:
        assert shim.read_bytes() == source.read_bytes()
for path, value in result['direct_provider_guards'].items():
    assert sha(Path(path)) == value
assert sha(Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')) == result['lean_sha256']
endpoint = (HERE / 'logs/IPRAPositive64.txt').read_text()
for name in ('positiveBridge', 'native_equivalence', 'standard_equivalence', 'reference_equivalence'):
    assert (f"'DiophantineConsistency.IPRAPositive64.{name}' depends on axioms: "
            '[propext, Classical.choice, Quot.sound]') in endpoint
print(json.dumps({'status': 'PASS', 'modules': len(records),
                  'direct_provider_guards': len(result['direct_provider_guards']),
                  'scope': 'read-only audit of retained captured-provider replay'}, indent=2))
