"""Record static bindings only; never import or execute a reviewed producer."""
import ast
import hashlib
import json
from pathlib import Path

ROOT = Path('/tmp/k215-generic-cd52')
OUT = Path('/tmp/k215-generic-cd52-peer')
PRODUCER = ROOT / 'production/generate_dominated_implication_lean.py'
EXPECTED = '49099c1c05e6a18a6c500a46f190545abfa441330ddeee7880a39ac7af9f077d'

def sha(raw):
    return hashlib.sha256(raw).hexdigest()

def binding(path):
    raw = path.read_bytes()
    return {'path': str(path), 'sha256': sha(raw), 'bytes': len(raw)}

raw = PRODUCER.read_bytes()
assert sha(raw) == EXPECTED
tree = ast.parse(raw)
constants = {}
imports = []
for node in tree.body:
    if isinstance(node, ast.Import):
        imports.extend(x.name for x in node.names)
    elif isinstance(node, ast.ImportFrom):
        imports.append(node.module)
    elif isinstance(node, ast.Assign) and len(node.targets) == 1 and isinstance(node.targets[0], ast.Name):
        key = node.targets[0].id
        if key in {'SOURCE', 'TEMPLATE_PINS', 'EXPECTED_CORE'}:
            constants[key] = ast.literal_eval(node.value)
assert set(imports) == {'__future__', 'argparse', 'hashlib', 'json', 'pathlib', 're'}
for node in ast.walk(tree):
    if isinstance(node, ast.Call):
        name = getattr(node.func, 'id', getattr(node.func, 'attr', ''))
        assert name not in {'exec', 'eval', '__import__', 'exec_module', 'compile'}

inputs = [ROOT / 'production' / constants['SOURCE'], ROOT / 'production/rho8cd/derivation.txt']
assert sha(inputs[0].read_bytes()) == 'c0c9eb59ad7076b7753b1a5d7d690e26f96936229fdd875dad926bb210d6fb13'
assert sha(inputs[1].read_bytes()) == '3cbf1ed6114ff44da836578e58c9d5308d347a8b1d664e83c1983e800d285776'
templates = []
for name, pin in constants['TEMPLATE_PINS'].items():
    path = ROOT / 'production/dominated_implication_templates' / name
    assert sha(path.read_bytes()) == pin
    templates.append(binding(path))
candidate = ROOT / 'candidate/DominatedImplication.lean'
assert sha(candidate.read_bytes()) == constants['EXPECTED_CORE']
prior = OUT / 'review.json'
assert sha(prior.read_bytes()) == '081a96980e1a2dca8eb7217e30b783a2a930c365ac536eed754d7bd4cb78b38e'
result = {
    'status': 'PASS_INDEPENDENT_SELF_CONTAINED_PRODUCER_SOURCE_PEER',
    'reviewer': 'review_upstream_reflection',
    'producer': binding(PRODUCER),
    'report': binding(OUT / 'producer-review.md'),
    'record_script': binding(Path(__file__)),
    'inputs': [binding(p) for p in inputs],
    'templates': templates,
    'reviewed_output': binding(candidate),
    'prior_mathematical_api_peer': binding(prior),
    'imported_modules': imports,
    'historical_unexecuted_draft': [binding(ROOT / 'history/producer-import-draft' / n) for n in ['generate_dominated_implication_lean.py', 'reason.md']],
    'findings': [],
    'producer_executed': False,
    'delivered_code_imported_or_executed': False,
    'compiler_invoked': False,
    'scope': 'Full source/template read and static raw/AST bindings; actual production reproduction and Lean checks are separate root-owned evidence.',
    'remaining': ['Independent root reproduction of --out and --check against the reviewed exact core and adapter.'],
}
(OUT / 'producer-review.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({'status': result['status'], 'receipt_sha256': sha((OUT / 'producer-review.json').read_bytes())}))
