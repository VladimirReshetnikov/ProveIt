#!/usr/bin/env python3
"""Read-only review of the positive-zero theorem and fresh divisibility build."""
from hashlib import sha256
import json
from pathlib import Path
import subprocess
import sys

D = Path(__file__).resolve().parents[2]
P = D/'research/ordinary12-qcube92-candidate'
B = P/'observations/binding-attempt01'
E = P/'observations/existence-attempt03'
M = P/'observations/model-attempt01'
old_dir = D/'research/ordinary12-ipra-bridge/free-j-first-divisibility-prototype'
PIN = {
    P/'QCube92Existence.lean': '62b030d3c8d0ccfac46b4b0c41be58c67dbe96e7794d01c284c317499c456e9d',
    P/'EXISTENCE.md': '0dbc9dd0bdb558e5a860580f2ec3d7ba9ecc53fd9bb0221d0f9d5afd5b454dd5',
    P/'FreeJRootBinding.lean': '5d826d8f1cf5ce4a11c45f4a6762ba0729a5e282a1356bce0aeb02f49c58083b',
    old_dir/'FreeJRootBinding.lean': '5d826d8f1cf5ce4a11c45f4a6762ba0729a5e282a1356bce0aeb02f49c58083b',
    old_dir/'replay-receipt.json': 'ac23e8dfbf895294c909f34202c45327cf50dc583f61605ac08d086e68155e7b',
    P/'run-binding.py': 'b66de5fd78d7e05fe4fb0aed3185a12399ffd5ebd6eaf0e2b3d7d343c0d003a2',
    P/'run-existence.py': '6ddc322eb4cad3f0df3a59dacc7d8b546144801a46ac1365ee22e643810d07bb',
    B/'terminal.json': '33244178345f82cd685772581ab75a43c0cfbf2e77fc3a27cc726ae480ee3777',
    B/'FreeJRootBinding-source.txt': '5d826d8f1cf5ce4a11c45f4a6762ba0729a5e282a1356bce0aeb02f49c58083b',
    B/'stdout': '7a98fb47e18c93ff73921bb43a91efcec67f1bc54e6a671328fcab71fb8ece5f',
    E/'terminal.json': '815778824d17b0689fc6c9439ab51a8cb53167b1f688a1d0d6b8fe567148c897',
    E/'QCube92Existence-source.txt': '62b030d3c8d0ccfac46b4b0c41be58c67dbe96e7794d01c284c317499c456e9d',
    E/'stdout': 'a633c1e3606143777b8f5c3636c45cb13be79e165181f8f046220b29730cca97',
    M/'terminal.json': 'c0e2490784bd82fd8ed179ab0681367dc001d9f99b0791455e836d4922843bc7',
}

def must(ok, message):
    if not ok:
        raise SystemExit(message)

def digest(path):
    return sha256(path.read_bytes()).hexdigest()

for path, value in PIN.items():
    must(digest(path) == value, 'input hash mismatch: ' + str(path))
source = (P/'QCube92Existence.lean').read_text()
binding_source = (P/'FreeJRootBinding.lean').read_text()
must(source.splitlines()[:2] == ['import QCube92Model', 'import FreeJRootBinding'], 'unexpected direct imports')
must('variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]' in source, 'model assumptions mismatch')
statement = ('theorem positive_zero_iff (p : Fin 4 → ℕ) (hbeta : 0 < (p 0 : V)) :\n'
             '    (∃ v : Fin 12 → V, (∀ i, 0 < v i) ∧ InternalZero (graph (integerPorts p)).output v) ↔\n'
             '    (∃ v : Fin 12 → V, (∀ i, 0 < v i) ∧ InternalZero (literal (integerPorts p)) v) := by')
must(statement in source, 'existence theorem statement mismatch')
for marker in ('transform_positive p v hv', 'zero_iff_transformed p v',
               'FreeJSumSquares.zero_iff_literal (integerPorts p)',
               'FreeJRootBinding.first_factor_forces_Y_divisible p v hz (hv 0) hbeta',
               'have hsY : v 6 = q * (q * q) * s', 'have hspos : 0 < s',
               'have htransform : transform p w = v'):
    must(marker in source, 'missing proof ingredient: ' + marker)
binding_statement = ('theorem first_factor_forces_Y_divisible (p : Fin 4 → ℕ) (v : Fin 12 → V)\n'
                     '    (hz : InternalZero (literal (fun j => (p j:ℤ))) v)\n'
                     '    (hJ : 0 < v 0) (hbeta : 0 < (p 0:V)) :\n'
                     '    (1+v 0*(p 0:V))^3 ∣ v 6 := by')
must(binding_statement in binding_source, 'divisibility theorem statement mismatch')
must((P/'FreeJRootBinding.lean').read_bytes() == (old_dir/'FreeJRootBinding.lean').read_bytes(), 'divisibility source differs from earlier source')

prior = D/'reviews/ordinary12-qcube92-model-independent/check.py'
prev = subprocess.run([sys.executable, '-I', '-S', '-B', str(prior)], capture_output=True, check=True)
must(not prev.stderr and json.loads(prev.stdout)['model_attempt_exit'] == 0, 'prior model/algebra/graph review failed')

binding = json.loads((B/'terminal.json').read_text())
existence = json.loads((E/'terminal.json').read_text())
model = json.loads((M/'terminal.json').read_text())
old_receipt = json.loads((old_dir/'replay-receipt.json').read_text())
must(old_receipt['status'] == 'PASS_BOUNDED_FREEJ_FIRST_DIVISIBILITY' and old_receipt['lean_exit_code'] == 0, 'earlier divisibility replay not successful')

def audit_run(receipt, directory, source_name, expected_count, sample_count, minimum):
    must(receipt['exit'] == 0 and receipt['reason'] is None and receipt['before'] == receipt['after'], 'accepted run failed')
    must(receipt['selected_provider_unchanged'], 'recorded provider drift')
    for path, value in receipt['before'].items():
        file = Path(path)
        must(file.is_file() and digest(file) == value, 'direct input mismatch: ' + path)
    must(digest(directory/'stdout') == receipt['stdout_sha256'] and digest(directory/'stderr') == receipt['stderr_sha256'], 'log hash mismatch')
    log = (directory/'stdout').read_text()
    must(not (directory/'stderr').read_bytes() and not any(x in log for x in ('sorryAx','error:','warning:')), 'bad run log')
    command = receipt['command']
    output = Path(command[command.index('-o')+1])
    compiled_source = Path(command[command.index('-o')-1])
    must(digest(output) == receipt['object_sha256'], 'output object mismatch')
    must(digest(compiled_source) == PIN[P/source_name], 'compiled source mismatch')
    must(len(receipt['samples']) == sample_count and min(s['mem_available_kib'] for s in receipt['samples']) == minimum, 'sample mismatch')
    paths = receipt['lean_path'].split(':')
    provider = {}
    for root in paths[:-1]:
        for file in sorted(Path(root).rglob('*.olean')):
            must(file.is_file(), 'missing provider object')
            provider[str(file)] = {'sha256': digest(file), 'realpath': str(file.resolve())}
    must(provider == receipt['selected_provider_before'] and len(provider) == expected_count, 'selected provider mismatch')
    return provider, paths, output

b_provider, b_paths, b_obj = audit_run(binding, B, 'FreeJRootBinding.lean', 74, 4, 18146888)
e_provider, e_paths, e_obj = audit_run(existence, E, 'QCube92Existence.lean', 77, 2, 18518996)
must(max(len(s['lean']) for s in binding['samples']) == 2 and max(len(s['lean']) for s in existence['samples']) == 1, 'sampled Lean process count mismatch')

binding_log = (B/'stdout').read_text()
for name in ('root_rep', 'first_shape', 'rhs_pair', 'first_scaled_norm', 'first_root_quotient',
             'folded_quotient_forces_Y_divisible', 'first_factor_forces_Y_divisible'):
    must("'FreeJRootBinding." + name + "' depends on axioms:" in binding_log, 'missing binding axiom report: ' + name)
expected = ''.join("'FreeJQCube92Existence." + name + "' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
                   for name in ('transform_positive', 'positive_zero_iff'))
must((E/'stdout').read_text() == expected, 'existence axiom report mismatch')
must(e_paths[3:] == b_paths, 'provider order mismatch')
must(e_provider.items() >= b_provider.items(), 'binding providers changed in existence run')
model_obj = Path(model['command'][model['command'].index('-o')+1])
must(Path(e_paths[0]) == model_obj.parent and Path(e_paths[1]) == b_obj.parent, 'direct provider precedence mismatch')
must(e_provider[str(model_obj)]['sha256'] == model['object_sha256'], 'model object not the recorded object')
must(e_provider[str(b_obj)]['sha256'] == binding['object_sha256'], 'fresh divisibility object not the recorded object')
# Direct selected object hashes also match the earlier captured divisibility receipt.
old_links = old_receipt['inner_receipt']['seed_links']
for name in ('Ordinary12FreeJ', 'ArithmeticAdaptiveFirstDivisibility2011'):
    suffix = '/DiophantineConsistency/' + name + '.olean'
    old = ([old_receipt['inner_receipt']['freej_receipt']['object_sha256']]
           if name == 'Ordinary12FreeJ'
           else [v['sha256'] for k, v in old_links.items() if k.endswith(suffix)])
    selected = [v['sha256'] for k, v in b_provider.items() if k.endswith(suffix)]
    must(len(old) == len(selected) == 1 and old == selected, 'direct hash mismatch: ' + name)
    candidates = [Path(root)/suffix.lstrip('/') for root in b_paths if (Path(root)/suffix.lstrip('/')).is_file()]
    must(candidates and digest(candidates[0]) == old[0], 'first matching dependency mismatch: ' + name)
for path, value in PIN.items():
    must(digest(path) == value, 'input changed during review: ' + str(path))
for provider in (b_provider, e_provider):
    for path, info in provider.items():
        file = Path(path)
        must(digest(file) == info['sha256'] and str(file.resolve()) == info['realpath'], 'provider changed during review: ' + path)
must(digest(b_obj) == binding['object_sha256'] and digest(e_obj) == existence['object_sha256'], 'output changed during review')
print(json.dumps({'positive_zero_iff_hypothesis': 'beta positive in IΣ₁ model',
                  'binding_attempt_exit': binding['exit'], 'existence_attempt_exit': existence['exit'],
                  'binding_provider_files': len(b_provider), 'existence_provider_files': len(e_provider),
                  'direct_objects_and_historical_hashes': 'PASS', 'prior_model_review': 'PASS'}, indent=2))
