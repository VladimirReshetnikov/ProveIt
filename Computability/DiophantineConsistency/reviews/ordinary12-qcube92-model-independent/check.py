#!/usr/bin/env python3
"""Read-only review of the q-cube model theorem and its author receipt."""
from hashlib import sha256
import json
from pathlib import Path
import subprocess
import sys

D = Path(__file__).resolve().parents[2]
P = D/'research/ordinary12-qcube92-candidate'
O = P/'observations/model-attempt01'
A = P/'observations/attempt05'
PIN = {
    P/'QCube92Model.lean': '4f3b882c9ff4fa10672437797864bb64bfd4bb4355a7b837a5ee3f84c799acea',
    P/'MODEL.md': 'ac606c0114ed4d8a32697ad73a067be2cdf62ddf1a07ede037b78cbee7714f9e',
    P/'run-model.py': '51e414cc6f3e7d7f8cf2e58d2eeeec1eb687a6f0e71807a254e1b1a2abb80916',
    P/'QCube92.lean': 'd79cdacdeb36d6d080d71284b501d651be80312ae85edb43c270f5360244e8aa',
    P/'candidate.json': '3a21d323adb96788a4b46c0b33800e07f2d1cb708b5c3c53ab709f6e186acee3',
    O/'terminal.json': 'c0e2490784bd82fd8ed179ab0681367dc001d9f99b0791455e836d4922843bc7',
    O/'QCube92Model-source.txt': '4f3b882c9ff4fa10672437797864bb64bfd4bb4355a7b837a5ee3f84c799acea',
    O/'stdout': '68c1d83282c130a3240b08945ae716826548488e70ef8254f9bdb0e1e17717ea',
    A/'terminal.json': 'aaf66f7a256fb37d8412a8b92e595314ff42c097a5c83af0fbcf421f587f6d59',
}

def must(ok, message):
    if not ok:
        raise SystemExit(message)

def digest(path):
    return sha256(path.read_bytes()).hexdigest()

for file, value in PIN.items():
    must(digest(file) == value, 'input hash mismatch: ' + str(file))
source = (P/'QCube92Model.lean').read_text()
receipt = json.loads((O/'terminal.json').read_text())
algebra = json.loads((A/'terminal.json').read_text())
must(source.splitlines()[0] == 'import QCube92', 'unexpected direct import')
must('variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]' in source, 'model hypothesis mismatch')
must('def integerPorts (p : Fin 4 → ℕ) : Fin 4 → ℤ := fun i => (p i : ℤ)' in source, 'port interpretation mismatch')
transform = ('def transform (p : Fin 4 → ℕ) (v : Fin 12 → V) : Fin 12 → V :=\n'
             '  let q := 1 + v 0 * (p 0 : V)\n  Function.update v 6 (q * (q * q) * v 6)')
must(transform in source, 'valuation transformation mismatch')
statement = ('theorem zero_iff_transformed (p : Fin 4 → ℕ) (v : Fin 12 → V) :\n'
             '    InternalZero (graph (integerPorts p)).output v ↔\n'
             '      InternalZero (FreeJSumSquares.squareLiteral (integerPorts p)) (transform p v) := by')
must(statement in source, 'model theorem statement mismatch')
for ingredient in ('internalZero_iff', 'sq_nonneg', 'mul_self_eq_zero.mp', 'cube_ne_zero',
                   'rw [lift_cast, first_eval, main_eval, ordinary_eval]', 'mul_eq_zero'):
    must(ingredient in source, 'missing inspected proof ingredient: ' + ingredient)

# The separately reviewed algebra source and 92-row graph binding remain valid.
prior = D/'reviews/ordinary12-qcube92-algebra-independent/check.py'
external = subprocess.run([sys.executable, '-I', '-S', '-B', str(prior)], capture_output=True, check=True)
prior_result = json.loads(external.stdout)
must(not external.stderr and prior_result['graph_rows'] == 92 and prior_result['attempt05_exit'] == 0, 'prior algebra review failed')

must(receipt['exit'] == 0 and receipt['reason'] is None and receipt['before'] == receipt['after'], 'model attempt not successful')
must(receipt['selected_provider_unchanged'], 'recorded provider drift')
for path, value in receipt['before'].items():
    file = Path(path)
    must(file.is_file() and digest(file) == value, 'direct input mismatch: ' + path)
must(digest(O/'stdout') == receipt['stdout_sha256'] and digest(O/'stderr') == receipt['stderr_sha256'], 'model log hash mismatch')
expected = ''.join("'FreeJQCube92Model." + name + "' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
                   for name in ('lift_cast', 'cube_ne_zero', 'zero_iff_transformed'))
must((O/'stdout').read_text() == expected and not (O/'stderr').read_bytes(), 'unexpected axiom report')
must(not any(x in (O/'stdout').read_text() for x in ('sorryAx', 'error:', 'warning:')), 'bad log content')
command = receipt['command']
output = Path(command[command.index('-o')+1])
compiled_source = Path(command[command.index('-o')-1])
must(digest(output) == receipt['object_sha256'], 'model output hash mismatch')
must(digest(compiled_source) == PIN[P/'QCube92Model.lean'], 'compiled source mismatch')
must(len(receipt['samples']) == 5 and min(s['mem_available_kib'] for s in receipt['samples']) == 18488796, 'sample observation mismatch')
must(all(len(s['lean']) <= 1 for s in receipt['samples']), 'sample Lean count mismatch')
paths = receipt['lean_path'].split(':')
must(paths[1:] == algebra['lean_path'].split(':'), 'model provider order differs from algebra run')
provider = {}
for root in paths[:-1]:
    for file in sorted(Path(root).rglob('*.olean')):
        must(file.is_file(), 'missing selected object')
        provider[str(file)] = {'sha256': digest(file), 'realpath': str(file.resolve())}
must(provider == receipt['selected_provider_before'] and len(provider) == 75, 'selected provider inventory mismatch')
must(algebra['selected_provider_before'].items() <= provider.items(), 'previous selected provider changed')
direct = Path(paths[0])/'QCube92.olean'
must(str(direct) in provider and provider[str(direct)]['sha256'] == algebra['object_sha256'], 'algebra object mismatch')
for file, value in PIN.items():
    must(digest(file) == value, 'input changed during review: ' + str(file))
for path, info in provider.items():
    file = Path(path)
    must(digest(file) == info['sha256'] and str(file.resolve()) == info['realpath'], 'provider changed during review: ' + path)
must(digest(output) == receipt['object_sha256'], 'model output changed during review')
print(json.dumps({'model_attempt_exit': receipt['exit'], 'model_object_sha256': receipt['object_sha256'],
                  'provider_files_rehashed': len(provider), 'prior_algebra_object_matches': True,
                  'prior_algebra_source_and_graph_review': 'PASS', 'model_claim': 'transformed valuation iff'}, indent=2))
