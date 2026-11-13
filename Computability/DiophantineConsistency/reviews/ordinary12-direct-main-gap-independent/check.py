#!/usr/bin/env python3
"""Read-only source and artifact review of the conditional direct-gap lemma."""
from hashlib import sha256
import json
import os
from pathlib import Path
import subprocess
import sys

if sys.flags.optimize:
    raise SystemExit('optimized Python refused')

D = Path(__file__).resolve().parents[2]
P = D / 'research/ordinary12-direct-main-probe'
B = D / 'research/ordinary12-qcube92-candidate/observations/halt2-attempt01/terminal.json'
R = [P / f'observations/gapbalance-attempt0{i}' for i in (1, 2, 3)]
PINS = {
    P / 'GAPBALANCE.md': 'ee590dae5b3049de17b3c24c6201cd1f51b16a4a10e92cc1f1a3953b571d7446',
    P / 'DirectMainGapBalance.lean': '75c3912f85260c07f1b2a9d5922cd89960f9d2362b052056c198b9e1516556c3',
    P / 'run-gapbalance.py': 'a90345da101ec8b5b0c971025c66becdd6e3e01d98174a9c0c0352a2aadc1fb7',
    R[0] / 'terminal.json': 'f30d95cf3f270e019874dfaaa72f646c4b278801626b883980a55baa8af26a55',
    R[1] / 'terminal.json': '31ef86f2ffe99e0b9f21ee1dad248e3d5677ed9556b003e3022b379ad04d155d',
    R[2] / 'terminal.json': 'e8d204fd2f7f5a25ab9a457c2260a439775af114e44a3da0b61149c387f98b0c',
    B: '8d2d63d824e117c795566756f60c2b3de4b7bff891cdfe85e8eae728bc38556f',
}

def need(condition, message):
    if not condition:
        raise SystemExit(message)

def sha(path):
    return sha256(Path(path).read_bytes()).hexdigest()

def verify_pins():
    for path, value in PINS.items():
        need(sha(path) == value, 'input hash mismatch: ' + str(path))

verify_pins()
source = (P / 'DirectMainGapBalance.lean').read_text()
need(source.splitlines()[0] == 'import DirectMainProjection', 'wrong direct import')
for fragment in (
    'variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]',
    'theorem gap_of_balance (U X a c H G R k main w : V)',
    '(hU : 0<U) (hR : R+1≤k)',
    '(hbalance : U*(X+a*c)+H*(U*G+R+1)=H*k+U*main)',
    '(hmain : (a+1)*c<main) (hgrowth : X+H*w<c) : w<G',
    'mul_le_mul_of_nonneg_left hR',
    'le_of_mul_le_mul_left hmul hU',
    'lt_of_mul_lt_mul_left hscale',
):
    need(fragment in source, 'missing statement or proof step: ' + fragment)
need('set_option linter.' not in source, 'unexpected local linter suppression')

# The exact balance, the main-root lower bound, and all variables positive do
# not alone imply w<G: the separately assumed growth bound fails here. This
# is an abstract arithmetic instance, not a claimed zero of the draft graph.
U, X, a, c, H, G, rank, k, main, w = 1, 2, 1, 1, 7, 1, 1, 2, 10, 2
need(U > 0 and rank + 1 <= k and (a + 1) * c < main, 'counterexample assumptions')
need(U * (X + a*c) + H * (U*G + rank + 1) == H*k + U*main, 'counterexample balance')
need(not X + H*w < c and not w < G, 'counterexample must omit growth')

receipts = [json.loads((folder / 'terminal.json').read_text()) for folder in R]
for index, (folder, receipt) in enumerate(zip(R, receipts), 1):
    need(receipt['reason'] is None and receipt['union_count'] == 1291 and receipt['union_unchanged'], 'receipt status')
    need(sha(folder / 'source.txt') == receipt['source_sha256'] == receipt['source_after'], 'source snapshot mismatch')
    need(receipt['runner_sha256'] == receipt['runner_after'] == sha(P / 'run-gapbalance.py'), 'runner mismatch')
    need(receipt['lean_sha256'] == receipt['lean_after'] == sha(receipt['command'][0]), 'Lean binary mismatch')
    need(receipt['base_receipt_sha256'] == sha(B), 'base receipt mismatch')
    need(sha(folder / 'stdout') == receipt['stdout_sha256'] and sha(folder / 'stderr') == receipt['stderr_sha256'], 'log hash mismatch')
    need(not (folder / 'stderr').read_bytes(), 'unexpected stderr')
    need(receipt['projection_producer_sha256'] == 'e2510b3deeebc7d4067710ad1f3210191e6189050a9b3bfa8641f9a9a2bf3182', 'projection producer hash')
    need(sha(Path(receipt['lean_path'].split(':')[0]) / 'DirectMainProjection.olean') == receipt['projection_producer_sha256'], 'projection import resolution')
    out = Path(receipt['output_root']) / 'DirectMainGapBalance.olean'
    if receipt['object_sha256'] is not None:
        need(sha(out) == receipt['object_sha256'], 'output object mismatch')
    log = (folder / 'stdout').read_text()
    if index == 1:
        need(receipt['exit'] != 0 and 'error:' in log and 'sorryAx' in log, 'attempt01 failure not preserved')
    elif index == 2:
        need(receipt['exit'] == 0 and log.count('warning:') == 1 and 'Variable name `hH`' in log, 'attempt02 warning mismatch')
    else:
        expected = "'DirectMainGapBalance.gap_of_balance' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
        need(receipt['exit'] == 0 and log == expected, 'attempt03 output mismatch')
        need(receipt['source_sha256'] == sha(P / 'DirectMainGapBalance.lean'), 'accepted source differs')

base = json.loads(B.read_text())
lib = Path(receipts[2]['lean_path'].split(':')[1])
def verify_union():
    actual = {x.relative_to(lib).as_posix(): x for x in lib.rglob('*') if x.is_file()}
    need(len(actual) == 1291 and set(actual) == set(base['union']), 'selected union membership')
    for name, path in actual.items():
        rec = base['union'][name]
        need(path.is_symlink() and os.readlink(path) == rec['link'] and
             str(path.resolve(strict=True)) == rec['resolved'] and sha(path) == rec['sha256'],
             'selected object changed: ' + name)

verify_union()
prior = subprocess.run([sys.executable, '-I', '-S', '-B',
    str(D / 'reviews/ordinary12-direct-main-independent/check.py')], capture_output=True, check=True)
need(not prior.stderr and json.loads(prior.stdout)['status'] == 'PASS', 'prior model review failed')
verify_union()
verify_pins()
need(sha(Path(receipts[2]['output_root']) / 'DirectMainGapBalance.olean') == receipts[2]['object_sha256'], 'accepted output drift')
print(json.dumps({
    'status': 'PASS',
    'explicit_growth_assumption': True,
    'abstract_counterexample_without_growth': True,
    'attempts': ['error', 'warning-rejected', 'accepted'],
    'selected_union_objects': 1291,
    'prior_projection_review': 'PASS',
    'preexisting_lean_processes': len(receipts[2]['preflight']['lean']),
    'maximum_sampled_lean_processes': max(len(x['lean']) for x in receipts[2]['samples']),
    'scope': 'conditional model lemma; no 90-graph or iPRA theorem',
}, indent=2))
