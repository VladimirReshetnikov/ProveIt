#!/usr/bin/env python3
"""Replay the finite evidence in this research archive; no <196 claim."""
from pathlib import Path
import hashlib, json, subprocess, sys, tempfile

ROOT = Path(__file__).resolve().parent
if not __debug__:
    raise SystemExit('Run without -O: assertions in the inherited checkers are required.')

def require(test, msg):
    if not test:
        raise RuntimeError(msg)

def run(rel, *args):
    p = subprocess.run([sys.executable, str(ROOT / rel), *map(str, args)],
                       cwd=ROOT, text=True, capture_output=True)
    if p.returncode:
        raise RuntimeError(f'{rel} failed:\n{p.stdout}\n{p.stderr}')
    return p.stdout

manifest = json.loads((ROOT / 'MANIFEST.json').read_text())
for rel, digest in manifest['sha256'].items():
    p = ROOT / rel
    require(p.is_file(), f'Missing file: {rel}')
    require(hashlib.sha256(p.read_bytes()).hexdigest() == digest,
            f'Changed input or artifact: {rel}')
print(f"PASS: {len(manifest['sha256'])} artifact hashes.")

with tempfile.TemporaryDirectory(prefix='pa-consistency-replay-') as td:
    td = Path(td)
    run('comparison/compare_designs.py', '--output', td / 'comparison.json')
    comp = json.loads((td / 'comparison.json').read_text())
    require(len(comp['tables']) == 30, 'Wrong table census')
    require(comp['incoming_u208_graph_classes'] == 20, 'Wrong U208 graph census')
    require(len(comp['isomorphism_witnesses']) == 16, 'Missing isomorphism witnesses')
    require(len(comp['accepted_helper_equivalences']) == 18, 'Missing helper certificates')
    print('PASS: 30 tables, 20 U208 graph classes, 16 isomorphism maps, 18 helper proofs, 2 startups.')

    hilbert = json.loads(run('logic/check_split_head.py'))
    counts = [hilbert[x]['nodes'] for x in ['new_to_old', 'old_to_new', 'old_to_explosion']]
    require(counts == [77, 77, 17], f'Unexpected Hilbert certificate counts: {counts}')
    run('logic/check_frozen_certificates.py')
    print('PASS: split-head Hilbert certificates (77, 77, 17 nodes).')

    controls = json.loads(run('logic/check_rewrite_countermodels.py'))
    require(controls['retained_rewrite_controls'] == 8000, 'Wrong rewrite controls')
    require(controls['omit_head3_separator_controls'] == 23056, 'Wrong first separator controls')
    require(controls['omit_head4_separator_controls'] == 23056, 'Wrong second separator controls')
    print('PASS: explicit rewrite counterexamples and finite separator controls.')

    run('combinations/emitter189.py', '--output', td / 'emitter189.json')
    print('PASS: 201-token baseline and 189-token joint emitter reconstruction.')
    run('combinations/joint_dictionary/check_obstruction.py')
    print('PASS: exact seven-zero obstruction for the fixed 66-cost dictionary.')
    run('physical_search/replay.py', '--quick', '--output', td / 'physical-baseline')
    phys = json.loads((td / 'physical-baseline' / 'receipt.json').read_text())
    require(phys['context_summary']['count'] == 2412, 'Wrong source-context census')
    print('PASS: 4,959 baseline symbolic cases, exact startup, and 2,412 radius-two contexts.')

comb = json.loads((ROOT / 'combinations/original_receipts.json').read_text())
require(len(comb) == 12, 'Wrong combination census')
require(all(x['symbolic_ok'] for x in comb), 'A retained combination failed its recorded symbolic check')
require(min(x['best_states'] for x in comb) == 196, 'Unexpected retained minimum')
print('PASS: recorded 12-way combination scope and minimum state count (not a rerun).')

for mode, trials, nodes in [('split_head', 50000, 74), ('split_positive', 75000, 74), ('head_padding', 50000, 68)]:
    r = json.loads((ROOT / 'results' / f'{mode}_receipt.json').read_text())
    require(r['trials'] == trials and r['best_raw_nodes'] == nodes, f'Wrong grammar receipt: {mode}')
    require(r['baseline_states'] == 196 and r['priced_layouts'] == 0 and r['best_physical'] is None,
            f'Misrepresented physical status: {mode}')
print('PASS: finite grammar search receipts distinguish raw nodes from physical machines.')
print('RESULT: reproducible research evidence; no verified sub-196 machine or new full PA biconditional.')
