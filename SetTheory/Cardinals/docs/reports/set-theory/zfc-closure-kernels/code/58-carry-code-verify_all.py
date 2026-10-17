#!/usr/bin/env python3
"""Reproduce the final artifact and all checks using only the standard library.

Run from any directory with Python 3.10 or later, without -O. This creates
updated evidence records. It does not rebuild the inherited Lean/Rocq proofs.
"""
from pathlib import Path
import hashlib
import json
import os
import subprocess
import sys
import time
import regenerate
from verify_retiming import expected_boot_ones

ROOT = Path(__file__).resolve().parents[1]

def structural_and_canonical_check():
    baseline, table, canonical, mapping, old, canon = regenerate.construct()
    result = regenerate.verify()
    # A fresh literal run of the delivered canonical table checks the
    # renumbering at the actual blank endpoint as well as row by row.
    state, head, ones = 0, 0, set()
    for tick in range(585431):
        assert state != 250, (tick, 'unexpected halt')
        write, move, state = canonical[state, int(head in ones)]
        if write:
            ones.add(head)
        else:
            ones.discard(head)
        head += 1 if move == 'R' else -1
    assert (state, head, ones) == (92, -3, expected_boot_ones())
    result['canonical_complete_blank_replay'] = 'PASS: 585431 transitions'
    # Exact deterministic state bisimulation with equal writes and moves.
    labels = sorted({q for q, b in canonical})
    partition = {q: 0 for q in labels}
    refinements = []
    while True:
        signatures, updated = {}, {}
        for q in labels:
            sig = tuple((w, d, 'H' if t == 250 else partition[t])
                        for b in (0, 1) for w, d, t in [canonical[q, b]])
            updated[q] = signatures.setdefault(sig, len(signatures))
        refinements.append(len(signatures))
        if updated == partition:
            break
        partition = updated
    assert len(set(partition.values())) == 250
    result['ordinary_exact_bisimulation_classes'] = 250
    result['refinement_counts'] = refinements
    result['minimality_claim'] = 'None: graph and exact bisimulation only.'
    return result

def main():
    if not __debug__:
        raise RuntimeError('Assertions are required; run Python without -O.')
    began = time.monotonic()
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE='1')
    table = ROOT/'machine/zfc_prefix250_old.tm'
    program = ROOT/'sources/Prog254.v'
    evidence = ROOT/'evidence'
    structure = structural_and_canonical_check()
    (evidence/'regeneration-and-canonical-audit.json').write_text(
        json.dumps(structure, indent=2)+'\n')
    commands = [
        ['verify_retiming.py', '--table', str(table), '--output',
         str(evidence/'retiming-verification.json')],
        ['check_prefix_affine.py'],
        ['check_prefix_boxes.py'],
        ['check_candidate250.py', '--table', str(table), '--program', str(program),
         '--output', str(evidence/'final250-literal-audit.json')],
        ['check_local_contracts.py', '--table', str(table), '--output',
         str(evidence/'final250-local-contracts-audit.json')],
        ['check_boot250.py', '--table', str(table), '--output',
         str(evidence/'final250-boot-audit.json')],
    ]
    records = []
    for command in commands:
        start = time.monotonic()
        completed = subprocess.run([sys.executable, '-B',
            str(ROOT/'code'/command[0]), *command[1:]],
            cwd=ROOT, env=env, text=True, capture_output=True)
        if completed.returncode:
            print(completed.stdout)
            print(completed.stderr, file=sys.stderr)
            raise RuntimeError(f'Failed: {command[0]}')
        elapsed = time.monotonic()-start
        print(f'PASS {command[0]} ({elapsed:.2f} s)', flush=True)
        records.append(dict(script=command[0], status='PASS', seconds=elapsed))
    relevant = [ROOT/'machine/zfc_prefix250.tm', table, program,
                ROOT/'sources/instruction-sites.json']
    result = dict(status='PASS', working_states=250, transition_rows=500,
        checks=records, total_seconds=time.monotonic()-began,
        inputs={str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                for p in relevant},
        proof_status='Conventional mathematical proof with reproducible finite '
                     'certificates; no new kernel-checked endpoint in this bundle.')
    (evidence/'reproduction.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()
