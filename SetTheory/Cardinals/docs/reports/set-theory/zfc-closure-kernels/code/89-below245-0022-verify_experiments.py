#!/usr/bin/env python3
"""Quick, solver-free replay of the new theory and negative certificates."""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]


def main():
    if not __debug__:
        raise RuntimeError('Assertions must remain enabled; do not use -O.')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    out = args.output.resolve() if args.output else Path(tempfile.mkdtemp(prefix='zfc245-experiments-'))
    if out.exists() and any(out.iterdir()):
        raise ValueError('The output directory must be new or empty.')
    out.mkdir(parents=True, exist_ok=True)
    start = time.monotonic()
    env = os.environ.copy()
    env['PYTHONDONTWRITEBYTECODE'] = '1'

    def run(name, *command):
        result = subprocess.run([sys.executable, '-B', *map(str, command)],
            cwd=ROOT, env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        (out / (name + '.log')).write_text(result.stdout)
        if result.returncode:
            raise RuntimeError(name + ' failed:\n' + result.stdout[-5000:])
        print('PASS: ' + name, flush=True)
        return result.stdout

    encoded = json.loads(run('exact-bound-and-grammar-audits',
                             ROOT / 'experiments/encoding/quick_verify.py'))
    assert encoded['status'] == 'PASS'
    certificate = encoded['certificate']
    assert certificate['grammar_lower_bound'] == certificate['witness_rules'] == 128
    assert certificate['tree_nodes'] == 9 and certificate['universe_reconstructed']
    assert not certificate['scanner_guard_used'] and not certificate['optimizer_imported']
    assert len(encoded['abstract_grammar_audits']) == 9
    (out / 'encoding.json').write_text(json.dumps(encoded, indent=2) + '\n')

    run('64-source-variants', ROOT / 'theory/converse_theory.py',
        '--output', out / 'converse_source.json')
    sources = json.loads((out / 'converse_source.json').read_text())
    assert sources == json.loads((ROOT / 'theory/converse_source.json').read_text())
    variants = sources['anchored_variants']
    assert len(variants) == 64
    assert all(v['finest_operation_count'] == 1270 for v in variants.values())
    assert all(v['full_macro_stack_contract_checked'] and
               v['single_destructive_u_read_checked'] for v in variants.values())
    assert min(v['minimum_dictionary_calls'] for v in variants.values()) == 493
    assert sum(not v['C_G_membership_converse'] for v in variants.values()) == 32

    run('all-start-blank-obstruction', ROOT / 'experiments/runtime/code/verify_blank_escape.py',
        '--output', out / 'blank-obstruction.json')
    blank = json.loads((out / 'blank-obstruction.json').read_text())
    assert blank['status'] == 'PASS_FINITE_PREFIXES_AND_INDUCTIVE_ESCAPE'
    assert (blank['provable_escape_starts'], blank['halting_starts'], blank['unresolved_starts']) == (243, 2, 0)
    assert blank == json.loads((ROOT / 'experiments/runtime/results/spare0_blank_certificate.json').read_text())
    run('spare-zero-local-inductions', ROOT / 'experiments/runtime/code/verify_spare_zero.py',
        '--package', ROOT / 'vendor/routing245', '--output', out / 'spare-zero-local.json')
    local = json.loads((out / 'spare-zero-local.json').read_text())
    assert local['status'] == 'PASS_LOCAL_MACROS'
    # This quick replay checks the stored expensive proof's identity and
    # completeness. It does not claim to reexecute the whole-frame search.
    stored = json.loads((ROOT / 'experiments/runtime/results/spare0_full_symbolic_result.json').read_text())
    table = ROOT / 'experiments/runtime/inputs/spare0_245_old.tm'
    assert stored['status'] == 'PASS' and stored['complete']
    assert stored['table_sha256'] == hashlib.sha256(table.read_bytes()).hexdigest()
    assert stored['counts']['cases'] == len(stored['cases']) == 8391
    assert stored['counts']['symbolic_rules'] == 2312645 and len(stored['rows']) == 490
    summary = dict(status='PASS_RESEARCH_EXPERIMENT_REPLAY', exact_grammar_lower_bound=128,
        bounded_model_only=True, source_variants=64, same_numeric_calculus_variants=32,
        best_dictionary_calls=493, baseline_dictionary_calls=533,
        elementary_blank_escapes=243, finite_halting_starts=2,
        spare_zero_local_inductions_replayed=True, stored_whole_frame_complete=True,
        expensive_whole_frame_reexecuted=False, seconds=round(time.monotonic() - start, 3),
        output=str(out), sub245_machine_found=False)
    (out / 'verification.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps(summary, indent=2))


if __name__ == '__main__':
    main()
