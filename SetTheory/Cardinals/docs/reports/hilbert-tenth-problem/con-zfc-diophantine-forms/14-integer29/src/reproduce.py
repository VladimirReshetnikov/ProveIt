#!/usr/bin/env python3
"""Rebuild and audit the delivered Diophantine specifications offline.

Finite audits supplement the ordinary proofs. They do not prove the full
compiler theorem, evaluate the astronomical coefficient integers, replay
Lean/Rocq, or supply an accepting K215 witness.
"""
from __future__ import annotations

import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / 'data'
VENDOR = ROOT / 'vendor' / 'blank67'


def require(ok, message):
    if not ok:
        raise ValueError(message)


def read(path):
    return json.loads(path.read_text())


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def run(script, *args):
    cp = subprocess.run([sys.executable, str(script), *map(str, args)],
                        cwd=ROOT, text=True, capture_output=True)
    if cp.returncode:
        raise RuntimeError(cp.stdout + cp.stderr)
    return cp.stdout


def main():
    receipt = {
        'status': 'PASS',
        'snapshot': '3b201cdea32d2c816f5f3d20734051f25fd3ef14',
        'scope': {
            'exact_gate_algebra_and_counts': True,
            'source_and_machine_hashes': True,
            'finite_pell_and_local_tableau_diagnostics': True,
            'new_lean_or_rocq_formalization': False,
            'giant_coefficients_materialized': False,
            'all_k215_windows_enumerated': False,
            'accepting_k215_witness_exhibited': False,
            'consistency_decided': False,
        },
    }
    manifest = read(ROOT / 'SOURCE_MANIFEST.json')
    for row in manifest['files']:
        path = ROOT / row['artifact_path']
        require(hashlib.sha256(path.read_bytes()).hexdigest() == row['sha256'],
                'Source hash mismatch: ' + row['artifact_path'])
    receipt['pinned_source_hashes_checked'] = len(manifest['files'])
    print('Pinned source hashes: PASS', flush=True)

    with tempfile.TemporaryDirectory(prefix='con_zfc_rebuild_') as work:
        work = Path(work)
        run(ROOT / 'src' / 'build_ordinary.py',
            '--base', VENDOR / 'fixed_blank_system_61.json', '--out', work)
        run(ROOT / 'src' / 'build_integer29.py',
            '--ordinary-dir', work, '--normalized-dir', VENDOR,
            '--output-dir', work)
        names = [
            'blank_ordinary_system61', 'blank_ordinary_poly69',
            'blank_ordinary_sos78', 'blank_ordinary_quartic33',
            'blank_ordinary_integer29_system113',
            'blank_ordinary_integer29_poly121',
            'blank_ordinary_integer29_sos130',
            'blank_normalized_integer29_poly119',
            'blank_normalized_integer29_poly120',
        ]
        for name in names:
            require(read(work / (name + '.json')) == read(DATA / (name + '.json')),
                    'Rebuilt packet mismatch: ' + name)
        receipt['reproduced_packets'] = names
        receipt['integer_substitution_audit'] = read(work / 'integer29_verification.json')
        print('Nine equation packets rebuilt identically: PASS', flush=True)

        audit = load('ordinary_audit', ROOT / 'src' / 'verify_combinations.py')
        receipt['ordinary_audits'] = {
            name: audit.circuit_check(read(work / (name + '.json')))
            for name in names[:3]
        }
        receipt['quadratic_audit'] = audit.quadratic_check(
            read(work / 'blank_ordinary_quartic33.json'))
        # Also check the complete graph and ledgers of every integer circuit,
        # without repeating the degree calculations already run by its emitter.
        integer_graphs = {}
        for name in names[4:]:
            packet = read(work / (name + '.json'))
            known = set(packet['witnesses'] + packet['fixed_numerals'])
            require(len(packet['witnesses']) == 29, 'Incorrect integer arity')
            produced = set()
            mul = add = 0
            for reg, op, left, right in packet['source']:
                require(reg not in known and op in ('+', '-', '*'), 'Invalid gate')
                require(all(type(v) is int or v in known for v in (left, right)),
                        'Unknown operand')
                known.add(reg)
                produced.add(reg)
                mul += op == '*'
                add += op != '*'
            require(packet['ledger'] == dict(operations=mul + add, M=mul, A=add),
                    'Integer ledger mismatch')
            needed = set([packet['output']] if 'output' in packet else
                         [v for row in packet['comparisons'] for v in row
                          if isinstance(v, str)])
            for reg, _, left, right in reversed(packet['source']):
                if reg in needed:
                    needed.update(v for v in (left, right) if isinstance(v, str))
            require(produced <= needed and
                    set(packet['witnesses'] + packet['fixed_numerals']) <= needed,
                    'Dead integer gate or port')
            integer_graphs[name] = dict(all_gates_and_ports_live=True, **packet['ledger'])
        receipt['integer_graphs'] = integer_graphs
        run(ROOT / 'src' / 'check_odd_multiplier.py',
            '--output', work / 'odd.json')
        receipt['odd_multiplier_diagnostics'] = read(work / 'odd.json')
        print('Circuit, degree, quartic, and odd-multiplier audits: PASS', flush=True)

        sys.path.insert(0, str(VENDOR))
        import verify_k215
        import blank_helical
        import count_blank_alphabet
        import compiler_constants
        rows = verify_k215.parse_tm((DATA / 'k215.tm').read_bytes())
        expected_rows = read(VENDOR / 'k215_transitions.json')
        # The exact byte hash is enforced by parse_tm. The exported JSON is
        # retained as provenance; all dynamic checks use the literal table.
        require(len(rows) == 430, 'Transition count')
        receipt['machine_binding'] = {
            'sha256': hashlib.sha256((DATA / 'k215.tm').read_bytes()).hexdigest(),
            'states': 215, 'transition_rows': 430,
            'first_transition': list(rows[0]),
        }
        require(compiler_constants.specification() ==
                read(VENDOR / 'k215_constants.json')['constants'],
                'Coefficient recipe changed')
        receipt['coefficient_layout'] = compiler_constants.verify()
        receipt['local_tableau'] = blank_helical.verify(rows)
        receipt['alphabet_count'] = count_blank_alphabet.verify(rows, True)
        require(receipt['alphabet_count']['lifted_alphabet_cardinality'] ==
                1420903358357108792377, 'Incorrect window cardinality')
        print('Coefficient recipe, local windows, and exact alphabet census: PASS', flush=True)

    (ROOT / 'VERIFICATION.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print('All selected audits passed. See VERIFICATION.json for scope.', flush=True)


if __name__ == '__main__':
    main()
