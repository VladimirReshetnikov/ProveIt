#!/usr/bin/env python3
"""Read-only finite verification of the delivered ZFC Diophantine packet.

Run with Python 3.10 or later. Only the standard library is required.
--write-report writes verification.json after every check has succeeded.
No enormous coefficient, complete window list, or Pell witness is expanded.
The mathematical semantic proof is in paper/fixed_input_zfc.pdf.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
PIN = 'cdd582bec13f908df3711fa9e05d1ddac368a5db'
sys.dont_write_bytecode = True


def require(condition, message):
    if not condition:
        raise ValueError(message)


def run_json(path):
    command = [sys.executable, '-B']
    if sys.flags.optimize:
        command.append('-O')
    command.append(str(ROOT/path))
    completed = subprocess.run(command, cwd=ROOT, capture_output=True,
                               text=True, check=True)
    data = json.loads(completed.stdout)
    require(data['status'] == 'PASS', 'failed subcheck: '+str(path))
    return data


def source_hashes():
    sources = json.loads((ROOT/'inherited_files.json').read_text())
    for item in sources:
        raw = (ROOT/item['archive_path']).read_bytes()
        require(hashlib.sha256(raw).hexdigest() == item['sha256'],
                'pinned file changed: '+item['archive_path'])
    return {'status': 'PASS', 'source_commit': PIN,
            'checked_inherited_files': len(sources)}


def machine_and_coefficients():
    # Import only the delivered sibling programs. Their main blocks are not run.
    sys.path.insert(0, str(ROOT/'coefficients'))
    import fixed_machine as fm
    import coefficient_recipe as cr
    import verify_bridge as vb
    m = fm.Machine()
    receipt = fm.verify()
    require(receipt == json.loads((ROOT/'coefficients/machine_receipt.json').read_text()),
            'normalized machine receipt changed')
    table = dict(states=list(m.states), alphabet=list(m.alphabet),
                 start=fm.Q0, halt=fm.HALT, blank=0,
                 original_state_order=list(m.source_states),
                 transitions=[[q, a, *m.delta(q, a)]
                              for q in m.states for a in m.alphabet],
                 row_format=['state', 'read', 'next_state', 'write', 'move'])
    require(table == json.loads((ROOT/'coefficients/normalized_machine.json').read_text()),
            'emitted normalized machine differs from exact construction')
    spec = cr.specification()
    require(spec == json.loads((ROOT/'coefficients/coefficient_specification.json').read_text()),
            'coefficient specification changed')
    expected_ports = {'Bm1', 'Kconstant', 'MC', 'MF', 'W0', 'W0plus2d'}
    require(expected_ports <= set(spec['definitions']), 'missing coefficient port')
    for path in sorted((ROOT/'arithmetic').glob('*.json')):
        packet = json.loads(path.read_text())
        if 'fixed_numerals' in packet:
            require(set(packet['fixed_numerals']) == expected_ports,
                    'unexpected fixed coefficient ports: '+path.name)
    bridge = dict(machine=receipt, cross_counter=vb.crosscheck_counter(),
                  coefficient_bounds=vb.verify_coefficient_bounds(),
                  toy_coefficients=vb.verify_toy_materialization())
    require(bridge == json.loads((ROOT/'coefficients/bridge_verification.json').read_text()),
            'bridge receipt changed')
    return {'status': 'PASS', **bridge}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write-report', action='store_true')
    args = parser.parse_args()
    report = {'status': 'PASS', 'source_commit': PIN,
              'scope': ('Finite source, machine, compiler-parameter and algebra checks. '
                        'No fresh Lean/Rocq endpoint build or kernel proof of the new '
                        'Diophantine equivalence; no decision of ZFC consistency.'),
              'pinned_sources': source_hashes(),
              'positive_arithmetic': run_json(Path('arithmetic/build_fixed_sources.py')),
              'closed_forms': run_json(Path('arithmetic/verify_closed_forms.py')),
              'integer_arithmetic': run_json(Path('arithmetic/build_integer_sources.py')),
              'local_identities': run_json(Path('proofs/check_local_identities.py')),
              'machine_and_coefficients': machine_and_coefficients()}
    if args.write_report:
        (ROOT/'verification.json').write_text(json.dumps(report, indent=2)+'\n')
    print('PASS: pinned inherited files; seven positive circuits; two integer circuits;')
    print('      exact local identities; table isomorphism and folded simulation;')
    print('      emitted machine; window census; coefficient bounds and toy compiler.')
    print('Scope: finite/algebra verification; the universal semantic proof is in the paper.')


if __name__ == '__main__':
    main()
