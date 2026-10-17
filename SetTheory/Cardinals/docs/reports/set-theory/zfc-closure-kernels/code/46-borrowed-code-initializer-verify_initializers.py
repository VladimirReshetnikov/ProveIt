"""Fast offline check of the packaged initializer controls and certificates.

No source repository, network, third-party package, Coq, or Lean is required.
This checks finite artifacts. It does not certify an internal Con(ZFC) theorem.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True

from exact_state_quotient import parse, verify
from odometer_initializer import make_register_clock, make_zero_single_sentinel, simulate


def main():
    parser = argparse.ArgumentParser()
    package = Path(__file__).resolve().parents[2]
    parser.add_argument('--data-dir', type=Path, default=package/'data/initializer')
    parser.add_argument('--machine-dir', type=Path, default=package/'machines/initializer')
    args = parser.parse_args()
    info = json.loads((args.data_dir/'final_controls_summary.json').read_text())
    checks = []
    formula_instances = {}
    negatives = 0
    for record in info['records']:
        raw_data = (args.machine_dir/record['raw_table']).read_bytes()
        q_data = (args.machine_dir/record['quotient_table']).read_bytes()
        assert hashlib.sha256(raw_data).hexdigest() == record['raw_sha256']
        assert hashlib.sha256(q_data).hexdigest() == record['quotient_sha256']
        raw, quotient = parse(raw_data), parse(q_data)
        certificate = json.loads((args.data_dir/record['quotient_certificate']).read_text())
        verify(raw, quotient, certificate)
        assert len(raw)//2 == record['raw_states']
        assert len(quotient)//2 == record['quotient_states']
        assert certificate['state_map'][record['raw_root_state']] == record['quotient_root_state']
        c = record['initializer']
        assert c['counter_bits'] == 9 and c['gap'] == 513 and c['shared_exit']
        seed = c['initial_registers'][0]
        if seed not in formula_instances:
            table, plain = (make_zero_single_sentinel(9) if seed == 0 else
                            make_register_clock(9, nextproof=2))
            formula_instances[seed] = plain, simulate(table, plain)
        plain, predicted = formula_instances[seed]
        assert c['initializer_states'] == plain['initializer_states']-1
        assert c['blank_steps'] == plain['blank_steps']+20
        assert record['blank_run']['head'] == predicted['head']
        assert record['blank_run']['final_ones'] == predicted['final_ones']
        q, h, tape = 0, 0, set()
        for steps in range(c['blank_steps']+1):
            if q == record['raw_root_state']:
                break
            w, d, q = raw[q, int(h in tape)]
            if w:
                tape.add(h)
            else:
                tape.discard(h)
            h += 1 if d == 'R' else -1
        assert q == record['raw_root_state'] and steps == c['blank_steps']
        assert h == predicted['head'] and tape == set(predicted['final_ones'])
        checks.append(dict(table=record['quotient_table'], states=len(quotient)//2,
                           blank_steps=steps, exact_quotient_verified=True,
                           full_tape_boot_verified=True))
        if not negatives:
            # Both a false terminal identification and a wrong output action
            # must be rejected by the row checker, independently of hashes.
            bad = dict(certificate, state_map=certificate['state_map'][:])
            bad['state_map'][-1] = 0
            try:
                verify(raw, quotient, bad)
            except AssertionError:
                negatives += 1
            else:
                raise AssertionError('checker accepted a false terminal map')
            corrupt = dict(quotient)
            w, d, t = corrupt[0, 0]
            corrupt[0, 0] = 1-w, d, t
            try:
                verify(raw, corrupt, certificate)
            except AssertionError:
                negatives += 1
            else:
                raise AssertionError('checker accepted a changed write')
    print(json.dumps(dict(passed=True, controls_checked=len(checks),
                         standalone_formula_instances=len(formula_instances),
                         corrupted_certificates_rejected=negatives,
                         kernel_checked=False, consistency_theorem_claimed=False,
                         results=checks), indent=2))


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('assertions must be enabled')
    main()
