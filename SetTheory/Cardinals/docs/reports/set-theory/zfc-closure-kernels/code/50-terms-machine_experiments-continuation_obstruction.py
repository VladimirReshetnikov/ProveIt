#!/usr/bin/env python3
"""Audit a finite decoder rewrite and a functional-encoding obstruction.

The 34-transition rewrite is a literal finite-window certificate. The
residual collision concerns the ORIGINAL register program at two PCs. It
does not claim that the subsequently mutated TM follows those residuals.
Additional literal mutant prefixes are saved separately to expose that gap.
No blank reachability, nonhalting, lower bound, or equivalence is asserted.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import sys


def load(name, file):
    spec = importlib.util.spec_from_file_location(name, file)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    assert __debug__, 'Assertions must remain enabled'
    base = args.repo / 'Computability/BusyBeaver/Research/ZFC'
    sys.path.insert(0, str(base))
    audit = load('continuation_obstruction_audit', base / 'candidate252_independent_audit.py')
    continuations = load('continuation_obstruction_original', base / 'permutation252_continuations.py')
    table_file = base / 'candidate-permutation252/zfc_permutation252_old.tm'
    numeric = audit.read_table(table_file.read_bytes())
    assert hashlib.sha256(audit.encode(numeric)).hexdigest() == audit.EXPECTED_SHA
    changed = {row: (w, d, 252 if target == 204 else target)
               for row, (w, d, target) in numeric.items() if row[0] != 204}
    assert len(changed) == 502
    program = args.repo / 'lib/jeff-busy-beaver-zfc254/ZF/m254/coq/tm/Prog254.v'
    nodes = continuations.read_nodes(program)
    # The scanned positions are recorded before every transition. An arbitrary
    # completion outside this finite window cannot affect this exact trace.
    state, head = 96, 0
    ones = {-1} | set(range(10))
    local_trace = []
    for tick in range(34):
        read = int(head in ones)
        w, direction, following = changed[state, read]
        local_trace.append({'step': tick, 'state': state, 'head': head,
                            'read': read, 'write': w, 'move': direction,
                            'next_state': following})
        if w:
            ones.add(head)
        else:
            ones.discard(head)
        head += 1 if direction == 'R' else -1
        state = following
    assert (state, head, ones) == (96, 0, {-1} | (set(range(10)) - {6}))
    scanned = [step['head'] for step in local_trace]
    window = [min(scanned), max(scanned)]
    assert window == [-11, 6]
    collision = []
    for n, k in ((1, 1), (2, 0)):
        registers = (0, 0, 0, 0, n, 0, k, 0, 0)
        expected = continuations.original_residual_trace(nodes, '11111111', registers, 100)
        alternate = continuations.original_residual_trace(nodes, '1111110111', registers, 100)
        assert expected['status'] == alternate['status'] == 'main_join'
        assert expected['registers_at_join'] == [0, 0, 0, 0, n + k, 0, 0, 0, 0]
        assert alternate['registers_at_join'] == [0, n, 0, 0, n + k, 0, 0, 0, 0]
        assert len(expected['trace']) - 1 == 3 * k + 1
        assert len(alternate['trace']) - 1 == 7 * n + 3 * k + 3
        collision.append({'initial_registers': list(registers), 'n': n, 'k': k,
                          'expected_original_residual': expected,
                          'alternate_original_residual': alternate})
    assert collision[0]['expected_original_residual']['registers_at_join'] == \
           collision[1]['expected_original_residual']['registers_at_join']
    assert collision[0]['alternate_original_residual']['registers_at_join'] != \
           collision[1]['alternate_original_residual']['registers_at_join']
    literal_prefixes = []
    for n, k in ((1, 1), (2, 0)):
        logical = [0, 0, 0, 0, n, 0, k, 0, 0]
        physical = [logical[audit.NEWPHYS.index(r)] for r in range(9)]
        state, head = 96, 0
        ones = audit.paint('1111111111', 40, physical, [0, 1, 0], 0)
        frames = []
        outcome = 'fuel_limit'
        for tick in range(1, 20001):
            if state == 254:
                outcome = 'halt'
                break
            w, direction, state = changed[state, int(head in ones)]
            if w:
                ones.add(head)
            else:
                ones.discard(head)
            head += 1 if direction == 'R' else -1
            if state != 96:
                continue
            clean = [frame for frame in continuations.frames(nodes, ones, head)
                     if frame['decoded']['clean']]
            if clean:
                frame = clean[0]
                frames.append({'ticks': tick, 'head': head, **frame})
                if frame['decoded']['consumed'] == '000':
                    outcome = 'main_join_frame'
                    break
                if len(frames) == 20:
                    outcome = 'twenty_clean_frames'
                    break
        assert frames[0]['ticks'] == 34 and frames[0]['pc'] == '1111110111'
        assert len(frames) >= 2 and frames[1]['pc'] == '111'
        literal_prefixes.append({'input_logical': logical, 'prepared_pc': '1111111111',
                                 'input_spares': [0, 1, 0], 'fuel': 20000,
                                 'outcome': outcome, 'stopped_ticks': tick,
                                 'final_state': state, 'final_head': head,
                                 'final_whole_ones': sorted(ones), 'clean_frames': frames})
    report = {'scope': __doc__, 'source_commit': 'fab89c5d26b81cd2ccab2ee5d213ff23725c7726',
              'source_table_sha256': audit.EXPECTED_SHA,
              'driver_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'program_sha256': hashlib.sha256(program.read_bytes()).hexdigest(),
              'mutation': {'deleted_state': 204, 'redirect_target': 252},
              'literal_window_certificate': {'steps': 34, 'start_state': 96,
                  'start_head': 0, 'pc_before': '1111111111', 'pc_after': '1111110111',
                  'scanned_window': window, 'input_ones_in_window': [-1] + list(range(7)),
                  'final_state': 96, 'final_head': 0,
                  'sole_tape_change': {'position': 6, 'before': 1, 'after': 0},
                  'trace': local_trace,
                  'proof_scope': 'For every tape agreeing with the stated input on [-11,6], regardless of every exterior cell. Induction on the listed34 literal rows proves the endpoint; no register-box macro is used.'},
              'functional_join_collision': collision,
              'general_residual_formulas': {
                  'domain': 't,k in N; n in N positive; s2=0; other primary registers fixed',
                  'expected_F': '(tw,p1,s1)=(t,n+k,0)',
                  'alternate_G': '(tw,p1,s1)=(t+n,n+k,0)',
                  'source_step_counts': {'expected': '3k+1', 'alternate': '7n+3k+3'},
                  'nonfactorization': 'No function E of the expected primary register tuple alone satisfies G=E after F for all domain inputs. The two recorded inputs have equal F and unequal G.',
                  'limits': 'Does not exclude encodings depending on spare suffixes, saved history, additional invariants, entry recodings, or nonfunctional relations. These formulas describe original residuals, not the subsequent mutated TM.'},
              'continued_mutated_table_prefixes': literal_prefixes,
              'status': 'literal_finite_window_and_original_residual_collision_verified'}
    args.output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({'status': report['status'], 'window': window,
                      'continued_mutant_stops': [(p['outcome'], p['stopped_ticks'])
                                                for p in literal_prefixes]}, indent=2))


if __name__ == '__main__':
    main()
