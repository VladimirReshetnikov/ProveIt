"""Independent directed CLI tests for the atomic-transport restriction."""
import copy
import json
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
C = [0, 0, 0, 0]
ZERO_WITNESS = [0, 0]
r0 = [0, 0, 0]
one = [0]
E = [r0, one]
D = [0, 0, E]
DI = [0, 0, 0, ZERO_WITNESS]
A = [0, 0, D]
QE_E = [[E], 0, 0, E]
QE_D = [[D], 0, 0, D]
DE_D = [D, 0, 0, []]
DE_A = [A, 0, 0, []]

cases = []
def add(label, packet, expected):
    cases.append((label, packet, expected))

add('R0', [C, E], True)
add('R0_wrong_result', [C, [r0, 0]], False)
add('R_counter_only', [C, [[[0], 0, 3], 0]], True)
add('R_state_only', [C, [[[0], 0, 1], [0, 0, 1]]], True)
update = [7, 5, 5]
state = [0, 0, update]
add('R_both_slots_original_update_retained', [C, [[[0], 0, update], [0, state, state]]], True)
bad_state = [0, 0, [0, 5, 5]]
add('R_counter_opened_update_wrongly_reused', [C, [[[0], 0, update], [0, bad_state, bad_state]]], False)
add('R_two_child_counter_ignored_by_update', [C, [[[0, 0], 0, 0], 0]], False)
add('R_three_child_counter_ignored_by_update', [C, [[[0, 0, 0], 0, 0], 0]], False)
add('R_unscoped_negative_seed', [C, [[0, -1, 0], [-1]]], False)
add('R_unscoped_positive_seed', [C, [[0, 7, 0], [7]]], False)
add('R_unscoped_ignored_update', [C, [[0, 0, -1], one]], False)
add('atomic_transport', [C, C, [E, r0, one, [1, one]], [one, one]], True)
for value, label in [(float('inf'), 'positive_infinity'),
                     (float('-inf'), 'negative_infinity'),
                     (float('nan'), 'nan')]:
    r = [[0], 0, 3]
    add('nonfinite_template_hole_' + label,
        [C, C, [[r, 0], r, 0, [value, 0]], [0, 0]], True)
add('compound_transport_forbidden', [C, [E, r0, one, D], D], False)
add('closure_transport_forbidden', [C, [E, r0, one, [E]], [E]], False)
add('atomic_transport_malformed_motive', [C, [E, r0, one, 0], E], False)
add('DI_closed_equation', [C, DI, D], True)
add('DI_future_negative_used_witness', [C, [0, 0, 0, -1], [0, 0, [3, 3]]], False)
add('DI_free_positive_used_witness', [C, [0, 0, 0, 1], [0, 0, [3, 3]]], False)
add('DE_empty_motive_then_QE_equation', [C, QE_E, C, DI, DE_D, E], True)
bad_de = [D, 0, 0, 0]
add('DE_scalar_motive_rejected_by_length_guard', [C, QE_E, C, DI, bad_de, E], False)
add('QE_compound_matrix_still_allowed', [C, DI, QE_D, C, DI, DI, DE_A, D], True)
add('QE_wrong_target_no_DE_fallback', [C, [[E], 0, one, [0, one]], C, DI, DE_D, E], False)
add('standalone_Q_no_hypothesis_goal', [C, [E]], False)
add('standalone_scalar_truth', [C, 0], False)
add('standalone_empty_truth', [C, []], False)
add('false_equation', [C, [0, one]], False)
add('bad_goal_arity', [C, [0, 0, 0, 0]], False)

programs = [ROOT / 'code/checker.py', ROOT / 'code/readable_checker.py']
results = []
for path in programs:
    for optimized in [False, True]:
        for label, certificate, expected in cases:
            cmd = [sys.executable] + (['-O'] if optimized else []) + [str(path)]
            proc = subprocess.run(cmd, input=json.dumps(certificate), text=True,
                                  capture_output=True, timeout=10)
            accepted = proc.returncode == 0 and proc.stdout == 'ACCEPT\n'
            assert accepted == expected, (path.name, label, proc.stdout, proc.stderr)
            results.append({'program':path.name, 'optimized':optimized,
                            'case':label, 'accepted':accepted, 'expected':expected})
receipt = {'checks':len(results), 'all_passed':True, 'results':results}
(HERE / 'boundary_receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps({'checks':len(results), 'all_passed':True}))
