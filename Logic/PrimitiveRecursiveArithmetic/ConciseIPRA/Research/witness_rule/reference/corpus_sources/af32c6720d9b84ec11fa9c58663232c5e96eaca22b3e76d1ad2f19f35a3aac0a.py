"""Finite positive, adversarial and public-interface checks; no metatheorem."""
import copy
import gzip
import json
from pathlib import Path
import subprocess
import sys

import producer as P

ROOT = Path(__file__).resolve().parent


def build_cases():
    cases = P.build_cases()
    # Nested scalar recursors must keep the outer state separate from the
    # inner state while correctly crossing the successor's two dummy slots.
    outer, inner = 'nested_outer_state', 'nested_inner_state'
    update = P.I(P.V(outer), P.V(outer), inner,
                 P.S(P.I(P.V(inner), P.V(outer), 'third_state', P.V('third_state'))))
    proof = P.compute(P.I(P.ONE, P.TWO, outer, update))
    emitter = P.Emitter()
    packet = emitter.packet(proof)
    cases.append({'name': 'nested_state_capture_avoidance', 'accept': True,
                  'meaning': 'A one-step equation with nested recursors using distinct inner and outer states.',
                  'packet': packet, 'proof_tree': proof, 'trace': emitter.trace,
                  'allocations': -emitter.floor})

    # A nonvacuous zero witness genuinely uses the retained induction
    # hypothesis.  The producer must emit the explicit I0/transport bridge.
    x, y, z, state = 'zero_x', 'zero_y', 'zero_z', 'zero_state'
    def loop(n, seed):
        return P.I(n, seed, state, P.V(state))
    body = P.Eq(loop(P.V(y), P.V(x)), 0)
    premise = P.transitivity(P.compute(loop(P.S(P.V(z)), 0)),
                             P.hyp(P.Eq(loop(P.V(z), 0), 0)),
                             'zero_step_hole')
    proof = P.introduction(P.D(x, y, body), 0, z, 'progress', premise)
    emitter = P.Emitter()
    packet = emitter.packet(proof)
    cases.append({'name': 'nonvacuous_zero_witness_induction', 'accept': True,
                  'meaning': 'Zero witness compiled through an explicit I0 equality and two transport directions.',
                  'packet': packet, 'proof_tree': proof, 'trace': emitter.trace,
                  'allocations': -emitter.floor})

    def raw(name, packet, accept, meaning):
        cases.append({'name': name, 'packet': packet, 'accept': accept,
                      'meaning': meaning})

    zero_source = [0, 0, 0]
    zero_axiom = [zero_source, 0]
    false_goal = [0, [0]]
    raw('false_from_computation', [[0, zero_source, 0, 0], false_goal], False,
        'A computation equation cannot establish zero equals successor zero.')
    raw('atomic_goal_cannot_use_DI', [[0, 0, 0, [0, 0]], false_goal], False,
        'Two equality fields cause too many opener arguments in DI.')
    raw('future_goal_parameter', [[0, zero_source, 0, 0], [-1, -1]], False,
        'A root goal cannot name an eigenparameter not yet allocated.')
    raw('failed_major_cannot_fall_through',
        [[0, zero_source, 0, 0], [false_goal, None, None, 0], zero_axiom], False,
        'The major is verified before a neutral continuation is available.')
    raw('neutral_equation_does_not_prove_false',
        [[0, zero_source, 0, 0], [0, zero_source, 0, 0],
         [zero_axiom, None, None, 0], false_goal], False,
        'Triplicating a true equation creates only a truth alias.')
    raw('no_direct_context_injection',
        [[0, [0, 0, 5], 1, 0], false_goal], False,
        'An exposed update slot beyond the one-state scope cannot forge an axiom.')
    raw('escaping_update_slot',
        [[0, [0, 0, 5], 1, 0], [[[0], 0, 5], zero_source]], False,
        'The demanded recursive image validates and rejects update coordinate5.')
    raw('unused_DI_witness_payload',
        [[[], 0, 0, -999], [[0, 0]]], True,
        'An unused witness payload is inert; the goal is D of zero equals zero.')
    raw('missing_update_payload',
        [[0, [0, 0, None], 1, 0], false_goal], False,
        'JSON null is not a numerical update.')
    raw('inert_base_predecessor',
        [[0, [{"unused": "inert"}, 0, 0], 0, 0], zero_axiom], True,
        'The base constructor ignores the predecessor payload by design.')
    high = [0, 0, 0, 0]
    raw('large_formula_case_is_true',
        [[[], 0, 0, [0]], [high]], True,
        'The extra-arity matrix denotes truth; its D closure is a theorem.')
    raw('large_formula_progress_is_true',
        [[0, 0, 0, [0]], [high]], True,
        'An even extra-arity matrix is constant truth, so progress is harmless.')
    raw('large_numeric_seed_is_zero',
        [[0, [0, high, 0], 0, 0], [[0, high, 0], high]], True,
        'Extra-arity numerical data denote zero; the supplied equation is I0.')

    def mutated(source_name, name, rule, mutate, meaning, mode=None):
        case = next(c for c in cases if c['name'] == source_name)
        packet = copy.deepcopy(case['packet'])
        event = next(e for e in case['trace'] if e['rule'] == rule
                     and (mode is None or e['mode'] == mode))
        mutate(packet[event['packet_index']])
        raw(name, packet, False, meaning)

    mutated('nonvacuous_witness_DE_roundtrip', 'unallocated_named_DI_witness',
            'DI', lambda p: p.__setitem__(3, -999),
            'A genuine witness-dependent proof rejects a future witness.')
    mutated('atomic_progress_closure', 'base_does_not_replace_IH',
            'DI', lambda p: p.__setitem__(0, []),
            'The test proof genuinely uses its current equation, not just its base.',
            mode='progress')
    mutated('Q_arbitrary_term_specialization', 'unallocated_named_Q_target',
            'QE', lambda p: p.__setitem__(2, -999),
            'A target-dependent QE proof rejects an unallocated target.')
    mutated('Q_arbitrary_term_specialization', 'Q_nonzero_source_rejected',
            'QE', lambda p: p.__setitem__(1, [0]),
            'A conditional closure cannot specialize from an arbitrary nonzero base.')
    return cases


def main():
    kernels = ['checker.py', 'checker_bytes.py', 'checker_tokens.py', 'checker_ast.py', 'readable_checker.py']
    cases = build_cases()
    rows = []
    for case in cases:
        for kernel in kernels:
            for optimized in (False, True):
                command = [sys.executable] + (['-O'] if optimized else []) + [str(ROOT.parent / 'code' / kernel)]
                run = subprocess.run(command, input=json.dumps(case['packet']),
                                     text=True, capture_output=True, timeout=10)
                accepted = run.returncode == 0 and run.stdout.strip() == 'ACCEPT'
                matched = accepted == case['accept']
                # Every negative path must fail closed, not print ACCEPT then crash.
                if not accepted:
                    matched = matched and 'ACCEPT' not in run.stdout and run.returncode != 0
                rows.append({'name': case['name'], 'kernel': kernel,
                             'optimized': optimized, 'expected': case['accept'],
                             'accepted': accepted, 'pass': matched})
    # Parsing failures are also checked through the complete CLI.
    for kernel in kernels:
        for data in ('', '{', 'null', '[]', '{}', '[null]', '[true]', '["a"]'):
            for optimized in (False, True):
                command = [sys.executable] + (['-O'] if optimized else []) + [str(ROOT.parent / 'code' / kernel)]
                run = subprocess.run(command, input=data, text=True, capture_output=True, timeout=10)
                rows.append({'name': 'malformed_outer_' + repr(data), 'kernel': kernel,
                             'optimized': optimized, 'expected': False,
                             'accepted': run.returncode == 0 and run.stdout.strip() == 'ACCEPT',
                             'pass': run.returncode != 0 and 'ACCEPT' not in run.stdout})
    result = {'scope': 'Finite executable checks; not a proof of universal soundness.',
              'certificate_count': len(cases), 'runs': len(rows),
              'passed': sum(r['pass'] for r in rows), 'results': rows}
    (ROOT.parent / 'evidence/certificates.json').write_text(json.dumps({'cases': cases}, indent=2) + '\n')
    (ROOT.parent / 'evidence/checker_validation.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k:v for k,v in result.items() if k != 'results'}))
    failed = [x for x in rows if not x['pass']]
    if failed:
        print(json.dumps(failed, indent=2))
        raise SystemExit(1)


if __name__ == '__main__':
    main()
