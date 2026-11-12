"""Complete-CLI checks for the composed codec, plus targeted unsafe mutations.

This finite suite does not prove universal checker soundness.
"""
import copy
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile

import producer as P

ROOT = Path(__file__).resolve().parent


def build_cases():
    cases = P.build_cases()

    def add(name, proof, meaning):
        emitter = P.Emitter()
        packet = emitter.packet(proof)
        cases.append({'name': name, 'packet': packet, 'accept': True,
                      'meaning': meaning, 'proof_tree': proof, 'trace': emitter.trace})

    outer, inner = 'nested_outer_state', 'nested_inner_state'
    update = P.I(P.V(outer), P.V(outer), inner,
                 P.S(P.I(P.V(inner), P.V(outer), 'third_state', P.V('third_state'))))
    add('nested_state_capture_avoidance', P.compute(P.I(P.ONE, P.TWO, outer, update)),
        'The state substitution crosses nested iterators and successor dummy slots.')
    x, y, z, state = 'zero_x', 'zero_y', 'zero_z', 'zero_state'
    def loop(n, seed):
        return P.I(n, seed, state, P.V(state))
    body = P.Eq(loop(P.V(y), P.V(x)), 0)
    premise = P.transitivity(P.compute(loop(P.S(P.V(z)), 0)),
                             P.hyp(P.Eq(loop(P.V(z), 0), 0)), 'zero_step_hole')
    add('nonvacuous_zero_witness_induction',
        P.introduction(P.D(x, y, body), 0, z, 'progress', premise),
        'A literal-zero existential witness and an essential equation induction hypothesis.')

    def raw(name, packet, accept, meaning):
        cases.append({'name': name, 'packet': packet, 'accept': accept, 'meaning': meaning})

    raw('atomic_goal_cannot_use_DI', [[0, 0, 0, 0], [[0, 0], [0]]], False,
        'Its binary numerical left side denotes zero, so the requested equality is false.')
    raw('successor_wrapper_is_essential',
        [[None, [0, 0], [0], 0], [[[0, 0], [0], 0], 0]], False,
        'A nonempty predecessor can denote zero; arithmetic supply must construct its successor.')
    raw('unused_DI_witness_payload', [[[], 0, 0, -999], [[0, 0]]], True,
        'The unused witness is inert; the goal is D of zero equals zero.')
    high = [0, 0, 0, 0]
    raw('large_formula_case_is_true', [[[], 0, 0, [0]], [high]], True,
        'The extra-arity matrix is the declared constant truth.')
    raw('large_formula_progress_is_true', [[0, 0, 0, [0]], [high]], True,
        'Progress at an extra-arity even matrix is harmless because that matrix is truth.')
    raw('large_numeric_seed_is_zero', [[None, 0, high, 0], [[0, high, 0], high]], True,
        'Extra-arity numerical data are the declared zero alias.')
    raw('exposed_update_slot_rejected',
        [[None, [0, 0], 0, 7], [[[[0, 0]], 0, 7], [[0, 0], 0, 7]]], False,
        'A recursive image demanded at an out-of-scope update slot must validate before use.')
    spec = next(c for c in cases if c['name'] == 'Q_arbitrary_term_specialization')
    invalid = copy.deepcopy(spec['packet'])
    event = next(e for e in spec['trace'] if e['rule'] == 'QE')
    invalid[event['packet_index']][1] = [0]
    raw('Q_nonzero_source_rejected', invalid, False,
        'A closure needs its zero instance; an arbitrary nonzero source cannot replace it.')
    prefix = P.Emitter().packet(P.reflexivity(0))[:-1]
    raw('unproved_major_cannot_transport', prefix + [[[0, [0]], 0, [0], [0, 3]], [0, [0]]], False,
        'The false equality major cannot be skipped while proving a reflexive minor.')
    return cases


def run_checker(path, data, optimized=False):
    command = [sys.executable] + (['-O'] if optimized else []) + [str(path)]
    completed = subprocess.run(command, input=data, text=True, capture_output=True, timeout=8)
    accepted = completed.returncode == 0 and completed.stdout == 'ACCEPT\n'
    return accepted, completed.returncode, completed.stdout, completed.stderr


def main():
    cases = build_cases()
    kernels = ['checker.py', 'checker_explicit.py', 'checker_short.py', 'checker_guarded_ast.py']
    records = []
    for case in cases:
        for kernel in kernels:
            for optimized in (False, True):
                accepted, code, out, err = run_checker(ROOT / kernel, json.dumps(case['packet']), optimized)
                passed = accepted == case['accept'] and (accepted or (code != 0 and 'ACCEPT' not in out))
                records.append({'case': case['name'], 'kernel': kernel, 'optimized': optimized,
                                'expected': case['accept'], 'accepted': accepted, 'pass': passed})
    for data in ('', '{', 'null', '[]', '{}', '[null]', '[true]', '["a"]', '[["a",0]]', '[[{},0]]'):
        for kernel in kernels:
            for optimized in (False, True):
                accepted, code, out, err = run_checker(ROOT / kernel, data, optimized)
                records.append({'case': 'malformed_' + repr(data), 'kernel': kernel, 'optimized': optimized,
                                'expected': False, 'accepted': accepted,
                                'pass': not accepted and code != 0 and 'ACCEPT' not in out})
    source = (ROOT / 'checker.py').read_text()
    mutation_specs = [
        ('drop_successor_constructor', 's and [s]', 's', 'successor_wrapper_is_essential'),
        ('drop_exact_DI_shape', 'i(*a, t, 2)', 'i(a[0], t, 2)', 'atomic_goal_cannot_use_DI'),
        ('allow_compound_progress', 'm or len(a) % 2 == m', 'm or m == 0 or len(a) % 2 == m',
         'forbidden_compound_progress'),
        ('skip_major_proof', '        c(m, g)\n', '', 'unproved_major_cannot_transport'),
    ]
    mutants = []
    with tempfile.TemporaryDirectory() as directory:
        for name, old, new, case_name in mutation_specs:
            assert source.count(old) == 1
            candidate = Path(directory) / (name + '.py')
            candidate.write_text(source.replace(old, new))
            case = next(c for c in cases if c['name'] == case_name)
            for optimized in (False, True):
                accepted, code, out, err = run_checker(candidate, json.dumps(case['packet']), optimized)
                mutants.append({'mutation': name, 'case': case_name, 'optimized': optimized,
                                'unsafe_acceptance_observed': accepted, 'pass': accepted})
    result = {'scope': 'Finite implementation checks and deliberately unsafe mutations; not a universal metatheorem.',
              'candidate_hashes': {name: hashlib.sha256((ROOT/name).read_bytes()).hexdigest() for name in kernels},
              'certificate_count': len(cases), 'ordinary_cli_runs': len(records),
              'ordinary_passes': sum(x['pass'] for x in records),
              'mutation_runs': len(mutants), 'mutation_passes': sum(x['pass'] for x in mutants),
              'cli_results': records, 'mutation_results': mutants}
    (ROOT/'test_cases.json').write_text(json.dumps({'cases': cases}, indent=2)+'\n')
    (ROOT/'test_results.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('cli_results','mutation_results')},indent=2))
    failures = [x for x in records + mutants if not x['pass']]
    if failures:
        print(json.dumps(failures, indent=2))
        raise SystemExit(1)


if __name__ == '__main__':
    main()
