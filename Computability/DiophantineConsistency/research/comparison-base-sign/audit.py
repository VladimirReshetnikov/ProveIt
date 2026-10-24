#!/usr/bin/env python3
"""Fresh actual-row use audit for an existential comparison-base lift.

No source builder, author checker, optimizer, Lean or historical emitter is
imported. The small polynomial collector is from our separate independent peer.
"""
import argparse
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
PEER = ROOT / 'reviews/main-root-modulus-signs-peer.py'
spec = importlib.util.spec_from_file_location('independent_sign_peer', PEER)
poly = importlib.util.module_from_spec(spec)
spec.loader.exec_module(poly)
P, plus, times = poly.P, poly.plus, poly.times

def need(ok, message):
    if not ok:
        raise ValueError(message)

def load(path):
    return json.loads(path.read_bytes())

def sha(path):
    return sha256(path.read_bytes()).hexdigest()

def pell(a, n):
    x, y = 1, 0
    for _ in range(n):
        x, y = a*x + (a*a-1)*y, x + a*y
    return x, y

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path, required=True)
    cli = ap.parse_args()
    prior = ROOT / 'research/main-root-and-modulus-signs'
    manifest = load(prior / 'MANIFEST.json')
    for rel, h in manifest['files'].items():
        need(sha(prior / rel) == h, 'frozen sign packet: ' + rel)
    for rel, h in load(prior / 'SOURCE_PINS.json')['files'].items():
        need(sha(ROOT / rel) == h, 'frozen whole source pin: ' + rel)
    raw_path = ROOT / 'candidates/projected-radius-mixed-bounds/source/raw_builder.json'
    interfaces_path = ROOT / 'candidates/projected-radius-mixed/arithmetic_interfaces.json'
    raw, interfaces = load(raw_path), load(interfaces_path)
    cert = load(prior / 'CERTIFICATE.json')
    rows = [P(row['terms']) for row in raw['rows']]
    gate_vars = [i for i, v in enumerate(raw['variables'])
                 if v['kind'] in ('gate', 'square_difference')]
    gate_rows = interfaces['all_gate_rows']
    need(len(gate_vars) == len(gate_rows) == 1029, 'whole topological gate inventory')
    gate_set = set(gate_rows)
    changed_free = {657, 658} | {
        seed[key][1] for seed in interfaces['seeds']
        for key in ('S', 'R', 'Squotient', 'Rquotient')}
    need(len(changed_free) == 62 and
         changed_free <= set(interfaces['private_free_variables']),
         'exact private free reconstruction slots')
    changed = set(changed_free)
    descendants = []
    bindings = []
    for var, row_index in zip(gate_vars, gate_rows):
        row = rows[row_index]
        variables = poly.vars_(row)
        coefficient = row.get((var,))
        need(coefficient in (-1, 1) and max(variables) == var and
             all(var not in monomial or monomial == (var,) for monomial in row),
             'exact topological unit gate row')
        dependencies = variables - {var}
        if dependencies & changed:
            changed.add(var)
            descendants.append(var)
            bindings.append({'variable': var, 'row': row_index,
                             'dependencies': sorted(dependencies)})
    constraints = [i for i in interfaces['private_non_gate_rows']
                   if poly.vars_(rows[i]) & changed]
    need(len(descendants) == 141 and len(constraints) == 46,
         'complete changed gate and constraint counts')
    expected_constraints = {616} | {
        seed['rows'][key] for seed in interfaces['seeds']
        for key in ('norm3', 'S_mod_U', 'R_mod_4Y')}
    need(set(constraints) == expected_constraints,
         'only comparison norms/congruences and B_mod_U may change')
    checked_ideals = 0
    def ideal(cut, target_constraint):
        nonlocal checked_ideals
        got = {}
        nongates = []
        for term in cut['row_combination']:
            got = plus(got, times(P(term['multiplier']), rows[term['row']]))
            if term['row'] not in gate_set:
                nongates.append(term)
        need(got == P(cut['polynomial']), 'complete comparison ideal')
        need(nongates == [{'multiplier': [[1, []]], 'row': target_constraint}],
             'one unit constraint pivot after all gates are restored')
        checked_ideals += 1
    ideal(cert['comparison_base_congruence'], 616)
    for data, seed in zip(cert['seeds'], interfaces['seeds']):
        for key in ('norm3', 'S_mod_U', 'R_mod_4Y'):
            ideal(data['cuts'][key], seed['rows'][key])
    remaining = set(cert['remaining_raw_guard_indices']) - {657}
    need(len(remaining) == 78 and not remaining & changed,
         'all other 78 retained guard values are literally unchanged')
    power_arguments = {v[1] for call in raw['powers']
                       for v in (call['base'], call['exponent'], call['output'])}
    all_main_pairs = {v[1] for seed in raw['indices'] for v in seed['pair']}
    power_quotients = {call['quotient'] for call in cert['power_calls']}
    need(not changed & (set(range(643)) | power_arguments | all_main_pairs |
                        power_quotients | {643, 644, 645, 646, 655, 656, 917, 1214}),
         'prefix/frame/unit/V/discriminant/all main pairs/power calls stay fixed')
    # Collect the two lift identities over a free integer polynomial ring.
    # sign(U)*U is used for abs(U); cancellation itself needs no sign axiom.
    A, U, V, q4, B, bq, t, sign = [poly.V(i) for i in range(8)]
    one, four = poly.C(1), poly.C(4)
    qnew = plus(q4, times(times(sign, U), t))
    Bnew = plus(B, poly.product([four, V, sign, U, t]))
    bqnew = plus(bq, poly.product([four, V, sign, t]))
    old_constructor = plus(B, plus(one, poly.product([four, V, plus(q4, one)])), -1)
    new_constructor = plus(Bnew, plus(one, poly.product([four, V, plus(qnew, one)])), -1)
    old_congruence = plus(plus(B, A, -1), times(U, bq), -1)
    new_congruence = plus(plus(Bnew, A, -1), times(U, bqnew), -1)
    need(new_constructor == old_constructor and new_congruence == old_congruence,
         'both complete universal lift identities')
    parity_cases = 0
    for a in range(2, 8):
        for h in range(13):
            x, y = pell(a, h)
            xm, ym = pell(-a, h)
            need(xm == (-1)**h*x and ym == (-1 if h % 2 == 0 else 1)*y,
                 'negative-base recurrence parity control')
            parity_cases += 1
    lifts = 0
    for a in range(2, 5):
        for k in range(1, 4):
            x, y = pell(a, k)
            u, v = pell(a, 2*k*y)
            need(v % (y*y) == 0 and u % 2 == 1,
                 'finite comparison fixture common-unit premises')
            q = ((a-1)*pow(4*v, -1, u)) % u - u
            b = 1 + 4*v*q
            q4, bq = q-1, (b-a)//u
            s, r = pell(b, k)
            need(b <= -3 and (b-a) % u == 0 and (s-x) % u == 0 and
                 (r-k) % (4*y) == 0 and s*s-(b*b-1)*r*r == 1,
                 'actual negative comparison-base signed fixture')
            for unit_sign in (-1, 1):
                us = unit_sign*u
                bqs = unit_sign*bq
                t = abs(q4)+1
                q4new = q4 + abs(us)*t
                bnew = b + 4*v*abs(us)*t
                bqnew = bqs + 4*v*unit_sign*t
                sn, rn = pell(bnew, k)
                need(q4new >= 0 and bnew == 1+4*v*(q4new+1) and
                     bnew-a == us*bqnew and bnew >= 5 and
                     (sn-x) % us == 0 and (rn-k) % (4*y) == 0 and
                     sn*sn-(bnew*bnew-1)*rn*rn == 1,
                     'signed-U lift and fresh comparison controls')
                lifts += 1
    result = {
        'status': 'PASS', 'optimized_python': bool(sys.flags.optimize),
        'source_pins': {str(p.relative_to(ROOT)): sha(p) for p in
                        (raw_path, interfaces_path, prior/'README.md',
                         prior/'CERTIFICATE.json', prior/'MANIFEST.json', PEER)},
        'whole_original_rows': len(rows), 'whole_raw_coordinates': len(raw['variables']),
        'whole_topological_unit_gate_rows': len(gate_rows),
        'changed_free_coordinates': sorted(changed_free),
        'changed_gate_rows': bindings,
        'affected_private_constraints': constraints,
        'complete_unit_constraint_ideals': checked_ideals,
        'universal_collected_lift_identities': 2,
        'unchanged_guard_count': len(remaining),
        'unchanged_all_main_pairs_including_derived': True,
        'unchanged_all_power_arguments_and_quotients': True,
        'finite_controls': {'negative_base_parity': parity_cases,
                            'negative_B_lifts_with_both_U_signs': lifts},
        'scope': 'Exact fresh private-use closure and ordinary reconstruction '
                 'support, not a materialized quartic or Lean/internal-ZFC theorem. '
                 'Finite Pell instances are diagnostics; the ordinary proof is in README.md.'}
    cli.output.write_text(json.dumps(result, indent=2, sort_keys=True)+'\n')
    print(json.dumps({k: result[k] for k in
                      ('status', 'whole_original_rows', 'whole_raw_coordinates',
                       'complete_unit_constraint_ideals', 'unchanged_guard_count',
                       'finite_controls')}, indent=2))

if __name__ == '__main__':
    main()
