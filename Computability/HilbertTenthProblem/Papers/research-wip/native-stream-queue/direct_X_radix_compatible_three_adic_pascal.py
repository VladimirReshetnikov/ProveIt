#!/usr/bin/env python3
"""Fresh small modular controls and byte binding; no saved code or arrays run."""
import hashlib
import json
from math import gcd
from pathlib import Path

HERE = Path(__file__)
BASE = Path('/home/codex/.codex/worktrees/2a71/Proofs/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue')
PINNED = [
    ('direct_X_canonical_three_adic_family_pascal.md', 'c18f09aa7fd0b4eb89bbdbbca2a5b5ad3aed3f5d559e6afb02034cb9bb62f7cc', None),
    ('direct_X_canonical_resonance_repair_aristotle.md', 'addf7b16329a70f002478895295e5979f1b0561f9b1962cfe3bafc9cd467f1e9', None),
    ('complete75_half_binomial_compiler.md', '68edf3bc40238ccf47b023d7358e4be62664a2d78a60b6fae19de14b67208117', (1, 70)),
    ('direct_X_authentic_outer_root.md', '35d5d5080a615583779f31b1985768045455ab6cbbfc394dac4b93cc2713a617', (1, 49)),
]

def check(condition, name):
    if not condition:
        raise ValueError(name)

def sha(data):
    return hashlib.sha256(data).hexdigest()

def two_depth(number):
    check(number > 0, 'positive integer in valuation')
    return (number & -number).bit_length() - 1

def small_order(modulus):
    check(gcd(3, modulus) == 1, 'unit premise')
    residue = 1
    for exponent in range(1, modulus + 1):
        residue = 3 * residue % modulus
        if residue == 1:
            return exponent
    raise ValueError('finite unit group did not return to one')

def main():
    dependencies = []
    for name, pin, interval in PINNED:
        path = BASE / name
        raw = path.read_bytes()
        check(sha(raw) == pin, 'dependency ' + name)
        lines = raw.splitlines(keepends=True)
        first, last = interval or (1, len(lines))
        dependencies.append({
            'path': str(path), 'sha256': pin, 'bytes': len(raw),
            'read_span': [first, last], 'read_span_sha256': sha(b''.join(lines[first-1:last])),
        })
    cases = []
    for d in (3, 5, 7, 9):
        B = 1 << d
        m = B - 1
        order = small_order(m)
        c = 1 << (3*d + 1)
        period = order * c // gcd(order, c)
        for n in (1, 2, 3, 4):
            k = n * period
            e = 3*k + c
            check(k >= c and e % c == 0, 'progression depth')
            check(B * pow(3, k, m) % m == 1, 'repunit residue')
            check(e - 1 >= 3*k, 'three-adic theorem depth')
            check(pow(3, e-k, B) == 1, 'packed-index residue after cancelling 3^k')
            tau = 3 + two_depth(e)
            modulus = 1 << (tau + 1)
            R_plus_one_residue = 2 * (pow(3, e, modulus) - 1) % modulus
            check(R_plus_one_residue == 1 << tau, 'exact LTE residue')
            check(tau >= 3*d + 4 and tau - 2 >= 3*d + 2, 'binary scale margin')
            check(c > 3*d and B**4 >= 16, 'symbolic threshold premises')
            cases.append({
                'synthetic_width_d': d, 'B': B, 'unit_order': order, 'c': c,
                'L': period, 'progression_number': n, 'k': k, 'e': e,
                'q_mod_B_minus_one': 1, 'exact_v2_R_plus_one': tau,
                'modulus_for_R_plus_one': modulus, 'R_plus_one_residue': R_plus_one_residue,
                'proved_v2_Y_lower_bound': tau - 2,
                'inherited_exact_v3_Y': e - 1,
                'three_power_e_minus_k_mod_B': 1,
                'materialized_q_R_X_or_Y': False,
            })
    identity_cases = 0
    for toy_q in range(2, 13):
        for toy_gamma in (3, 5, 9):
            # Generic polynomial identities, not members of the proposed family.
            direct = toy_gamma*toy_q**3 - 3 - (2*toy_q-1)*(toy_q**2-1)
            corrected = (toy_gamma-2)*toy_q**3 + toy_q**2 + 2*toy_q - 4
            check(direct == corrected and direct > 0, 'corrected lower-endpoint identity')
            check(corrected + 1 != direct, 'retained draft off-by-one')
            identity_cases += 1
    note = HERE.with_suffix('.md')
    result = {
        'status': 'PASS: finite modular controls and metadata; all-size theorem is the proof',
        'author_note': {'path': str(note), 'sha256': sha(note.read_bytes())},
        'fresh_helper_sha256': sha(HERE.read_bytes()), 'dependencies': dependencies,
        'controls': cases, 'control_count': len(cases), 'small_orders_checked': 4,
        'generic_corrected_identity_controls': identity_cases,
        'correction_inventory': [{
            'location': 'author note equation (8), lower endpoint',
            'old_constant': -3, 'correct_constant': -4,
            'old_rhs_minus_actual_difference': 1,
            'found_by': 'root independent challenge before freeze',
            'retention': 'numbered Review remark 3; generic q=2, Gamma=3 gives 13 versus 12',
            'theorem_effect': 'none; corrected difference remains positive',
        }],
        'scope': {
            'controls_are_authentic_compiler_instances': False,
            'prior_three_adic_helper_run_or_imported': False,
            'any_saved_source_array_evaluated': False,
            'any_predecessor_code_run_or_imported': False,
            'family_q_R_X_Y_or_native_witnesses_materialized': False,
            'full_direct_X83_zero_claimed': False,
        },
    }
    print(json.dumps(result, sort_keys=True, indent=2))

if __name__ == '__main__':
    main()
