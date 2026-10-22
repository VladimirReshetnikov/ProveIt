#!/usr/bin/env python3
"""Exact finite recipe and modular fingerprints for the strict K215 tuple.

The four (astronomically large) coefficients are NEVER expanded.  Every
exponent below is a fixed, finite integer.  Modular exponentiation evaluates
the recipe for any positive modulus without division or coprimality premises.

Import coefficients_mod(m) for the four circuit ports beta, K0, MC, MF.
IMPORTANT: the port called MF is shifted: MF_native + B_base - 1.
Import compiler_constants_mod(m) to inspect the intermediate fixed constants.

Running without arguments writes data/COEFFICIENT_BINDING.json and
data/coefficient_residues.json.  Running with --modulus M prints that one
modular fingerprint and does not rewrite the default files.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from functools import lru_cache
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / 'data'
RECIPE_ID = 'k215-strict-four-cell-5252-5pow16'
PIN = 'f0ae4e0991ca44a7bb4e5671d42e33d775e48035'
MACHINE_SHA256 = 'fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090'
WINDOW_SHA256 = 'baa3d2b5296b818b2e6488c1b06fda29e405d9b4cf5dd19a3c38fbdd1ba658d7'
PORTS = ['beta', 'K0', 'MC', 'MF']
PORT_MAPPING = {
    'beta': 'B_base-1',
    'K0': 'DC+B_base*DR',
    'MC': 'MC_native',
    'MF': 'MF_native+B_base-1',
}
SCALARS = {
    'k': 5252, 'a': 439, 'ell': 13, 'p': 1075, 'm': 7013,
    'dummy_count': 2, 'dummy_start': 10520, 'M': 11839,
    'anchor_factors': [1, 3, 5, 11], 'Emax': 130229, 'Hc': 226259,
    'T1': 487157, 'T2': 747619, 'bmin': 36871, 'b': 78125,
    'L': 1953125, 'd': 152587890625,
    'copy_offsets': [8764, 8325, 7886, 7008],
    'bare_shifts': [1317, 226698, 47356, 94712],
    'mu_bit_length': 36856, 'mu_population': 2847,
    'clause_mass_bit_length': 22893, 'carry_bound_bit_length': 22909,
    'native_support': 7014, 'field_targets': 1319, 'mod5_unit': 3,
}
ANCHORS = (11839, 35517, 59195, 130229)
DUMMIES = (10520, 10521)
DEFAULT_MODULI = (4, 5, 8, 65537, 1000000007)
CIRCUITS = (
    'merger12_system.json', 'merger12_product.json',
    'merger13_system.json', 'merger13_product.json',
    'integer26_system.json', 'integer26_product.json',
    'retained16_system59.json',
)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha256(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def load_authenticated_windows():
    """Check the supplied finite inputs against the frozen reviewed tuple."""
    require(sha256(DATA / 'k215.tm') == MACHINE_SHA256,
            'The literal K215 transition-table hash does not match.')
    require(sha256(DATA / 'strict_windows.json') == WINDOW_SHA256,
            'The strict-window ordering/hash does not match.')
    windows = json.loads((DATA / 'strict_windows.json').read_text())
    require(len(windows) == SCALARS['k'], 'Wrong number of tile selectors.')
    require(windows[0] == [434, 435, 436, 1], 'Wrong Start selector.')
    require(windows[1] == [438, 0, 0, 438], 'Wrong forbidden selector.')
    require(all(len(w) == 4 and all(type(s) is int and 0 <= s < 439 for s in w)
                for w in windows), 'Malformed tile data.')
    receipt = json.loads((DATA / 'strict_compiler_checks.json').read_text())
    require(receipt['scalars'] == SCALARS, 'Compiler scalar receipt changed.')
    require(receipt['window_sha256'] == WINDOW_SHA256, 'Receipt/window mismatch.')
    return windows


def native_support():
    """The complete finite set of radix positions, including two low dummies."""
    support = set(range(5252))
    for offset in SCALARS['copy_offsets']:
        support.update(range(offset, offset + 439))
    support.update(DUMMIES)
    support.update(ANCHORS)
    require(len(support) == 7014 and max(support) == 130229,
            'Native support is not the frozen support.')
    return tuple(sorted(support))


def _compiler_constants_mod(modulus, windows):
    require(type(modulus) is int and modulus > 0, 'Modulus must be a positive integer.')
    m = modulus
    # These are modular residues, not expanded integer constants.
    A = pow(2, 13, m)
    rho = pow(2, 78125, m)
    B = pow(2, 152587890625, m)
    powers = [1 % m]
    for _ in range(2835):
        powers.append(powers[-1] * A % m)

    @lru_cache(maxsize=None)
    def rp(exponent):
        require(type(exponent) is int and exponent >= 0, 'Invalid fixed exponent.')
        return pow(rho, exponent, m)

    mu = (A - 2 + sum(powers[1:2836])) % m
    clause = {}
    anchor_sum = sum(powers[t] for t in range(1757, 1761))
    for index, tile in enumerate(windows):
        clause[index] = (1 + sum(powers[1 + slot * 439 + symbol]
                                for slot, symbol in enumerate(tile))
                         + anchor_sum) % m
    for slot, offset in enumerate(SCALARS['copy_offsets']):
        for symbol in range(439):
            clause[offset + symbol] = powers[1 + slot * 439 + symbol]
    for index, position in enumerate(ANCHORS):
        clause[position] = powers[1757 + index]
    for position in DUMMIES:
        clause[position] = 0
    support = native_support()
    require(set(clause) == set(support), 'Clause coefficients do not cover the support.')

    DC = (sum(rp(e) for e in SCALARS['bare_shifts'])
          + sum(clause[e] * (rp(487157 - e) + rp(747619 - e))
                for e in support)) % m
    DR = rp(226259)
    MF0 = (mu * (rp(487157) + rp(747619))
           + sum(rp(8325 + j) for j in range(439))
           + sum(rp(226259 + 8764 + j) + rp(226259 + 8325 + j)
                 for j in range(439))
           + rp(59195) + rp(130229)) % m
    MC = (B - 1 - sum(rp(e) for e in support if e != 1)
          - 2 * rp(10520)) % m
    MF_native = (MF0 + 4) % m
    return {
        'A_c': A, 'rho': rho, 'B_base': B, 'mu': mu,
        'DC': DC, 'DR': DR, 'MF0': MF0,
        'MC_native': MC, 'MF_native': MF_native,
        'beta': (B - 1) % m,
        'K0': (DC + B * DR) % m,
        'MC': MC,
        'MF': (MF_native + B - 1) % m,
    }


def compiler_constants_mod(modulus):
    """Return intermediate constants and four circuit ports modulo modulus."""
    return _compiler_constants_mod(modulus, load_authenticated_windows())


def coefficients_mod(modulus):
    """Return precisely beta,K0,MC,MF modulo modulus; MF is the SHIFTED port."""
    values = compiler_constants_mod(modulus)
    return {name: values[name] for name in PORTS}


def binding_document():
    """A machine-readable, complete finite description of the integer tuple."""
    load_authenticated_windows()
    return {
        'schema': 'k215-strict-four-cell-binding-v1',
        'recipe_id': RECIPE_ID,
        'repository_pin': PIN,
        'machine': {
            'path': 'data/k215.tm', 'sha256': MACHINE_SHA256,
            'transition_json': 'data/k215_transitions.json',
            'transition_json_sha256': sha256(DATA / 'k215_transitions.json'),
            'working_states': 215, 'symbols': 2, 'start_state': 0,
            'blank_symbol': 0, 'halt_state': 215,
            'padding_actions': [[215, 0, 0, 0, 215], [215, 1, 1, 0, 215]],
            'padding_action_order': ['state', 'read', 'write', 'move', 'next_state'],
        },
        'windows': {
            'path': 'data/strict_windows.json', 'sha256': WINDOW_SHA256,
            'count': 5252, 'strict_count': 5251,
            'coordinate_order': ['left', 'center', 'right', 'next_center'],
            'selector_0_start': [434, 435, 436, 1],
            'selector_1_forbidden': [438, 0, 0, 438],
            'remaining_order': 'lexicographic, excluding the already listed Start',
        },
        'scalars': SCALARS,
        'fixed_numerals': PORTS,
        'port_mapping': PORT_MAPPING,
        'mask_convention': 'MF is the shifted port MF_native+B_base-1; never substitute MF_native.',
        'recipe': {
            'A_c': '2^13', 'rho': '2^78125', 'B_base': 'rho^1953125 = 2^152587890625',
            'mu': 'A_c-2+sum(A_c^j, j=1..2835)',
            'support': {
                'selectors_inclusive': [0, 5251],
                'copy_intervals_inclusive': [[8764, 9202], [8325, 8763],
                                              [7886, 8324], [7008, 7446]],
                'dummy_positions': list(DUMMIES), 'anchor_positions': list(ANCHORS),
                'cardinality': 7014,
            },
            'clause_coefficients': {
                'selector_i': '1+A_c^(1+l_i)+A_c^(440+c_i)+A_c^(879+r_i)+A_c^(1318+n_i)+sum(A_c^t,t=1757..1760)',
                'copy_left_8764_plus_j': 'A_c^(1+j), j=0..438',
                'copy_center_8325_plus_j': 'A_c^(440+j), j=0..438',
                'copy_right_7886_plus_j': 'A_c^(879+j), j=0..438',
                'copy_next_7008_plus_j': 'A_c^(1318+j), j=0..438',
                'anchor_exponents_in_anchor_order': [1757, 1758, 1759, 1760],
                'both_dummies': 0,
            },
            'DC': 'rho^1317+rho^226698+rho^47356+rho^94712+sum(v_e*(rho^(487157-e)+rho^(747619-e)),e in support)',
            'DR': 'rho^226259',
            'MF0': 'mu*(rho^487157+rho^747619)+sum(rho^(8325+j),j=0..438)+sum(rho^(226259+8764+j)+rho^(226259+8325+j),j=0..438)+rho^59195+rho^130229',
            'MC_native': 'B_base-1-sum(rho^e,e in support with e!=1)-2*rho^10520',
            'MF_native': 'MF0+4',
        },
        'circuits': {
            filename: {'recipe_id': RECIPE_ID, 'fixed_numerals': PORTS}
            for filename in CIRCUITS
        },
        'evaluator': {
            'path': 'code/coefficient_recipe.py',
            'sha256': sha256(Path(__file__)),
            'callable': 'coefficients_mod(modulus)',
            'internal_callable': 'compiler_constants_mod(modulus)',
            'method': 'Finite sums and modular powers only; valid for every positive modulus without division.',
        },
        'proofs': ['proofs/STRICT_COMPILER_REVIEW.md', 'reference/t4_compiler_proof.md',
                   'reference/blank_helical_proof.md'],
        'status': 'Exact finite coefficient recipe; final giant integers are not materialized.',
    }


def fingerprint(modulus, values):
    return {
        'modulus': modulus,
        'ports': {name: values[name] for name in PORTS},
        'internal': {name: value for name, value in values.items() if name not in PORTS},
        'two_DC_minus_DR': (2 * values['DC'] - values['DR']) % modulus,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--modulus', type=int, help='Print one fingerprint instead of writing the default ledgers.')
    args = parser.parse_args()
    windows = load_authenticated_windows()
    if args.modulus is not None:
        values = _compiler_constants_mod(args.modulus, windows)
        print(json.dumps(fingerprint(args.modulus, values), indent=2))
        return
    binding = binding_document()
    rows = [fingerprint(m, _compiler_constants_mod(m, windows)) for m in DEFAULT_MODULI]
    by_modulus = {row['modulus']: row for row in rows}
    require(by_modulus[4]['ports']['MC'] == 2, 'MC is not 2 modulo 4.')
    require(by_modulus[8]['internal']['MF_native'] == 4, 'MF_native is not 4 modulo 8.')
    require(by_modulus[5]['two_DC_minus_DR'] == 3, 'The five-adic tuning coefficient is not a unit.')
    binding_path = DATA / 'COEFFICIENT_BINDING.json'
    binding_path.write_text(json.dumps(binding, indent=2) + '\n')
    residues = {
        'schema': 'k215-strict-four-cell-residues-v1', 'recipe_id': RECIPE_ID,
        'binding_path': 'data/COEFFICIENT_BINDING.json',
        'binding_sha256': sha256(binding_path),
        'windows_sha256': WINDOW_SHA256, 'machine_sha256': MACHINE_SHA256,
        'fingerprints': rows,
        'checks': {'MC_mod_4_is_2': True, 'MF_native_mod_8_is_4': True,
                   'two_DC_minus_DR_mod_5_is_3': True},
        'scope': 'Modular fingerprints authenticate this recipe; they do not decide solvability or replace the compiler proof.',
    }
    (DATA / 'coefficient_residues.json').write_text(json.dumps(residues, indent=2) + '\n')
    print(json.dumps({'status': 'PASS', 'recipe_id': RECIPE_ID,
                      'moduli': list(DEFAULT_MODULI), 'checks': residues['checks'],
                      'outputs': ['data/COEFFICIENT_BINDING.json', 'data/coefficient_residues.json']}, indent=2))


if __name__ == '__main__':
    main()
