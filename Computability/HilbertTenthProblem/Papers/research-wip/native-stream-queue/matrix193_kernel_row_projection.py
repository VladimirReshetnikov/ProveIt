#!/usr/bin/env python3
"""Complete pinned-data matrix recoding and a two-coordinate target interface."""
import argparse
import copy
import hashlib
import itertools
import json
from pathlib import Path

PINS = {
    'group_directed_semigroup193.json': 'c802f1ca0fde3cfcc856dd0f14ea2bf6270e1a9a924fe9743ee00c4336891639',
    'group_directed_semigroup193.md': '75f7e527b62717f21394750842a5569adc56231f1f6d6fab5e359e63b71ce56e',
    'matrix193_schreier_recode.json': 'e2a01632a9689aaf9ef5966b9f92772b59d71cd4d392d46346ebc890aa8dc9ea',
    'matrix193_schreier_recode.md': '17d67b09b8c05a453be7f23b66a3582fd90c776d57d6e32979b78425bd904f55',
    'u15_unary_block_interface.json': 'a08e400d61ae5df0a25916f899d7e1e9e0225bc1d1d40052d4dc89ed435c30a0',
    'u15_unary_block_interface.md': 'cdc686700af3545609796034e0a2c906bd0438b6bcabc0c0b267954cc9d20452',
}
P = [[1, 2], [0, 1]]
Q = [[1, 0], [2, 1]]
SOURCE = [
    ['cu11', '*', 'chi', 'c11'], ['dv11', '*', 'psi', 'd11'],
    ['target11', '-', 'cu11', 'dv11'],
    ['cu12', '*', 'chi', 'c12'], ['dv12', '*', 'psi', 'd12'],
    ['target12', '-', 'cu12', 'dv12'],
]


def need(ok, msg):
    if not ok:
        raise ValueError(msg)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def unique(pairs):
    out = {}
    for k, v in pairs:
        need(k not in out, 'duplicate JSON key')
        out[k] = v
    return out


def nonfinite(x):
    raise ValueError('nonfinite JSON ' + x)


def read(path):
    return json.loads(path.read_text(), object_pairs_hook=unique, parse_constant=nonfinite)


def exact(a, b):
    if type(a) is not type(b):
        return False
    if isinstance(a, dict):
        return a.keys() == b.keys() and all(exact(a[k], b[k]) for k in a)
    if isinstance(a, list):
        return len(a) == len(b) and all(exact(x, y) for x, y in zip(a, b))
    return a == b


def identity(n):
    return [[int(i == j) for j in range(n)] for i in range(n)]


def mul(a, b):
    n = len(a)
    return [[sum(a[i][k] * b[k][j] for k in range(n)) for j in range(n)] for i in range(n)]


def det(a):
    return a[0][0] * a[1][1] - a[0][1] * a[1][0]


def inv(a):
    need(det(a) == 1, 'determinant-one inverse')
    return [[a[1][1], -a[0][1]], [-a[1][0], a[0][0]]]


def power(a, n):
    if n < 0:
        return power(inv(a), -n)
    out = identity(len(a))
    while n:
        if n & 1:
            out = mul(out, a)
        a = mul(a, a)
        n //= 2
    return out


def block(a, b):
    return [r + [0, 0] for r in a] + [[0, 0] + r for r in b]


def reduce_word(w):
    out = []
    for a in w:
        need(a in [-2, -1, 1, 2], 'ambient letter')
        if out and out[-1] == -a:
            out.pop()
        else:
            out.append(a)
    return out


def inverse_word(w):
    return [-a for a in reversed(w)]


def ambient(w):
    out = identity(2)
    for a in w:
        m = P if abs(a) == 1 else Q
        out = mul(out, m if a > 0 else inv(m))
    return out


def E(j):
    return [-2] * j + [1] + [2] * j


def q_exponent(w):
    return sum(1 if a == 2 else -1 if a == -2 else 0 for a in w)


def word_image(w, codes):
    out = identity(2)
    for a in w:
        out = mul(out, codes[a])
    return out


def emit(parent, codes):
    matrices = []
    for kind in ['A', 'B']:
        for t in parent['tiles']:
            i = t['id']
            lower = ambient(E(i))
            upper = word_image(t['h'] if kind == 'A' else t['g'], codes)
            if kind == 'B':
                upper = inv(upper)
                lower = mul(mul(inv(P), inv(lower)), P)
            matrices.append({'name': kind + str(i), 'tile_id': i, 'matrix': block(upper, lower)})
    matrices.append({'name': 'C', 'tile_id': None,
                     'matrix': block(inv(word_image(parent['terminal'] + '#', codes)), P)})
    return matrices


def stats(matrices):
    values = [x for g in matrices for r in g['matrix'] for x in r]
    return {'generators': len(matrices), 'entry_slots': len(values),
            'nonzero_entries': sum(x != 0 for x in values),
            'maximum_absolute_entry': max(map(abs, values)),
            'maximum_magnitude_bits': max(abs(x).bit_length() for x in values),
            'sum_magnitude_bits': sum(abs(x).bit_length() for x in values)}


def run_source(chi, psi, C, D):
    values = {'chi': chi, 'psi': psi, 'c11': C[0][0], 'c12': C[0][1],
              'd11': D[0][0], 'd12': D[0][1]}
    for n, op, a, b in SOURCE:
        values[n] = values[a] * values[b] if op == '*' else values[a] - values[b]
    return [values['target11'], values['target12']]


def verify(root):
    for name, pin in PINS.items():
        need(sha((root / name).read_bytes()) == pin, 'pin ' + name)
    original = read(root / 'group_directed_semigroup193.json')
    parent = original['packet']
    letters = parent['alphabet'] + [parent['separator']]
    need(len(letters) == 20 and letters[:2] == ['0', '1'], 'active alphabet')
    # Invertible basis change: a=E0 E1^-1, b=E1; E0=ab.
    words = [reduce_word(E(0) + inverse_word(E(1))), E(1)] + [E(j) for j in range(2, 20)]
    need(reduce_word(words[0] + words[1]) == E(0), 'Nielsen inverse E0=ab')
    need(words[1:] == [E(j) for j in range(1, 20)], 'remaining basis unchanged')
    need(all(q_exponent(w) == 0 for w in words), 'upper kernel membership')
    code_words = dict(zip(letters, words))
    codes = {a: ambient(w) for a, w in code_words.items()}
    old_codes = {a: ambient(E(j)) for a, j in parent['top_codes'].items()}
    need(exact(emit(parent, old_codes), parent['generators']), 'all original entries reconstructed')
    generators = emit(parent, codes)
    need(len(generators) == len({tuple(x for r in g['matrix'] for x in r) for g in generators}) == 193, 'distinct full array')
    for old, new in zip(parent['generators'], generators):
        need(old['name'] == new['name'] and old['tile_id'] == new['tile_id'], 'stable generator indices')
        m = new['matrix']; top = [r[:2] for r in m[:2]]; bottom = [r[2:] for r in m[2:]]
        need(bottom == [r[2:] for r in old['matrix'][2:]], 'all lower blocks unchanged')
        need(det(top) == det(bottom) == 1, 'block determinants')
        for b in [top, bottom]:
            need([[x % 2 for x in row] for row in b] == identity(2), 'Gamma2 block')
    for tile in parent['tiles']:
        w = E(tile['id'])
        need(q_exponent(w) == q_exponent([-1] + inverse_word(w) + [1]) == 0, 'lower kernel words')
    W = word_image('01010111', codes)
    need(W == mul(power(P, 3), power(ambient(E(1)), 2)), 'physical block word')
    need(W[0][0] + W[1][1] == -94, 'block trace')
    B = mul(W, W); a0 = (B[0][0] + B[1][1]) // 2
    D = [[B[i][j] - a0 * int(i == j) for j in range(2)] for i in range(2)]
    Delta = a0*a0 - 1
    need(a0 == 4417 and mul(D, D) == [[Delta, 0], [0, Delta]], 'quadratic power algebra')
    witness = original['accepting_witness']; product = identity(4)
    by_name = {g['name']: g['matrix'] for g in generators}
    for name in witness['generator_word']:
        product = mul(product, by_name[name])
    w = witness['input']['configuration_word']
    target = block(inv(word_image(w + '#', codes)), P)
    need(product == target and len(witness['generator_word']) == 167, 'complete accepting product')
    projected = [target[0][0], target[0][1], target[2][2], target[2][3]]
    need(projected[2:] == [1, 2], 'constant lower row')
    # Literal six-row circuit, retaining every supplied coefficient and output.
    free = {'chi', 'psi', 'c11', 'c12', 'd11', 'd12'}
    known = set(free); dependencies = {}
    for n, op, a, b in SOURCE:
        need(n not in known and a in known and b in known and op in ['*', '-'], 'source closure')
        known.add(n); dependencies[n] = [a, b]
    live = set(); pending = ['target11', 'target12']
    while pending:
        n = pending.pop()
        if n not in live:
            live.add(n); pending.extend(dependencies.get(n, []))
    need(live == known and sum(row[1] == '*' for row in SOURCE) == 4, 'full source liveness/ledger')
    # Exact powers and generic fixed-context assembly; these are diagnostic
    # context words, not materialized arbitrary-program compiler outputs.
    contexts = ['', '0', '1', 'A', '[', ']', '#', '01', '[A0', '10]']
    chi, psi = 1, 0; powers = []; assemblies = []
    for x in range(13):
        minus = [[chi * int(i == j) - psi * D[i][j] for j in range(2)] for i in range(2)]
        need(minus == power(B, -x), 'exact indexed power')
        powers.append({'x': x, 'chi': chi, 'psi': psi, 'negative_power': minus})
        for u, v in itertools.product(contexts, repeat=2):
            L = inv(word_image(v + '#', codes)); R = inv(word_image(u, codes))
            C = mul(L, R); F = mul(mul(L, D), R)
            row = run_source(chi, psi, C, F)
            full = mul(mul(L, minus), R)
            need(row == full[0], 'six-operation context assembly')
            need(full == inv(word_image(u + '01010111'*(2*x) + v + '#', codes)), 'literal word target')
            assemblies.append([u, v, x, row])
        chi, psi = a0*chi + Delta*psi, chi + a0*psi
    signed_codes = [codes[a] for a in letters[:4]]
    signed_codes += [inv(m) for m in signed_codes]
    seen = {}; reduced_words = 0
    for length in range(4):
        for index_word in itertools.product(range(8), repeat=length):
            if any((a + 4) % 8 == b for a, b in zip(index_word, index_word[1:])):
                continue
            value = identity(2)
            for index in index_word:
                value = mul(value, signed_codes[index])
            row = tuple(value[0])
            need(row not in seen, 'bounded distinct reduced words/rows')
            seen[row] = index_word; reduced_words += 1
    # Necessity of the subgroup condition: Gamma(2) alone does not suffice.
    bad = power(Q, 2)
    need(bad[0] == identity(2)[0] and bad != identity(2), 'unipotent row collision')
    packet = copy.deepcopy(parent)
    packet['schema'] = 'literal-directed-u15-semigroup193-kernel-row-v1'
    del packet['top_codes']; del packet['changed_generators']
    packet['top_words_in_PQ'] = code_words; packet['top_matrices'] = codes
    packet['generators'] = generators; packet['ledger'] = stats(generators)
    previous = read(root / 'matrix193_schreier_recode.json')
    return {'status': 'PASS', 'source_sha256': sha(Path(__file__).read_bytes()), 'pins': PINS,
            'packet': packet, 'old_statistics': stats(parent['generators']),
            'schreier1057_statistics': stats(previous['packet']['generators']),
            'new_statistics': stats(generators),
            'block': {'word': '01010111', 'matrix': W, 'trace': -94, 'square': B,
                      'Pell_parameter': a0, 'Delta': Delta, 'D': D, 'checked_powers': powers},
            'projected_relation': {'varying_integer_inputs': ['upper11', 'upper12'],
                'observed_matrix_positions_zero_based': [[0, 0], [0, 1], [2, 2], [2, 3]],
                'constant_lower_row': [1, 2], 'nonempty_positive_products_only': True,
                'both_block_groups_have_Q_exponent_zero': True},
            'target_assembly': {'source': SOURCE, 'supplied_ports': sorted(free),
                'varying_Pell_ports': ['chi', 'psi'], 'fixed_context_coefficients': ['c11', 'c12', 'd11', 'd12'],
                'outputs': ['target11', 'target12'], 'M': 4, 'A': 2, 'total': 6,
                'scope': 'Correctly indexed Pell coordinates supplied. Index relation and unbounded product certificate are not included.'},
            'accepting_witness': {'input_word': w, 'generator_word': witness['generator_word'],
                'product': product, 'target': target, 'projected_target': projected},
            'evidence': {'all_parent_entries_reconstructed': 3088, 'new_entries_emitted': 3088,
                'lower_blocks_unchanged': 193, 'diagnostic_context_assemblies': len(assemblies),
                'assemblies_sha256': sha(json.dumps(assemblies, separators=(',', ':')).encode()),
                'distinct_reduced_words_first_rows': reduced_words,
                'Gamma2_alone_counterexample': bad},
            'scope': 'Complete fixed193 recoding and exact projected membership equivalence; finite diagnostics do not establish freeness or universal simulation.',
            'new_universal_Diophantine_bound': False, 'predecessor_code_executed': False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, required=True)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--output', type=Path); mode.add_argument('--expect', type=Path)
    args = parser.parse_args(); result = verify(args.root.resolve())
    serialized = json.dumps(result, indent=2, sort_keys=True) + '\n'
    need(exact(result, json.loads(serialized)), 'exact JSON roundtrip')
    if args.expect:
        need(exact(result, read(args.expect)), 'type-exact saved receipt')
    else:
        args.output.write_text(serialized)
    print(json.dumps({'status': 'PASS', 'statistics': result['new_statistics'],
                      'target_operations': 6, 'Pell_parameter': 4417, 'evidence': result['evidence']}, sort_keys=True))


if __name__ == '__main__':
    main()
