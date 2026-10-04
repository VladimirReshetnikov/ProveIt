#!/usr/bin/env python3
"""Pinned-data recoding of all193 matrices through a checked19-sheet cover."""
import argparse
import copy
import hashlib
import json
from pathlib import Path

PINS = {
    'group_directed_semigroup193.json': 'c802f1ca0fde3cfcc856dd0f14ea2bf6270e1a9a924fe9743ee00c4336891639',
    'group_directed_semigroup193.md': '75f7e527b62717f21394750842a5569adc56231f1f6d6fab5e359e63b71ce56e',
    'u15_unary_block_interface.json': 'a08e400d61ae5df0a25916f899d7e1e9e0225bc1d1d40052d4dc89ed435c30a0',
    'u15_unary_block_interface.md': 'cdc686700af3545609796034e0a2c906bd0438b6bcabc0c0b267954cc9d20452',
}
P = [[1, 2], [0, 1]]
Q = [[1, 0], [2, 1]]


def need(ok, message):
    if not ok:
        raise ValueError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def exact(a, b):
    if type(a) is not type(b):
        return False
    if isinstance(a, dict):
        return a.keys() == b.keys() and all(exact(a[k], b[k]) for k in a)
    if isinstance(a, list):
        return len(a) == len(b) and all(exact(x, y) for x, y in zip(a, b))
    return a == b


def unique(pairs):
    out = {}
    for key, value in pairs:
        need(key not in out, 'duplicate JSON key')
        out[key] = value
    return out


def bad_constant(value):
    raise ValueError('nonfinite JSON ' + value)


def read_json(path):
    return json.loads(path.read_text(), object_pairs_hook=unique, parse_constant=bad_constant)


def identity(n):
    return [[int(i == j) for j in range(n)] for i in range(n)]


def mul(a, b):
    n = len(a)
    return [[sum(a[i][k] * b[k][j] for k in range(n)) for j in range(n)] for i in range(n)]


def det(a):
    return a[0][0] * a[1][1] - a[0][1] * a[1][0]


def inv(a):
    need(len(a) == 2 and det(a) == 1, 'SL2 inverse')
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
    return [row + [0, 0] for row in a] + [[0, 0] + row for row in b]


def reduce_word(word):
    out = []
    for letter in word:
        need(letter in (-2, -1, 1, 2), 'ambient free letter')
        if out and out[-1] == -letter:
            out.pop()
        else:
            out.append(letter)
    return out


def inverse_word(word):
    return [-x for x in reversed(word)]


def ambient(word):
    out = identity(2)
    for letter in word:
        a = P if abs(letter) == 1 else Q
        out = mul(out, a if letter > 0 else inv(a))
    return out


def cover():
    # Right actions: P fixes0 and cycles1..18; Q interchanges0,1.
    p_action = [0] + list(range(2, 19)) + [1]
    q_action = [1, 0] + list(range(2, 19))
    need(sorted(p_action) == sorted(q_action) == list(range(19)), 'cover permutations')
    paths = [[]] + [[2] + [1] * r for r in range(18)]
    def end(word):
        v = 0
        for letter in word:
            action = p_action if abs(letter) == 1 else q_action
            v = action[v] if letter > 0 else action.index(v)
        return v
    need([end(w) for w in paths] == list(range(19)), 'tree paths reach every vertex')
    tree_edges = {(0, 2)} | {(v, 1) for v in range(1, 18)}
    chords = []
    for v in range(19):
        for letter, action in [(1, p_action), (2, q_action)]:
            w = reduce_word(paths[v] + [letter] + inverse_word(paths[action[v]]))
            if (v, letter) in tree_edges:
                need(w == [], 'tree edge contracts')
            else:
                need(w and end(w) == 0, 'non-tree closed loop')
                chords.append({'vertex': v, 'letter': letter, 'word': w})
    basis = [[1], [2, 2], [2] + [1] * 18 + [-2]]
    basis += [[2] + [1] * r + [2] + [-1] * r + [-2] for r in range(1, 18)]
    need(len(chords) == 20 and {tuple(c['word']) for c in chords} == {tuple(w) for w in basis}, 'all20 Schreier basis words')
    need(len(tree_edges) == 18 and 38 - 19 + 1 == 20, 'cover/tree Euler count')
    # Change the first2 basis elements from P,Q^2 to a=P Q^2,b=Q^-2.
    new_basis = [[1, 2, 2], [-2, -2]] + basis[2:]
    need(reduce_word(new_basis[0] + new_basis[1]) == basis[0], 'P=a*b')
    need(inverse_word(new_basis[1]) == basis[1], 'Q^2=b^-1')
    need(all(end(w) == 0 for w in new_basis), 'recoded generators are cover loops')
    return {'vertices': 19, 'P_action': p_action, 'Q_action': q_action,
            'tree_paths': paths, 'tree_edges': [list(e) for e in sorted(tree_edges)],
            'chords': chords, 'old_basis': basis, 'new_basis': new_basis}


def word_image(word, codes):
    out = identity(2)
    for letter in word:
        out = mul(out, codes[letter])
    return out


def emit(packet, codes):
    out = []
    for kind in ('A', 'B'):
        for tile in packet['tiles']:
            i = tile['id']
            lower = ambient([-2] * i + [1] + [2] * i)
            if kind == 'A':
                upper = word_image(tile['h'], codes)
            else:
                upper = inv(word_image(tile['g'], codes))
                lower = mul(mul(inv(P), inv(lower)), P)
            out.append({'name': kind + str(i), 'tile_id': i, 'matrix': block(upper, lower)})
    out.append({'name': 'C', 'tile_id': None,
                'matrix': block(inv(word_image(packet['terminal'] + packet['separator'], codes)), P)})
    return out


def stats(generators):
    values = [x for g in generators for row in g['matrix'] for x in row]
    return {'generators': len(generators), 'matrix_entry_slots': len(values),
            'nonzero_entries': sum(x != 0 for x in values),
            'maximum_absolute_entry': max(map(abs, values)),
            'maximum_entry_magnitude_bits': max(abs(x).bit_length() for x in values),
            'sum_entry_magnitude_bits': sum(abs(x).bit_length() for x in values)}


def verify(root):
    for name, pin in PINS.items():
        need(sha((root / name).read_bytes()) == pin, 'pin ' + name)
    parent = read_json(root / 'group_directed_semigroup193.json')
    original = parent['packet']
    old_codes = {s: ambient([-2] * j + [1] + [2] * j) for s, j in original['top_codes'].items()}
    need(exact(emit(original, old_codes), original['generators']), 'all original193 matrices reconstructed')
    graph = cover()
    letters = original['alphabet'] + [original['separator']]
    need(len(letters) == len(set(letters)) == 20 and letters[:2] == ['0', '1'], 'active alphabet')
    words = dict(zip(letters, graph['new_basis']))
    codes = {s: ambient(w) for s, w in words.items()}
    need(all(det(m) == 1 for m in codes.values()), 'letter determinants')
    generators = emit(original, codes)
    need(len({tuple(x for row in g['matrix'] for x in row) for g in generators}) == 193, 'all193 distinct')
    for old, new in zip(original['generators'], generators):
        need(old['name'] == new['name'] and old['tile_id'] == new['tile_id'], 'generator identity')
        need([row[2:] for row in old['matrix'][2:]] == [row[2:] for row in new['matrix'][2:]], 'unchanged lower block')
        need(det([row[:2] for row in new['matrix'][:2]]) == 1 and det([row[2:] for row in new['matrix'][2:]]) == 1, 'block determinants')
    witness = parent['accepting_witness']
    tiles = {t['id']: t for t in original['tiles']}
    sequence = witness['inner_tile_sequence']
    input_word = witness['input']['configuration_word']
    lhs = input_word + '#' + ''.join(tiles[i]['h'] for i in sequence)
    rhs = ''.join(tiles[i]['g'] for i in sequence) + original['terminal'] + '#'
    need(lhs == rhs, 'literal accepted word equation')
    expected_word = ['A' + str(i) for i in sequence] + ['C'] + ['B' + str(i) for i in reversed(sequence)]
    need(expected_word == witness['generator_word'] and len(expected_word) == 167, 'full witness generator word')
    by_name = {g['name']: g['matrix'] for g in generators}
    product = identity(4)
    for name in expected_word:
        product = mul(product, by_name[name])
    target = block(inv(word_image(input_word + '#', codes)), P)
    need(product == target, 'all16 recoded accepting product entries')
    W = word_image('01010111', codes)
    need(W == [[-47, 6], [-8, 1]] and W == mul(power(P, 3), power(Q, -4)), 'universal block image')
    even = mul(W, W)
    a0 = (even[0][0] + even[1][1]) // 2
    D = [[even[i][j] - a0 * int(i == j) for j in range(2)] for i in range(2)]
    Delta = a0 * a0 - 1
    need(a0 == 1057 and Delta == 1117248 and mul(D, D) == [[Delta, 0], [0, Delta]], 'new quadratic algebra')
    chi, psi = 1, 0
    powers = []
    for x in range(13):
        plus = [[chi * int(i == j) + psi * D[i][j] for j in range(2)] for i in range(2)]
        minus = [[chi * int(i == j) - psi * D[i][j] for j in range(2)] for i in range(2)]
        need(plus == power(even, x) and minus == power(even, -x), 'indexed Pell powers')
        need(chi * chi - Delta * psi * psi == 1, 'Pell norm')
        powers.append({'x': x, 'chi': chi, 'psi': psi, 'positive_power': plus, 'negative_power': minus})
        chi, psi = a0 * chi + Delta * psi, chi + a0 * psi
    packet = copy.deepcopy(original)
    packet['schema'] = 'literal-directed-u15-semigroup193-schreier19-v1'
    del packet['top_codes']
    del packet['changed_generators']
    packet['top_words_in_PQ'] = words
    packet['top_matrices'] = codes
    packet['generators'] = generators
    packet['ledger'].update(stats(generators))
    packet['ledger'].pop('largest_retained_top_code')
    packet['ledger'].pop('changed_retained_generators')
    packet['ledger'].pop('unchanged_retained_generators')
    packet['ledger']['upper_blocks_equal_to_parent'] = sum(o['matrix'][:2] == n['matrix'][:2] for o, n in zip(original['generators'], generators))
    packet['ledger']['cover_vertices'] = 19
    return {'status': 'PASS', 'source_sha256': sha(Path(__file__).read_bytes()), 'pins': PINS,
            'packet': packet, 'cover': graph, 'old_statistics': stats(original['generators']),
            'new_statistics': stats(generators),
            'accepting_witness': {'input_word': input_word, 'inner_tile_sequence': sequence,
                'generator_word': expected_word, 'target': target, 'product': product,
                'tile_count': len(sequence), 'generator_word_length': len(expected_word)},
            'universal_block': {'word': '01010111', 'matrix': W, 'trace': -46,
                'square': even, 'Pell_base': a0, 'Delta': Delta, 'D': D,
                'old_Pell_base': 39979681, 'checked_powers': powers},
            'evidence_counts': {'original_entries_reconstructed': 3088, 'new_entries_emitted': 3088,
                'cover_directed_edges': 38, 'tree_edges': 18, 'free_basis_elements': 20,
                'lower_blocks_unchanged': 193, 'accepting_product_entries': 16, 'Pell_powers': 13},
            'scope': 'Full fixed matrix recode and finite accepted product; universality uses the pinned word theorem and faithful cover basis. No arbitrary-program compiler execution.',
            'arithmetic_scope': 'The correctly indexed Pell-coordinate assembly still costs12 operations; exact index relation and unbounded membership certificate remain unpaid.',
            'new_universal_Diophantine_bound': False, 'predecessor_code_executed': False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, required=True)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--expect', type=Path)
    mode.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = verify(args.root.resolve())
    serialized = json.dumps(result, indent=2, sort_keys=True) + '\n'
    need(exact(result, json.loads(serialized)), 'type-exact JSON roundtrip')
    if args.expect:
        need(exact(result, read_json(args.expect)), 'exact saved receipt')
    else:
        args.output.write_text(serialized)
    print(json.dumps({'status': 'PASS', 'statistics': result['new_statistics'], 'Pell_base': 1057}, sort_keys=True))


if __name__ == '__main__':
    main()
