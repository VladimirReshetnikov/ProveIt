#!/usr/bin/env python3
"""Fresh finite corroboration of the all-size vertical-borrow obstruction.

No predecessor program is executed/imported. Pinned source/proof files are
read as bytes only. Finite relaxed blocks are not native zero fixtures.
"""
import argparse
import hashlib
import itertools
import json
from pathlib import Path

WIP = Path('Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue')
OLD = Path('Computability/HilbertTenthProblem/Papers/1980')
PINS = [
    (WIP / 'complete83_shared_projection_scout.json', 'dd9e105d295bf2fb3e3b0246234bb68cb78487ee919405bc052f2b67a9def34c', 'unchanged full source bytes'),
    (WIP / 'complete83_shared_projection_math.md', '1a9923b7202bef2e5a640b3b27c942423b9d9829d9fc6e7f4b55fa5c4d91053c', 'source-aligned offset and positive inverse'),
    (WIP / 'complete83_dyadic_negative_offset_exclusion.md', '9e24c06c8627e50718f0b00236df7dbb83e8ac9701bc3536e097148b3ae922f2', 'negative dyadic branch exclusion'),
    (WIP / 'complete83_dyadic_native_mask_recovery.md', '6fc07e4989926e868587cc43a4140c8534cde57358859dfe940b9151be21ac94', 'dyadic W=0 native masks'),
    (WIP / 'complete83_signed_transport_partial_recovery.md', '5904b0d16501921473de2ef2bfc52dff612450808a4df8c8469f85f6cae848c7', 'full partial decoding proof, all cells occupied and positive rotation aligned'),
    (WIP / 'complete83_even_radix_boundary.md', 'eba3e2944154dd7ff28e5b20d5e32e8ee6a0138b515c8e5f3846979dadaaa8dc', 'odd-q exclusion; non-dyadic diagnostic scope unchanged'),
    (OLD / 'FIXED_RAW_UNIVERSAL_81_PROOF.md', 'e8321ed4b6e3dd19fadcb33c3b6a3fd9aa487e9051463d4bdcd89884ae26803f', 'Section 1: literal Start H,H,H; at least three distinct tiles'),
    (OLD / 'FIXED_RAW_UNIVERSAL_78_PROOF.md', 'b28ddb9aec5225cda7dabc85fb952daf49de4041cf35910f62dabf3893749d39', 'Sections 1-4: one-hot copies, six contiguous vertical blocks and exact positive contributions'),
    (OLD / 'FIXED_RAW_UNIVERSAL_76_PROOF.md', '75a13b5fd0c44c3ec91366306fb5876a3ea2f867e464b84cebd46ca08d060f87', 'Section 1: unchanged tile geometry and optional high-monomial separation'),
]


def require(value, message):
    if not value:
        raise ValueError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def local_checks():
    passing = []
    for p, n, incoming in itertools.product(range(3), range(2), range(2)):
        raw = p - n - incoming
        outgoing = int(raw < 0)
        digit = raw + 32 * outgoing
        if digit % 2 == 0:
            require(incoming or not outgoing, 'borrow was created')
            require(not outgoing or (incoming, p, n) == (1, 0, 1), 'unexpected persistence')
            require(n or not outgoing, 'zero negative digit failed to reset')
            passing.append({'positive': p, 'negative': n, 'incoming': incoming,
                            'outgoing': outgoing, 'digit': digit})
    require(len(passing) == 6, 'local table count')
    return passing


def block_checks():
    tested = accepted = 0
    transitions = {}
    for alphabet in range(3, 9):
        for own, previous_last, incoming in itertools.product(range(alphabet), range(2), range(2)):
            negative = [previous_last] + [int(s - 1 == own) for s in range(1, alphabet)]
            require(sum(negative) == 1 - int(own == alphabet - 1) + previous_last,
                    'shift endpoint count')
            require(sum(negative) <= 2 and 0 in negative, 'no resetting digit')
            ends = set()
            for left, right in itertools.product(range(alphabet), repeat=2):
                positive = [int(s == left) + int(s == right) for s in range(alphabet)]
                require(sum(positive) == 2, 'positive one-hot count')
                borrow = incoming
                passes = True
                for p, n in zip(positive, negative):
                    raw = p - n - borrow
                    next_borrow = int(raw < 0)
                    digit = raw + 32 * next_borrow
                    if digit % 2:
                        passes = False
                        break
                    require(borrow or not next_borrow, 'restart within block')
                    borrow = next_borrow
                tested += 1
                if passes:
                    require(borrow == 0, 'first block failed to reset by its end')
                    if incoming == 0:
                        require(sum(negative) % 2 == 0, 'borrow-free odd weight')
                    accepted += 1
                    ends.add(borrow)
            transitions[(alphabet, own, previous_last, incoming)] = ends

    patterns = 0
    # Previous block plus three middle-row labels and one repeated top label.
    # Positive one-hot pairs remain completely unconstrained between blocks.
    for alphabet in range(3, 8):
        for previous, m2, m1, m0, top in itertools.product(range(alphabet), repeat=5):
            labels = [m2, m1, m0, top, top, top]
            states = {0, 1}
            prev = previous
            for index, own in enumerate(labels):
                next_states = set()
                for incoming in states:
                    next_states.update(transitions[(alphabet, own, int(prev == alphabet - 1), incoming)])
                states = next_states
                prev = own
                if index >= 4:
                    require(not states, 'constant top row admitted relaxed six-block solution')
            patterns += 1
    return {'one_hot_block_assignments': tested, 'passing_block_assignments': accepted,
            'alphabet_sizes': list(range(3, 9)), 'six_block_relaxed_negative_patterns': patterns,
            'six_block_alphabets': list(range(3, 8)), 'six_block_survivors': 0}


def geometry_checks():
    cases = 0
    order = [(1, 2), (1, 1), (1, 0), (0, 2), (0, 1), (0, 0)]
    for alphabet in range(3, 33):
        for selectors in range(2, 8):
            start = selectors + 3 * alphabet
            positions = [start + (2 - r) * 3 * alphabet + (2 - c) * alphabet + s
                         for r, c in order for s in range(alphabet)]
            require(positions == list(range(start + 3 * alphabet, start + 9 * alphabet)),
                    'vertical targets not contiguous')
            require(all(start <= e - 1 < start + 9 * alphabet for e in positions),
                    'negative predecessor left tile-copy block')
            cases += 1
    return {'synthetic_layout_parameter_pairs': cases, 'actual_order': order,
            'formula_scope': 'arbitrary integer alphabet>=3; finite corroboration only'}


def build(root, companions):
    dependencies = []
    for relative, expected, scope in PINS:
        path = root / relative
        if not path.exists():
            path = companions / relative.name
        data = path.read_bytes()
        require(digest(data) == expected, f'pin mismatch: {relative}')
        dependencies.append({'logical_path': str(relative), 'sha256': expected,
                             'bytes': len(data), 'read_scope': scope})
    return {'schema': 'complete83_dyadic_zero_offset_exclusion_v1',
            'source_sha256': digest(Path(__file__).read_bytes()),
            'proof_sha256': digest((companions / 'complete83_dyadic_zero_offset_exclusion.md').read_bytes()),
            'dependencies': dependencies, 'passing_local_table': local_checks(),
            'one_hot_checks': block_checks(), 'geometry_checks': geometry_checks(),
            'scope': {'predecessor_execution': False, 'native_zero_evaluation': False,
                      'source_change': False, 'unconstrained_universal_83_claim': False,
                      'theorem': 'No dyadic W=0 positive zero on actual compiler slice',
                      'corollary': 'Every dyadic zero has U=H*rho for positive integer rho',
                      'remaining_radix_sector': 'even and non-dyadic'}}


def unique_pairs(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, 'duplicate JSON key')
        result[key] = value
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, required=True)
    parser.add_argument('--companion-dir', type=Path, default=Path('/tmp'))
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument('--output', type=Path)
    modes.add_argument('--expect', type=Path)
    args = parser.parse_args()
    receipt = build(args.root, args.companion_dir)
    if args.output:
        with args.output.open('x') as stream:
            stream.write(json.dumps(receipt, indent=2, sort_keys=True) + '\n')
    else:
        old = json.loads(args.expect.read_text(), object_pairs_hook=unique_pairs)
        require(json.dumps(old, sort_keys=True) == json.dumps(receipt, sort_keys=True), 'receipt mismatch')
    print('PASS: dyadic W=0 exclusion finite evidence; no predecessor execution')


if __name__ == '__main__':
    main()
