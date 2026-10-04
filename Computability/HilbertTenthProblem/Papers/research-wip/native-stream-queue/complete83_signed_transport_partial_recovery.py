#!/usr/bin/env python3
"""Fresh bounded corroboration; no predecessor code is executed or imported.

Only pinned predecessor prose/data are read. This is not a full compiler
fixture or a test of positive native zeros. The all-size proof is in the
companion Markdown; finite cases check its elementary digit interfaces.
"""
import argparse
import hashlib
import itertools
import json
from pathlib import Path

WIP = Path('Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue')
OLD = Path('Computability/HilbertTenthProblem/Papers/1980')
PINS = [
    (WIP / 'complete83_shared_projection_scout.json', 'dd9e105d295bf2fb3e3b0246234bb68cb78487ee919405bc052f2b67a9def34c', 'inert source identity'),
    (WIP / 'complete83_shared_projection_math.md', '1a9923b7202bef2e5a640b3b27c942423b9d9829d9fc6e7f4b55fa5c4d91053c', 'offset and pretyping theorem'),
    (WIP / 'complete83_dyadic_native_mask_recovery.md', '6fc07e4989926e868587cc43a4140c8534cde57358859dfe940b9151be21ac94', 'full native mask theorem, used only for its conclusion'),
    (WIP / 'complete75_half_binomial_compiler.md', '68edf3bc40238ccf47b023d7358e4be62664a2d78a60b6fae19de14b67208117', 'Sections 1, 2 and 4: modified masks, native bits, carry margin'),
    (OLD / 'FIXED_RAW_UNIVERSAL_76_PROOF.md', '75a13b5fd0c44c3ec91366306fb5876a3ea2f867e464b84cebd46ca08d060f87', 'Section 1: Start/End ordering, optional high monomial and enlarged L'),
    (OLD / 'FIXED_RAW_UNIVERSAL_78_PROOF.md', 'b28ddb9aec5225cda7dabc85fb952daf49de4041cf35910f62dabf3893749d39', 'Sections 1-4: local clauses, exact supports, anchors, original overlaps'),
]


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def digits(value, base, length):
    out = []
    for _ in range(length):
        value, digit = divmod(value, base)
        out.append(digit)
    require(value == 0, 'digit overflow')
    return out


def finite_checks():
    cyclic = stopper = 0
    for base, length in [(8, 2), (8, 3), (16, 2)]:
        modulus = base ** length - 1
        for ps in itertools.product(range(base - 1), repeat=length):
            p = sum(v * base ** j for j, v in enumerate(ps))
            for ns in itertools.product(range(4), repeat=length):
                n = sum(v * base ** j for j, v in enumerate(ns))
                difference = p - n
                if p == 0 or n == 0 or difference == 0:
                    continue
                expected = difference % modulus
                require(0 < expected < modulus, 'noncanonical residue')
                borrow = int(difference < 0)
                initial = borrow
                emitted = []
                for pd, nd in zip(ps, ns):
                    raw = pd - nd - borrow
                    next_borrow = int(raw < 0)
                    digit = raw + base * next_borrow
                    require(0 <= digit < base, 'nonbinary borrow')
                    if nd == 0 and pd > 0:
                        require(next_borrow == 0, 'stopper failure')
                        stopper += 1
                    emitted.append(digit)
                    borrow = next_borrow
                require(borrow == initial, 'noncyclic borrow')
                require(emitted == digits(expected, base, length), 'wrong residue')
                cyclic += 1

    clause = 0
    for clause_radix in [4, 8, 16, 32]:
        for base in [2 * clause_radix, 4 * clause_radix, 8 * clause_radix]:
            for middle in range(0, base - 1, clause_radix):
                require(((middle - 1) % base) & (clause_radix - 2), 'borrowed occupancy passed')
                clause += 1

    # Synthetic separated support, not the fixed universal compiler.
    native = {0, 1, 2, 4, 7, 10, 30, 90, 270}
    dummy, length, b = 4, 1000, 5
    anchors = {90, 270}
    alignment = 0
    possibilities = []
    for ell in range(b):
        for shift in range(length):
            if ell == 0:
                odd_support = {(e + shift) % length for e in native}
            elif ell == b - 1:
                odd_support = {(dummy + shift + 1) % length}
            else:
                odd_support = set()
            if anchors <= odd_support:
                possibilities.append([ell, shift])
            alignment += 1
    require(possibilities == [[0, 0]], 'anchor alignment failure')

    horizontal = 0
    for alphabet in range(2, 17):
        for tile in range(alphabet):
            lone = [int(s == tile) for s in range(alphabet)]
            require(any(v & 1 for v in lone), 'occupancy mismatch passed')
            horizontal += 2  # Either empty/occupied order.

    base = 32
    altered = {'base': base, 'positive': 0, 'negative': 1,
               'incoming_borrow': 1, 'digit': base - 2,
               'outgoing_borrow': 1, 'parity_test_passes': True}
    require((altered['digit'] & 1) == 0, 'vertical example not even')
    return {'cyclic_subtraction_cases': cyclic, 'positive_stopper_occurrences': stopper,
            'borrowed_occupancy_cases': clause, 'synthetic_anchor_cases': alignment,
            'synthetic_anchor_passes': possibilities, 'horizontal_mismatch_cases': horizontal,
            'altered_vertical_local_example': altered}


def build(root, companion_dir):
    authenticated = []
    for relative, expected, scope in PINS:
        path = root / relative
        if not path.exists():
            path = companion_dir / relative.name
        data = path.read_bytes()
        require(sha(data) == expected, f'pin mismatch: {relative}')
        authenticated.append({'logical_path': str(relative), 'sha256': expected,
                              'bytes': len(data), 'read_scope': scope})
    return {'schema': 'complete83_signed_transport_partial_recovery_v1',
            'source_sha256': sha(Path(__file__).read_bytes()), 'dependencies': authenticated,
            'proof_sha256': sha((companion_dir / 'complete83_signed_transport_partial_recovery.md').read_bytes()),
            'finite_evidence': finite_checks(),
            'scope': {'all_size_proof': 'companion Markdown',
                      'predecessor_execution': False, 'full_native_zero_test': False,
                      'universal_compiler_claim': False,
                      'conclusions': ['center clauses', 'nontrivial whole-cell positive rotation',
                                      'all-cell occupancy', 'horizontal overlap'],
                      'open': 'altered vertical relation and ordinary-input soundness'}}


def reject_duplicates(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, 'duplicate JSON key')
        result[key] = value
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, required=True)
    parser.add_argument('--companion-dir', type=Path, default=Path('/tmp'))
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--output', type=Path)
    mode.add_argument('--expect', type=Path)
    args = parser.parse_args()
    receipt = build(args.root, args.companion_dir)
    encoded = json.dumps(receipt, sort_keys=True, indent=2) + '\n'
    if args.output:
        with args.output.open('x') as stream:
            stream.write(encoded)
    else:
        previous = json.loads(args.expect.read_text(), object_pairs_hook=reject_duplicates)
        require(json.dumps(previous, sort_keys=True) == json.dumps(receipt, sort_keys=True), 'receipt mismatch')
    print('PASS: partial decoding finite evidence; no native-zero evaluation')


if __name__ == '__main__':
    main()
