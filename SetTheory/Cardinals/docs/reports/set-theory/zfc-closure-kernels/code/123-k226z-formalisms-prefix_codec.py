#!/usr/bin/env python3
"""A fully declared binary prefix codec for finite equational presentations.

Every symbol and its arity/variable kind is included in the binary header.
This is a packet encoding, not a binary Turing-machine implementation.
"""
from collections import Counter
from hashlib import sha256
import argparse
import heapq
import json
from pathlib import Path


def require(condition, reason):
    if not condition:
        raise ValueError(reason)


def variable_counts(term):
    if isinstance(term, str):
        return Counter([term])
    answer = Counter()
    for child in term[1:]:
        answer.update(variable_counts(child))
    return answer


def prepare(data):
    signature = data['signature']
    require(all(type(a) is int and 0 <= a <= 2 for a in signature.values()), 'Arity outside codec')
    frequencies = Counter()
    variables = []

    def visit(term, env):
        if isinstance(term, str):
            symbol = ('v', env[term])
            frequencies[symbol] += 1
            return symbol
        name = term[0]
        require(name in signature and len(term) == signature[name] + 1, 'Malformed term')
        symbol = ('f', name)
        frequencies[symbol] += 1
        return (symbol, *(visit(child, env) for child in term[1:]))

    equations = []
    for left, right in data['equations']:
        counts = variable_counts(left) + variable_counts(right)
        env = {name: i for i, name in enumerate(sorted(counts, key=lambda n: (-counts[n], n)))}
        variables.append(env)
        equations.append((visit(left, env), visit(right, env)))
    require(not variable_counts(data['start']) and not variable_counts(data['target']), 'Nonground query')
    endpoints = [visit(data[k], {}) for k in ('start', 'target')]
    require(set(signature) == {s[1] for s in frequencies if s[0] == 'f'}, 'Unused operation declaration')
    return equations, endpoints, frequencies, variables


def encode(data):
    equations, endpoints, frequencies, variables = prepare(data)
    heap, serial = [], 0
    for symbol, weight in sorted(frequencies.items(), key=lambda x: str(x[0])):
        heapq.heappush(heap, (weight, serial, ('leaf', symbol)))
        serial += 1
    require(len(heap) >= 2, 'This codec requires at least two symbols')
    while len(heap) > 1:
        wa, _, a = heapq.heappop(heap)
        wb, _, b = heapq.heappop(heap)
        heapq.heappush(heap, (wa + wb, serial, ('node', a, b)))
        serial += 1
    tree = heap[0][2]
    codes, leaves = {}, []

    def header(node, prefix=''):
        if node[0] == 'node':
            return '0' + header(node[1], prefix + '0') + header(node[2], prefix + '1')
        symbol = node[1]
        codes[symbol] = prefix
        kind = 3 if symbol[0] == 'v' else data['signature'][symbol[1]]
        leaves.append({'symbol': list(symbol), 'code': prefix, 'kind': kind,
                       'frequency': frequencies[symbol]})
        return {2: '10', 3: '110', 0: '1110', 1: '1111'}[kind]

    book = header(tree)

    def term_bits(term):
        if term[0] == 'v':
            return codes[term]
        return codes[term[0]] + ''.join(term_bits(c) for c in term[1:])

    terms = [''.join(term_bits(t) for t in pair) for pair in equations]
    query = ''.join(term_bits(t) for t in endpoints)
    bits = book + ''.join('1' + row for row in terms) + '0' + query
    return bits, {'header_bits': len(book), 'equation_term_bits': sum(map(len, terms)),
                  'equation_framing_bits': len(equations) + 1, 'query_bits': len(query),
                  'complete_packet_bits': len(bits), 'leaves': leaves,
                  'local_variable_maps': variables,
                  'bits_sha256': sha256(bits.encode('ascii')).hexdigest()}


def decode(bits):
    """Decode using only the packet. No source signature or Huffman table is read."""
    require(isinstance(bits, str) and all(c in '01' for c in bits), 'Nonbit input')
    cursor, arities, variable_count = 0, [], 0

    def take(n):
        nonlocal cursor
        require(cursor + n <= len(bits), 'Truncated packet')
        value = bits[cursor:cursor+n]
        cursor += n
        return value

    def parse_book():
        nonlocal variable_count
        if take(1) == '0':
            return ('node', parse_book(), parse_book())
        if take(1) == '0':
            kind = 2
        elif take(1) == '0':
            kind = 3
        else:
            kind = int(take(1))
        if kind == 3:
            result = ('v', variable_count)
            variable_count += 1
        else:
            result = ('f', len(arities), kind)
            arities.append(kind)
        return ('leaf', result)

    tree = parse_book()
    require(tree[0] == 'node' and arities, 'Malformed alphabet')

    def parse_term():
        node = tree
        while node[0] == 'node':
            node = node[1 + int(take(1))]
        symbol = node[1]
        if symbol[0] == 'v':
            return 'v' + str(symbol[1])
        return [symbol[1], *(parse_term() for _ in range(symbol[2]))]

    equations = []
    while take(1) == '1':
        equations.append([parse_term(), parse_term()])
    start, target = parse_term(), parse_term()
    require(cursor == len(bits), 'Trailing data')
    require(not variable_counts(start) and not variable_counts(target), 'Nonground endpoints')
    return {'signature_arities': arities, 'variable_capacity': variable_count,
            'equations': equations, 'start': start, 'target': target}


def expected_decoding(data, metadata):
    operations, variable_slots, arities = {}, {}, []
    for leaf in metadata['leaves']:
        family, name = leaf['symbol']
        if family == 'v':
            variable_slots[name] = 'v' + str(len(variable_slots))
        else:
            operations[name] = len(operations)
            arities.append(data['signature'][name])

    def rename(term, env):
        if isinstance(term, str):
            return variable_slots[env[term]]
        return [operations[term[0]], *(rename(c, env) for c in term[1:])]

    equations = [[rename(t, env) for t in pair]
                 for pair, env in zip(data['equations'], metadata['local_variable_maps'])]
    return {'signature_arities': arities, 'variable_capacity': len(variable_slots),
            'equations': equations, 'start': rename(data['start'], {}),
            'target': rename(data['target'], {})}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    raw = args.input.read_bytes()
    data = json.loads(raw)
    bits, metrics = encode(data)
    decoded = decode(bits)
    require(decoded == expected_decoding(data, metrics), 'Decoded presentation differs up to renaming')
    for n in range(len(bits)):
        try:
            decode(bits[:n])
        except (ValueError, RecursionError):
            pass
        else:
            raise ValueError(f'Accepted strict truncation {n}')
    malformed = [bits + '0', bits + '1', bits[:-1] + 'x']
    for value in malformed:
        try:
            decode(value)
        except ValueError:
            pass
        else:
            raise ValueError('Accepted malformed control')
    receipt = {'status': 'COMPLETE_PREFIX_PACKET_ROUND_TRIP_PASS',
               'input_sha256': sha256(raw).hexdigest(), 'metrics': metrics,
               'all_operation_arities_and_variables_declared_in_packet': True,
               'exact_equations_and_query_up_to_bijective_renaming': True,
               'strict_truncations_rejected': len(bits), 'malformed_controls_rejected': len(malformed),
               'scope': 'A different fully declared bit codec for the same equational presentation. '
                        'The codebook is charged. The Turing-machine parser, proof search, writer, '
                        'and initialization are not implemented or charged as states.',
               'turing_machine_state_bound': None}
    args.out.mkdir(parents=True, exist_ok=True)
    (args.out / 'prefix.bits').write_text(bits + '\n')
    (args.out / 'decoded.json').write_text(json.dumps(decoded, indent=2) + '\n')
    (args.out / 'verification.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()
