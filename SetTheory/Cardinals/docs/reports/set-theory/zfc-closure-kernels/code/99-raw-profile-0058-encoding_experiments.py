#!/usr/bin/env python3
"""Fully charged prefix and selective DAG encodings for the clause payloads.

Only static syntax is measured. The code-length table and dictionary are data;
the cost of a binary TM implementing either codec is not claimed.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import heapq
import itertools
import json
from pathlib import Path

import raw_profiles as r


def huffman_lengths(freq, alphabet_size):
    heap = [(freq[i], i, i) for i in range(alphabet_size) if freq[i]]
    heapq.heapify(heap)
    serial = alphabet_size
    while len(heap) > 1:
        a, _, x = heapq.heappop(heap)
        b, _, y = heapq.heappop(heap)
        heapq.heappush(heap, (a+b, serial, (x, y)))
        serial += 1
    lengths = [0] * alphabet_size
    def visit(t, depth):
        if isinstance(t, int):
            lengths[t] = max(depth, 1)
        else:
            visit(t[0], depth+1)
            visit(t[1], depth+1)
    visit(heap[0][2], 0)
    return lengths


def canonical_codes(lengths):
    if any(x < 0 or x > 15 for x in lengths):
        raise ValueError('length does not fit four-bit dictionary field')
    ordered = sorted((n, i) for i, n in enumerate(lengths) if n)
    codes = {}
    value = previous = 0
    for n, i in ordered:
        value <<= n - previous
        if value >= 1 << n:
            raise ValueError('oversubscribed prefix dictionary')
        codes[i] = format(value, '0'+str(n)+'b')
        value += 1
        previous = n
    return codes


def gamma(n):
    if n < 1:
        raise ValueError('gamma input must be positive')
    b = bin(n)[2:]
    return '0' * (len(b)-1) + b


class Codec:
    def __init__(self, rows, variables, constants, functions):
        self.rows = r.canonical(rows)
        self.variables = variables
        self.constants = list(constants)
        self.functions = list(functions)
        self.ops = [('v'+str(i), 0) for i in range(variables)]
        self.ops += [(c, 0) for c in constants]
        self.ops += list(functions)
        self.op_id = {n: i for i, (n, _) in enumerate(self.ops)}
        self.compounds = Counter()
        def count(t):
            if isinstance(t, str) or len(t) == 1:
                return
            self.compounds[t] += 1
            for a in t[1:]:
                count(a)
        for row in self.rows:
            for _, _, a, b in row:
                count(a); count(b)
        self.repeated = sorted((t for t, n in self.compounds.items() if n > 1),
                               key=lambda t: (r.g.term_nodes(t), repr(t)))

    def term_symbols(self, dictionary):
        ids = {t: len(self.ops)+i for i, t in enumerate(dictionary)}
        def term(t, definition=False):
            if t in ids and not definition:
                return [ids[t]]
            if isinstance(t, str):
                return [self.op_id[t]]
            result = [self.op_id[t[0]]]
            for a in t[1:]:
                result.extend(term(a))
            return result
        defs = [term(t, True) for t in dictionary]
        body = [[(s, p, term(a), term(b)) for s, p, a, b in row] for row in self.rows]
        return defs, body

    def encode(self, dictionary=(), dictionary_header=True):
        dictionary = list(dictionary)
        if dictionary != sorted(dictionary, key=lambda t: (r.g.term_nodes(t), repr(t))):
            raise ValueError('dictionary must be topologically ordered')
        defs, body = self.term_symbols(dictionary)
        count = Counter(i for d in defs for i in d)
        count.update(i for row in body for _, _, a, b in row for t in (a, b) for i in t)
        lengths = huffman_lengths(count, len(self.ops)+len(dictionary))
        codes = canonical_codes(lengths)
        header = (gamma(len(dictionary)+1) if dictionary_header else '')
        header += ''.join(format(n, '04b') for n in lengths)
        definition_bits = ''.join(codes[i] for d in defs for i in d)
        body_bits = ''
        for row in body:
            body_bits += format(len(row), '03b')
            for s, p, a, b in row:
                body_bits += str(int(s)) + format(r.PREDICATES.index(p), '02b')
                body_bits += ''.join(codes[i] for t in (a, b) for i in t)
        body_bits += '000'
        bits = header + definition_bits + body_bits
        assert self.decode(bits, dictionary_header) == self.rows
        return bits, {'bits': len(bits), 'bytes': (len(bits)+7)//8,
            'dictionary_entries': len(dictionary), 'header_bits': len(header),
            'definition_bits': len(definition_bits), 'body_bits': len(body_bits),
            'max_prefix_code_length': max(lengths), 'lengths': lengths,
            'dictionary': dictionary,
            'sha256': hashlib.sha256(bits.encode()).hexdigest(), 'round_trip': True}

    def decode(self, bits, dictionary_header=True):
        cursor = 0
        def take(n):
            nonlocal cursor
            if cursor+n > len(bits):
                raise ValueError('truncated encoded stream')
            chunk = bits[cursor:cursor+n]
            cursor += n
            if any(c not in '01' for c in chunk):
                raise ValueError('nonbinary stream')
            return int(chunk, 2)
        def read_gamma():
            n = 0
            while take(1) == 0:
                n += 1
            return (1 << n) + (take(n) if n else 0)
        count = read_gamma()-1 if dictionary_header else 0
        lengths = [take(4) for _ in range(len(self.ops)+count)]
        codes = canonical_codes(lengths)
        inverse = {s: i for i, s in codes.items()}
        limit = max(lengths)
        definitions = []
        def opcode():
            word = ''
            for _ in range(limit):
                word += str(take(1))
                if word in inverse:
                    return inverse[word]
            raise ValueError('invalid prefix code')
        def term():
            op = opcode()
            if op >= len(self.ops):
                i = op - len(self.ops)
                if i >= len(definitions):
                    raise ValueError('forward dictionary reference')
                return definitions[i]
            if op < self.variables:
                return 'v'+str(op)
            name, arity = self.ops[op]
            return (name,) + tuple(term() for _ in range(arity))
        for _ in range(count):
            definitions.append(term())
        rows = []
        while True:
            n = take(3)
            if not n:
                if cursor != len(bits):
                    raise ValueError('trailing bytes')
                return rows
            row = []
            for _ in range(n):
                s, p = bool(take(1)), r.PREDICATES[take(2)]
                row.append((s, p, term(), term()))
            rows.append(row)

    def optimize(self, exhaustive=True):
        if exhaustive:
            choices = (tuple(t for i, t in enumerate(self.repeated) if mask >> i & 1)
                       for mask in range(1 << len(self.repeated)))
        else:
            choices = [(), tuple(self.repeated)]
        best = None
        examined = 0
        for dictionary in choices:
            bits, metrics = self.encode(dictionary)
            examined += 1
            key = (len(bits), len(dictionary), repr(dictionary))
            if best is None or key < best[0]:
                best = (key, bits, metrics)
        best[2]['subsets_examined'] = examined
        best[2]['repeated_compound_candidates'] = len(self.repeated)
        best[2]['exhaustive_within_declared_subsets'] = exhaustive
        return best[1], best[2]

    def full_dag_fixed_references(self):
        """All compounds topologically stored, no Huffman compression.

        Function ids have fixed ceil(log2(function count)) bits. At each
        definition child references range only over earlier nodes. Body
        roots all use the final fixed reference width. All fields charged.
        """
        ns = sorted(self.compounds, key=lambda t: (r.g.term_nodes(t), repr(t)))
        terminals = self.variables + len(self.constants)
        ids = {('v'+str(i) if i < self.variables else
                (self.constants[i-self.variables],)): i for i in range(terminals)}
        function_width = (len(self.functions)-1).bit_length()
        table_bits = 0
        for i, term in enumerate(ns):
            width = (terminals+i-1).bit_length()
            assert all(a in ids for a in term[1:])
            table_bits += function_width + (len(term)-1)*width
            ids[term] = terminals+i
        root_width = (terminals+len(ns)-1).bit_length()
        syntax = 3*(len(self.rows)+1) + 3*sum(map(len, self.rows))
        root_bits = 2*sum(map(len, self.rows))*root_width
        header = len(gamma(len(ns)+1))
        return {'unique_compounds': len(ns), 'child_edges': sum(len(t)-1 for t in ns),
            'header_bits': header, 'table_bits': table_bits,
            'literal_and_clause_syntax_bits': syntax,
            'root_reference_bits': root_bits,
            'bits': header+table_bits+syntax+root_bits}


def controls():
    fs = r.g.signature(False, True)
    eq = r.g.equality_clauses(False, fs)
    out = {}
    for ext in (False, True):
        core = r.g.source_clauses(False, True) + ([r.ce.extensional_clause()] if ext else [])
        name = 'FC16' if ext else 'FC15'
        out[name+'_source44'] = Codec(core+eq, 6, ['d'], fs)
        out[name+'_incoming'] = Codec(core+[eq[i] for i in [1,2,3,11,12]], 6, ['d'], fs)
    return out


def emit(output):
    output.mkdir(parents=True, exist_ok=True)
    all_codecs = controls()
    for ext, fused, transport in itertools.product((False,True), repeat=3):
        name = r.variant_name(ext, fused, transport)
        all_codecs[name] = Codec(r.clauses(ext, fused, transport), 4, r.CONSTANTS, r.signature(fused))
    all_codecs['RP18V'] = Codec(r.clauses(evaluation_member=True), 4, r.CONSTANTS, r.signature(True))
    results = {'status': 'fully charged static data encodings only; no TM state count', 'variants': {}}
    for name, codec in all_codecs.items():
        plain_bits, plain = codec.encode((), dictionary_header=False)
        result = {'plain_huffman': plain, 'full_fixed_dag': codec.full_dag_fixed_references()}
        if name.startswith('RP'):
            best_bits, best = codec.optimize()
            result['selective_dictionary'] = best
            (output/(name+'.shared.bits')).write_text(best_bits+'\n')
            (output/(name+'.shared.json')).write_text(json.dumps(best,indent=2)+'\n')
        (output/(name+'.huffman.bits')).write_text(plain_bits+'\n')
        result['proper_function_signature'] = codec.functions
        result['variable_slots'] = codec.variables
        result['constant_names'] = codec.constants
        results['variants'][name] = result
    (output/'results.json').write_text(json.dumps(results,indent=2)+'\n')
    return results


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--output', type=Path, default=r.HERE/'encoding_results')
    args=ap.parse_args()
    result=emit(args.output)
    print(json.dumps({k:{
        'huffman':v['plain_huffman']['bits'],
        'full_dag':v['full_fixed_dag']['bits'],
        'selective':v.get('selective_dictionary',{}).get('bits'),
        'subsets':v.get('selective_dictionary',{}).get('subsets_examined')}
        for k,v in result['variants'].items()},indent=2))


if __name__=='__main__':
    main()
