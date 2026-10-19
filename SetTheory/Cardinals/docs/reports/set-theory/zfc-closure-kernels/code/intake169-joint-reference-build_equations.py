#!/usr/bin/env python3
"""Compile finite predicate clauses into a concrete ground-rewriting target.

Optimizations are truth-table-certified propositional regroupings.  The
encoder measures the full equations, the Sheffer law, truth definition,
ground endpoints, opcode width and signature arities.  No TM count follows.
"""
from __future__ import annotations
from hashlib import sha256
from itertools import product
from math import ceil, log2
from pathlib import Path
import argparse
import json
import time
from equational_search import Kernel, freeze, nodes, variables

ROOT = Path(__file__).resolve().parent
D, TOP = ('d',), ('top',)


def N(a, b):
    return ('N', a, b)


SHEFFER = (N(N('x', N(N('y', 'x'), 'x')), N('y', N('z', 'x'))), 'y')
TOP_DEFINITION = (TOP, N(D, N(D, D)))
SIGNATURE = {'d': 0, 'top': 0, 'V': 2, 'C': 3, 'I': 2, 'A': 2,
             'U': 2, 'F': 2, 'p_E': 2, 'p_Inc': 2, 'p_Eq': 2, 'N': 2}


def atom(literal):
    return ('p_' + literal[1], freeze(literal[2]), freeze(literal[3]))


def negate(t):
    return N(t, t)


def disjoin(a, b):
    return N(negate(a), negate(b))


def naive_clause(clause):
    terms = [atom(l) if l[0] else negate(atom(l)) for l in clause]
    t = terms[0]
    for u in terms[1:]:
        t = disjoin(t, u)
    return t, TOP


def atom_tables(group):
    atoms = sorted({atom(l) for c in group for l in c}, key=repr)
    width = 1 << len(atoms)
    mask = (1 << width) - 1
    truth = {a: sum(((k >> i) & 1) << k for k in range(width))
             for i, a in enumerate(atoms)}
    target = mask
    for clause in group:
        value = 0
        for literal in clause:
            value |= truth[atom(literal)] ^ (0 if literal[0] else mask)
        target &= value
    return atoms, truth, target, mask


def optimized_equation(group, rounds=4):
    atoms, tables, target, mask = atom_tables(group)
    best = {mask: (1, TOP)}
    for a in atoms:
        best[tables[a]] = (nodes(a), a)
    # This bounded expression search is a heuristic. Every result is checked
    # exactly; no claim of globally shortest NAND equations is made.
    for _ in range(rounds):
        items = list(best.items())
        candidates = dict(best)
        for i, (m1, (cost1, t1)) in enumerate(items):
            for m2, (cost2, t2) in items[i:]:
                m = mask ^ (m1 & m2)
                cost = 1 + cost1 + cost2
                if m not in candidates or cost < candidates[m][0]:
                    candidates[m] = cost, N(t1, t2)
        if all(best.get(m, (10**30,))[0] == v[0] for m, v in candidates.items()):
            break
        best = candidates
    bad = target ^ mask
    choices = [(a[0] + best[m ^ bad][0], a[1], best[m ^ bad][1])
               for m, a in best.items() if m ^ bad in best]
    if not choices:
        if len(group) != 1:
            raise ValueError('bounded synthesis found no equation')
        result = naive_clause(group[0])
    else:
        _, left, right = min(choices, key=lambda x: x[0])
        result = left, right
    if len(group) == 1:
        naive = naive_clause(group[0])
        if sum(map(nodes, naive)) < sum(map(nodes, result)):
            result = naive
    assert check_equation(group, result)
    return result, {'atoms': len(atoms), 'truth_assignments': 1 << len(atoms),
                    'source_clauses': len(group), 'tree_nodes': sum(map(nodes, result)),
                    'represented_boolean_functions': len(best)}


def check_equation(group, equation):
    atoms, tables, target, mask = atom_tables(group)
    def value(t):
        if t == TOP:
            return mask
        if t in tables:
            return tables[t]
        assert t[0] == 'N'
        return mask ^ (value(t[1]) & value(t[2]))
    return (value(equation[0]) ^ value(equation[1])) == (target ^ mask)


def pretty(term):
    if isinstance(term, str):
        return term
    return term[0] if len(term) == 1 else term[0] + '(' + ','.join(pretty(x) for x in term[1:]) + ')'


def canonical_equation(equation):
    names = sorted(variables(equation[0]) | variables(equation[1]))
    mapping = {v: 'v' + str(i) for i, v in enumerate(names)}
    def cv(t):
        return mapping[t] if isinstance(t, str) else (t[0],) + tuple(cv(x) for x in t[1:])
    return cv(equation[0]), cv(equation[1])


def encode_packet(equations, signature, start, target):
    """Fixed-opcode prefix with a fully charged compact metadata header.

    Signature order is executable program data; external printed names are
    documentation only. Header: 8-bit symbol count, 3-bit arity per symbol,
    8-bit local variable capacity. Payload: repeated 1 + two prefix terms,
    a final 0, and the two prefix ground endpoints. Constructor tags follow
    variable tags. Tree arities determine every boundary, including endpoints.
    """
    equations = [canonical_equation(e) for e in equations]
    capacity = max(len(variables(a) | variables(b)) for a, b in equations)
    symbols = list(signature)
    width = max(1, ceil(log2(capacity + len(symbols))))
    def enc(t):
        tag = int(t[1:]) if isinstance(t, str) else capacity + symbols.index(t[0])
        return format(tag, '0' + str(width) + 'b') + ('' if isinstance(t, str) else ''.join(enc(x) for x in t[1:]))
    header = format(len(symbols), '08b') + ''.join(format(signature[s], '03b') for s in symbols) + format(capacity, '08b')
    rules = ''.join('1' + enc(a) + enc(b) for a, b in equations) + '0'
    endpoints = enc(start) + enc(target)
    return header + rules + endpoints, {'local_variable_capacity': capacity,
        'opcode_width': width, 'signature_symbols': len(symbols),
        'signature_and_capacity_bits': len(header), 'equation_payload_bits': len(rules),
        'ground_endpoint_bits': len(endpoints), 'complete_packet_bits': len(header + rules + endpoints),
        'equations': len(equations), 'rewrite_orientations': 2 * len(equations),
        'both_side_tree_nodes': sum(nodes(t) for e in equations for t in e)}


def decode_packet(bits, symbols):
    position = 0
    def read(n):
        nonlocal position
        if position + n > len(bits):
            raise ValueError('truncated bit packet')
        piece = bits[position:position+n]
        if any(b not in '01' for b in piece):
            raise ValueError('nonbinary packet')
        position += n
        return int(piece, 2)
    count = read(8)
    if count != len(symbols):
        raise ValueError('signature name count mismatch')
    signature = {s: read(3) for s in symbols}
    capacity = read(8)
    width = max(1, ceil(log2(capacity + count)))
    def term():
        tag = read(width)
        if tag < capacity:
            return 'v' + str(tag)
        if tag >= capacity + count:
            raise ValueError('invalid constructor tag')
        symbol = symbols[tag-capacity]
        return (symbol,) + tuple(term() for _ in range(signature[symbol]))
    equations = []
    while read(1):
        equations.append((term(), term()))
    start, target = term(), term()
    if position != len(bits):
        raise ValueError('trailing bit data')
    # This also rejects variables in the claimed ground endpoints.
    Kernel(signature, equations, start, target)
    return signature, equations, start, target


def build(output=ROOT):
    source = freeze(json.loads((ROOT/'reference/FC13B_complete.json').read_text()))
    grouped = [[i] for i in range(len(source))]
    for indices in [[2, 3, 4], [6, 7], [10, 11]]:
        grouped = [g for g in grouped if g[0] not in indices]
        grouped.append(indices)
    grouped.sort(key=lambda g:g[0])
    out = {}
    for name, groups, optimize in [('literal', [[i] for i in range(len(source))], False),
                                    ('grouped', grouped, True)]:
        equations = [SHEFFER, TOP_DEFINITION]
        certificates = []
        for indices in groups:
            group = [source[i] for i in indices]
            eq, cert = optimized_equation(group) if optimize else (naive_clause(group[0]), {})
            assert check_equation(group, eq)
            equations.append(eq)
            certificates.append(dict(cert, source_indices=indices, equation=eq))
        start, target = N(TOP, TOP), TOP
        bits, stats = encode_packet(equations, SIGNATURE, start, target)
        decoded = decode_packet(bits, list(SIGNATURE))
        assert decoded == (SIGNATURE, [canonical_equation(e) for e in equations], start, target)
        for bad in [bits[:-1], bits+'0']:
            try:
                decode_packet(bad, list(SIGNATURE))
            except ValueError:
                pass
            else:
                raise AssertionError('bad packet accepted')
        data = {'name': 'FC13B_' + name + '_equational', 'signature': SIGNATURE,
                'equations': equations, 'start': start, 'target': target,
                'status': 'finite equational frontend and complete ideal search; no binary TM state count',
                'source_groups': certificates}
        (output/(name+'.json')).write_text(json.dumps(data, indent=2)+'\n')
        (output/(name+'.bits')).write_text(bits+'\n')
        (output/(name+'.equations')).write_text('\n'.join(f'{i}: {pretty(a)} = {pretty(b)}' for i,(a,b) in enumerate(equations))+'\n')
        stats['packet_sha256'] = sha256((bits+'\n').encode()).hexdigest()
        out[name] = stats
    (output/'metrics.json').write_text(json.dumps(out, indent=2)+'\n')
    return out


if __name__ == '__main__':
    print(json.dumps(build(), indent=2))
