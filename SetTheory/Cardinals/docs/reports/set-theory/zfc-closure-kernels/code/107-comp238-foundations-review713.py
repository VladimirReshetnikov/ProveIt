#!/usr/bin/env python3
"""Independent literal packet and propositional review of the E713 artifact.

Does not import its constructor. This checks transcription and encoding only;
the associated ordinary model-theoretic review is in review713.txt.
"""
import argparse
import hashlib
import itertools
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
DEFAULT = HERE / 'generated'


def fmt(t):
    if isinstance(t, str):
        return t
    return t[0] if len(t) == 1 else t[0] + '(' + ','.join(fmt(x) for x in t[1:]) + ')'


def names(t):
    if isinstance(t, str):
        return {t}
    found = set()
    for child in t[1:]:
        found |= names(child)
    return found


def normalized(t, local):
    if isinstance(t, str):
        return ('variable', local.index(t))
    return (t[0], tuple(normalized(x, local) for x in t[1:]))


def review(input_dir):
    data = json.loads((input_dir / 'E713.json').read_text())
    bits = (input_dir / 'E713.bits').read_text().strip()
    assert set(bits) == {'0', '1'}
    assert hashlib.sha256(bits.encode()).hexdigest() == '3cd0c3d0fb8d8640cfef1f44e0c22d377dd930de88a94093a2ef7650e22c9e72'
    pos = 0
    def integer(n):
        nonlocal pos
        end = pos + n
        assert end <= len(bits)
        result = int(bits[pos:end], 2)
        pos = end
        return result
    count = integer(8)
    arities = [integer(3) for _ in range(count)]
    capacity = integer(8)
    symbols = list(data['signature'])
    assert count == len(symbols) == 12
    assert arities == list(data['signature'].values())
    assert capacity == 4 and pos == 52
    width = 1
    while 2 ** width < count + capacity:
        width += 1
    assert width == 4
    term_nodes = []
    def term():
        # Read a preorder tree with a stack of unfinished parents. This is
        # structurally different from the constructor's recursive parser.
        parents = []
        n = 0
        while True:
            opcode = integer(width)
            n += 1
            assert opcode < count + capacity
            if opcode < capacity:
                result = ('variable', opcode)
            else:
                index = opcode - capacity
                arity = arities[index]
                if arity:
                    parents.append([symbols[index], arity, []])
                    continue
                result = (symbols[index], ())
            while parents:
                parent = parents[-1]
                parent[2].append(result)
                if len(parent[2]) < parent[1]:
                    break
                parents.pop()
                result = (parent[0], tuple(parent[2]))
            else:
                term_nodes.append(n)
                return result
    equations = []
    while integer(1):
        equations.append((term(), term()))
    end_equations = pos
    start, target = term(), term()
    assert pos == len(bits) == 713
    wanted = []
    for left, right in data['equations']:
        local = sorted(names(left) | names(right))
        wanted.append((normalized(left, local), normalized(right, local)))
    assert equations == wanted and len(equations) == 8
    assert start == normalized(data['start'], [])
    assert target == normalized(data['target'], [])
    assert sum(term_nodes[:-2]) == 159
    assert sum(term_nodes[-2:]) == 4
    assert end_equations - 52 == 8 + 1 + 4 * 159 == 645

    # Evaluate the *literal decoded JSON equation*, treating exactly the eight
    # intended predicate applications as independent propositional atoms.
    atom_names = [
        'p_eps(P(Next(b,z),P(Target(b),b)),V(b,d))',
        'p_E(Mem(b,z),Next(b,z))',
        'p_E(Mem(b,z),z)',
        'p_E(W(x,d),x)',
        'p_E(x,Target(b))',
        'p_eps(P(y,P(x,b)),V(b,d))',
        'p_E(y,Target(b))',
        'p_eps(P(y,P(Next(b,y),b)),V(b,d))',
    ]
    def value(t, atoms):
        if t == ['d']:
            return True
        if isinstance(t, list) and t[0] == 'N':
            return not (value(t[1], atoms) and value(t[2], atoms))
        return atoms[fmt(t)]
    for vals in itertools.product((False, True), repeat=8):
        r, e, f, a, b, c, d, s = vals
        bad = r and e and not f
        hull = ((a or not c or d) and (not b or not c or d)
                and (not d or s))
        atoms = dict(zip(atom_names, vals))
        left, right = data['equations'][7]
        assert (value(left, atoms) == value(right, atoms)) == (bad or hull)

    # Check the actual binder's three predicate applications and universal
    # two-valued semantics, including selected witnesses and all finite lists.
    qname = 'p_eps(s,Q(a))'
    wname = 'p_eps(P(W(s,a),s),a)'
    zname = 'p_eps(P(z,s),a)'
    quantifier_cases = 0
    for length in range(1, 6):
        for vals in itertools.product((False, True), repeat=length):
            for chosen in range(length):
                for q in (False, True):
                    left, right = data['equations'][6]
                    sat = all(value(left, {qname:q, wname:vals[chosen], zname:z})
                              == value(right, {qname:q, wname:vals[chosen], zname:z})
                              for z in vals)
                    expected = q == any(not z for z in vals) and (not q or not vals[chosen])
                    assert sat == expected
                    quantifier_cases += 1
    return {
        'status': 'INDEPENDENT_LITERAL_PACKET_AND_PROPOSITIONAL_REVIEW_PASS',
        'bits_sha256': hashlib.sha256(bits.encode()).hexdigest(),
        'complete_bits': len(bits), 'header_bits': 52,
        'equation_marker_bits': 9, 'equation_term_nodes': 159,
        'equation_term_bits': 636, 'endpoint_bits': 16,
        'symbols': 12, 'variable_capacity': 4, 'opcode_width': 4,
        'equations': 8, 'literal_closure_truth_assignments': 256,
        'literal_quantifier_cases': quantifier_cases,
        'constructor_imported': False,
        'scope': 'Exact encoding and literal transcription; does not test EPSC consistency or replace the ordinary model-theoretic proof.',
    }


if __name__ == '__main__':
    if not __debug__:
        raise SystemExit('Assertions must remain enabled.')
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--input-dir', type=Path, default=DEFAULT)
    p.add_argument('--output', type=Path, default=HERE / 'review713.json')
    args = p.parse_args()
    result = review(args.input_dir)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))
