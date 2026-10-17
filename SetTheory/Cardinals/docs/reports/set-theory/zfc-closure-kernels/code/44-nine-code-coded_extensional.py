#!/usr/bin/env python3
"""FC16*: extensionality through the existing assignment/class language.

The primary FC15* theory is unchanged.  This optional control adds one
guarded four-literal clause and no new functions.  Its complete Eq-eliminated
payload uses the same nine-function ground signature and four-bit opcodes.
The semantic diagnostics below test the added clause under the stipulated
core assignment/class semantics.  They are not finite models of FC16*.
"""
from __future__ import annotations

import argparse
from itertools import product
import json
from pathlib import Path

import ground_kernel as g


def xor_class(a, b):
    """NAND formula for exclusive OR; repeated subterms are really emitted."""
    return g.f('N', g.f('N', a, g.f('N', a, b)),
               g.f('N', b, g.f('N', a, b)))


def extensional_clause():
    a, b, j = 'a', 'b', 'j'
    s = g.f('C', g.f('C', g.d, g.d, a), g.q, b)
    t = xor_class(g.f('A', j, g.d), g.f('A', j, g.q))
    return [g.Eq(j, g.d), g.Eq(j, g.q), g.Eq(a, b),
            g.I(s, g.f('Q', j, t))]


def native_clauses():
    return g.source_clauses(False, True) + [extensional_clause()]


def full_clauses():
    fs = g.signature(False, True)
    return native_clauses() + g.equality_clauses(False, fs)


def _read_stream(bits):
    """Independent decoder for this fixed four-bit template format."""
    arities = [2, 3, 2, 2, 2, 3, 3, 3, 2]
    names = ['V', 'C', 'N', 'A', 'Q', 'W', 'Y', 'Z', 'H']
    predicates = ['E', 'Inc', 'G', 'Eq']
    at = 0

    def take(k):
        nonlocal at
        if at + k > len(bits):
            raise ValueError('truncated stream')
        part = bits[at:at+k]
        at += k
        if any(c not in '01' for c in part):
            raise ValueError('nonbinary stream')
        return int(part, 2)

    def term():
        op = take(4)
        if op < 6:
            return 'v' + str(op)
        if op == 6:
            return ('d',)
        tag = op - 7
        return (names[tag],) + tuple(term() for _ in range(arities[tag]))

    result = []
    while True:
        n = take(3)
        if n == 0:
            if at != len(bits):
                raise ValueError('trailing stream data')
            return result
        row = []
        for _ in range(n):
            positive = bool(take(1))
            predicate = predicates[take(2)]
            row.append((positive, predicate, term(), term()))
        result.append(row)


def _canonical(clauses):
    def variables(t):
        if isinstance(t, str):
            return {t}
        found = set()
        for x in t[1:]:
            found.update(variables(x))
        return found

    result = []
    for row in clauses:
        names = set()
        for _, _, a, b in row:
            names.update(variables(a))
            names.update(variables(b))
        rename = {v: 'v' + str(i) for i, v in enumerate(sorted(names))}

        def term(t):
            if isinstance(t, str):
                return rename[t]
            return (t[0],) + tuple(term(x) for x in t[1:])

        result.append([(s, p, term(a), term(b)) for s, p, a, b in row])
    return result


def _ground_independent(clauses, bound):
    """A second arithmetic instantiator, independent of g.ground_term."""
    names = ['V', 'C', 'N', 'A', 'Q', 'W', 'Y', 'Z', 'H']
    predicates = ['E', 'Inc', 'G', 'Eq']

    def pair(a, b):
        s = a + b
        return s * (s + 1) // 2 + b

    def pack(values):
        out = values[-1]
        for a in reversed(values[:-1]):
            out = pair(a, out)
        return out

    for row in _canonical(clauses):
        vs = set()

        def collect(t):
            if isinstance(t, str):
                vs.add(t)
            else:
                for x in t[1:]:
                    collect(x)

        for _, _, a, b in row:
            collect(a)
            collect(b)
        ordered = sorted(vs)
        for values in product(range(bound + 1), repeat=len(ordered)):
            env = dict(zip(ordered, values))

            def term(t):
                if isinstance(t, str):
                    return env[t]
                if t[0] == 'd':
                    return 0
                args = [term(x) for x in t[1:]]
                return 1 + names.index(t[0]) + 16 * pack(args)

            yield tuple((1 if s else -1) *
                        (1 + predicates.index(p) + 4 * pair(term(a), term(b)))
                        for s, p, a, b in row)


def _semantic_checks():
    """Check the actual new AST against finite membership relations.

    Selectors are three distinct coordinate labels.  The value carrier has
    size 1, 2 or 3.  This is a local assignment/class-semantic diagnostic,
    not an interpretation of all one-domain FC core axioms in a finite set.
    """
    row = extensional_clause()
    rel_count = clause_count = extensional_count = 0
    necessary_guards = [0, 0]

    for size in (1, 2, 3):
        for mask in range(1 << (size * size)):
            rel_count += 1

            def member(x, y):
                return bool((mask >> (x * size + y)) & 1)

            extensional = all(a == b or any(member(z, a) != member(z, b)
                                           for z in range(size))
                              for a in range(size) for b in range(size))
            extensional_count += extensional
            all_rows = True
            for a in range(size):
                for b in range(size):
                    for j in range(3):
                        env = {'a': a, 'b': b, 'j': j}

                        def value(t):
                            if isinstance(t, str):
                                return env[t]
                            if t == ('d',):
                                return 0
                            if t == ('N', ('d',), ('d',)):
                                return 1
                            raise AssertionError(('not a selector/value', t))

                        def assignment(t):
                            if t == ('d',):
                                return {0: 0, 1: 0, 2: 0}
                            assert t[0] == 'C'
                            result = assignment(t[1])
                            result[value(t[2])] = value(t[3])
                            return result

                        def holds(t, s):
                            if t[0] == 'N':
                                return not (holds(t[1], s) and holds(t[2], s))
                            if t[0] == 'A':
                                return member(s[value(t[1])], s[value(t[2])])
                            assert t[0] == 'Q'
                            coordinate = value(t[1])
                            return any(holds(t[2], {**s, coordinate: z})
                                       for z in range(size))

                        s = assignment(row[-1][2])
                        incidence = holds(row[-1][3], s)
                        witness = any(member(z, a) != member(z, b)
                                      for z in range(size))
                        actual = (j == 0 or j == 1 or a == b or incidence)
                        expected = (j in (0, 1) or a == b or witness)
                        assert actual == expected
                        if j == 2:
                            assert incidence == witness
                        if j in (0, 1) and extensional and a != b and not incidence:
                            necessary_guards[j] += 1
                        all_rows = all_rows and actual
                        clause_count += 1
            assert all_rows == extensional
    assert all(n > 0 for n in necessary_guards)
    return {'finite_relations': rel_count,
            'extensional_finite_relations': extensional_count,
            'clause_evaluations': clause_count,
            'freshness_guard_necessity_witnesses': necessary_guards}


def checks():
    fs = g.signature(False, True)
    full = full_clauses()
    metrics = g.metrics(full, False, fs)
    expected = {'clauses': 30, 'literals': 86, 'term_nodes': 368,
                'max_variables': 6, 'max_term_depth': 6,
                'template_bits': 1823, 'term_opcode_bits': 4}
    for k, v in expected.items():
        assert metrics[k] == v, (k, metrics[k], v)
    bits = g.payload_bits(full, False, fs)
    assert _read_stream(bits) == _canonical(full)
    malformed = 0
    for bad in (bits[:-1], bits + '0', bits[:17]):
        try:
            _read_stream(bad)
        except ValueError:
            malformed += 1
        else:
            raise AssertionError('accepted malformed stream')
    substitutions = 0
    for bound in (0, 1, 2):
        actual = list(g.instances(full, bound, False, True))
        independently = list(_ground_independent(full, bound))
        assert actual == independently
        substitutions += len(actual)
    semantic = _semantic_checks()
    return {'pass': True, 'independent_template_roundtrip': True,
            'malformed_stream_rejections': malformed,
            'independent_ground_instance_comparisons': substitutions,
            'semantic_diagnostic_scope': 'added clause under stipulated core '
                'assignment/class semantics; not finite FC16 models',
            **semantic}


def generate(output: Path):
    output = Path(output)
    output.mkdir(parents=True, exist_ok=True)
    fs = g.signature(False, True)
    native, full = native_clauses(), full_clauses()
    metrics = {
        'theory': 'FC16* with one class-coded Extensionality clause',
        'native': g.metrics(native, False, fs),
        'equality_free': g.metrics(full, False, fs),
        'functions': fs,
        'predicates': g.PREDICATES,
        'term_radix': 16,
        'padding_constructors': 7,
        'scope': 'logical payload and reference search input; no binary state count',
    }
    stem = output / 'fc16_coded_extensional'
    stem.with_suffix('.json').write_text(json.dumps(full, indent=2) + '\n')
    (output / 'fc16_coded_extensional_native.json').write_text(
        json.dumps(native, indent=2) + '\n')
    bits = g.payload_bits(full, False, fs)
    stem.with_suffix('.bits').write_text(bits + '\n')
    padded = bits + '0' * ((-len(bits)) % 8)
    stem.with_suffix('.bin').write_bytes(int(padded, 2).to_bytes(len(padded) // 8, 'big'))
    (output / 'fc16_coded_extensional_metrics.json').write_text(
        json.dumps(metrics, indent=2) + '\n')
    result = checks()
    (output / 'fc16_coded_extensional_validation.json').write_text(
        json.dumps(result, indent=2) + '\n')
    return {'metrics': metrics, 'validation': result}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path,
                        default=Path(__file__).resolve().parents[1] / 'data')
    args = parser.parse_args()
    print(json.dumps(generate(args.output), indent=2))


if __name__ == '__main__':
    main()
