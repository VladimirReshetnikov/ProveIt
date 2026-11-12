"""Independent named-syntax replay for deterministic witness discharge.

This audit imports no implementation helper from the proposed checker. It
parses de Bruijn input into globally fresh named binders, normalizes that
representation, and performs replacement of names before re-encoding.
The finite replay evidence does not prove the universal interpretation theorem.
"""
from dataclasses import dataclass
import itertools
import json
from pathlib import Path
import sys


class Invalid(ValueError):
    pass


def require(condition):
    if not condition:
        raise Invalid('invalid certificate')


ZERO = ('zero',)
ONE = ('succ', ZERO)
IDS = itertools.count()


def fresh_bound():
    return ('bound', next(IDS))


def free(index):
    return ('var', ('free', index))


def term(raw, scope, bound=()):
    if type(raw) is int:
        if raw == 0:
            return ZERO
        if raw < 0:
            require(-scope <= raw)
            return free(raw)
        require(raw <= len(bound))
        return ('var', bound[raw - 1])
    require(type(raw) is list)
    if len(raw) == 2:
        require(type(raw[0]) is int and raw[0] == 0)
        return ('succ', term(raw[1], scope, bound))
    require(len(raw) == 3)
    state = fresh_bound()
    return ('iter', term(raw[0], scope, bound), term(raw[1], scope, bound),
            state, term(raw[2], scope, (state,) + bound))


def formula(raw, scope, bound=()):
    require(type(raw) is list)
    if len(raw) == 2:
        return ('eq', term(raw[0], scope, bound), term(raw[1], scope, bound))
    require(len(raw) == 1)
    witness, coordinate = fresh_bound(), fresh_bound()
    return ('D', witness, coordinate,
            formula(raw[0], scope, (coordinate, witness) + bound))


def encode(node, bound=()):
    tag = node[0]
    if tag == 'zero':
        return 0
    if tag == 'var':
        name = node[1]
        return name[1] if name[0] == 'free' else bound.index(name) + 1
    if tag == 'succ':
        return [0, encode(node[1], bound)]
    if tag == 'eq':
        return [encode(node[1], bound), encode(node[2], bound)]
    if tag == 'D':
        return [encode(node[3], (node[2], node[1]) + bound)]
    require(tag == 'iter')
    return [encode(node[1], bound), encode(node[2], bound),
            encode(node[4], (node[3],) + bound)]


def replace(node, name, value):
    tag = node[0]
    if tag == 'zero':
        return node
    if tag == 'var':
        return value if node[1] == name else node
    if tag == 'succ':
        return ('succ', replace(node[1], name, value))
    if tag == 'eq':
        return ('eq', replace(node[1], name, value), replace(node[2], name, value))
    if tag == 'D':
        return node if name in node[1:3] else ('D', *node[1:3], replace(node[3], name, value))
    require(tag == 'iter')
    return ('iter', replace(node[1], name, value), replace(node[2], name, value),
            node[3], node[4] if name == node[3] else replace(node[4], name, value))


def normal(node):
    tag = node[0]
    if tag in ('zero', 'var'):
        return node
    if tag == 'succ':
        return ('succ', normal(node[1]))
    if tag == 'eq':
        return ('eq', normal(node[1]), normal(node[2]))
    if tag == 'D':
        return ('D', *node[1:3], normal(node[3]))
    require(tag == 'iter')
    count, initial, update = normal(node[1]), normal(node[2]), normal(node[4])
    if count == ZERO:
        return initial
    if count[0] == 'succ':
        prior = normal(('iter', count[1], initial, node[3], update))
        return normal(replace(update, node[3], prior))
    return ('iter', count, initial, node[3], update)


def canonical(raw, scope, is_formula):
    result = formula(raw, scope) if is_formula else term(raw, scope)
    require(encode(normal(result)) == raw)
    return result


def same(a, b):
    return encode(a) == encode(b)


@dataclass(frozen=True)
class Clause:
    base: object
    variable: tuple
    body: tuple


def infer(expected, proof, context, counts):
    scope = len(context) - 1
    # Validate the expected formula independently even at recursive goals.
    expected_raw = encode(expected)
    canonical(expected_raw, scope, True)
    require(type(proof) is list and proof and type(proof[0]) is str)
    tag = proof[0]
    if tag == 'u':
        require(len(proof) == 4)
        index, target_raw, premise = proof[1:]
        require(type(index) is int and 0 <= index < len(context))
        target = canonical(target_raw, scope, False)
        clause = context[index]
        if clause.base is not None:
            infer(clause.base, premise, context, counts)
        result = normal(replace(clause.body, clause.variable, target))
        require(same(result, expected))
        counts['Use'] += 1
        return result
    if tag == 'i':
        require(len(proof) == 3 and expected[0] == 'D')
        witness = canonical(proof[1], scope, False)
        body = normal(replace(expected[3], expected[1], witness))
        eigen = free(-scope - 1)
        mode = eigen if body[0] == 'eq' and witness == ZERO else ZERO
        assumption = normal(replace(body, expected[2], mode))
        step = normal(replace(body, expected[2], ('succ', eigen)))
        local = context + [Clause(None, fresh_bound(), assumption)]
        infer(step, proof[2], local, counts)
        counts['Intro'] += 1
        return expected
    if tag == 'e':
        require(len(proof) == 5)
        matrix, branch_formula, major, branch = proof[1:]
        paired = canonical([matrix], scope, True)
        infer(paired, major, context, counts)
        eigen = free(-scope - 1)
        body = normal(replace(paired[3], paired[1], eigen))
        base = normal(replace(body, paired[2], ZERO))
        row = normal(replace(body, paired[2], ONE))
        target = eigen
        if same(base, ('eq', ZERO, ZERO)) and row[0] == 'eq' and row[1] == eigen:
            target = row[2]
            counts['ActiveName'] += 1
        local = context + [Clause(base, paired[2], body)]
        result = canonical(branch_formula, scope + 1, True)
        infer(result, branch, local, counts)
        exported = normal(replace(result, eigen[1], target))
        require(same(exported, expected))
        counts['Name'] += 1
        return exported
    raise Invalid('unknown proof rule')


def check(data):
    require(type(data) is list and len(data) == 2)
    expected = canonical(data[0], 0, True)
    variable = fresh_bound()
    reflexivity = Clause(None, variable, ('eq', ('var', variable), ('var', variable)))
    counts = dict(Use=0, Intro=0, Name=0, ActiveName=0)
    infer(expected, data[1], [reflexivity], counts)
    return counts


def main():
    if len(sys.argv) == 1:
        check(json.load(sys.stdin))
        print('ACCEPT')
        return
    records = []
    totals = dict(Use=0, Intro=0, Name=0, ActiveName=0)
    for path in sorted(Path(sys.argv[1]).glob('*.json')):
        counts = check(json.loads(path.read_text()))
        for key in totals:
            totals[key] += counts[key]
        records.append({'file': path.name, 'counts': counts})
    result = {'replayed': len(records), 'totals': totals, 'records': records,
              'method': 'Independent named binders, normalization and substitution; no checker helper imports'}
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
