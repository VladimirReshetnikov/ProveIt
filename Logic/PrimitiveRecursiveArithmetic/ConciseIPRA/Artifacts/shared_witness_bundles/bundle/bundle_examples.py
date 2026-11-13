"""Construct and exercise certificates for the shared-witness reference calculus."""

import ast
import gzip
import io
import json
from pathlib import Path
import tokenize

from bundle_checker import (
    accepts, check, falpha, ffree, fresh, fsub, Invalid, names, talpha,
    tfree, tsub,
)


def succ(t):
    return ['s', t]


def iterator(n, a, u, h):
    return ['i', n, a, u, h]


def weaken(proof, cutoff, amount):
    # The string 'h' occurs only as a hypothesis-instruction tag in this grammar.
    if type(proof) is not list:
        return proof
    if len(proof) == 2 and proof[0] == 'h':
        i = proof[1]
        return ['h', i + amount if i >= cutoff else i]
    return [weaken(x, cutoff, amount) for x in proof]


def expand_both(proof, left, right):
    return ['e', 1, right, ['e', 0, left, proof]]


def contract_both(proof):
    return ['c', 1, ['c', 0, proof]]


def transport(s, t, template_variable, h, r, major, minor, context_length=0, scope=()):
    """Compile s=t, h(s)=r to r=h(t), using a two-component bundle.

    major and minor are proofs in the same existing context. Supply its length
    as context_length and its entire numerical scope as scope (including unused
    parameters). The output proof has that context too. No numerical term of
    s,t,h,r is normalized here.
    """
    first = fresh(s, t, h, r, major, minor, template_variable, list(scope))
    x, y, z, b, u = range(first, first + 5)
    hx = tsub(h, {template_variable: x})

    def gate(counter, payload):
        return iterator(counter, 0, u, payload)

    rows = [[y, ['=', gate(y, x), gate(y, t)]],
            [y, ['=', gate(y, hx), gate(y, r)]]]
    bundle = ['d', x, rows]
    hs = tsub(h, {template_variable: s})
    branches = [
        [z, 'c', expand_both(weaken(major, context_length, 1),
                             gate(succ(z), s), gate(succ(z), t))],
        [z, 'c', expand_both(weaken(minor, context_length, 1),
                             gate(succ(z), hs), gate(succ(z), r))],
    ]
    closed = ['d', bundle, s, branches]
    hb = tsub(h, {template_variable: b})
    opened_rows = [(b, t), (hb, r)]
    recovered = []
    for i, (left, right) in enumerate(opened_rows):
        base = expand_both(['r', 0], gate(0, left), gate(0, right))
        row = ['q', ['h', context_length + i], base, succ(0)]
        recovered.append(contract_both(row))
    return ['o', closed, b, ['v', recovered[0], recovered[1]]]


def induction_example(parameter=9):
    x, y, u, z, b = 1, 2, 3, 4, 5
    body = ['=', iterator(y, 0, u, u), 0]
    bundle = ['d', x, [[y, body]]]
    step = ['e', 0, iterator(succ(z), 0, u, u), ['h', 0]]
    closed = ['d', bundle, 0, [[z, 'p', step]]]
    closure = ['o', closed, b, ['h', 0]]
    base = ['e', 0, iterator(0, 0, u, u), ['r', 0]]
    goal = ['=', iterator(parameter, 0, u, u), 0]
    return [goal, ['q', closure, base, parameter]]


def run():
    directory = Path(__file__).resolve().parent
    examples = {}
    one = succ(0)
    s = iterator(0, one, 1, 1)
    p = ['e', 0, s, ['r', one]]
    h, variable = succ(2), 2
    hs = tsub(h, {variable: s})
    theorem = ['=', hs, succ(one)]
    examples['root_congruence'] = [theorem, transport(s, one, variable, h, hs,
                                                    p, ['r', hs])]
    examples['equation_induction'] = induction_example()
    e, p = induction_example()
    s, t = e[1:]
    h, variable = succ(20), 20
    hs = tsub(h, {variable: s})
    theorem = ['=', hs, succ(0)]
    examples['induction_then_transport'] = [
        theorem, transport(s, t, variable, h, hs, p, ['r', hs], scope={9})]
    examples['empty_bundle_auxiliary'] = [
        ['=', 0, 0], ['o', ['d', ['d', 1, []], 0, []], 2, ['r', 0]]]
    receipts = {}
    for name, document in examples.items():
        if not accepts(document):
            raise RuntimeError('positive certificate rejected: ' + name)
        path = directory / (name + '.json')
        path.write_text(json.dumps(document, separators=(',', ':')) + '\n')
        receipts[name] = {'accepted': True, 'certificate_bytes': path.stat().st_size}

    # Unused ambient parameters still count for the eigenvariable side condition.
    s = iterator(0, one, 1, 1)
    major, variable, h = ['e', 0, s, ['r', one]], 2, succ(2)
    hs = tsub(h, {variable: s})
    minor = ['r', hs]
    colliding = fresh(s, one, h, hs, major, minor, variable) + 2
    context = [['=', colliding, colliding]]
    certificate = transport(s, one, variable, h, hs, major, minor,
                            context_length=1, scope={colliding})
    got = check(certificate, {colliding}, context)
    if falpha(got) != falpha(['=', hs, succ(one)]):
        raise RuntimeError('ambient-scope compiler regression')
    receipts['ambient_scope_transport'] = {'accepted': True}

    # Simultaneous replacement must not re-substitute inside an inserted term.
    if fsub(['=', 1, 2], {1: 2, 2: 0}) != ['=', 2, 0]:
        raise RuntimeError('simultaneous-substitution regression')
    t = tsub(iterator(0, 0, 2, 1), {1: 2})
    if tfree(t) != {2}:
        raise RuntimeError('term capture-avoidance regression')
    a = fsub(['d', 1, [[2, ['=', 3, 1]]]], {3: 1})
    if ffree(a) != {1}:
        raise RuntimeError('bundle capture-avoidance regression')
    if falpha(a) != falpha(['d', 10, [[20, ['=', 1, 10]]]]):
        raise RuntimeError('shared-binder alpha-equivalence regression')

    negatives = {
        'nonvariable_transport_source':
            [['=', 0, 0], ['v', ['r', 0], ['r', 0]]],
        'wrong_root_expansion':
            [['=', one, 0], ['e', 0, iterator(0, one, 1, 1), ['r', 0]]],
        'unproved_zero_successor': [['=', 0, one], ['r', 0]],
        'boolean_variable': [['=', True, True], ['r', True]],
        'nonpublic_empty_bundle': [['d', 1, []], ['d', ['d', 1, []], 0, []]],
        'wrong_bundle_witness': json.loads(json.dumps(examples['root_congruence'])),
        'case_in_place_of_induction': json.loads(json.dumps(examples['equation_induction'])),
        'missing_shared_component': json.loads(json.dumps(examples['root_congruence'])),
    }
    negatives['wrong_bundle_witness'][1][1][2] = 0
    # qe / open / close / first branch / mode
    negatives['case_in_place_of_induction'][1][1][1][3][0][1] = 'c'
    negatives['missing_shared_component'][1][1][1][2].pop()
    for name, document in negatives.items():
        if accepts(document):
            raise RuntimeError('negative certificate accepted: ' + name)
        receipts[name] = {'accepted': False}

    # Check the discharge condition itself, independently of final-goal matching.
    leaking = ['o', ['d', ['d', 1, []], 0, []], 2, ['r', 2]]
    try:
        check(leaking, set(), [])
    except Invalid:
        receipts['eigenvariable_escape'] = {'accepted': False}
    else:
        raise RuntimeError('eigenvariable escaped')

    source = (directory / 'bundle_checker.py').read_bytes()
    normalized = (ast.unparse(ast.parse(source)) + '\n').encode()
    skip = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.INDENT,
            tokenize.DEDENT, tokenize.NEWLINE, tokenize.NL, tokenize.COMMENT}
    receipts['reference_checker_size'] = {
        'raw_bytes': len(source),
        'normalized_bytes': len(normalized),
        'significant_tokens': sum(t.type not in skip for t in
                                 tokenize.generate_tokens(io.StringIO(normalized.decode()).readline)),
        'ast_nodes': len(list(ast.walk(ast.parse(normalized)))),
        'gzip9_normalized_bytes': len(gzip.compress(normalized, compresslevel=9, mtime=0)),
        'status': 'Readable reference; no minimum claim.'
    }
    output = directory / 'bundle_results.json'
    output.write_text(json.dumps(receipts, indent=2) + '\n')
    print(json.dumps(receipts, indent=2))


if __name__ == '__main__':
    run()
