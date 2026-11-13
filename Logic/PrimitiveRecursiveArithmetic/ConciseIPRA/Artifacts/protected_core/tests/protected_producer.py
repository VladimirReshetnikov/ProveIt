"""Untrusted producer for protected guarded certificates.

This module does not use the source_dispatch general zero-source theorem.
It normalizes the selected finite derivations by maintaining both directions
of each derived equation. Its permitted equation leaves have nonzero syntax
on at least one side. All primitive Tr occurrences in its output have a
nonzero source. The generated proof trees keep every D matrix unchanged.
"""
import itertools
import json
from pathlib import Path

import producer as P
import guarded as G

serial = itertools.count()


def fresh(label):
    return 'protected_' + label + '_' + str(next(serial))


def W(term):
    return P.I(0, term, '_box_state', 0)


def refl(term):
    result = P.reflexivity(term, fresh('refl'))
    return result


def sym(proof):
    if proof['goal'][1] == 0:
        if proof['goal'][2] == 0:
            return proof
        raise ValueError('Unsafe symmetry requested by producer')
    return P.symmetry(proof, fresh('sym'))


def trans(first, second):
    if first['goal'][2] != second['goal'][1] or second['goal'][1] == 0:
        raise ValueError('Unsafe transitivity requested by producer')
    return P.transitivity(first, second, fresh('trans'))


def zero_join(first, second):
    """Derive a=b from a=0 and b=0, with a and b nonzero syntax.

    Only computation, reflexivity, and nonzero-source transport occur.
    No cases, induction, closure, or general zero-source normalizer occurs.
    """
    if first['goal'][1] == 0 or second['goal'][1] == 0:
        raise ValueError('zero_join requires nonzero terms')
    if first['goal'][2] != 0 or second['goal'][2] != 0:
        raise ValueError('zero_join requires zero endpoints')
    common = W(0)

    def to_box(proof):
        source = proof['goal'][1]
        hole = fresh('box_hole')
        backwards = P.transport(proof, hole, P.Eq(W(P.V(hole)), W(source)),
                                refl(W(source)))
        forwards = sym(backwards)
        hole = fresh('unbox_hole')
        return P.transport(P.compute(W(source)), hole, P.Eq(P.V(hole), common), forwards)

    return trans(to_box(first), sym(to_box(second)))


def pair_from_safe(proof):
    """Produce both directions when the forward source is nonzero (or 0=0)."""
    return proof, sym(proof)


def pair_trans(first, second):
    a, middle = first[0]['goal'][1:]
    other_middle, b = second[0]['goal'][1:]
    if middle != other_middle:
        raise ValueError('Producer endpoints do not match')
    if middle != 0:
        return trans(first[0], second[0]), trans(second[1], first[1])
    if a == 0:
        return second
    if b == 0:
        return first
    result = zero_join(first[0], second[1])
    return pair_from_safe(result)


def pair_congruence(pair, variable, term):
    source, target = pair[0]['goal'][1:]
    transform = lambda value: P.substitute(term, variable, value)
    if source != 0:
        forward = P.congruence(pair[0], transform, fresh('cong'))
        return pair_from_safe(forward)
    if target != 0:
        reverse = P.congruence(pair[1], transform, fresh('cong'))
        return sym(reverse), reverse
    result = refl(transform(0))
    return result, result


def normalize(proof, memo=None):
    """Return a proof and, for an equation, its reverse.

    This executable normalization supports exactly the named proof language
    needed by these fixtures. A raw unguarded equation hypothesis beginning
    0=t with t nonzero, or a non-equational Tr template, raises an error.
    Such an error is not silently treated as a theorem or as a certificate.
    """
    if memo is None:
        memo = {}
    if id(proof) in memo:
        return memo[id(proof)]
    rule = proof['rule']
    goal = proof['goal']
    out = dict(proof)
    children = {}
    for key in ('major', 'minor', 'premise', 'continuation'):
        if key in proof:
            children[key] = normalize(proof[key], memo)
            out[key] = children[key][0]
    if rule == 'Tr':
        if proof['motive'][0] != 'eq':
            raise ValueError('This finite normalizer handles equational Tr only')
        if out['major']['goal'][1] != 0 and (goal[1] != 0 or goal[2] == 0):
            # The original inference is already safe, and its conclusion
            # admits the immediate safe reversal. Avoid expanding it.
            result = pair_from_safe(out)
        else:
            left, right = proof['motive'][1:]
            left_pair = pair_congruence(children['major'], proof['variable'], left)
            right_pair = pair_congruence(children['major'], proof['variable'], right)
            result = pair_trans(pair_trans(left_pair[::-1], children['minor']), right_pair)
    elif goal[0] != 'eq':
        result = out, None
    elif rule in ('DE', 'Neutral'):
        backwards = dict(out)
        backwards['goal'] = P.Eq(goal[2], goal[1])
        backwards['continuation'] = children['continuation'][1]
        result = out, backwards
    else:
        result = pair_from_safe(out)
    if result[0]['goal'] != goal:
        raise ValueError('Normalization changed the concluding formula')
    if result[1] is not None and result[1]['goal'] != P.Eq(goal[2], goal[1]):
        raise ValueError('Normalizer supplied an incorrect reverse equation')
    memo[id(proof)] = result
    return result


def audit(proof):
    seen = set()
    forbidden = []
    rules = {}
    guarded = 0
    unguarded = 0

    def inspect_formula(formula):
        nonlocal guarded, unguarded
        if formula[0] == 'eq':
            return
        if formula[0] == 'q':
            inspect_formula(formula[2])
            return
        if formula[0] != 'd':
            raise ValueError('Unknown formula in proof audit')
        matrix = formula[3]
        if matrix[0] == 'eq':
            ok = all(isinstance(term, tuple) and term[0] == 'i'
                     and term[1] == P.V(formula[2]) and term[2] == 0
                     for term in matrix[1:])
            guarded += int(ok)
            unguarded += int(not ok)
        inspect_formula(matrix)

    def visit(node):
        if id(node) in seen:
            return
        seen.add(id(node))
        rules[node['rule']] = rules.get(node['rule'], 0) + 1
        inspect_formula(node['goal'])
        if 'motive' in node:
            inspect_formula(node['motive'])
        if node['rule'] == 'Tr' and node['major']['goal'][1] == 0:
            forbidden.append(node['goal'])
        for key in ('major', 'minor', 'premise', 'continuation'):
            if key in node:
                visit(node[key])

    visit(proof)
    return dict(distinct_nodes=len(seen), rules=rules, forbidden_zero_sources=forbidden,
                guarded_atomic_D_in_distinct_nodes=guarded,
                unguarded_atomic_D_in_distinct_nodes=unguarded)


def protected_equation(proof):
    return P.congruence(proof, W, fresh('wrap'))


def explosion():
    contradiction = P.Eq(W(0), W(P.ONE))
    target = P.Eq(W(P.TWO), W(0))
    zero_one = G.unwrap_equation(P.hyp(contradiction), P.compute(W(0)), P.compute(W(P.ONE)))
    def selected(v):
        return P.C(v, target[1], target[2])
    changed = P.congruence(zero_one, selected, fresh('explode'))
    result = G.join(G.sym(P.compute(selected(0))),
                    G.join(changed, P.compute(selected(P.ONE))))
    if result['goal'] != target:
        raise ValueError('Explosion fixture has the wrong conclusion')
    return G.implication_intro(contradiction, target, result)


def proofs():
    result = []
    for row in G.build_proofs():
        if not row['expected'] or not row['canonical_goal']:
            continue
        proof = row['proof']
        if proof['goal'][0] == 'eq':
            proof = protected_equation(proof)
        result.append(dict(name='protected_' + row['name'], proof=proof))
    equation = protected_equation(P.compute(P.I(0, P.ONE, '_demo', P.TWO)))
    lifted = G.lift_intro(equation)
    result.append(dict(name='protected_guard_padding_forward', proof=lifted))
    result.append(dict(name='protected_guard_padding_reverse', proof=G.lift_elim(lifted)))
    result.append(dict(name='protected_explosion_implication', proof=explosion()))
    return result


def build(directory):
    directory = Path(directory)
    directory.mkdir(parents=True, exist_ok=True)
    rows = []
    for row in proofs():
        expanded = P.expand_proof(row['proof'])
        proof = normalize(expanded)[0]
        check = audit(P.expand_proof(proof))
        if check['forbidden_zero_sources']:
            raise ValueError('Zero-source transport remained after normalization')
        if check['unguarded_atomic_D_in_distinct_nodes']:
            raise ValueError('An unguarded atomic D appeared in a canonical proof')
        out = dict(name=row['name'], audit=check, packets={})
        for lexical, neutral, dialect in ((True, True, 'local'), (False, False, 'global')):
            packet = G.make_packet(proof, lexical, neutral)
            filename = row['name'] + '_' + dialect + '.json'
            (directory / filename).write_text(json.dumps(packet, separators=(',', ':')) + '\n')
            out['packets'][dialect] = dict(filename=filename, instructions=len(packet) - 1)
        rows.append(out)
    (directory / 'index.json').write_text(json.dumps(rows, indent=2) + '\n')
    return rows


if __name__ == '__main__':
    import sys
    print(json.dumps(build(sys.argv[1]), indent=2))
