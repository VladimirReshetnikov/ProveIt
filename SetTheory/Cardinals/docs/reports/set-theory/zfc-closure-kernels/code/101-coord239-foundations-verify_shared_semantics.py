#!/usr/bin/env python3
"""Independent bounded regressions for the new structural specializations.

The finite membership universes below are transcription controls only. They
are NOT asserted to model EPSC, the complete equations, or Con(ZFC).
"""
from __future__ import annotations

import itertools
import json
import random
from pathlib import Path

D = ('d',)


def P(x, s):
    return ('P', x, s)


def A(i, j):
    return ('A', i, j)


def Q(a):
    return ('Q', a)


def numeral(index):
    value = D
    for _ in range(index):
        value = A(value, D)
    return value


def index_value(index):
    answer = 0
    while isinstance(index, tuple) and len(index) == 3 and index[0] == 'A' and index[2] == D:
        answer += 1
        index = index[1]
    return answer


def lookup(environment, selector):
    n = index_value(selector)
    for _ in range(n):
        environment = environment[2] if (isinstance(environment, tuple)
                       and len(environment) == 3 and environment[0] == 'P') else D
    return environment[1] if (isinstance(environment, tuple)
                            and len(environment) == 3 and environment[0] == 'P') else 0


def incidence(environment, code, relation, domain=(0,1)):
    if code == D:
        return False
    if code[0] == 'P':
        return not (incidence(environment, code[1], relation, domain)
                    and incidence(environment, code[2], relation, domain))
    if code[0] == 'A':
        return (lookup(environment, code[1]), lookup(environment, code[2])) in relation
    if code[0] == 'Q':
        return any(incidence(P(z, environment), code[1], relation, domain) for z in domain)
    raise ValueError('unknown class constructor')


def source_semantics(formula, environment, relation, domain=(0,1)):
    if formula[0] == 'atom':
        return (environment[formula[1]], environment[formula[2]]) in relation
    if formula[0] == 'nand':
        return not (source_semantics(formula[1], environment, relation, domain)
                    and source_semantics(formula[2], environment, relation, domain))
    if formula[0] == 'exists':
        return any(source_semantics(formula[1], (z, *environment), relation, domain)
                   for z in domain)
    raise ValueError('unknown source constructor')


def compile_formula(formula, depth=0):
    # Free inputs x,y,p1,p2 use slots 1,0,3,4. Descriptor code is slot 2.
    if formula[0] == 'atom':
        def slot(i):
            return i if i < depth else (1,0,3,4)[i-depth] + depth
        return A(numeral(slot(formula[1])), numeral(slot(formula[2])))
    if formula[0] == 'nand':
        return P(compile_formula(formula[1], depth), compile_formula(formula[2], depth))
    if formula[0] == 'exists':
        return Q(compile_formula(formula[1], depth + 1))
    raise ValueError('unknown source constructor')


def run():
    randomizer = random.Random(946)
    def formula(fuel, depth=0):
        if fuel == 0 or randomizer.randrange(4) == 0:
            return ('atom', randomizer.randrange(depth+4), randomizer.randrange(depth+4))
        if randomizer.randrange(2):
            return ('nand', formula(fuel-1, depth), formula(fuel-1, depth))
        return ('exists', formula(fuel-1, depth+1))
    formulas = [formula(4) for _ in range(64)]
    reification_checks = 0
    spare_pick_checks = 0
    arbitrary_false_witness_checks = 0
    native_checks = 0
    selectors = [D, ('opaque',)] + [numeral(i) for i in range(8)]
    selectors += [A(A(('opaque',),D),D), A(D,('opaque',))]
    environments = [D, ('opaque',), P(0,D), P(1,P(0,D)), P(1,('opaque',))]
    for x, s, j in itertools.product(range(4), environments, selectors):
        assert lookup(P(x,s),D) == x
        assert lookup(P(x,s),A(j,D)) == lookup(s,j)
        native_checks += 2
    for mask in range(16):
        relation = {(x,y) for x in range(2) for y in range(2) if mask >> (2*x+y) & 1}
        def W(s, c):
            if c == D:
                # The spare slice is a member selector on the object s.
                return next((z for z in (0,1) if (z,s) in relation), 0)
            return next((z for z in (0,1) if incidence(P(z,s),c,relation)), 0)
        for x in (0,1):
            if any((u,x) in relation for u in (0,1)):
                assert (W(x,D),x) in relation
            assert incidence(P(W(x,D),x),D,relation) is False
            assert incidence(x,Q(D),relation) is False
            spare_pick_checks += 1
        for s, z in itertools.product(environments, (0,1,2,3)):
            assert not incidence(P(z,s),D,relation)
            assert not incidence(s,Q(D),relation)
            arbitrary_false_witness_checks += 1
        for f in formulas:
            c = compile_formula(f)
            for x,y,p1,p2 in itertools.product((0,1),repeat=4):
                descriptor = P(c,P(p1,P(p2,D)))
                packed = P(y,P(x,descriptor))
                recovered = lookup(descriptor,D)
                assert recovered == c
                assert incidence(packed,recovered,relation) == source_semantics(f,(x,y,p1,p2),relation)
                # The chosen witness equation is checked for the modified class code.
                assert incidence(packed,Q(c),relation) == incidence(P(W(packed,c),packed),c,relation)
                reification_checks += 1
    # A cons is not required to commute; only its predicate value is symmetric.
    assert P(0,1) != P(1,0)
    # The shared class P(d,d) is true, even though both children d denote false.
    assert incidence(D,P(D,D),set()) is True
    return {
        'status': 'bounded transcription regressions only; no finite EPSC model claimed',
        'native_head_and_tail_checks': native_checks,
        'shared_cons_nand_formula_and_witness_checks': reification_checks,
        'spare_member_choice_checks': spare_pick_checks,
        'arbitrary_false_class_witness_checks': arbitrary_false_witness_checks,
        'structural_noncommutativity_and_nand_controls': 2,
    }


if __name__ == '__main__':
    if not __debug__:
        raise SystemExit('Assertions must be enabled; omit -O.')
    result = run()
    output = Path(__file__).resolve().parent/'generated'/'shared_semantics_verification.json'
    output.parent.mkdir(exist_ok=True)
    output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
