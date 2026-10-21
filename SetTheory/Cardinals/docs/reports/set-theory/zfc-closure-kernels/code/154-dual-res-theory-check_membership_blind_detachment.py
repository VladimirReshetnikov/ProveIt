#!/usr/bin/env python3
"""Finite semantic regression for the membership-blind theorem rule.

This checks ordinary two-element irreflexive structures, not models of K or
ZFC. The all-model proof is in membership_blind_detachment.md.
"""
from functools import cache
from itertools import product
from math import isqrt
from pathlib import Path
import json

if not __debug__:
    raise RuntimeError('Run without Python optimization')


def P(a, b):
    return (a+b)*(a+b+1)//2+b


def unP(n):
    s = (isqrt(8*n+1)-1)//2
    b = n-s*(s+1)//2
    return s-b, b


def quotient(h):
    q, r = divmod(h, 4)
    return max(0,q-1) if r == 1 else q


def decode(h):
    return unP(quotient(h))


@cache
def fv(n):
    if n == 0:
        return frozenset()
    a, b = unP(n//4)
    k = n % 4
    if k == 0:
        return fv(a) | fv(b)
    if k == 2:
        return fv(b) - {a}
    return frozenset((a,b))


def model(relation):
    def value(n, assignment):
        if n == 0:
            return True
        a, b = unP(n//4)
        k = n % 4
        if k == 0:
            return not value(a,assignment) or value(b,assignment)
        if k == 1:
            return (assignment.get(a,0),assignment.get(b,0)) in relation
        if k == 3:
            return assignment.get(a,0) == assignment.get(b,0)
        return all(value(b,{**assignment,a:x}) for x in (0,1))
    @cache
    def valid(n):
        labels = tuple(sorted(fv(n)))
        return all(value(n,dict(zip(labels,vs))) for vs in product((0,1),repeat=len(labels)))
    return valid


def main():
    field_checks = 0
    for a,b,k in product(range(129),range(129),(0,2,3)):
        h = 4*P(a,b)+k
        assert decode(h) == (a,b), (h,a,b,k,decode(h))
        field_checks += 1
    arithmetic_checks = 0
    for h in range(100001):
        if h < 2:
            walk_count = 0
        else:
            n = h-2
            walk_count = n//4 + (n%4 == 2)
        assert walk_count == quotient(h)
        arithmetic_checks += 1
    semantic_checks = 0
    successful_premises = 0
    halt_checks = 0
    for i,j in product((False,True),repeat=2):
        relation = frozenset(([(0,1)] if i else []) + ([(1,0)] if j else []))
        valid = model(relation)
        for h in range(10001):
            a,b = decode(h)
            if valid(h) and valid(a):
                assert valid(b), (relation,h,a,b)
                successful_premises += 1
            semantic_checks += 1
            if h%4 == 1 or (h%4 == 3 and h%16 != 3):
                assert not valid(h), ('unsafe_halt',relation,h)
                halt_checks += 1
    # Deliberately apply the same extra walk to a quantifier code in the old
    # tag layout. Q(1,0)=6 is globally valid, while the wrong decoder outputs
    # unP(2)=(0,1), deriving false1 from truth0. This demonstrates that the
    # semantic restriction on which tag may be misdecoded is substantive.
    valid = model(frozenset())
    bad_h = 6
    bad_a,bad_b = unP(bad_h//4+1)
    assert valid(bad_h) and valid(bad_a) and not valid(bad_b)
    result = {
        'status':'MEMBERSHIP_BLIND_RULE_REGRESSION_PASS',
        'exact_I_Q_E_field_checks':field_checks,
        'arithmetic_case_checks':arithmetic_checks,
        'two_element_irreflexive_models':4,
        'semantic_rule_checks':semantic_checks,
        'satisfied_rule_premises':successful_premises,
        'safe_halt_code_checks':halt_checks,
        'negative_control':{'cached':bad_h,'wrong_fields':[bad_a,bad_b],
                            'premises_valid':True,'conclusion_valid':False},
        'scope':'Finite semantic regression, not a K/ZFC model check and not a source/TM proof.',
    }
    Path(__file__).with_name('membership_blind_receipt.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__ == '__main__':
    main()
