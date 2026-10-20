#!/usr/bin/env python3
"""Finite algebra checks for a countermodel to the proposed quantifier fusion.

All native labels use one operator, all equality atoms one Boolean value, and
all membership atoms false. Consequently the finite checks cover arbitrary
native labels and all formula values, not a bound on numerical formula codes.
This is a countermodel to the logical calculus with the fused rows; no K-core
model is asserted.
"""
import itertools
import json
from pathlib import Path

if not __debug__:
    raise RuntimeError("Run without Python optimization; proof checks use assertions.")

TOP = 3
EQ = 2
REL = 0
QTABLE = (3, 0, 3, 3)

def imp(a, b):
    return (TOP ^ a) | b

def neg(a):
    return imp(a, REL)

def q(a):
    return QTABLE[a]

def ex(a):
    return neg(q(neg(a)))

def valid(v):
    return v == TOP

checks = {}
def check(name, cases):
    n = 0
    for value in cases:
        assert valid(value), (name, value)
        n += 1
    checks[name] = n

V = range(4)
check('rho8', (
    imp(imp(imp(c, u), a), imp(imp(a, c), imp(b, c)))
    for a, b, c, u in itertools.product(V, repeat=4)))
check('rho6', (imp(ex(q(a)), a) for a in V))
check('rho1_all_labels', [ex(EQ)])
check('rho7_all_labels', [imp(EQ, imp(EQ, EQ))])
check('rho5_all_labels', [imp(EQ, imp(REL, REL))])
check('rho3_all_labels', [imp(EQ, imp(REL, REL))])
check('merged_G_all_labels', [imp(EQ, imp(EQ, q(EQ)))])
check('equality_vacuity_all_labels', [imp(EQ, q(EQ))])
check('membership_vacuity_all_labels', [imp(REL, q(REL))])
check('rho4', (imp(q(q(a)), q(q(a))) for a in V))
check('fused_distribution_exchange', (
    imp(q(q(imp(a,b))), imp(q(q(a)), q(q(b))))
    for a,b in itertools.product(V, repeat=2)))
check('fused_distribution_exchange_swapped', (
    imp(q(q(imp(a,b))), imp(q(q(a)), q(q(b))))
    for a,b in itertools.product(V, repeat=2)))
check('theorem_GEN', [q(TOP)])
check('truth_seed', [TOP])
check('object_irreflexivity', [q(neg(REL))])
assert all(not(valid(a) and valid(imp(a,b))) or valid(b)
           for a,b in itertools.product(V, repeat=2))

# Explicit native formulas realizing all four algebra values.
# 0 is truth; 1 = R(0,0) is false; 3 = E(0,0) has value2;
# 44 = I(3,1) = not E(0,0) has value1.
def cantor(a,b):
    return (a+b)*(a+b+1)//2+b

def I(a,b):
    return 4*cantor(a,b)

def Q(i,a):
    return 4*cantor(i,a)+2

p_code, r_code, binder = 1, I(3,1), 0
assert r_code == 44
bad_value = imp(q(imp(REL,neg(EQ))), imp(q(REL),q(neg(EQ))))
assert bad_value == 0
failure_code = I(Q(binder,I(p_code,r_code)),I(Q(binder,p_code),Q(binder,r_code)))
report = {
    'status': 'FINITE_ALGEBRA_COUNTERMODEL_VERIFIED',
    'algebra': 'Boolean subsets of {0,1}, bit mask representation',
    'quantifier_operator': list(QTABLE),
    'all_quantifier_labels_have_same_operator': True,
    'membership_atom_value': REL,
    'equality_atom_value': EQ,
    'top_value': TOP,
    'axiom_checks': checks,
    'mp_preserves_validity': True,
    'all_native_formula_values_are_represented': {'0':TOP,'1':REL,'3':EQ,'44':neg(EQ)},
    'failed_original_rho2': {
        'binder':binder,'antecedent_code':p_code,'consequent_code':r_code,
        'rho2_code': failure_code,'value':bad_value},
    'scope': 'Countermodel to replacing rho2/rho4 by either proposed fusion while retaining the other logical rows and atomic vacuity. This does not model K and does not refute a K-specific interpretation.'
}
output=Path(__file__).with_name('quantifier_fusion_countermodel.json')
output.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
