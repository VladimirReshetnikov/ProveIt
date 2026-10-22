#!/usr/bin/env python3
"""Lift the ordinary-strong seven-equation K215 system to 79 natural variables.

There are 16 shifted primary variables and 63 gate variables, all nonnegative.
Sixty-three gate equations and seven final comparisons are quadratic. Their
sum of squares is a single quartic. This construction uses the all-zero-set
nonnegativity audit in QUADRATIC_LIFT.md; it is not a generic claim that signed
circuits can be lifted to natural gate variables without proof.
"""
from __future__ import annotations

import argparse
from collections import defaultdict
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import random


def check(condition, message):
    if not condition:
        raise ValueError(message)


# Sparse integer polynomials use monomials as sorted (name, exponent) tuples.
# The five named coefficient ports are included as formal symbols for exact
# coefficient verification, but excluded when measuring degree in unknowns.
def literal(n):
    return {(): n} if n else {}


def symbol(name):
    return {((name, 1),): 1}


def add(p, q, sign=1):
    out = defaultdict(int, p)
    for monomial, coefficient in q.items():
        out[monomial] += sign * coefficient
    return {m: c for m, c in out.items() if c}


def multiply(p, q):
    out = defaultdict(int)
    for m, c in p.items():
        for n, d in q.items():
            exponents = defaultdict(int, m)
            for variable, exponent in n:
                exponents[variable] += exponent
            out[tuple(sorted(exponents.items()))] += c*d
    return {m: c for m, c in out.items() if c}


def encode_poly(p):
    return [{"coefficient": c, "powers": dict(m)} for m, c in sorted(p.items())]


def evaluate_poly(p, values):
    total = 0
    for monomial, coefficient in p.items():
        term = coefficient
        for variable, exponent in monomial:
            term *= values[variable] ** exponent
        total += term
    return total


def degree(p, variables):
    return max((sum(e for v, e in m if v in variables) for m in p), default=0)


def evaluate_source(source, supplied):
    env = dict(supplied)
    for name, op, left, right in source:
        l = left if type(left) is int else env[left]
        r = right if type(right) is int else env[right]
        env[name] = l+r if op == '+' else l-r if op == '-' else l*r
    return env


def lift(source):
    witnesses = source['witnesses']
    constants = source['fixed_numerals']
    rows = source['source']
    check(len(witnesses) == 16 and len(rows) == 63, "unexpected source size")
    check(source['comparisons'] == [
        ['norm_first', 1], ['norm_main', 1], ['norm_aux', 1],
        ['norm_index', 1], ['norm_transport', 1],
        ['ordinary_ic2_square', 'R16'], ['C_after_alpha', 'marked_rhs']],
        "requires the ordinary-strong seven-comparison source")
    indexed = {row[0]: row for row in rows}
    check(indexed['aux_square_gap'] == ['aux_square_gap','-','H2','aux_y2'], "gap binding changed")
    check(indexed['L17'] == ['L17','*','R16','aux_square_gap'], "gap consumer changed")
    check(indexed['norm_aux'] == ['norm_aux','+','L17','aux_y2'], "auxiliary norm changed")
    changed = [list(row) for row in rows]
    for row in changed:
        if row[0] == 'aux_square_gap':
            row[:] = ['aux_square_gap','-','aux_y2','H2']
        elif row[0] == 'norm_aux':
            row[:] = ['norm_aux','-','aux_y2','L17']
    names = ['v_'+x for x in witnesses] + ['g_'+row[0] for row in changed]
    check(len(set(names)) == len(names) == 79, "duplicate lifted variable")
    variable_set = set(names)
    env = {x: add(literal(1), symbol('v_'+x)) for x in witnesses}
    env.update({x: symbol(x) for x in constants})
    residuals = []
    for name, op, left, right in changed:
        check(name not in env, "non-acyclic or duplicate gate")
        l = literal(left) if type(left) is int else env[left]
        r = literal(right) if type(right) is int else env[right]
        rhs = add(l,r) if op == '+' else add(l,r,-1) if op == '-' else multiply(l,r)
        output = symbol('g_'+name)
        residuals.append((name, add(output,rhs,-1)))
        env[name] = output
    for index, (left, right) in enumerate(source['comparisons'], 1):
        l = literal(left) if type(left) is int else env[left]
        r = literal(right) if type(right) is int else env[right]
        residuals.append(('comparison_'+str(index), add(l,r,-1)))
    check(len(residuals) == 70, "wrong quadratic equation count")
    check(max(degree(p,variable_set) for _,p in residuals) == 2, "wrong residual degree")
    quartic = {}
    for _, residual in residuals:
        quartic = add(quartic,multiply(residual,residual))
    check(degree(quartic,variable_set) == 4, "wrong quartic degree")
    # The first square alone gives this pure monomial, certifying exact degree.
    check(quartic.get((('v_tau_root',4),)) == 1, "quartic leader changed")
    packet = {
        'title':'Explicit 79-natural-variable quartic and 70 quadratic equations',
        'source_snapshot':source['snapshot'],
        'source_system':'fixed_input63_ordinary_system.json',
        'variable_domain':'nonnegative integers, including zero',
        'variables':names, 'variable_count':79,
        'primary_shift':{x:'1+v_'+x for x in witnesses},
        'fixed_numerals':constants,
        'nonnegative_gate_source':changed,
        'equations':[{'name':name,'polynomial':encode_poly(p)} for name,p in residuals],
        'equation_convention':'Every listed polynomial is equal to zero.',
        'quadratic_equation_count':70,
        'quartic':encode_poly(quartic),
        'quartic_equation_convention':'The displayed quartic polynomial is equal to zero.',
        'quartic_terms':len(quartic),
        'degree_in_unknowns':4,
        'fixed_numeral_convention':'The five named ports are fixed integer coefficients from fixed_constants.json, not additional unknowns.',
        'proof':'QUADRATIC_LIFT.md',
        'scope':'Exact arithmetic lift with zero-set nonnegativity proof; no new Lean/Rocq verification.',
    }
    return packet, changed, residuals, quartic


def verify(source, changed, residuals, quartic):
    # Local sign transformation is an exact polynomial identity.
    Q,H,Y = (symbol(x) for x in ('Q','H','Y'))
    original = add(multiply(Q,add(H,Y,-1)),Y)
    transformed = add(Y,multiply(Q,add(Y,H,-1)),-1)
    check(original == transformed, "auxiliary sign identity failed")
    rng = random.Random(215791670)
    for case in range(64):
        values = {name:rng.randrange(-3,5) for name in source['witnesses']}
        values.update(dict(Bm1=15,Kconstant=11,MC=2,MF=19,W0=8192))
        before = evaluate_source(source['source'],values)
        after = evaluate_source(changed,values)
        for name, *_ in source['source']:
            expected = -before[name] if name in ('aux_square_gap','L17') else before[name]
            check(after[name] == expected, 'all-value sign transformation mismatch: '+name)
        point = {c:values[c] for c in source['fixed_numerals']}
        point.update({'v_'+w:values[w]-1 for w in source['witnesses']})
        point.update({'g_'+name:after[name] for name,*_ in changed})
        evaluated = [evaluate_poly(p,point) for _,p in residuals]
        check(evaluated[:63] == [0]*63, "gate equations do not reproduce circuit")
        expected_comparisons = []
        for left,right in source['comparisons']:
            l = left if type(left) is int else before[left]
            r = right if type(right) is int else before[right]
            expected_comparisons.append(l-r)
        check(evaluated[63:] == expected_comparisons, "comparison changed under lift")
        check(evaluate_poly(quartic,point) == sum(e*e for e in expected_comparisons),
              "expanded quartic does not match exact sum of squares")
    return {'status':'PASS', 'lifted_natural_variables':79,
            'quadratic_equations':70, 'exact_quartic_degree':4,
            'expanded_quartic_terms':len(quartic),
            'exact_auxiliary_sign_identity':True,
            'signed_all_value_circuit_checks':64,
            'gate_equations_checked':64*63,
            'final_comparisons_checked':64*7,
            'expanded_quartic_evaluations_checked':64,
            'nonnegativity_audit':'QUADRATIC_LIFT.md; proved at solutions on admissible coefficient slices',
            'diagnostic_coefficients_are_valid_compiler_slice':False,
            'actual_K215_positive_solution_constructed':False}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source',type=Path,default=Path(__file__).with_name('fixed_input63_ordinary_system.json'))
    parser.add_argument('--output',type=Path,default=Path(__file__).with_name('quadratic_lift.json'))
    parser.add_argument('--receipt',type=Path,default=Path(__file__).with_name('quadratic_lift_checks.json'))
    args=parser.parse_args()
    raw=args.source.read_bytes(); source=json.loads(raw)
    packet,changed,residuals,quartic=lift(source)
    packet['source_sha256']=hashlib.sha256(raw).hexdigest()
    receipt=verify(source,changed,residuals,quartic)
    receipt['source_sha256']=packet['source_sha256']
    args.output.write_text(json.dumps(packet,indent=2)+'\n')
    args.receipt.write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))


if __name__=='__main__':
    main()
