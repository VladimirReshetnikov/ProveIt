#!/usr/bin/env python3
"""Exact symbolic checks accompanying four algebraic counterinterpretations.

These checks concern the proposed code calculus, not the Turing machine.
The mathematical proofs quantify over all codes; bounded checks are regressions.
"""
from functools import lru_cache
from itertools import product
from math import isqrt
import json

if not __debug__:
    raise SystemExit('Run without -O: this audit requires Python assertions.')


def pair(a, b):
    t = a + b
    return t * (t + 1) // 2 + b


def unpair(n):
    t = (isqrt(8 * n + 1) - 1) // 2
    b = n - t * (t + 1) // 2
    return t - b, b


def imp(a, b): return ('imp', a, b)
def rel(a, b): return ('rel', a, b)
def all_(a, b): return ('all', a, b)
def neg(a): return imp(a, 1)
def conj(a, b): return neg(imp(a, neg(b)))
def exists(a, b): return neg(all_(a, neg(b)))


def luk(a, b, c, u):
    return imp(imp(imp(c, u), a), imp(imp(a, c), imp(b, c)))


def old(a, b): return imp(exists(a, all_(a, b)), b)
def dual(a, b): return imp(b, all_(a, exists(a, b)))
def qi(a, b, c): return imp(all_(a, imp(b, c)), imp(all_(a, b), all_(a, c)))
def comm(a, b, c): return imp(all_(a, all_(b, c)), all_(b, all_(a, c)))


def bundle_c(a, b, c):
    power = exists(c, conj(all_(b, imp(all_(c, imp(rel(c, b), rel(c, a))),
                                       rel(b, c))), rel(c, b)))
    transitive = all_(c, imp(rel(c, a), rel(c, b)))
    return exists(b, conj(all_(a, imp(rel(a, b), conj(power, transitive))),
                          rel(c, b)))


def bundle_g(a, b, c):
    witness = exists(b, conj(c, rel(b, c)))
    return exists(c, conj(all_(a, imp(rel(a, b), all_(b, imp(c, witness)))),
                          all_(b, imp(rel(b, c), exists(a, c)))))


def bundle(a, b, c):
    vacuity = imp(rel(a, b), all_(c, rel(a, b)))
    return conj(vacuity, conj(bundle_c(a, b, c), bundle_g(a, b, c)))


@lru_cache(None)
def valuation(code):
    """F=true; forall is identity; only Rel(1,1) is false."""
    if code == 0:
        return True
    if isinstance(code, int):
        q, index = divmod(code, 3)
        a, b = unpair(q)
        tag = ('imp', 'rel', 'all')[index]
    else:
        tag, a, b = code
    if tag == 'imp':
        return not valuation(a) or valuation(b)
    if tag == 'rel':
        return (a, b) != (1, 1)
    return valuation(b)


@lru_cache(None)
def toggle_valuation(code, assignment):
    """assignment is the frozenset of variables currently having Boolean value 1.

    Rel(a,b) means value(a)=0 and value(b)=1.  Quantifier a toggles a.
    Thus F=Rel(0,0) is genuinely false at every assignment.
    """
    if code == 0:
        return True
    if isinstance(code, int):
        q, index = divmod(code, 3)
        a, b = unpair(q)
        tag = ('imp', 'rel', 'all')[index]
    else:
        tag, a, b = code
    if tag == 'imp':
        return not toggle_valuation(a, assignment) or toggle_valuation(b, assignment)
    if tag == 'rel':
        return a not in assignment and b in assignment
    return toggle_valuation(b, assignment ^ frozenset([a]))


@lru_cache(None)
def two_world_valuation(code):
    """Return a two-bit truth set: bit 0 is w and bit 1 is v.

    Q0 has w -> {w,v}, v -> {v}; every other Q is identity.
    F=Rel00 has truth set {v}; A=Rel01 has truth set {w}.
    This checks the later published generic-extension counterexample, not
    a model of the candidate's particular CP/GIC theory bundles.
    """
    if code == 0:
        return 3
    if isinstance(code, int):
        q, index = divmod(code, 3)
        a, b = unpair(q)
        tag = ('imp', 'rel', 'all')[index]
    else:
        tag, a, b = code
    if tag == 'imp':
        return (3 ^ two_world_valuation(a)) | two_world_valuation(b)
    if tag == 'rel':
        return {(0, 0): 2, (0, 1): 1}.get((a, b), 0)
    value = two_world_valuation(b)
    if a != 0:
        return value
    return (1 if value == 3 else 0) | (value & 2)


def two_world_checks():
    # These codes represent all four possible two-world truth assignments.
    payloads = [0, 1, 7, 13]
    assert {two_world_valuation(p) for p in payloads} == {0, 1, 2, 3}
    counts = dict(propositional=0, dual=0, distribution=0, commutation=0,
                  fresh_vacuity=0, modus_ponens=0, generalization=0)
    for a, b, c, u in product(payloads, repeat=4):
        assert two_world_valuation(luk(a, b, c, u)) == 3
        counts['propositional'] += 1
    # 0 and 1 represent the two quantifier operators; every positive label
    # has exactly the operator tested at 1.
    for x, p in product((0, 1), payloads):
        assert two_world_valuation(dual(x, p)) == 3
        counts['dual'] += 1
    for x, p, q in product((0, 1), payloads, payloads):
        assert two_world_valuation(qi(x, p, q)) == 3
        counts['distribution'] += 1
    for x, y, p in product((0, 1), (0, 1), payloads):
        assert two_world_valuation(comm(x, y, p)) == 3
        counts['commutation'] += 1
    for a, b, c in product(range(4), repeat=3):
        if c != a and c != b:
            assert two_world_valuation(imp(rel(a, b), all_(c, rel(a, b)))) == 3
            counts['fresh_vacuity'] += 1
    for p, q in product(payloads, repeat=2):
        if (two_world_valuation(p) == 3
                and two_world_valuation(imp(p, q)) == 3):
            assert two_world_valuation(q) == 3
        counts['modus_ponens'] += 1
    for x in (0, 1):
        assert two_world_valuation(all_(x, 0)) == 3
        counts['generalization'] += 1

    atom = rel(0, 1)
    dn_atom = neg(neg(atom))
    quantified_atom = all_(0, atom)
    gamma = [dn_atom, imp(quantified_atom, 1)]
    assert two_world_valuation(1) == 2
    assert two_world_valuation(atom) == 1
    assert all(two_world_valuation(g) == 3 for g in gamma)
    assert two_world_valuation(quantified_atom) == 0
    assert two_world_valuation(all_(0, dn_atom)) == 3
    assert two_world_valuation(neg(neg(quantified_atom))) == 2
    assert two_world_valuation(imp(1, all_(0, 1))) == 3
    table = {
        'F': 1, 'A': atom, 'DN_F_A': dn_atom,
        'Q0_A': quantified_atom, 'Q0_A_implies_F': gamma[1],
        'Q0_DN_F_A': all_(0, dn_atom),
        'DN_F_Q0_A': neg(neg(quantified_atom)),
    }
    return {
        'counts': counts,
        'world_order': ['w', 'v'],
        'truth_table': {
            name: [bool(two_world_valuation(f) & (1 << w)) for w in (0, 1)]
            for name, f in table.items()
        },
        'source': 'dual_quantifier_gap.md at ProveIt commit '
                  'e7c4cadf9b180e4b1801755b09777a7572412360',
        'scope': 'Dual plus the two common Gamma axioms cannot derive F. '
                 'The old-calculus derivation uses its written DNE theorem, '
                 'GEN, and MP. No CP/GIC model or machine claim is made.',
    }


@lru_cache(None)
def constant_quantifier_valuation(code, codec=3):
    """Every universal operator is true; all atoms and Bottom are false.

    The optional primitive-Bottom coding has tags Imp0, Bottom1, Rel2,
    All3 modulo 4. All residue-1 codes denote Bottom, including code 1.
    """
    if code == 0:
        return True
    if isinstance(code, int):
        q, index = divmod(code, codec)
        if codec == 4 and index == 1:
            return False
        a, b = unpair(q)
        tag = (('imp', 'rel', 'all')[index] if codec == 3
               else {0: 'imp', 2: 'rel', 3: 'all'}[index])
    else:
        tag, a, b = code
    if tag == 'all':
        return True
    if tag == 'rel':
        return False
    return (not constant_quantifier_valuation(a, codec)
            or constant_quantifier_valuation(b, codec))


def psc_template(matrix, k):
    """The exact curried wrapper in the late source, built symbolically."""
    sub = lambda x, y, z: all_(z, imp(rel(z, x), rel(z, y)))
    subset_bound = all_(0, exists(k, all_(1, imp(matrix, sub(1, k, 0)))))
    guard = imp(neg(sub(0, 1, k)), rel(0, k))
    closed = all_(0, imp(guard, all_(1, imp(matrix, rel(1, k)))))
    support = all_(1, imp(rel(1, k), exists(0, matrix)))
    return imp(subset_bound, all_(1, exists(k, conj(closed, support))))


def psc_checks():
    counts = dict(propositional=0, other_logical=0, psc_templates=0,
                  ir=0, negative_cp_gic_controls=0)
    for codec in (3, 4):
        ev = lambda p: constant_quantifier_valuation(p, codec)
        assert ev(0) and not ev(1)
        # Code 0=Imp(0,0) respects its truth-alias equation in both codings.
        assert ev(imp(0, 0)) == ev(0)
        for a, b, c, u in product((0, 1), repeat=4):
            assert ev(luk(a, b, c, u))
            counts['propositional'] += 1
        for x, p, q in product((0, 1), (0, 1), (0, 1)):
            for f in (old(x, p), qi(x, p, q), comm(x, 1-x, p),
                      imp(rel(x, 1-x), all_(2, rel(x, 1-x)))):
                assert ev(f)
                counts['other_logical'] += 1
        for matrix in (0, 1, 2, 7, 13, 101):
            assert ev(psc_template(matrix, matrix + 2))
            counts['psc_templates'] += 1
        assert ev(all_(1, neg(rel(1, 1))))
        counts['ir'] += 1
        assert not ev(imp(all_(0, 1), 1))
        for p, q in product((0, 1), repeat=2):
            if ev(p) and ev(imp(p, q)):
                assert ev(q)
        for x in (0, 1):
            assert ev(all_(x, 0))
    for matrix in (0, 1, 2, 7, 13, 101):
        ev = constant_quantifier_valuation
        assert not ev(bundle_c(0, 1, matrix))
        assert not ev(bundle_g(0, 1, matrix))
        assert not ev(bundle(0, 1, matrix))
        counts['negative_cp_gic_controls'] += 1
    return {
        'counts': counts,
        'source': 'psc_backend_experiment.md at ProveIt commit '
                  'e7c4cadf9b180e4b1801755b09777a7572412360',
        'F_value': False,
        'universal_operator_is_constant_true': True,
        'ordinary_universal_specialization_is_invalid': True,
        'scope': 'All instances of the stated PSC source axioms are valid '
                 'by the displayed structural argument; finite regressions '
                 'are checked here. Induction on derivations excludes F. '
                 'The actual CP/GIC bundles fail this valuation. No literal '
                 'Turing-machine nonhalting theorem is asserted.',
    }


def main():
    codes = [0, 1, 2, 7, 13]
    counts = dict(propositional=0, other_logical=0, bundles=0, toggle=0)
    for a, b, c, u in product(codes, repeat=4):
        assert valuation(luk(a, b, c, u))
        counts['propositional'] += 1
    for a, b, c in product(codes, repeat=3):
        for f in (dual(a, b), qi(a, b, c), comm(a, b, c),
                  imp(rel(a, b), all_(c, rel(a, b)))):
            assert valuation(f)
            counts['other_logical'] += 1
        if c != a and c != b:
            assert valuation(bundle(a, b, c))
            counts['bundles'] += 1
    counter_atom = 3 * pair(1, 1) + 1
    counter_explosion = 3 * pair(1, counter_atom)
    assert counter_atom == 13 and counter_explosion == 354
    assert valuation(1) and not valuation(counter_atom)
    assert not valuation(counter_explosion)
    assert not valuation(old(0, counter_atom))
    a = 3 * pair(0, 1) + 1
    ui = 3 * pair(3 * pair(0, a) + 2, a)
    witness_assignment = frozenset([0, 1])
    assert ui == 19686
    assert not toggle_valuation(1, witness_assignment)
    assert not toggle_valuation(ui, witness_assignment)
    assignments = [frozenset(i for i in range(4) if mask >> i & 1) for mask in range(16)]
    for assignment in assignments:
        for x in range(4):
            for f in codes:
                assert toggle_valuation(old(x, f), assignment)
                assert toggle_valuation(dual(x, f), assignment)
                counts['toggle'] += 2
    print(json.dumps({
        'status': 'algebraic countermodel checks passed',
        'counts': counts,
        'first_countermodel': {
            'F_value': True, 'false_atom_code': counter_atom,
            'nonderivable_explosion_code': counter_explosion,
            'old_rho6_is_not_valid': True,
            'scope': 'all dual logical axioms and CP/GIC bundles; induction proves every generated theorem true'},
        'second_countermodel': {
            'F_value': False, 'invalid_universal_instantiation_code': ui,
            'assignment_ones': [0, 1],
            'scope': 'pure equality-free logical fragment only; no assertion about CP/GIC'},
        'third_countermodel': two_world_checks(),
        'fourth_countermodel': psc_checks(),
        'limitation': 'The first two models leave the particular CP/GIC refutation target open. '
                      'The third refutes generic preservation for arbitrary common extensions. '
                      'The fourth excludes the PSC source-calculus target. No check establishes '
                      'a claim about any literal Turing machine halting or not halting.'
    }, indent=2))


if __name__ == '__main__':
    main()
