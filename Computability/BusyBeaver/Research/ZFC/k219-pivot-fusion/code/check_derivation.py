#!/usr/bin/env python3
"""Finite schema derivations relative to the retained classical bridge.

This checker treats ordinary classical tautology use as an explicitly checked
derived rule of the retained rho8/rho6 bridge. It does not formalize that
inherited bridge or substitute for an exact native-code proof assistant proof.
"""
import argparse
import itertools
import json
from pathlib import Path

F = ('F',)
I = lambda a, b: ('I', a, b)
N = lambda a: I(a, F)
Q = lambda i, a: ('Q', i, a)
Ex = lambda i, a: N(Q(i, N(a)))
E = lambda a, b: ('E', a, b)
R = lambda a, b: ('R', a, b)


class Proof:
    def __init__(self, name):
        self.name = name
        self.steps = []
        self.truth_rows = 0

    def add(self, rule, formula, premises=(), detail=None):
        self.steps.append(dict(index=len(self.steps), rule=rule, formula=formula,
                               premises=list(premises), detail=detail))
        return len(self.steps)-1

    def formula(self, p):
        return self.steps[p]['formula']

    def ax(self, kind, *args):
        if kind == 'rho1':
            i, a = args
            f = Ex(i, E(i, a))
        elif kind == 'rho2':
            i, a, b = args
            f = I(Q(i, I(a, b)), I(Q(i, a), Q(i, b)))
        elif kind == 'rho6':
            i, a = args
            f = I(Ex(i, Q(i, a)), a)
        elif kind == 'G':
            a, b, u = args
            k = ('membership-code', a, b)
            f = I(E(u, a), I(E(u, b), Q(k, E(a, b))))
        else:
            raise ValueError(kind)
        return self.add(kind, f, detail=args)

    def taut(self, goal, *premises):
        formula = goal
        for p in reversed(premises):
            formula = I(self.formula(p), formula)
        atoms = set()
        def collect(f):
            if f[0] == 'I':
                collect(f[1]); collect(f[2])
            elif f != F:
                atoms.add(f)
        collect(formula)
        atoms = sorted(atoms, key=repr)
        assert len(atoms) <= 12, ('Finite check bound', len(atoms))
        def val(f, env):
            if f == F: return False
            if f[0] == 'I': return not val(f[1], env) or val(f[2], env)
            return env[f]
        for values in itertools.product((False, True), repeat=len(atoms)):
            assert val(formula, dict(zip(atoms, values))), ('Not tautological', formula, values)
            self.truth_rows += 1
        return self.add('classical-tautology-and-MP', goal, premises,
                        dict(atoms=len(atoms), valuations=2**len(atoms)))

    def gen(self, i, p):
        return self.add('closed-theorem-GEN', Q(i, self.formula(p)), (p,), i)

    def qmono(self, i, p):
        op, a, b = self.formula(p)
        assert op == 'I'
        g = self.gen(i, p)
        d = self.ax('rho2', i, a, b)
        return self.taut(I(Q(i, a), Q(i, b)), g, d)

    def exmono(self, i, p):
        op, a, b = self.formula(p)
        assert op == 'I'
        contra = self.taut(I(N(b), N(a)), p)
        lifted = self.qmono(i, contra)
        return self.taut(I(Ex(i, a), Ex(i, b)), lifted)

    def ex_mp(self, i, a, b):
        contra = self.taut(I(I(a, b), I(N(b), N(a))))
        lifted = self.qmono(i, contra)
        d = self.ax('rho2', i, N(b), N(a))
        return self.taut(I(Q(i, I(a, b)), I(Ex(i, a), Ex(i, b))), lifted, d)

    def serial(self, i, a):
        e = E(i, i)
        weaken = self.taut(I(a, I(e, a)))
        lifted = self.qmono(i, weaken)
        emp = self.ex_mp(i, e, a)
        exists = self.ax('rho1', i, i)
        return self.taut(I(Q(i, a), Ex(i, a)), lifted, emp, exists)

    def double_q(self, i, a):
        serial = self.serial(i, Q(i, a))
        eliminate = self.ax('rho6', i, a)
        return self.taut(I(Q(i, Q(i, a)), a), serial, eliminate)

    def reflexivity(self, x):
        z = ('membership-code', x, x)
        e = E(x, x)
        g = self.ax('G', x, x, z)
        contracted = self.taut(I(E(z, x), Q(z, e)), g)
        lifted = self.exmono(z, contracted)
        exists = self.ax('rho1', z, x)
        eliminate = self.ax('rho6', z, e)
        return self.taut(e, lifted, exists, eliminate)

    def bundle(self, a, b, c, u):
        # c is either an arbitrary parameter under the displayed gate, or
        # the external finite-proof choice max(a,b)+1. No constraint on u.
        assert c == 'c' or c == ('fresh', a, b)
        m = I(E(u, a), I(R(u, b), Q(c, R(a, b))))
        d = ('unchanged-Qcore', a, b, c)
        p = self.add('new-gated-bundle', N(I(m, d)), detail={'gate': ['c != a', 'c != b']})
        return self.taut(m, p), self.taut(N(d), p)

    def vacuity(self, a, b, c):
        m, k = self.bundle(a, b, c, a)
        e = self.reflexivity(a)
        v = self.taut(I(R(a, b), Q(c, R(a, b))), m, e)
        return v, k


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--out', type=Path, required=True)
    args = ap.parse_args()
    if args.out.exists(): raise FileExistsError(args.out)
    assert __debug__
    a, b, c, u = 'a', 'b', 'c', 'u'
    proof = Proof('new-to-old')
    v, k = proof.vacuity(a, b, c)
    old_bundle = proof.taut(N(I(proof.formula(v), ('unchanged-Qcore', a, b, c))), v, k)
    fresh = ('fresh', a, b)
    v2, _ = proof.vacuity(a, b, fresh)
    lifted = proof.qmono(fresh, v2)
    qq = proof.double_q(fresh, R(a, b))
    eliminate = proof.taut(I(Q(fresh, R(a, b)), R(a, b)), lifted, qq)
    m, _ = proof.bundle(a, b, fresh, u)
    rho5 = proof.taut(I(E(u, a), I(R(u, b), R(a, b))), m, eliminate)
    old = Proof('old-to-new')
    d = ('unchanged-Qcore', a, b, c)
    vformula = I(R(a, b), Q(c, R(a, b)))
    ob = old.add('old-gated-bundle', N(I(vformula, d)), detail={'gate': ['c != a', 'c != b']})
    ov = old.taut(vformula, ob)
    ok = old.taut(N(d), ob)
    r5 = old.add('old-rho5', I(E(u, a), I(R(u, b), R(a, b))))
    nm = old.taut(I(E(u, a), I(R(u, b), Q(c, R(a, b)))), ov, r5)
    nb = old.taut(N(I(old.formula(nm), d)), nm, ok)
    result = dict(status='RELATIVE_FINITE_SCHEMA_DERIVATIONS_PASS',
                  retained_axioms=['rho1', 'rho2', 'rho6', 'unrestricted rho8 via classical bridge', 'G'],
                  assumptions=['Inherited all-native-code relative-classical bridge justifies each finitely checked tautology.',
                               'The gate is c!=a,b; choose fresh=max(a,b)+1 to recover ungated rho5.',
                               'No axiom of K is opened or translated; its original native Qcore and private label remain fixed.'],
                  conclusions={'new-to-old': {'old_bundle': old_bundle, 'rho5': rho5}, 'old-to-new': {'new_bundle': nb}},
                  steps={'new-to-old': proof.steps, 'old-to-new': old.steps},
                  counts={'new_to_old_steps': len(proof.steps), 'old_to_new_steps': len(old.steps),
                          'boolean_valuation_checks': proof.truth_rows+old.truth_rows},
                  limits=['Schema-level Python check, not Lean/Rocq and not an internal PA theorem.',
                          'No source interpreter or binary runtime is established by this check.'])
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({'status': result['status'], **result['counts']}, sort_keys=True))


if __name__ == '__main__': main()
