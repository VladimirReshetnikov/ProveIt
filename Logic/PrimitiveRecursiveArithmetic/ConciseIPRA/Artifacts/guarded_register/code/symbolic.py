"""Build and check finite symbolic equations for the guarded-J bootstrap.

This is an untrusted proof producer. Every result is checked by checker_j.prove
with an empty hypothesis context and the stated numerical parameter scope.
The checker has no rewriting or normalization rule.
"""
import importlib.util
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('guarded_kernel', ROOT / 'checker_j.py')
k = importlib.util.module_from_spec(spec)
spec.loader.exec_module(k)
S = k.succ
lift = lambda t: k.subst(t, delta=1)
f = lambda n, a: ['j', n, lift(a)]
ONE = S(0)
W = lambda t: f(ONE, t)


def power(fn, n, t):
    for _ in range(n):
        t = fn(t)
    return t


def Z2(t):
    return f(t, ONE)


def Z(t):
    return power(W, 2, Z2(Z2(t)))


def G(c, a):
    return power(W, 3, f(power(S, 2, a), Z(c)))


def C(c, a, b):
    return power(W, 3, f(power(S, 2, a), G(c, power(S, 4, b))))


def P(t):
    return C(t, 0, W(t))


class Equation:
    def __init__(self, left, right, proof):
        self.left, self.right, self.proof = left, right, proof


def refl(t):
    alias = ['js', 0, lift(t)]
    return Equation(t, t, ['tr', 1, alias, alias])


def symmetry(e):
    return Equation(e.right, e.left, ['tr', 1, refl(e.left).proof, e.proof])


def transitivity(e, f_eq):
    if e.right != f_eq.left:
        raise ValueError('Proof producer has mismatched equation endpoints')
    if e.left == e.right:
        return f_eq
    if f_eq.left == f_eq.right:
        return e
    return Equation(e.left, f_eq.right, ['tr', 1, f_eq.proof, symmetry(e).proof])


def congruence(e, template):
    left = k.subst(template, (e.left,))
    right = k.subst(template, (e.right,))
    if e.left == e.right:
        return refl(left)
    return Equation(left, right, ['tr', template, e.proof, refl(left).proof])


def constant_zero(a):
    return Equation(f(0, a), S(a), ['j0', lift(a)])


def constant_successors(n, a):
    return Equation(f(S(n), S(a)), a, ['js', n, lift(a)])


cache = {}


def normalize(t):
    """Use only f(0,a)=S(a) and f(S(n),S(a))=a, below all contexts."""
    key = json.dumps(t, separators=(',', ':'))
    if key in cache:
        return cache[key]
    if type(t) is int:
        result = refl(t)
    else:
        if t[0] != 'j' or k.subst(t[2], (0,), 1) != t[2]:
            raise ValueError('This producer handles only state-free f terms')
        n, a = t[1], k.subst(t[2], (0,))
        en, ea = normalize(n), normalize(a)
        first = congruence(en, f(1, lift(a)))
        second = congruence(ea, f(lift(en.right), 1))
        result = transitivity(first, second)
        nn, aa = en.right, ea.right
        if nn == 0:
            result = transitivity(result, constant_zero(aa))
        elif type(nn) is list and nn[2] == 0 and type(aa) is list and aa[2] == 0:
            result = transitivity(result, constant_successors(nn[1], aa[1]))
    cache[key] = result
    return result


def main():
    cases = [
        ('f_zero', 1, f(0, 1), S(1)),
        ('f_successors', 2, f(S(1), S(2)), 2),
        ('W_successor', 1, W(S(1)), 1),
        ('W_three_zero', 0, power(W, 3, 0), 0),
        ('Z_zero', 0, Z(0), ONE),
        ('Z_successor', 1, Z(S(1)), 0),
        ('G_zero', 1, G(0, 1), 0),
        ('G_successor', 2, G(S(1), 2), 2),
        ('C_zero', 2, C(0, 1, 2), 1),
        ('C_successor', 3, C(S(1), 2, 3), 3),
        ('P_zero', 0, P(0), 0),
        ('P_successor', 1, P(S(1)), 1),
    ]
    output = ROOT / 'certificates' / 'symbolic'
    output.mkdir(parents=True, exist_ok=True)
    records = []
    for name, depth, term, expected in cases:
        e = normalize(term)
        if e.left != term or e.right != expected:
            raise ValueError(('Producer failed', name, e.right, expected))
        goal = k.eq(term, expected)
        k.formula(goal, depth)
        actual = k.prove(e.proof, depth=depth)
        if actual != goal:
            raise ValueError(('Kernel rejected producer result', name))
        payload = {'scope': depth, 'goal': goal, 'proof': e.proof}
        encoded = json.dumps(payload, separators=(',', ':')) + '\n'
        (output / (name + '.json')).write_text(encoded)
        records.append({'name': name, 'scope': depth, 'certificate_bytes': len(encoded.encode()),
                        'accepted_by_kernel': True})
        print(name, depth, len(encoded.encode()), flush=True)
    result = {'checks': len(records), 'failures': 0, 'hypotheses': [],
              'interface': 'checker_j.prove(proof, context=(), depth=scope), with formula validation at scope',
              'note': 'Open parameters are arbitrary. These finite certificates do not prove the general iPRA bridge.',
              'results': records}
    (ROOT / 'symbolic_evidence.json').write_text(json.dumps(result, indent=2) + '\n')


if __name__ == '__main__':
    main()
