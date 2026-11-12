"""Untrusted derived rules and proof compilers for the mirror experiment.

The checker imports none of this file. All produced certificates are replayed.
"""
import importlib.util
from pathlib import Path
import sys
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tests'))
from verify_mirror import M, Z, V, S, I, Eq, Proofs
spec = importlib.util.spec_from_file_location('native_reference', ROOT / 'reference/native_checker.py')
N = importlib.util.module_from_spec(spec)
spec.loader.exec_module(N)

def guard(b):
    return b[0] == '=' and b[2][:3] == ['i', V(0), b[1]]

def substitute(a, sigma, depth=0):
    return M.walk(a, lambda i, d: V(i) if i < d else M.shift(sigma[i - d], d), depth)

def up(sigma):
    return [V(0)] + [M.shift(t) for t in sigma]

def syntactic_substitution(p, sigma):
    """Literal proof substitution; safe for renaming, possibly unsafe otherwise."""
    match p:
        case ['hyp', i]:
            return p
        case ['refl', a]:
            return ['refl', substitute(a, sigma)]
        case ['eval', p, q]:
            return ['eval', syntactic_substitution(p, sigma), syntactic_substitution(q, sigma)]
        case ['zero', a, h]:
            return ['zero', substitute(a, sigma), substitute(h, sigma, 1)]
        case ['succ', c, a, h]:
            return ['succ', substitute(c, sigma), substitute(a, sigma), substitute(h, sigma, 1)]
        case ['tr', a, b, p, q]:
            return ['tr', substitute(a, sigma, 1), substitute(b, sigma, 1), syntactic_substitution(p, sigma), syntactic_substitution(q, sigma)]
        case ['qe', t, p, q]:
            return ['qe', substitute(t, sigma), syntactic_substitution(p, sigma), syntactic_substitution(q, sigma)]
        case ['de', a, p, q]:
            return ['de', substitute(a, sigma), syntactic_substitution(p, sigma), syntactic_substitution(q, up(sigma))]
        case ['di', b, t, p]:
            return ['di', substitute(b, sigma, 2), substitute(t, sigma), syntactic_substitution(p, up(sigma))]
        case ['qi', b, p]:
            return ['qi', substitute(b, sigma, 1), syntactic_substitution(p, up(sigma))]
    raise ValueError('unknown proof constructor')

def add_hypothesis(p, depth=0):
    """Insert an ambient context entry; local hypotheses keep their positions."""
    match p:
        case ['hyp', i]:
            return ['hyp', i + (i >= depth)]
        case ['refl', _] | ['zero', _, _] | ['succ', _, _, _]:
            return p
        case ['eval', p, q]:
            return ['eval', add_hypothesis(p, depth), add_hypothesis(q, depth)]
        case ['tr', a, b, p, q]:
            return ['tr', a, b, add_hypothesis(p, depth), add_hypothesis(q, depth)]
        case ['qe', t, p, q]:
            return ['qe', t, add_hypothesis(p, depth), add_hypothesis(q, depth)]
        case ['de', a, p, q]:
            return ['de', a, add_hypothesis(p, depth), add_hypothesis(q, depth + 1)]
        case ['di', b, t, p]:
            return ['di', b, t, add_hypothesis(p, depth + 1)]
        case ['qi', b, p]:
            return ['qi', b, add_hypothesis(p, depth + 1)]
    raise ValueError('unknown proof constructor')

def lift_proof(p, n):
    return add_hypothesis(syntactic_substitution(p, [V(i + 1) for i in range(n)]))

def base_proof(b, t, n, context):
    """The zero base of a mirrored matrix, in a scope containing fresh z."""
    assert guard(b)
    a = M.sub(['q', b], t)[1]
    base = M.shift(M.sub(a, Z))
    source, iterator = base[1:]
    assert iterator[:3] == ['i', Z, source]
    P = Proofs(n + 1, context)
    result = P.sym(P.zero(source, iterator[3]))
    assert P.conclusion(result) == base
    return result

def transform(p, old_context, old_n, sigma, new_context, hypotheses):
    """Simultaneous numerical substitution and substitution for hypotheses.

    sigma maps old_n variables to the new ambient scope. Each hypotheses[i]
    proves substitute(old_context[i],sigma) in new_context. Only the DI case
    needs a repair when substitution creates the mirror shape.
    """
    new_n = sigma.scope
    match p:
        case ['hyp', i]:
            return hypotheses[i]
        case ['refl', a]:
            return ['refl', substitute(a, sigma)]
        case ['eval', p, q]:
            return ['eval', transform(p, old_context, old_n, sigma, new_context, hypotheses), transform(q, old_context, old_n, sigma, new_context, hypotheses)]
        case ['qe', t, p, q]:
            return ['qe', substitute(t, sigma), transform(p, old_context, old_n, sigma, new_context, hypotheses), transform(q, old_context, old_n, sigma, new_context, hypotheses)]
        case ['de', a, p, q]:
            b = M.infer(p, old_context, old_n)[1]
            b_new = substitute(b, sigma, 2)
            old_branch = [['q', b]] + [M.shift(x) for x in old_context]
            new_branch = [['q', b_new]] + [M.shift(x) for x in new_context]
            lifted = [['hyp', 0]] + [lift_proof(r, new_n) for r in hypotheses]
            return ['de', substitute(a, sigma), transform(p, old_context, old_n, sigma, new_context, hypotheses), transform(q, old_branch, old_n + 1, ScopedTerms(up(sigma), new_n + 1), new_branch, lifted)]
        case ['di', b, t, q]:
            b_new, t_new = substitute(b, sigma, 2), substitute(t, sigma)
            a, a_new = M.sub(['q', b], t)[1], M.sub(['q', b_new], t_new)[1]
            old_guard, new_guard = guard(b), guard(b_new)
            if old_guard and not new_guard:
                raise AssertionError('substitution destroyed a literal mirror')
            old_h = a if old_guard else M.shift(M.sub(a, Z))
            new_h = a_new if new_guard else M.shift(M.sub(a_new, Z))
            old_branch = [old_h] + [M.shift(x) for x in old_context]
            new_branch = [new_h] + [M.shift(x) for x in new_context]
            first = base_proof(b_new, t_new, new_n, new_branch) if new_guard and not old_guard else ['hyp', 0]
            lifted = [first] + [lift_proof(r, new_n) for r in hypotheses]
            return ['di', b_new, t_new, transform(q, old_branch, old_n + 1, ScopedTerms(up(sigma), new_n + 1), new_branch, lifted)]
    raise ValueError('unknown mirror proof constructor')

class ScopedTerms(list):
    def __init__(self, values, scope):
        super().__init__(values)
        self.scope = scope

def substitute_derivation(p, context, n, sigma, m):
    return transform(p, context, n, ScopedTerms(sigma, m), [substitute(a, sigma) for a in context], [['hyp', i] for i in range(len(context))])

def case_di(b, t, branch, context, n):
    """Derived unrestricted case introduction in the mirror calculus."""
    if not guard(b):
        return ['di', b, t, branch]
    a = M.sub(['q', b], t)[1]
    old_context = [M.shift(M.sub(a, Z))] + [M.shift(x) for x in context]
    new_context = [a] + [M.shift(x) for x in context]
    hypotheses = [base_proof(b, t, n, new_context)] + [['hyp', i] for i in range(1, len(old_context))]
    converted = transform(branch, old_context, n + 1, ScopedTerms([V(i) for i in range(n + 1)], n + 1), new_context, hypotheses)
    return ['di', b, t, converted]

class NativeProofs:
    def __init__(self, n, context):
        self.n, self.g = n, context
    def conclusion(self, p):
        return N.infer(p, self.g, self.n)
    def refl(self, a):
        p = ['zero', a, V(0)]
        return ['tr', V(0), M.shift(a), p, p]
    def sym(self, p):
        source = self.conclusion(p)[1]
        return ['tr', V(0), M.shift(source), p, self.refl(source)]
    def trans(self, p, q):
        source = self.conclusion(p)[1]
        return ['tr', M.shift(source), V(0), q, p]
    def congr(self, h, p):
        source = self.conclusion(p)[1]
        instance = M.sub(h, source)
        return ['tr', M.shift(instance), h, p, self.refl(instance)]

def to_native(p, context=(), n=0):
    context = list(context)
    P = NativeProofs(n, context)
    match p:
        case ['hyp', i]:
            return p
        case ['refl', a]:
            return P.refl(a)
        case ['eval', p, q]:
            e, f = M.infer(p, context, n), M.infer(q, context, n)
            p, q = to_native(p, context, n), to_native(q, context, n)
            _, c, a, h = f[1]
            if c == Z:
                joined = P.trans(['zero', a, h], p)
            else:
                joined = P.trans(['succ', c[1], a, h], P.congr(h, p))
            return P.trans(P.sym(q), joined)
        case ['qe', t, p, q]:
            return ['qe', t, to_native(p, context, n), to_native(q, context, n)]
        case ['de', a, p, q]:
            b = M.infer(p, context, n)[1]
            branch_context = [['q', b]] + [M.shift(x) for x in context]
            return ['de', a, to_native(p, context, n), to_native(q, branch_context, n + 1)]
        case ['di', b, t, q]:
            a = M.sub(['q', b], t)[1]
            h = a if guard(b) else M.shift(M.sub(a, Z))
            branch_context = [h] + [M.shift(x) for x in context]
            branch = to_native(q, branch_context, n + 1)
            if guard(b):
                qi = ['qi', a, branch]
                branch = ['qe', S(V(0)), lift_proof(qi, n), ['hyp', 0]]
            return ['di', b, t, branch]
    raise ValueError('unknown mirror proof constructor')
