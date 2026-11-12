"""Untrusted proof producers and exact translations between the two calculi.

The command-line proof checkers do not import this module.
"""
import importlib.util
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def load(name):
    spec = importlib.util.spec_from_file_location(name, ROOT / (name + '.py'))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


general = load('general_context')
seed = load('seed_only')


class Builder:
    def __init__(self, mode, context=(), scope=0):
        self.mode, self.context, self.scope = mode, list(context), scope
        self.kernel = general if mode == 'general' else seed

    def conclusion(self, proof):
        return self.kernel.derive(proof, self.context, self.scope)

    def root(self, major, minor):
        return ['x', 1, major, minor] if self.mode == 'general' else ['x', major, minor]

    def refl(self, term):
        computation = ['r', 0, term, 1]
        return self.root(computation, computation)

    def sym(self, proof):
        equation = self.conclusion(proof)
        return self.root(proof, self.refl(equation[1]))

    def trans(self, first, second):
        # first: a=b; second: b=c.  Replace b by a in the left side of b=c.
        return self.root(self.sym(first), second)

    def congr(self, template, proof):
        equation = self.conclusion(proof)
        s, t = equation[1:]
        if self.mode == 'general':
            return self.sym(['x', template, proof, self.refl(general.subst(template, [s]))])
        # I(1,s;u.template)=template[s] and seed change give
        # I(1,t;u.template)=template[s].  Root replacement in the
        # t-computation then gives template[s]=template[t].
        bridge = ['x', proof, ['r', 0, s, template]]
        return self.root(bridge, ['r', 0, t, template])


def branch_context(goal, witness, context):
    body = general.shift(goal[1], 1, 2)
    lifted = general.shift(witness)
    eta = 1 if goal[1][0] == '=' and witness == 0 else 0
    hypothesis = general.subst(body, [eta, lifted])
    return [general.shift(a) for a in context] + [hypothesis]


def to_seed(proof, context=(), scope=0):
    """Translate a valid general-context proof, preserving context and conclusion."""
    context = list(context)
    general.derive(proof, context, scope)
    tag = proof[0]
    if tag in ('h', 'r'):
        return proof
    if tag == 'x':
        template, major, minor = proof[1:]
        p = to_seed(major, context, scope)
        q = to_seed(minor, context, scope)
        builder = Builder('seed', context, scope)
        return builder.root(builder.congr(template, p), q)
    if tag == 'q':
        witness, major, base = proof[1:]
        return ['q', witness, to_seed(major, context, scope), to_seed(base, context, scope)]
    if tag == 'e':
        goal, major, branch = proof[1:]
        paired = general.derive(major, context, scope)
        extended = [general.shift(a) for a in context] + [['Q', paired[1]]]
        return ['e', goal, to_seed(major, context, scope), to_seed(branch, extended, scope + 1)]
    goal, witness, branch = proof[1:]
    return ['i', goal, witness, to_seed(branch, branch_context(goal, witness, context), scope + 1)]


def to_general(proof, context=(), scope=0):
    """Translate a valid template-free proof by reconstructing its unique slot context."""
    context = list(context)
    seed.derive(proof, context, scope)
    tag = proof[0]
    if tag in ('h', 'r'):
        return proof
    if tag == 'x':
        major, minor = proof[1:]
        equation = seed.derive(major, context, scope)
        previous = seed.derive(minor, context, scope)
        if previous[1] == equation[1]:
            template = 1
        else:
            counter, _, body = previous[1]
            template = general.rec(general.shift(counter), 1, general.shift(body, 1, 1))
        return ['x', template, to_general(major, context, scope), to_general(minor, context, scope)]
    if tag == 'q':
        witness, major, base = proof[1:]
        return ['q', witness, to_general(major, context, scope), to_general(base, context, scope)]
    if tag == 'e':
        goal, major, branch = proof[1:]
        paired = seed.derive(major, context, scope)
        extended = [seed.shift(a) for a in context] + [['Q', paired[1]]]
        return ['e', goal, to_general(major, context, scope), to_general(branch, extended, scope + 1)]
    goal, witness, branch = proof[1:]
    return ['i', goal, witness, to_general(branch, branch_context(goal, witness, context), scope + 1)]
