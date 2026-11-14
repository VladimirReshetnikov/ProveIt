# Inherited emitter/term utilities from PA194N; its old command evaluator, word tests, and CLI
# have been removed. PA194DHS semantics and tests are in check_commands.py.
#!/usr/bin/env python3
"""Free-term emitter and no-push command certificates for PA194DHS.

Adapted from the supplied pa194_conpa_2026-11-13_2 symbolic checker.
The original no-push MP rule appeared earlier at 196 states in the supplied
conpa_tm_comparison_and_reduction_search packet; no novelty is claimed for
that command rule itself. This checker specializes it to the ten-entry AX.

No builder or compiler module is imported. The only arithmetic facts used by
the symbolic command check are Cantor projection identities, p(0,0)=0,
I(0,0)=0, I(a,b)=0 iff a=b=0, and constructor residues modulo four.
These executable checks support, and do not replace, pa194_calibration.tex.
"""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parent.parent


def require(claim, message):
    if not claim:
        raise ValueError(message)


TERMINALS = {'node49': ['push'], 'node55': ['copyD'],
             'node58': ['copyH'], 'node70': ['copyA'],
             'node65': ['cons'], 'node72': ['readH'],
             'node75': ['readDCons'], 'node142': ['copyGuard'],
             'node150': ['compareGuard'], 'node60': ['incT'] * 2,
             'node61': ['incT'] * 4}


def decode_word(path):
    data = json.loads(path.read_text())
    rules = data['rules']

    def expand(term, active=frozenset()):
        if isinstance(term, str):
            if term in TERMINALS:
                return TERMINALS[term]
            require(term in rules and term not in active, 'invalid grammar reference')
            return expand(rules[term], active | {term})
        if term == ['leaf', 'inc', 1]:
            return ['incT']
        if term in (['leaf', 'breakTo', 1], ['leaf', 'dec', 4]):
            return ['close']
        require(isinstance(term, list) and len(term) == 2, 'invalid grammar production')
        return expand(term[0], active) + expand(term[1], active)

    return expand(data['root'])


def emitter_check():
    word = decode_word(ROOT / 'inputs/grammar.json')
    require(len(word) == 190, 'word length')
    zero = ('zero',)
    succ = lambda a: ('succ', a)
    one = succ(zero)
    implication = lambda a, b: ('I', a, b)
    member = lambda a, b: succ(implication(a, b))
    universal = lambda a, b: succ(succ(implication(b, a)))
    equality = lambda a, b: succ(succ(succ(implication(a, b))))
    negative = lambda a: implication(a, one)
    conj = lambda a, b: negative(implication(a, negative(b)))
    exists = lambda a, b: negative(universal(a, negative(b)))
    t, a, d, h, x, y = [('parameter', s) for s in ('t', 'a', 'd', 'h', 'x', 'y')]
    top, D, H, stack = t, d, h, []
    fields = iter((y, x))
    reads = []
    for token in word[:-3]:
        if token == 'push':
            stack.append(top)
            top = zero
        elif token in ('copyD', 'copyH', 'copyA'):
            stack.append(top)
            top = dict(copyD=D, copyH=H, copyA=a)[token]
        elif token == 'cons':
            require(bool(stack), 'emitter underflow')
            top = implication(stack.pop(), top)
        elif token == 'incT':
            top = succ(top)
        elif token == 'readH':
            value = next(fields)
            reads.append(value)
            H = ('add', H, value)
        elif token == 'readDCons':
            value = next(fields)
            reads.append(value)
            D = ('add', D, value)
            top = implication(top, D)
        else:
            raise ValueError('unexpected body token: ' + token)
    require(reads == [y, x], 'argument read order')
    require(word[-3:] == ['copyGuard', 'compareGuard', 'close'], 'guard/cleanup suffix')
    rho = implication(implication(implication(H, d), D),
                      implication(implication(D, H), implication(a, H)))
    heads = [implication(exists(D, universal(D, H)), H),
             implication(universal(D, universal(a, H)), universal(a, universal(D, H))),
             implication(member(H, D), implication(equality(H, a), member(a, D))),
             implication(equality(H, D), implication(member(a, H), member(a, D))),
             exists(D, equality(H, D)),
             implication(universal(D, a), implication(universal(D, implication(a, H)),
                                                     universal(D, H)))]
    gamma = implication(D, universal(D, D))
    point = implication(a, member(a, D))
    V = implication(member(H, D), universal(a, member(H, D)))
    S = universal(D, conj(implication(member(H, D), point),
                         implication(member(a, D), a)))
    Q = universal(a, implication(S, negative(point)))
    require(stack == [t, universal(d, h), rho] + heads + [gamma], 'complete emitter stack')
    require(top == negative(implication(V, Q)), 'complete emitter top')
    return {'tokens': 190, 'inherited_separate_head_calculus': True,
            'pushed_items': 10, 'complete_stack_identity': True, 'complete_top_identity': True,
            'guard_and_proved_zero_return_suffix': True, 'all_parameters_symbolic': True}


# A second term language evaluates the exact command words. An atom represents
# an arbitrary natural, including zero and one. The 'i', 'u', and 'gate' tags
# carry arithmetic constructor properties, not assumptions about their truth.
Z = 0
ONE = 1


def atom(name):
    return ('atom', name)


def pair(a, b):
    return Z if a == Z and b == Z else ('pair', a, b)


def I(a, b):
    return Z if a == Z and b == Z else ('i', a, b)


def U(a, b):
    return ('u', a, b)


def add(a, b):
    if a == Z:
        return b
    if b == Z:
        return a
    if isinstance(a, int) and isinstance(b, int):
        return a + b
    return ('add', a, b)


def projections(w):
    if w == Z:
        return Z, Z
    if isinstance(w, tuple) and w[0] == 'pair':
        return w[1:]
    return ('hd', w), ('tl', w)


def residue(a):
    if isinstance(a, int):
        return a % 4
    return {'i': 0, 'u': 2, 'gate': 0}.get(a[0])


def positive(a):
    if isinstance(a, int):
        return a > 0
    if a[0] in ('u', 'positive'):
        return True
    if a[0] == 'i':
        return positive(a[1]) or positive(a[2])
    return False


def definitely_distinct(a, b):
    ra, rb = residue(a), residue(b)
    if ra is not None and rb is not None and ra != rb:
        return True
    return (a == Z and positive(b)) or (b == Z and positive(a))


def safe_sum(t, h, nonone=frozenset()):
    if isinstance(t, tuple) and t[0] == 'u':
        return True  # U >= 2
    if isinstance(h, tuple) and h[0] == 'u':
        return True
    rt, rh = residue(t), residue(h)
    if rt is not None and rh is not None and (rt + rh) % 4 != 1:
        return True
    return (t == Z and h in nonone) or (h == Z and t in nonone)


def source_heads(D, H, A, d, h):
    # Only the first seven heads' implication tag is used in the word proofs.
    # Their complete trees were independently checked by emitter_check above.
    gamma = I(D, U(D, D))
    six = [I(('lhs', j, D, A, H), ('rhs', j, D, A, H)) for j in range(6, 0, -1)]
    rho = I(I(I(H, d), D), I(I(D, H), I(A, H)))
    return [gamma] + six + [rho, U(d, h)]


def AX(c, x=0, y=0):
    return ('AX', c, x, y)


def MP(x):
    return ('MP', x)


S = ('S',)


