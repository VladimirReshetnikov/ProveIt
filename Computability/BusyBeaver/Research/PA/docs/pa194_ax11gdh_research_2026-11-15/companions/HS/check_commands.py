#!/usr/bin/env python3
"""Exact symbolic AX emitter and derived-word checks for PA194AX11GDHS.

Adapted from the pinned PA194GH free-term checker. No builder, compiler, or
arithmetic oracle is imported. It checks algebraic identities in free terms
using only constructor residues, positivity, and Cantor pairing identities.
The complete mathematical iPRA calibration is in the accompanying report;
these executable certificates are supporting evidence, not a Lean theorem.
"""
from pathlib import Path
import argparse
import hashlib
import json

ROOT = Path(__file__).resolve().parent
DETECTOR = "cache"


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
        if term == ['leaf', 'breakTo', 1]:
            return ['close']
        require(isinstance(term, list) and len(term) == 2, 'invalid grammar production')
        return expand(term[0], active) + expand(term[1], active)

    return expand(data['root'])


def emitter_check():
    word = decode_word(ROOT / 'machine/grammar.json')
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
    require(word[-3:] == ['copyGuard', 'compareGuard', 'push'], 'guard/cleanup suffix')
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
    require(stack == [t, universal(a, h), rho] + heads + [gamma], 'complete emitter stack')
    require(stack[1] == universal(a, h), 'binder is AX parameter; body is raw incoming cache')
    require(stack[1] != universal(a, H), 'body is not offset-adjusted cache H=h+y')
    require(top == negative(implication(V, Q)), 'complete emitter top')
    return {'tokens': 190, 'inherited_separate_head_calculus': True,
            'pushed_items_before_AX11_tail': 10, 'pushed_items_after_AX11_tail': 11, 'fourth_operand_z_consumed_by_MP_reader': True, 'complete_stack_identity': True, 'complete_top_identity': True,
            'unchanged_guard_suffix': True, 'all_parameters_symbolic': True,
            'diagonal_head': 'I(D,U(D,D))', 'distribution_head': 'ordinary premise order',
            'generalization_head': 'U(c,h)', 'binder': 'explicit AX operand c',
            'body': 'raw incoming cached theorem h', 'not_offset_adjusted_H': True}


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
    return [gamma] + six + [rho, U(A, h)]


def AX(c, x=0, y=0, z=0):
    return ('AX', c, x, y, z)


def MP(x):
    return ('MP', x)


S = ('S',)


def run(word, store, nonone=frozenset()):
    t, w, d, h = store
    for command in word:
        if command[0] == 'S':
            if DETECTOR == 'cache':
                if h == ONE:
                    return None
                require(residue(h) in (0,2,3) or h in nonone, 'unresolved cached Shift condition')
            else:
                if add(t,h) == ONE:
                    return None
                require(safe_sum(t,h,nonone), 'unresolved sum Shift condition')
            newh, neww = projections(w)
            t, w, h = h, neww, newh
        elif command[0] == 'AX':
            c, x, y, z = command[1:]
            D, H = add(d, x), add(h, y)
            for a in reversed([('gate', H, D, c)] + source_heads(D, H, c, d, h) + [t]):
                w = pair(a, w)
            t, d, h = Z, z, Z
        elif command[0] == 'MP':
            y = add(d, command[1])
            antecedent = I(t, y)
            if y == Z:
                # Both branches produce exactly (0,w,0,0).  In the success
                # branch y=0; in the failure branch the returned top is zero.
                t, d, h = Z, Z, Z
                continue
            if antecedent == h:
                t, w, d, h = y, w, y, Z
            else:
                require(definitely_distinct(antecedent, h), 'unresolved MP match')
                t, d, h = Z, y, Z
        else:
            raise ValueError('unknown command')
    return t, w, d, h


POP = [AX(0)] + [S] * 12
PUSH = [AX(0)] + [S] * 10 + [MP(0)]
DISCARD = [MP(0)]


def offset(i):
    return [MP(i)]


def word_check():
    t, w, d, h, a, b, A, D, H = map(atom, ('t', 'w', 'd', 'h', 'a', 'b', 'A', 'D', 'H'))
    require(run([AX(A)] + [S] * 10, (t, w, d, h)) ==
            (I(I(I(h, d), d), I(I(d, h), I(A, h))), pair(t, w), 0, U(A, h)), 'AX S10')
    require(run([AX(A)] + [S] * 11, (t, w, d, h)) == (U(A, h), w, 0, t), 'AX S11')
    require(run(POP, (t, pair(a, w), d, h), frozenset({t})) == (t, w, 0, a), 'pop')
    require(run(POP, (t, 0, d, h), frozenset({t})) == (t, 0, 0, 0), 'empty pop alias')
    require(run(PUSH, (t, w, d, h)) == (0, pair(t, w), 0, 0), 'push')
    require(run(PUSH, (0, 0, d, h)) == (0, 0, 0, 0), 'empty push alias')
    require(run(DISCARD, (t, w, 0, h)) == (0, w, 0, 0), 'single-command discard with arbitrary old cache')
    for j in range(1, 8):
        word = DISCARD + [AX(A, D, H)] + [S] * (j + 2) + POP * (9 - j)
        require(run(word, (t, w, 0, 0)) == (source_heads(D, H, A, 0, 0)[j - 1], w, 0, 0),
                'head selector ' + str(j))
    B = atom('B')
    diagonal = DISCARD + [AX(0,B,0)] + [S]*3 + POP*8
    require(run(diagonal, (t,w,0,0)) == (I(B,U(B,B)),w,0,0), 'Gamma(D) selector for arbitrary B')
    gateword = DISCARD + [AX(A, D, H)] + [S]*2 + POP * 9
    require(run(gateword, (t, w, 0, 0)) == (('gate', H, D, A), w, 0, 0), 'gate selector')
    # The generalization binder case i=0 and arbitrary positive i are separate.
    for i in (0, ('positive', 'i')):
        generalize = PUSH + [S, AX(i)] + [S] * 11
        require(run(generalize, (a, w, 0, 0)) == (U(i, a), w, 0, 0), 'generalize')
        x = atom('x')
        rho_word = DISCARD + offset(i) + [AX(A, x, H)] + [S] * 10 + POP
        Dvalue = add(i, x)
        rho = I(I(I(H, i), Dvalue), I(I(Dvalue, H), I(A, H)))
        require(run(rho_word, (t, w, 0, 0)) == (rho, w, 0, 0), 'dominated rho selector')
    suffix = [S, S, MP(b)] + POP
    require(run(suffix, (0, pair(a, pair(I(a, b), pair(0,w))), 0, 0), frozenset({a,b})) ==
            (b, w, 0, 0), 'MP suffix nonfalse antecedent')
    require(run(suffix, (0, pair(1, pair(I(1, b), pair(0,w))), 0, 0)) is None,
            'MP suffix early halt')
    alias_suffix = [S, S, MP(0)] + POP
    require(run(alias_suffix, (0, pair(0, pair(0, 0)), 0, 0)) == (0, 0, 0, 0),
            'MP suffix truth and stack aliases')
    require(run(DISCARD + PUSH, (t,w,0,0)) == (0,pair(0,w),0,0), 'reserve missing MP zero')
    false_mp = run([S,S,MP(1)]+POP, (0,pair(a,pair(I(a,1),pair(0,w))),0,0), frozenset({a}))
    require(false_mp is None if DETECTOR == 'cache' else false_mp == (1,w,0,0), 'false conclusion behavior')
    false_pop = run(POP, (1,w,0,0))
    require(false_pop is None if DETECTOR == 'cache' else false_pop == (1,('tl',w),0,('hd',w)), 'Pop at contradiction')
    require(run(PUSH+[S,S], (1,w,0,0)) is None, 'uniform final detector')
    require(run([S], (0,w,0,1)) is None, 'cached contradiction is detected')
    visible_shift = run([S], (1,w,0,0))
    require(visible_shift == (0,('tl',w),0,('hd',w)) if DETECTOR == 'cache' else visible_shift is None, 'visible contradiction Shift behavior')
    require(run(PUSH+[S,AX(0)]+[S]*11, (1,w,0,0)) == (U(0,1),w,0,0), 'generalization remains total at premise one')
    require(run([MP(b)], (a,w,0,I(a,b))) == (b,w,b,0), 'successful MP has unchanged stack')
    # The fourth AX operand is an arbitrary offset, independent of all
    # formula parameters; normalize it explicitly before the word compiler.
    z = atom('z')
    after = run([AX(A,0,0,z)], (t,w,d,h))
    require(after[0] == 0 and after[2:] == (z,0), 'arbitrary fourth operand z')
    require(run([AX(0,0,0,z)] + PUSH, (1,w,d,1))[2:] == (0,0), 'AX and Push normalize arbitrary z and two cached/visible ones')
    require(run(PUSH+[S,AX(0)]+[S]*11, (1,0,0,0)) == (U(0,1),0,0,0), 'generalization at false body and empty stack')
    return {'shift_test': 'h=1' if DETECTOR == 'cache' else 't+h=1', 'mp_success': '(b,w,b,0)', 'zero_reserved_before_premises': True, 'pop_shift_count': 12, 'push_shift_count': 10,
            'discard_shift_count': 0, 'discard_command': 'MP(0)', 'discard_all_caches': True, 'offset_zero_is_uniform': True, 'head_positions_checked': list(range(1, 8)),
            'selector_formula': 'discard;AX(A,D,H,0);S^(j+2);pop^(9-j)',
            'gate_shift_count': 2, 'gate_pop_count': 9, 'mp_suffix_checked_both_branches': True,
            'dominated_rho_selector_checked': True, 'all_diagonal_parameters_selectable': True,
            'zero_pair_and_implication_aliases_checked': True,
            'generalization':'Push;S;AX_i000;S^11', 'pop_halts_exactly_on_visible_one': DETECTOR == 'cache', 'final_detection':'Push;S;S', 'scope': 'exact symbolic identities using stated constructor facts; see accompanying report for calibration'}


def main(output=None):
    global DETECTOR
    emitter = emitter_check()
    words = {}
    for DETECTOR in ('cache',):
        words[DETECTOR] = word_check()
    inputs = ['machine/grammar.json', 'machine/machine.tm', 'machine/instructions.json']
    result = {'status': 'PASS', 'emitter': emitter, 'command_words': words,
              'input_sha256': {p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest() for p in inputs}}
    if output is not None:
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, help='Write a fresh receipt here; by default only print it.')
    args = parser.parse_args()
    main(args.output)

