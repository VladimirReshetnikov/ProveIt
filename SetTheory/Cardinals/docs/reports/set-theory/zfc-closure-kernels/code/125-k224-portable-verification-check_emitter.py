#!/usr/bin/env python3
"""Check the exact symbolic arithmetic expression emitted by the changed AX suffix.

Nodes are arithmetic code constructors: I(x,y)=4*P(x,y), R(i,j)=4*P(i,j)+1,
Q(i,x)=4*P(i,x)+2, E(i,j)=4*P(i,j)+3. Leaves a,b,c denote independent naturals.
Structural equality of these expression trees entails equality of the computed
natural codes for all inputs. The constructor macro contracts are connected to
the literal optimized source separately by construct_rel225.py's certificates.
"""
from pathlib import Path
from functools import cache
import argparse
import hashlib
import json
import re


def I(a, b): return 'I', a, b

def R(a, b): return 'R', a, b

def Q(a, b): return 'Q', a, b

def E(a, b): return 'E', a, b

def N(a): return I(a, 1)

def A(a, b): return N(I(a, N(b)))

def X(a, b): return N(Q(a, N(b)))

def XA(a, b, c): return N(Q(a, I(b, N(c))))


def formulas():
    a, b, c = 'a', 'b', 'c'
    subset = Q(c, I(R(c, a), R(c, b)))
    request = Q(b, I(c, X(b, A(c, R(b, c)))))
    support = X(a, A(c, Q(a, I(subset, request))))
    core = X(c, A(I(c, R(b, c)), Q(b, I(R(b, c), support))))
    rv = I(R(a, b), Q(c, R(a, b)))
    ev = I(E(a, b), Q(c, E(a, b)))
    original = A(core, A(rv, ev))
    request_f = Q(b, I(c, XA(b, c, R(b, c))))
    support_f = XA(a, c, Q(a, I(subset, request_f)))
    core_f = XA(c, I(c, R(b, c)), Q(b, I(R(b, c), support_f)))
    ev_kappa = I(E(a, b), Q(R(a, b), E(a, b)))
    fused = N(I(core_f, I(rv, N(ev))))
    canonical = N(I(core_f, I(rv, N(ev_kappa))))
    return original, fused, canonical


def execute(word):
    top, stack = 'initial_top', ['arbitrary_older_stack']
    for macro in word:
        if macro in (166, 121, 168, 177):
            stack.append(top)
            top = {166: 'a', 121: 'b', 168: 'c', 177: 1}[macro]
        elif macro == 218:
            top = N(top)
        else:
            constructor = {119: I, 181: R, 180: Q, 182: E, 178: A, 183: X}[macro]
            top = constructor(stack.pop(), top)
    assert stack == ['arbitrary_older_stack', 'initial_top']
    return top


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--baseline-root', type=Path,
                        default=Path(__file__).resolve().parents[1] / 'portable')
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    dag_file = args.baseline_root / 'baseline226/vendor/k230-rocq/coq/prog/Dag230.v'
    data = dag_file.read_bytes()
    assert hashlib.sha256(data).hexdigest() == '7f44c6bc6cb2e5a7a30c1267738c8df7bfd8e036987721ac0bb6bdc326e54eaf'
    nodes = {int(q): (a, b) for q, a, b in re.findall(
        r'\| (\d+) => \((E\w+(?: \d+)?), (E\w+(?: \d+)?)\)', data.decode())}
    macros = {166, 121, 168, 171, 177, 119, 181, 182, 180, 218,
              178, 183, 176, 158, 208, 192, 131, 211, 197}
    @cache
    def expand(q):
        if q in macros:
            return (q,)
        result = ()
        for edge in nodes[q]:
            kind, number = edge.split()
            assert kind == 'ENode'
            result += expand(int(number))
        return result
    ax = list(expand(236))
    assert len(ax) == 154
    original_word = ax[88:149]
    assert original_word[0:2] == [168, 168]
    assert original_word[-2:] == [178, 178]
    original, fused, canonical = formulas()
    assert execute(original_word) == original

    def transform(canonical_binder):
        word = []
        index = 88
        pairs = 0
        while index < 149:
            if canonical_binder and index == 141:
                assert ax[index] == 168
                word.extend((166, 121, 181))
                index += 1
            elif ax[index:index + 2] == [178, 183]:
                word.extend((218, 119, 180, 218))
                index += 2
                pairs += 1
            elif index == 147:
                assert ax[index:index + 2] == [178, 178]
                word.extend((218, 119, 119, 218))
                index += 2
            else:
                word.append(ax[index])
                index += 1
        assert pairs == 3
        return word

    fused_word = transform(False)
    canonical_word = transform(True)
    assert execute(fused_word) == fused
    assert execute(canonical_word) == canonical
    result = {
        'status': 'EXACT_SYMBOLIC_ARITHMETIC_EMITTER_PASS',
        'scope': 'All natural a,b,c and arbitrary previous top and stack; scratch registers initially zero. '
                 'This certificate checks emitted arithmetic syntax, not the logical equiconsistency theorem.',
        'primitive_codes': {'I': '4*P(x,y)', 'R': '4*P(x,y)+1',
                            'Q': '4*P(x,y)+2', 'E': '4*P(x,y)+3', 'false': 1},
        'original_word': original_word, 'fused_word': fused_word,
        'canonical_word': canonical_word,
        'original_expression': original, 'fused_expression': fused,
        'canonical_expression': canonical,
        'unchanged_outside_suffix': {'initial_AX_macro_count': 88, 'tail_macro_count': 5},
        'gate': 'if c=a or c=b then 0 else canonical_expression',
        'new_equality_helper': 'I(E(a,b),Q(R(a,b),E(a,b)))',
        'fresh_binder_arithmetic': 'R(a,b)=4*P(a,b)+1 > max(a,b), since P(a,b)>=a,b',
        'constructor_contracts': 'Pinned ProgLib230.v with the all-register local source bisimulations '
                                 'recorded by construct_rel225.py',
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: result[k] for k in ('status', 'new_equality_helper', 'gate')}, indent=2))


if __name__ == '__main__':
    main()
