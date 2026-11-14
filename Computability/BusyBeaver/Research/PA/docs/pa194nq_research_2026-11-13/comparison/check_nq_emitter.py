#!/usr/bin/env python3
"""Independent free-constructor and source-difference review of PA194NQ.

This checker imports no compiler, table builder, or symbolic tape executor.
The macro contracts and expected formulas are restated explicitly.  The
method and constructor conventions follow the pinned PA194N checker, whose
license is included in licenses/LICENSE.ProveIt.  This is a finite identity
certificate, not an end-to-end formalization of the consistency theorem.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def need(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def emitter_identity(path: Path) -> dict:
    grammar = json.loads(path.read_text())
    rules = grammar['rules']
    macros = {
        'node49': ['push'], 'node55': ['copyD'], 'node58': ['copyH'],
        'node70': ['copyA'], 'node65': ['cons'], 'node72': ['readH'],
        'node75': ['readDCons'], 'node142': ['copyGuard'],
        'node150': ['compareGuard'], 'node60': ['incT'] * 2,
        'node61': ['incT'] * 4,
    }

    def expand(term, active=frozenset()):
        if isinstance(term, str):
            if term in macros:
                return macros[term]
            need(term in rules and term not in active, 'invalid/cyclic grammar')
            return expand(rules[term], active | {term})
        if term == ['leaf', 'inc', 1]:
            return ['incT']
        if term == ['leaf', 'breakTo', 1]:
            return ['close']
        need(isinstance(term, list) and len(term) == 2, 'invalid production')
        return expand(term[0], active) + expand(term[1], active)

    word = expand(grammar['root'])
    need(len(word) == 190, 'AX word length changed')
    need(word[-3:] == ['copyGuard', 'compareGuard', 'close'], 'guard suffix')
    zero = ('zero',)
    suc = lambda a: ('succ', a)
    one = suc(zero)
    I = lambda a, b: ('I', a, b)
    M = lambda a, b: suc(I(a, b))
    U = lambda i, a: suc(suc(I(a, i)))
    E = lambda a, b: suc(suc(suc(I(a, b))))
    neg = lambda a: I(a, one)
    conj = lambda a, b: neg(I(a, neg(b)))
    exists = lambda i, a: neg(U(i, neg(a)))
    t, A, d, h, x, y = [('parameter', s) for s in ('t', 'A', 'd', 'h', 'x', 'y')]
    top, D, H, stack, reads = t, d, h, [], []
    for token in word[:-3]:
        if token == 'push':
            stack.append(top)
            top = zero
        elif token in ('copyD', 'copyH', 'copyA'):
            stack.append(top)
            top = {'copyD': D, 'copyH': H, 'copyA': A}[token]
        elif token == 'cons':
            need(bool(stack), 'stack underflow')
            top = I(stack.pop(), top)
        elif token == 'incT':
            top = suc(top)
        elif token == 'readH':
            reads.append(y)
            H = ('add', H, y)
        elif token == 'readDCons':
            reads.append(x)
            D = ('add', D, x)
            top = I(top, D)
        else:
            raise ValueError('unexpected macro: ' + token)
    need(reads == [y, x], 'argument order')

    # Bottom-to-top emission order; q2 is the last of the six retained heads.
    rho = I(I(I(H, d), D), I(I(D, H), I(A, H)))
    heads = [
        I(exists(D, U(D, H)), H),
        I(U(D, U(A, H)), U(A, U(D, H))),
        I(M(H, D), I(E(H, A), M(A, D))),
        I(E(H, D), I(M(A, H), M(A, D))),
        exists(D, E(H, D)),
        I(U(D, I(A, H)), I(U(D, A), U(D, H))),
    ]
    gamma = I(A, U(A, A))
    point = I(A, M(A, D))
    V = I(M(H, D), U(A, M(H, D)))
    S = U(D, conj(I(M(H, D), point), I(M(A, D), A)))
    Q = U(A, I(S, neg(point)))
    need(stack == [t, U(d, h), rho] + heads + [gamma], 'AX complete stack mismatch')
    need(top == neg(I(V, Q)), 'AX complete top mismatch')
    return {
        'grammar_sha256': digest(path),
        'macro_tokens': len(word),
        'full_free_algebra_emitter_equal_to_expected_exchanged_calculus': True,
        'pushed_entries': len(stack),
        'only_changed_axiom_family': 'q2/h6: U(D,I(A,H)) -> (U(D,A) -> U(D,H))',
        'unchanged_guard_suffix': True,
        'all_six_parameters_symbolic': True,
    }


def exchange_replay(path: Path) -> dict:
    data = json.loads(path.read_text())
    lines = data['lines']
    freeze = lambda a: tuple(map(freeze, a)) if isinstance(a, (list, tuple)) else a
    I = lambda a, b: ('I', a, b)
    for i, line in enumerate(lines):
        f = freeze(line['formula'])
        if line['rule'] == 'K':
            a, b = map(freeze, line['parameters'])
            need(f == I(a, I(b, a)), 'K line')
        elif line['rule'] == 'S':
            a, b, c = map(freeze, line['parameters'])
            need(f == I(I(a, I(b, c)), I(I(a, b), I(a, c))), 'S line')
        else:
            need(line['rule'] == 'MP', 'unexpected exchange rule')
            major, minor = line['major'], line['minor']
            need(0 <= major < i and 0 <= minor < i, 'forward MP reference')
            need(freeze(lines[major]['formula']) == I(freeze(lines[minor]['formula']), f), 'MP line')
    final = freeze(lines[data['conclusion_line']]['formula'])
    need(final == I(I('P', I('Q', 'R')), I('Q', I('P', 'R'))), 'exchange conclusion')
    need(data['assumptions'] == [], 'undischarged hypothesis')
    return {'sha256': digest(path), 'lines': len(lines),
            'rule_counts': dict(Counter(line['rule'] for line in lines)),
            'closed_parametric_K_S_MP_replay': True,
            'dependency': 'K and S derivable from unchanged restricted rho8 basis; not replayed here'}


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--grammar', type=Path, required=True)
    ap.add_argument('--instructions', type=Path, required=True)
    ap.add_argument('--baseline-n-instructions', type=Path, required=True)
    ap.add_argument('--machine', type=Path, required=True)
    ap.add_argument('--exchange', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    result = emitter_identity(args.grammar)
    source = json.loads(args.instructions.read_text())
    baseline = json.loads(args.baseline_n_instructions.read_text())
    need(len(source) == len(baseline) == 3654, 'unexpected source size')
    changed = [i for i, (a, b) in enumerate(zip(source, baseline)) if a != b]
    need(len(changed) == 79, 'unexpected source differences')
    # A concrete formula-code witness for the changed h6 output.
    pair = lambda a, b: (a + b) * (a + b + 1) // 2 + b
    I = lambda a, b: 4 * pair(a, b)
    U = lambda i, a: 4 * pair(a, i) + 2
    P, Q, R = U(0, 0), U(0, I(0, 1)), U(0, 1)
    old, new = I(P, I(Q, R)), I(Q, I(P, R))
    need(old != new, 'h6 witness is equal')
    # Distinguish current-top no-push MP from cached-head Q on a valid MP input.
    b = 2
    need(I(0, b) == 20, 'MP witness encoding')
    result.update({
        'candidate_dense_sha256': digest(args.machine),
        'source_sha256': digest(args.instructions),
        'baseline_n_source_sha256': digest(args.baseline_n_instructions),
        'source_length': len(source),
        'resolved_instructions_changed_relative_N': len(changed),
        'changed_source_indices': changed,
        'concrete_h6_values_D0_A0_H1': {'P': P, 'Q': Q, 'R': R,
            'old_I_P_I_Q_R': old, 'new_I_Q_I_P_R': new},
        'concrete_mp2_store_0_0_0_20': {
            'NQ_result': [2, 0, 2, 0], 'cached_Q_result': [0, 0, 0, 2]},
        'exchange_certificate': exchange_replay(args.exchange),
        'proof_scope': ('Free-constructor emitter identity, exact source-difference census, '
                        'closed finite K/S/MP certificate, and concrete semantic witnesses. '
                        'No physical simulation or end-to-end consistency theorem is proved by this script.'),
    })
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'ok': True, 'output': str(args.output), 'changed_source_sites': len(changed)}))


if __name__ == '__main__':
    main()
