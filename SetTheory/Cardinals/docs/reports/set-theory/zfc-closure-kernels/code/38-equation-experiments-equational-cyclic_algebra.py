#!/usr/bin/env python3
"""Seven-equation algebraic frontend: terms, witnesses, and cyclic translation.

This is an executable research kernel, NOT a compiled small Turing machine and
NOT an instantiated Con(ZFC) payload. See cyclic_proposal.md for the proofs and
the precise missing payload/compiler work. Uses only the Python standard library.

Terms are tuples: ('n', a, b), ('q', a), ('r', a), or constant 'c'. Patterns may
also contain variables 'x', 'y', 'z'. Every natural number decodes to a ground
term. A certificate supplies each local rewrite, its substitution, and context;
the checker never computes unifiers or reasons about free object variables.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from itertools import count
from math import isqrt
from pathlib import Path
from typing import Any, Iterator


Term = Any


def n(a: Term, b: Term) -> Term:
    return ('n', a, b)


def q(a: Term) -> Term:
    return ('q', a)


def r(a: Term) -> Term:
    return ('r', a)


def neg(a: Term) -> Term:
    return n(a, a)


def join(a: Term, b: Term) -> Term:
    return n(neg(a), neg(b))


def one(a: Term = 'c') -> Term:
    return n(a, n(a, a))


x, y, z = 'x', 'y', 'z'
BASIS = (
    ('Sh1', n(n(x, n(n(y, x), x)), n(y, n(z, x))), y),
    ('Rhom', r(n(x, y)), n(r(x), r(y))),
    ('R3', r(r(r(x))), x),
    ('Qext', join(x, q(x)), q(x)),
    ('Qadd', q(join(x, y)), join(q(x), q(y))),
    ('Qcomp', q(neg(q(x))), neg(q(x))),
    ('Qrot', q(r(q(r(r(x))))), r(q(r(r(q(x)))))),
)


def node_count(t: Term) -> int:
    return 1 if isinstance(t, str) else 1 + sum(node_count(a) for a in t[1:])


def basis_manifest() -> dict:
    rows = [{'name': name, 'left': lhs, 'right': rhs,
             'symbols_including_equality': node_count(lhs) + node_count(rhs) + 1}
            for name, lhs, rhs in BASIS]
    return {'signature': {'c': 0, 'n': 2, 'q': 1, 'r': 1},
            'pattern_variables': ['x', 'y', 'z'], 'equations': rows,
            'equations_total': len(rows),
            'symbols_total': sum(row['symbols_including_equality'] for row in rows),
            'status': 'Explicit kernel; Con(ZFC) target and TM compilation absent.'}


def freeze(t: Any) -> Term:
    """Validate and copy a ground term without using the Python call stack.

    JSON lists are converted to tuples. Cyclic Python containers, which are not
    finite terms and cannot arise from JSON, are explicitly rejected as well.
    """
    pending = [('visit', t)]
    values = []
    active = set()
    while pending:
        task = pending.pop()
        if task[0] == 'build':
            _, op, arity, identity = task
            children = values[-arity:]
            del values[-arity:]
            values.append((op, *children))
            active.remove(identity)
            continue
        node = task[1]
        if isinstance(node, str):
            if node != 'c':
                raise ValueError('ground leaf must be c')
            values.append('c')
            continue
        if not isinstance(node, (list, tuple)) or not node:
            raise ValueError('ground term must be c or an n/q/r application')
        op = node[0]
        arity = {'n': 2, 'q': 1, 'r': 1}.get(op) if isinstance(op, str) else None
        if arity is None or len(node) != arity + 1:
            raise ValueError('invalid operation or arity')
        identity = id(node)
        if identity in active:
            raise ValueError('cyclic container is not a finite ground term')
        active.add(identity)
        pending.append(('build', op, arity, identity))
        pending.extend(('visit', child) for child in reversed(node[1:]))
    return values[0]


def term_equal(left: Term, right: Term) -> bool:
    """Structural equality for already validated finite terms, iteratively."""
    pending = [(left, right)]
    while pending:
        a, b = pending.pop()
        if isinstance(a, str) or isinstance(b, str):
            if not (isinstance(a, str) and isinstance(b, str) and a == b):
                return False
            continue
        if a[0] != b[0] or len(a) != len(b):
            return False
        pending.extend(zip(a[1:], b[1:]))
    return True


def pair(a: int, b: int) -> int:
    if type(a) is not int or type(b) is not int or a < 0 or b < 0:
        raise ValueError('Cantor coordinates must be naturals')
    return (a + b) * (a + b + 1) // 2 + b


def unpair(k: int) -> tuple[int, int]:
    if type(k) is not int or k < 0:
        raise ValueError('Cantor code must be a natural')
    s = (isqrt(8 * k + 1) - 1) // 2
    b = k - s * (s + 1) // 2
    return s - b, b


def term_decode(k: int) -> Term:
    if type(k) is not int or k < 0:
        raise ValueError('term code must be a natural')
    pending = [('visit', k)]
    values = []
    while pending:
        task = pending.pop()
        if task[0] == 'build':
            op, arity = task[1:]
            children = values[-arity:]
            del values[-arity:]
            values.append((op, *children))
            continue
        code = task[1]
        if code == 0:
            values.append('c')
            continue
        a, tag = divmod(code - 1, 3)
        if tag < 2:
            pending.append(('build', 'q' if tag == 0 else 'r', 1))
            pending.append(('visit', a))
        else:
            left, right = unpair(a)
            pending.extend((('build', 'n', 2), ('visit', right), ('visit', left)))
    return values[0]


def term_encode(t: Term) -> int:
    t = freeze(t)
    pending = [('visit', t)]
    values = []
    while pending:
        task = pending.pop()
        if task[0] == 'build':
            if task[1] == 'n':
                right, left = values.pop(), values.pop()
                values.append(3 * pair(left, right) + 3)
            else:
                values.append(3 * values.pop() + (1 if task[1] == 'q' else 2))
            continue
        node = task[1]
        if isinstance(node, str):
            values.append(0)
            continue
        pending.append(('build', node[0]))
        pending.extend(('visit', child) for child in reversed(node[1:]))
    return values[0]


def subst(pattern: Term, bindings: dict[str, Term]) -> Term:
    if isinstance(pattern, str):
        return bindings[pattern] if pattern in ('x', 'y', 'z') else pattern
    return (pattern[0], *(subst(a, bindings) for a in pattern[1:]))


def context_apply(k: int, t: Term) -> Term:
    """Total surjection from naturals to all one-hole ground contexts.

    C_0[t]=t. Positive codes cycle through q(C[t]), r(C[t]),
    n(C[t],s), and n(s,C[t]); binary cases use Cantor pairing.
    """
    if type(k) is not int or k < 0:
        raise ValueError('context code must be a natural')
    frames = []
    while k:
        a, tag = divmod(k - 1, 4)
        if tag < 2:
            frames.append((tag, None))
            k = a
        else:
            left, right = unpair(a)
            if tag == 2:
                frames.append((tag, term_decode(right)))
                k = left
            else:
                frames.append((tag, term_decode(left)))
                k = right
    for tag, sibling in reversed(frames):
        if tag == 0:
            t = q(t)
        elif tag == 1:
            t = r(t)
        elif tag == 2:
            t = n(t, sibling)
        else:
            t = n(sibling, t)
    return t


@dataclass(frozen=True)
class Move:
    axiom: int
    reverse: bool
    context: int
    substitutions: tuple[int, int, int]


def move_decode(k: int) -> Move:
    if type(k) is not int or k < 0:
        raise ValueError('move code must be a natural')
    body, tag = divmod(k, 2 * len(BASIS))
    ctx, body = unpair(body)
    a, body = unpair(body)
    b, c = unpair(body)
    return Move(tag // 2, bool(tag % 2), ctx, (a, b, c))


def move_encode(m: Move) -> int:
    if type(m.axiom) is not int or not 0 <= m.axiom < len(BASIS):
        raise ValueError('axiom index outside fixed basis')
    if type(m.reverse) is not bool or len(m.substitutions) != 3:
        raise ValueError('malformed move')
    a, b, c = m.substitutions
    body = pair(m.context, pair(a, pair(b, c)))
    return 2 * len(BASIS) * body + 2 * m.axiom + int(m.reverse)


def move_endpoints(m: Move) -> tuple[Term, Term]:
    # Round-trip validation rejects fabricated or malformed direct Move values.
    move_encode(m)
    _, left, right = BASIS[m.axiom]
    values = {v: term_decode(k) for v, k in zip(('x', 'y', 'z'), m.substitutions)}
    left = context_apply(m.context, subst(left, values))
    right = context_apply(m.context, subst(right, values))
    return (right, left) if m.reverse else (left, right)


def list_encode(items: list[int]) -> int:
    out = 0
    for item in reversed(items):
        out = 1 + pair(item, out)
    return out


def list_decode(k: int) -> Iterator[int]:
    if type(k) is not int or k < 0:
        raise ValueError('list code must be a natural')
    while k:
        item, k = unpair(k - 1)
        yield item


def check(source: Term, target: Term, certificate: list[Move]) -> bool:
    """Check a fully ground finite rewrite chain under the seven fixed equations."""
    current, target = freeze(source), freeze(target)
    try:
        for m in certificate:
            left, right = move_endpoints(m)
            if not term_equal(left, current):
                return False
            current = right
    except (TypeError, ValueError, KeyError, IndexError):
        return False
    return term_equal(current, target)


def check_code(source: Term, target: Term, k: int) -> bool:
    return check(source, target, [move_decode(m) for m in list_decode(k)])


def search(source: Term, target: Term, limit: int | None = None) -> int | None:
    """Dovetail all finite witnesses. Unbounded call halts iff source=target.

    Equality here means derivability in the fixed equational basis, not Python
    syntax equality. The bounded version returns None when its budget expires;
    that is NOT evidence of nonderivability.
    """
    source, target = freeze(source), freeze(target)
    for k in count():
        if limit is not None and k >= limit:
            return None
        if check_code(source, target, k):
            return k


def df_translate(t: Term) -> Term:
    """Translate Df3 terms with n, f0,f1,f2 into n,q,r.

    Input may also use unary '-' and binary '+' as abbreviations. Leaves are
    preserved, so use c for ground expressions. No FOL-to-Df3 translation here.
    """
    if isinstance(t, str):
        return t
    op, *args = t
    if op == 'n' and len(args) == 2:
        return n(*(df_translate(a) for a in args))
    if op == '+' and len(args) == 2:
        return join(*(df_translate(a) for a in args))
    if op == '-' and len(args) == 1:
        return neg(df_translate(args[0]))
    if op in ('f0', 'f1', 'f2') and len(args) == 1:
        u = df_translate(args[0])
        if op == 'f0':
            return q(u)
        if op == 'f1':
            return r(q(r(r(u))))
        return r(r(q(r(u))))
    raise ValueError('invalid Df3 syntax')


def evaluate(t: Term, bindings: dict, operations: dict) -> Any:
    if isinstance(t, str):
        return bindings[t]
    return operations[t[0]](*(evaluate(a, bindings, operations) for a in t[1:]))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='command', required=True)
    sub.add_parser('basis')
    sub.add_parser('demo')
    validate = sub.add_parser('check', help='check certificate JSON')
    validate.add_argument('file', type=Path)
    args = parser.parse_args()
    if args.command == 'basis':
        print(json.dumps(basis_manifest(), indent=2))
    elif args.command == 'demo':
        cert = [Move(2, False, 0, (0, 0, 0))]
        code = list_encode([move_encode(m) for m in cert])
        print(json.dumps({'source': r(r(r('c'))), 'target': 'c',
                          'certificate_code': code,
                          'accepted': check_code(r(r(r('c'))), 'c', code),
                          'tampered_target_accepted': check_code(r(r(r('c'))), q('c'), code),
                          'basis_symbols': basis_manifest()['symbols_total']}, indent=2))
    else:
        payload = json.loads(args.file.read_text())
        result = check_code(payload['source'], payload['target'], payload['certificate_code'])
        print(json.dumps({'accepted': result}))
        raise SystemExit(0 if result else 1)


if __name__ == '__main__':
    main()
