#!/usr/bin/env python3
"""Symbolic command-word checks for the AX11 + cache-test + no-push protocol.

Standalone: imports no machine builder, source resolver, or existing checker.
The term algebra uses only total Cantor projections, p(0,0)=0, constructor
residues modulo five, and I(0,z)>0 for positive z. Universal branch conditions
are explicit; arbitrary atoms are never assumed unequal to one silently.
Physical source-to-command binding remains a separate obligation.
"""
from dataclasses import dataclass
from functools import reduce
from pathlib import Path
import argparse
import json


def check(condition, message):
    if not condition:
        raise AssertionError(message)


def v(name):
    return ("var", name)


def p(left, right):
    return 0 if left == right == 0 else ("pair", left, right)


def stack(items, tail):
    return reduce(lambda rest, item: p(item, rest), reversed(items), tail)


def unpair(value):
    if value == 0:
        return 0, 0
    if value[0] == "pair":
        return value[1], value[2]
    return ("hd", value), ("tl", value)


def imp(left, right):
    return 0 if left == right == 0 else ("imp", left, right)


def all_(label, body):
    return ("all", label, body)


def add(left, right):
    if left == 0:
        return right
    if right == 0:
        return left
    if isinstance(left, int) and isinstance(right, int):
        return left + right
    return ("add", left, right)


def residue(value):
    if isinstance(value, int):
        return value % 5
    return {"imp": 0, "all": 2, "gate": 0}.get(value[0])


def positive(value):
    if isinstance(value, int):
        return value > 0
    if value[0] in ("positive", "all"):
        return True
    if value[0] == "imp":
        return positive(value[1]) or positive(value[2])
    return False


def is_one(value, nonones):
    if value == 1:
        return True
    if value in nonones:
        return False
    r = residue(value)
    if r is not None and r != 1:
        return False
    if isinstance(value, int):
        return False
    raise AssertionError(("unresolved cache test", value))


def unequal(left, right):
    lr, rr = residue(left), residue(right)
    if lr is not None and rr is not None and lr != rr:
        return True
    return (left == 0 and positive(right)) or (right == 0 and positive(left))


def emitted(D, H, A, old_d, old_h):
    # The physical emitter checker supplies the exact six formula trees. The
    # compiler uses only their order, parameter coverage, and residue zero.
    ordinary = [imp(("head-left", j, D, A, H), ("head-right", j, D, A, H))
                for j in range(6, 0, -1)]
    rho = imp(imp(imp(H, old_d), D), imp(imp(D, H), imp(A, H)))
    return [("gate", H, D, A), imp(A, all_(A, A))] + ordinary + [rho, all_(old_d, old_h)]


S = ("shift",)


def AX(c, x=0, y=0, z=0):
    return ("ax", c, x, y, z)


def MP(x):
    return ("mp", x)


def run(commands, initial, nonones=frozenset()):
    top, rest, offset, cache = initial
    for command in commands:
        if command == S:
            if is_one(cache, nonones):
                return None
            head, tail = unpair(rest)
            top, rest, cache = cache, tail, head
        elif command[0] == "ax":
            _, c, x, y, z = command
            heads = emitted(add(offset, x), add(cache, y), c, offset, cache)
            rest = stack(heads + [top], rest)
            # Full MP is entered after a push, with top=offset=cache=0.
            # z=0: matched conclusion zero. z>0: mismatch, top zero.
            # Both cases return top=cache=0, offset=z, same stack.
            top, offset, cache = 0, z, 0
        elif command[0] == "mp":
            target = add(offset, command[1])
            major = imp(top, target)
            if target == 0:
                top = 0  # Both comparison branches agree.
            elif major == cache:
                top = target
            else:
                check(unequal(major, cache), ("unresolved MP", major, cache))
                top = 0
            offset, cache = target, 0
        else:
            raise AssertionError(command)
    return top, rest, offset, cache


PUSH = [AX(0)] + [S] * 10 + [MP(0)]
POP = [AX(0)] + [S] * 12
DISCARD = [MP(0)]


def verify():
    top, rest, offset, cache, a, b, D, H, A, z = map(
        v, ("top", "rest", "offset", "cache", "a", "b", "D", "H", "A", "z"))
    count = 0

    def equal(actual, expected, message):
        nonlocal count
        check(actual == expected, (message, actual, expected))
        count += 1

    # Independently check the post-push MP used in the AX command equation.
    equal(run([MP(0)], (0, rest, 0, 0)), (0, rest, 0, 0), "post-push zero field")
    positive_z = ("positive", "z")
    equal(run([MP(positive_z)], (0, rest, 0, 0)), (0, rest, positive_z, 0), "post-push positive field")
    equal(run([AX(A, D, H, z)], (top, rest, offset, cache)),
          (0, stack(emitted(add(offset, D), add(cache, H), A, offset, cache) + [top], rest), z, 0),
          "all-store four-field AX")
    equal(run([AX(A)] + [S] * 10, (top, rest, offset, cache)),
          (emitted(offset, cache, A, offset, cache)[8], p(top, rest), 0, all_(offset, cache)),
          "AX plus ten Shifts")
    equal(run([AX(A)] + [S] * 11, (top, rest, offset, cache)),
          (all_(offset, cache), rest, 0, top), "AX plus eleven Shifts")
    equal(run(PUSH, (top, rest, offset, cache)), (0, p(top, rest), 0, 0), "Push arbitrary store")
    equal(run(PUSH, (1, rest, offset, cache)), (0, p(1, rest), 0, 0), "Push one safely")
    equal(run(PUSH, (0, 0, offset, cache)), (0, 0, 0, 0), "Push zero alias")
    equal(run(POP, (top, p(a, rest), offset, cache), frozenset({top})), (top, rest, 0, a), "Pop non-one top")
    equal(run(POP, (1, p(a, rest), offset, cache)), None, "Pop one halts")
    equal(run(POP, (top, 0, offset, cache), frozenset({top})), (top, 0, 0, 0), "Pop empty stack")
    equal(run(DISCARD, (top, rest, 0, cache)), (0, rest, 0, 0), "Discard arbitrary cache")
    for j in range(9):
        selector = DISCARD + [AX(A, D, H)] + [S] * (j + 2) + POP * (9 - j)
        equal(run(selector, (top, rest, 0, 0)), (emitted(D, H, A, 0, 0)[j], rest, 0, 0), "selector " + str(j))
    for i in (0, ("positive", "i")):
        equal(run([MP(i)], (0, rest, 0, 0)), (0, rest, i, 0), "offset")
        gen = PUSH + [MP(i), S, AX(i)] + [S] * 11
        equal(run(gen, (a, rest, 0, 0)), (all_(i, a), rest, 0, 0), "generalization arbitrary premise")
        equal(run(gen, (1, rest, 0, 0)), (all_(i, 1), rest, 0, 0), "generalization premise one")
        x = v("x")
        actual_D = add(i, x)
        rho_selector = DISCARD + [MP(i), AX(A, x, H)] + [S] * 10 + POP
        expected_rho = imp(imp(imp(H, i), actual_D), imp(imp(actual_D, H), imp(A, H)))
        equal(run(rho_selector, (top, rest, 0, 0)), (expected_rho, rest, 0, 0), "restricted rho selector")
    suffix = [S, S, MP(b)] + POP
    equal(run(suffix, (0, stack([a, imp(a, b), 0], rest), 0, 0), frozenset({a, b})),
          (b, rest, 0, 0), "MP suffix non-one premises/conclusion")
    equal(run(suffix, (0, stack([1, imp(1, b), 0], rest), 0, 0)), None, "MP suffix antecedent one")
    equal(run([S, S, MP(1)] + POP, (0, stack([a, imp(a, 1), 0], rest), 0, 0), frozenset({a})),
          None, "MP suffix conclusion one")
    equal(run([S, S, MP(0)] + POP, (0, 0, 0, 0)), (0, 0, 0, 0), "MP full zero alias")
    equal(run(DISCARD + PUSH, (top, rest, 0, 0)), (0, p(0, rest), 0, 0), "reserve dummy zero")
    equal(run([S], (1, rest, 0, 0)), (0, ("tl", rest), 0, ("hd", rest)), "plain Shift does not test top")
    equal(run([S], (1, rest, 0, 1)), None, "cache guard halts at top and cache one")
    # The parser needs four fields, in source order y,x,z after c+2.
    x, y, tail = v("x"), v("y"), v("tail")
    def seed(c, x, y, z, tail):
        return p(("plus2", c), p(y, p(x, p(z, tail))))
    def parse(value):
        tag, value = unpair(value)
        yy, value = unpair(value)
        xx, value = unpair(value)
        zz, tail = unpair(value)
        return tag[1], xx, yy, zz, tail
    equal(parse(seed(A, x, y, z, tail)), (A, x, y, z, tail), "four-field inverse")
    equal(parse(seed(A, 0, 0, 0, 0)), (A, 0, 0, 0, 0), "zero-field inverse")
    equal(parse(p(("plus2", A), p(y, p(x, tail)))),
          (A, x, y, ("hd", tail), ("tl", tail)), "old three-field code is not valid")
    return {
        "status": "PASS", "symbolic_identities": count,
        "coefficient": 5, "AX_pushed_entries": 11, "AX_arity": 4,
        "AX_field_order": ["y", "x", "z"], "Shift_halt_test": "h=1",
        "MP_success": "(b,w,b,0)", "MP_failure": "(0,w,b,0)",
        "Push": "A(0,0,0,0);S^10;MP(0)",
        "Pop": "A(0,0,0,0);S^12; halts iff incoming t=1",
        "selector_j": "MP(0);A(A,D,H,0);S^(j+2);Pop^(9-j), j=0..8",
        "Gen_i": "Push;MP(i);S;A(i,0,0,0);S^11",
        "MP_suffix": "S;S;MP(b);Pop; halt iff a=1 or b=1",
        "refutation_word": "A(0,0,0,0);W_p;Pop",
        "scope": "Universal symbolic command identities, with explicit branch assumptions. Physical binding and inherited PA calibration are separate."
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = verify()
    output = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.write_text(output)
    print(output)
