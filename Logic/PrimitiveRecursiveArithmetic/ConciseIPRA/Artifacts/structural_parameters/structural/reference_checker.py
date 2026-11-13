"""Readable structural-parameter checker, with a checked public interface.

Input is one JSON value per line: a closed canonical public goal, then triples.
Unconsumed suffix lines are permitted, as in the comparison stream protocol.
This file is not the compact size claim. It validates the public grammar and
exact integer/list packet data explicitly. No assertions enforce validity.
"""
import json
import sys


class Rejected(Exception):
    pass


MISSING = object()


def raw_tree(a):
    return type(a) is int or type(a) is list and all(map(raw_tree, a))


def read_tree():
    a = json.loads(input())
    if not raw_tree(a):
        raise Rejected("input must contain only exact integers and arrays")
    return a


def term(a, slots):
    if type(a) is int:
        if a == 0:
            return True
        j = (a - 3) // 2
        return a >= 3 and a % 2 == 1 and j < len(slots) and slots[j]
    if type(a) is not list:
        return False
    if len(a) == 1:
        return term(a[0], [False, False] + slots)
    if len(a) == 3:
        n, initial, body = a
        return (term(n, [False] + slots)
                and term(initial, [False] + slots)
                and term(body, [True] + slots))
    return False


def public_goal(a, slots=None):
    if slots is None:
        slots = []
    if type(a) is not list:
        return False
    if len(a) == 2:
        return all(term(t, slots) for t in a)
    if len(a) != 1:
        return False
    body = a[0]
    if not public_goal(body, [True, True] + slots):
        return False
    if len(body) != 2:
        return True
    # In the counter child there is one dummy slot, so the newly bound
    # index y has coordinate 5, while 0 is the canonical initializer.
    return all(type(t) is list and len(t) == 3 and t[:2] == [5, 0]
               for t in body)


def opening(a, image=MISSING, depth=0):
    if type(a) is list:
        if len(a) >= 4:
            return a
        return [opening(b, image, depth + 5 - len(a)) for b in a]
    if type(a) not in (int, bool):
        raise Rejected("missing substitution image")
    if a < depth:
        return a
    if depth % 2 == 0:
        return 0
    return opening(image, depth=3)


def check(context, goal):
    packet = read_tree()
    if type(packet) is not list or len(packet) != 3:
        raise Rejected("a packet must have exactly three fields")
    source, target, template = packet
    computation = [[source and [source], target, template],
                   opening(template, packet, 3) if source else target]
    if opening(goal) in [*context, computation]:
        return

    # A fresh finite tree: every context entry, the goal, and each old
    # packet field is a proper subtree of this new opaque parameter token.
    name = packet + [context, goal]
    if opening(template, target) == goal:
        goal = opening(template, source)
        source = packet[:2] if source else [template] * 3

    hypothesis = source * 3
    if not hypothesis:
        if type(goal) is not list or len(goal) != 1:
            raise Rejected("introduction requires a unary goal")
        goal = opening(goal[0], template, 2)
        hypothesis = goal

    # The major is checked before its hypothesis is used. No shared
    # context or parameter token is changed by recursive checking.
    check(context, source)
    image = name if source or len(goal) == 2 else 0
    new_hypothesis = opening(hypothesis, image)
    new_goal = opening(goal, [name])
    check([*context, new_hypothesis], new_goal)


def main():
    goal = read_tree()
    if not public_goal(goal):
        raise Rejected("goal is outside the closed canonical guarded language")
    check([0], goal)
    print("ACCEPT")


if __name__ == "__main__":
    try:
        main()
    except (Rejected, ValueError, TypeError, EOFError, RecursionError, IndexError):
        print("REJECT", file=sys.stderr)
        sys.exit(1)
