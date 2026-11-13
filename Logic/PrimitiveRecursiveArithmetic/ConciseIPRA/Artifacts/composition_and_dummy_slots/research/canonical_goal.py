"""Exact closed Eq/D encoder image, uniform-zero-1 sorted-arity codec.

Unlike the small parity validator, this rejects references to padding slots.
This is a grammar validator only, not a proof checker.
"""


def term(a, available=()):
    if type(a) is int:
        return a == 1 or (a >= 3 and a % 2 == 1
                         and (a - 3) // 2 < len(available)
                         and available[(a - 3) // 2])
    if type(a) is not list:
        return False
    if len(a) == 1:
        return term(a[0], (False, False) + available)
    if len(a) == 3:
        return (term(a[0], (False,) + available)
                and term(a[1], (False,) + available)
                and term(a[2], (True,) + available))
    return False


def formula(a, available=()):
    if type(a) is not list:
        return False
    if len(a) == 1:
        return formula(a[0], (True, True) + available)
    if len(a) == 2:
        return term(a[0], available) and term(a[1], available)
    return False


if __name__ == '__main__':
    import json
    import sys
    try:
        goal = json.load(sys.stdin)
        valid = formula(goal)
    except (ValueError, RecursionError):
        valid = False
    print('CANONICAL' if valid else 'INVALID')
    sys.exit(0 if valid else 1)
