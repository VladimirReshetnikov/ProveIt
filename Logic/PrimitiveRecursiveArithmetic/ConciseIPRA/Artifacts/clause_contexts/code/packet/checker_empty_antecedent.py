"""Goal-directed four-pattern scalar iPRA with recursive formulas.

Input is a JSON array of proof packets followed by its closed goal. Packets
are consumed from right to left. Each packet is [b,t]: nonnegative integer b
uses contextual clause b at t; b=-1 introduces the goal at witness t; a
D formula b opens that proved formula (t must be 0); an
equation b performs Step using b and equation t. Reflexive goals are closed
by the fixed initial clause, without consuming a packet. Terms are integers
or lists of length one (successor) or three (zero-normal iterator); formulas
are [left,right] or ["d",matrix]. Free levels are negative, bound indices positive.

Unconditional contexts use the non-formula sentinel 0 for no antecedent.
All public and intermediate goals, rule arguments, and fresh scopes are
validated. Unconsumed input is rejected. No external helper is trusted.
"""
import json


def require(condition):
    if not condition:
        raise ValueError('Invalid certificate')


def term(a, scope, depth=0):
    if type(a) is int:
        return -scope <= a <= depth
    return (type(a) is list and len(a) in (1, 3)
            and (len(a) == 1 or a[0] != 0)
            and all(term(t, scope, depth + (len(a) == 3 and i == 2))
                    for i, t in enumerate(a)))


def formula(a, scope, depth=0):
    return (type(a) is list and len(a) == 2
            and (formula(a[1], scope, depth + 2) if a[0] == 'd'
                 else all(term(t, scope, depth) for t in a)))


def opening(a, value, depth=0):
    if type(a) is int:
        return value if a == depth + 1 else a - (a > depth + 1)
    if a[0] == 'd':
        return ['d', opening(a[1], value, depth + 2)]
    b = [opening(t, value, depth + (len(a) == 3 and i == 2))
         for i, t in enumerate(a)]
    return b[1] if len(a) == 3 and b[0] == 0 else b


def check(goal, context=()):
    scope = len(context)
    require(formula(goal, scope))
    if goal[0] == goal[1]:
        return
    major, data = packets.pop()
    fresh = -scope - 1
    if type(major) is int:
        if major >= 0:
            require(major < len(context) and term(data, scope))
            antecedent, body = context[major]
            require(goal == opening(body, data))
            if antecedent:
                check(antecedent, context)
        else:
            require(major == -1 and goal[0] == 'd' and term(data, scope))
            body = opening(goal[1], data, 1)
            eta = fresh if goal[1][0] != 'd' and data == 0 else 0
            check(opening(body, [fresh]), context + ((0, opening(body, eta)),))
    else:
        check(major, context)
        s, t = major
        if s == 'd':
            require(data == 0 and type(data) is int)
            body = opening(t, fresh, 1)
            check(goal, context + ((opening(body, 0), body),))
        else:
            check(data, context)
            match data:
                case [[[n], a, h], r]:
                    require(s == (a if n == 0 else [n, a, h])
                            and goal == [r, opening(h, t)])
                    return
            raise ValueError('Invalid step')


if __name__ == '__main__':
    packets = json.load(open(0))
    require(type(packets) is list and bool(packets))
    check(packets.pop())
    require(not packets)
    print('ACCEPT')
