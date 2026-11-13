"""Untrusted proof transformations between the fused and separate systems."""
import copy


def delta():
    return ['i', [0, 0], 0, ['u', 0, 0, None]]


def rename(a, levels):
    if type(a) is int:
        return levels.get(a, a)
    return [rename(t, levels) for t in a]


def evaluate(E, A, kernel):
    match E, A:
        case [s, t], [[[0, c], a, h], z] if s == a:
            return [z, kernel.sub(h, t if c == 0 else [c, t, h])]
    return A


def fused_to_control(p, kernel, g=None):
    if g is None:
        g = [([], [1, 1])]
    match p:
        case ['u', j, t, q]:
            return ['u', j, t, fused_to_control(q, kernel, g) if g[j][0] else copy.deepcopy(q)]
        case ['i', B0, t, r]:
            B = kernel.sub(B0, t, 1)
            u = kernel.sub(B, -len(g) if len(B0) == 2 and t == 0 else 0)
            return ['i', B0, t, fused_to_control(r, kernel, g + [([], u)])]
        case ['e', q, r, v]:
            D, = kernel.prove(q, g)
            B = kernel.sub(D, -len(g), 1)
            local = g + [(kernel.sub(B, 0), B)]
            return ['e', fused_to_control(q, kernel, g),
                    ['x', fused_to_control(r, kernel, local),
                     fused_to_control(v, kernel, local)]]
    raise ValueError('invalid fused proof')


def control_to_fused(p, kernel, sg=None, tg=None, levels=None, clauses=None):
    if sg is None:
        sg = [([], [1, 1])]
    if tg is None:
        tg = [([], [1, 1])]
    if levels is None:
        levels = {}
    if clauses is None:
        clauses = [0]

    def rec(q, sc=sg, tc=tg, lv=levels, cl=clauses):
        return control_to_fused(q, kernel, sc, tc, lv, cl)

    match p:
        case ['u', j, t, q]:
            A = kernel.sub(sg[j][1], t)
            q1 = rec(q)[1] if sg[j][0] else copy.deepcopy(q)
            return A, ['u', clauses[j], rename(t, levels), q1]
        case ['x', q, r]:
            local = tg + [([0, 0], [0, 0])]
            E, q1 = rec(q, tc=local)
            A, r1 = rec(r, tc=local)
            return evaluate(E, A, kernel), ['e', delta(), q1, r1]
        case ['e', q, r]:
            major, q1 = rec(q)
            D, = major
            B = kernel.sub(D, -len(sg), 1)
            B1 = kernel.sub(rename(D, levels), -len(tg), 1)
            A, r1 = rec(r, sg + [(kernel.sub(B, 0), B)],
                        tg + [(kernel.sub(B1, 0), B1)],
                        levels | {-len(sg): -len(tg)}, clauses + [len(tg)])
            return A, ['e', q1, delta(), r1]
        case ['i', B0, t, r]:
            B = kernel.sub(B0, t, 1)
            u = kernel.sub(B, -len(sg) if len(B0) == 2 and t == 0 else 0)
            B01, t1 = rename(B0, levels), rename(t, levels)
            B1 = kernel.sub(B01, t1, 1)
            u1 = kernel.sub(B1, -len(tg) if len(B01) == 2 and t1 == 0 else 0)
            _, r1 = rec(r, sg + [([], u)], tg + [([], u1)],
                        levels | {-len(sg): -len(tg)}, clauses + [len(tg)])
            return [B0], ['i', B01, t1, r1]
    raise ValueError('invalid control proof')
