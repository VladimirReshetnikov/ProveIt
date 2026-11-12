"""Untrusted translation from the pinned five-rule SeedEval checker.

The source has tagged terms, explicit reflexivity, and ordinary clause bases.
The target has untagged terms, a fixed reflexivity clause, and optionally fuses
SeedEval with D-elimination. Extra target eigenvariables are tracked explicitly.
"""
import importlib.util
from pathlib import Path


def load(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def delta():
    return ['i', [0, 0], 0, ['u', 0, 0, None]]


def code(a, levels):
    if type(a) is int:
        return levels.get(a, a)
    tag, *children = a
    children = [code(b, levels) for b in children]
    if tag == 's':
        return [0, children[0]]
    if tag in ('i', '=', 'd'):
        return children
    raise ValueError('unknown source syntax')


def translate(p, src, target, source_context=None, source_scope=0,
              target_context=None, levels=None, clauses=None, fused=True):
    if source_context is None:
        source_context = []
    if target_context is None:
        target_context = [([], [1, 1])]
    if levels is None:
        levels = {}
    if clauses is None:
        clauses = []
    sc, tg, ss = source_context, target_context, source_scope

    def child(q, sc1=sc, ss1=ss, tg1=tg, lv=levels, cl=clauses):
        return translate(q, src, target, sc1, ss1, tg1, lv, cl, fused)

    match p:
        case ['r', a]:
            return ['=', a, a], ['u', 0, code(a, levels), None]
        case ['u', j, t, q]:
            _, q1 = child(q)
            return src.opening(sc[j][1], t), ['u', clauses[j], code(t, levels), q1]
        case ['x', q, r]:
            local = tg + [([0, 0], [0, 0])] if fused else tg
            E, q1 = child(q, tg1=local)
            F, r1 = child(r, tg1=local)
            _, s, t = E
            _, upper, z = F
            _, _, a, h = upper
            c = upper[1][1]
            A = ['=', z, src.opening(h, t if c == 0 else ['i', c, t, h])]
            return A, ['e', delta(), q1, r1] if fused else ['x', q1, r1]
        case ['e', goal, q, r]:
            paired, q1 = child(q)
            Bsrc = src.opening(paired[1], -ss - 1, 1)
            Bnew = target.sub(code(paired, levels)[0], -len(tg), 1)
            sc1 = sc + [(src.opening(Bsrc, 0), Bsrc)]
            tg1 = tg + [(target.sub(Bnew, 0), Bnew)]
            _, r1 = child(r, sc1, ss + 1, tg1,
                          levels | {-ss - 1: -len(tg)}, clauses + [len(tg)])
            return goal, ['e', q1, delta(), r1] if fused else ['e', q1, r1]
        case ['i', goal, t, r]:
            Bsrc = src.opening(goal[1], t, 1)
            eta = -ss - 1 if goal[1][0] == '=' and t == 0 else 0
            Hsrc = src.opening(Bsrc, eta)
            goal1 = code(goal, levels)
            t1 = code(t, levels)
            Bnew = target.sub(goal1[0], t1, 1)
            Hnew = target.sub(Bnew, -len(tg) if len(goal1[0]) == 2 and t1 == 0 else 0)
            _, r1 = child(r, sc + [(['=', 0, 0], Hsrc)], ss + 1,
                          tg + [([], Hnew)], levels | {-ss - 1: -len(tg)},
                          clauses + [len(tg)])
            return goal, ['i', goal1[0], t1, r1]
    raise ValueError('unknown source proof')


def translate_document(data, source, target, fused=True):
    source.verify(data)
    A, p = translate(data['proof'], source, target, fused=fused)
    result = {'goal': code(A, {}), 'proof': p}
    target.check(result)
    return result
