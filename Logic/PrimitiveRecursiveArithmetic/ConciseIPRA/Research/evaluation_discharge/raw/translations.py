"""Untrusted exact-goal proof compilers for the raw fused calculus.

The trusted acceptance boundary is checker.py or control.py, never this file.
The scope maps account for extra fresh parameters introduced by dummy scopes.
"""
import importlib.util
from pathlib import Path


def load(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def rename(a, levels):
    if type(a) is int:
        return levels.get(a, a)
    return [rename(b, levels) for b in a]


def theta(n):
    """D(0=0), proved from its own temporary hypothesis, in n clauses."""
    return ['i', [0, 0], 0, ['u', n, 0, None]]


def evaluate(E, F, sub):
    match E, F:
        case [s, t], [[0, a, h], r] if s == a:
            return [r, t], True
        case [s, t], [[[0, c], a, h], r] if s == [c, a, h]:
            return [r, sub(h, t)], True
    return F, False


def from_reference(p, src, target, sc=None, ss=0, tg=None,
                   levels=None, clauses=None, fused=True):
    sc = [] if sc is None else sc
    tg = [([], [1, 1])] if tg is None else tg
    levels = {} if levels is None else levels
    clauses = [] if clauses is None else clauses

    def child(q, sc1=sc, ss1=ss, tg1=tg, lv=levels, cl=clauses):
        return from_reference(q, src, target, sc1, ss1, tg1, lv, cl, fused)

    match p:
        case ['r', a]:
            return [a, a], ['u', 0, rename(a, levels), None]
        case ['u', j, t, q]:
            _, q1 = child(q)
            return src.opening(sc[j][1], t), ['u', clauses[j], rename(t, levels), q1]
        case ['v', q, r]:
            local = tg + [([0, 0], [0, 0])] if fused else tg
            E, q1 = child(q, tg1=local)
            F, r1 = child(r, tg1=local)
            A, matched = evaluate(E, F, src.opening)
            if not matched:
                raise ValueError('invalid reference evaluation')
            return A, ['e', theta(len(tg)), q1, r1] if fused else ['v', q1, r1]
        case ['e', goal, q, r]:
            paired, q1 = child(q)
            Bsrc = src.opening(paired[0], -ss - 1, 1)
            Bnew = target.sub(rename(paired, levels)[0], -len(tg), 1)
            sc1 = sc + [(src.opening(Bsrc, 0), Bsrc)]
            tg1 = tg + [(target.sub(Bnew, 0), Bnew)]
            _, r1 = child(r, sc1, ss + 1, tg1,
                          levels | {-ss - 1: -len(tg)}, clauses + [len(tg)])
            out = ['e', q1, theta(len(tg1)), r1] if fused else ['e', q1, r1]
            return goal, out
        case ['i', goal, t, r]:
            Bsrc = src.opening(goal[0], t, 1)
            eta = -ss - 1 if len(goal[0]) == 2 and t == 0 else 0
            Hsrc = src.opening(Bsrc, eta)
            goal1, t1 = rename(goal, levels), rename(t, levels)
            Bnew = target.sub(goal1[0], t1, 1)
            Hnew = target.sub(Bnew, -len(tg) if len(goal1[0]) == 2 and t1 == 0 else 0)
            _, r1 = child(r, sc + [([0, 0], Hsrc)], ss + 1,
                          tg + [([], Hnew)], levels | {-ss - 1: -len(tg)},
                          clauses + [len(tg)])
            return goal, ['i', goal1[0], t1, r1]
    raise ValueError('invalid reference proof')


def translate_reference(data, src, target, fused=True):
    src.verify(data)
    A, p = from_reference(data['proof'], src, target, fused=fused)
    result = {'goal': A, 'proof': p}
    if A != data['goal']:
        raise ValueError('reference goal changed')
    target.check(result)
    return result


def between(p, src, target, source_fused, target_fused, sc=None, tg=None,
            levels=None, clauses=None):
    sc = [([], [1, 1])] if sc is None else sc
    tg = [([], [1, 1])] if tg is None else tg
    levels = {} if levels is None else levels
    clauses = list(range(len(sc))) if clauses is None else clauses

    def child(q, sc1=sc, tg1=tg, lv=levels, cl=clauses):
        return between(q, src, target, source_fused, target_fused,
                       sc1, tg1, lv, cl)

    tag = p[0]
    if tag == 'u':
        _, j, t, q = p
        u, B = sc[j]
        q1 = child(q)[1] if u else None
        return src.sub(B, t), ['u', clauses[j], rename(t, levels), q1]
    if tag == 'i':
        _, B0, t, r = p
        Bs = src.sub(B0, t, 1)
        Hs = src.sub(Bs, -len(sc) if len(B0) == 2 and t == 0 else 0)
        B1, t1 = rename(B0, levels), rename(t, levels)
        Bt = target.sub(B1, t1, 1)
        Ht = target.sub(Bt, -len(tg) if len(B1) == 2 and t1 == 0 else 0)
        _, r1 = child(r, sc + [([], Hs)], tg + [([], Ht)],
                      levels | {-len(sc): -len(tg)}, clauses + [len(tg)])
        return [B0], ['i', B1, t1, r1]
    if tag == 'v':
        _, q, r = p
        local = tg + [([0, 0], [0, 0])] if target_fused else tg
        E, q1 = child(q, tg1=local)
        F, r1 = child(r, tg1=local)
        A, matched = evaluate(E, F, src.sub)
        if not matched:
            raise ValueError('invalid control evaluation')
        return A, ['e', theta(len(tg)), q1, r1] if target_fused else ['v', q1, r1]
    if tag == 'e':
        q = p[1]
        paired, q1 = child(q)
        Bs = src.sub(paired[0], -len(sc), 1)
        Bt = target.sub(rename(paired, levels)[0], -len(tg), 1)
        sc1 = sc + [(src.sub(Bs, 0), Bs)]
        tg1 = tg + [(target.sub(Bt, 0), Bt)]
        lv = levels | {-len(sc): -len(tg)}
        cl = clauses + [len(tg)]
        if source_fused:
            E, r1 = child(p[2], sc1, tg1, lv, cl)
            F, v1 = child(p[3], sc1, tg1, lv, cl)
            A, matched = evaluate(E, F, src.sub)
            if target_fused:
                out = ['e', q1, r1, v1]
            else:
                out = ['e', q1, ['v', r1, v1] if matched else v1]
        else:
            A, v1 = child(p[2], sc1, tg1, lv, cl)
            out = ['e', q1, theta(len(tg1)), v1] if target_fused else ['e', q1, v1]
        return A, out
    raise ValueError('invalid source tag')


def translate(data, src, target, source_fused, target_fused):
    src.check(data)
    A, p = between(data['proof'], src, target, source_fused, target_fused)
    result = {'goal': A, 'proof': p}
    if A != data['goal']:
        raise ValueError('end sequent changed')
    target.check(result)
    return result


def to_reference(p, src, g=None):
    """Expand a fused proof into the independently implemented pinned checker.

    The fixed clause at target index zero becomes reference reflexivity;
    ordinary assumptions use the reference antecedent 0=0.
    Both scope conventions allocate the same fresh level in this direction.
    """
    g = [([], [1, 1])] if g is None else g
    tag = p[0]
    if tag == 'u':
        _, j, t, q = p
        u, B = g[j]
        A = src.sub(B, t)
        if j == 0:
            return A, ['r', t]
        q1 = to_reference(q, src, g)[1] if u else ['r', 0]
        return A, ['u', j - 1, t, q1]
    if tag == 'i':
        _, B0, t, r = p
        B = src.sub(B0, t, 1)
        H = src.sub(B, -len(g) if len(B0) == 2 and t == 0 else 0)
        _, r1 = to_reference(r, src, g + [([], H)])
        return [B0], ['i', [B0], t, r1]
    if tag == 'e':
        _, q, r, v = p
        paired, q1 = to_reference(q, src, g)
        B = src.sub(paired[0], -len(g), 1)
        local = g + [(src.sub(B, 0), B)]
        E, r1 = to_reference(r, src, local)
        F, v1 = to_reference(v, src, local)
        A, matched = evaluate(E, F, src.sub)
        return A, ['e', A, q1, ['v', r1, v1] if matched else v1]
    raise ValueError('invalid fused tag')


def translate_to_reference(data, src, reference):
    src.check(data)
    A, p = to_reference(data['proof'], src)
    result = {'goal': A, 'proof': p}
    if A != data['goal']:
        raise ValueError('end sequent changed')
    reference.verify(result)
    return result
