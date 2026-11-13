"""Untrusted exact-goal compilers between the split and fused diagonal calculi.

Adapted from evaluation_discharge/raw/translations.py at the pinned ProveIt
commit recorded in PROVENANCE.json. Acceptance is always rechecked by the
standalone target module. This file is not part of either trusted checker.
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


def diagonal(B):
    match B:
        case [[1, 1, _], [1, 1, _]]:
            return True
    return False


def theta(n):
    """D(0=0), using only the local assumption and introduction."""
    return ['i', [0, 0], 0, ['u', n, 0, None]]


def evaluate(E, F, sub):
    match E, F:
        case [s, t], [[0, a, h], r] if s == a:
            return [r, t], True
        case [s, t], [[[0, c], a, h], r] if s == [c, a, h]:
            return [r, sub(h, t)], True
        case [_], _:
            return F, False
    raise ValueError('rho is undefined')


def between(p, src, target, source_fused, target_fused, sc=None, tg=None,
            levels=None, clauses=None):
    sc = [([], [1, 1])] if sc is None else sc
    tg = [([], [1, 1])] if tg is None else tg
    levels = {} if levels is None else levels
    clauses = list(range(len(sc))) if clauses is None else clauses

    def child(q, sc1=sc, tg1=tg, lv=levels, cl=clauses):
        return between(q, src, target, source_fused, target_fused,
                       sc1, tg1, lv, cl)

    match p:
        case ['u', j, t, q]:
            u, B = sc[j]
            q1 = child(q)[1] if u else None
            return src.sub(B, t), ['u', clauses[j], rename(t, levels), q1]
        case ['i', B0, t, r]:
            Bs = src.sub(B0, t, 1)
            Hs = src.sub(Bs, -len(sc) if diagonal(B0) else 0)
            B1, t1 = rename(B0, levels), rename(t, levels)
            Bt = target.sub(B1, t1, 1)
            Ht = target.sub(Bt, -len(tg) if diagonal(B1) else 0)
            _, r1 = child(r, sc + [([], Hs)], tg + [([], Ht)],
                          levels | {-len(sc): -len(tg)}, clauses + [len(tg)])
            return [B0], ['i', B1, t1, r1]
        case ['v', q, r]:
            if source_fused:
                raise ValueError('split rule in a fused certificate')
            local = tg + [([0, 0], [0, 0])] if target_fused else tg
            E, q1 = child(q, tg1=local)
            F, r1 = child(r, tg1=local)
            A, matched = evaluate(E, F, src.sub)
            if not matched:
                raise ValueError('compound auxiliary is not a split Eval')
            return A, ['e', theta(len(tg)), q1, r1] if target_fused else ['v', q1, r1]
        case ['e', *_]:
            paired, q1 = child(p[1])
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
                out = ['e', q1, r1, v1] if target_fused else ['e', q1, ['v', r1, v1] if matched else v1]
            else:
                A, v1 = child(p[2], sc1, tg1, lv, cl)
                out = ['e', q1, theta(len(tg1)), v1] if target_fused else ['e', q1, v1]
            return A, out
    raise ValueError('invalid proof')


def translate(data, src, target, source_fused, target_fused):
    src.check(data)
    A, p = between(data['proof'], src, target, source_fused, target_fused)
    result = {'goal': A, 'proof': p}
    if A != data['goal']:
        raise ValueError('end sequent changed')
    target.check(result)
    return result


def substitute_proof(p, sigma):
    """Substitute rigid free parameters; sigma must avoid eigenparameters.

    This helper is for regression tests with a fixed scope size. The written
    structural theorem permits arbitrary capture-avoiding substitutions and
    first freshens eigenparameters. Renaming with changed scope sizes is
    implemented by between above, rather than by this convenience helper.
    """
    match p:
        case ['u', j, t, q]:
            return ['u', j, rename(t, sigma), None if q is None else substitute_proof(q, sigma)]
        case ['i', B, t, r]:
            return ['i', rename(B, sigma), rename(t, sigma), substitute_proof(r, sigma)]
        case ['v', q, r]:
            return ['v', substitute_proof(q, sigma), substitute_proof(r, sigma)]
        case ['e', *children]:
            return ['e', *(substitute_proof(q, sigma) for q in children)]
    raise ValueError('invalid proof')
