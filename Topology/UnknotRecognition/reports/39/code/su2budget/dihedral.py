"""Complete compressed feasibility for two noncommuting traceless SU(2) images.

For A^2=B^2=-1, put T=AB. Every word has normal form
(-1)^epsilon T^k A^s. Multiplication is integer arithmetic; no word expansion,
polynomial expansion, floating point, or algebraic-number materialization.
The knot-recognition interpretation still requires verified meridian provenance.
"""
from __future__ import annotations
from functools import reduce
from math import gcd
from .slp import Presentation, LimitExceeded


IDENTITY = (0, 0, 0)
LETTERS = {1: (0, 0, 1), -1: (1, 0, 1),
           2: (1, -1, 1), -2: (0, -1, 1)}


def multiply(x, y):
    e, k, s = x
    f, ell, t = y
    return ((e+f+s*t) & 1, k + (-ell if s else ell), s ^ t)


def inverse(x):
    e, k, s = x
    return (e ^ s, k if s else -k, s)


def normal_forms(p: Presentation, *, max_exponent_bits=100000,
                 max_nodes=1000000, check=lambda: None):
    if p.rank != 2:
        raise ValueError('exactly two generators required')
    live = p.live()
    if len(live) > max_nodes:
        raise LimitExceeded('normal-form live-node cap')
    values = {0: IDENTITY}
    peak = 0
    for v in live:
        check()
        rule = p.rules[v]
        value = LETTERS[rule[1]] if rule[0] == 't' else multiply(values[rule[1]], values[rule[2]])
        bits = abs(value[1]).bit_length()
        if bits > max_exponent_bits:
            raise LimitExceeded('normal-form exponent bit cap')
        peak = max(peak, bits)
        values[v] = value
    relators = tuple(multiply(values[u],inverse(values[v])) for u,v in p.relations)
    for _, k, _ in relators:
        if abs(k).bit_length() > max_exponent_bits:
            raise LimitExceeded('relation exponent bit cap')
        peak = max(peak,abs(k).bit_length())
    return relators, peak, len(live)


def analyze(relators):
    """Solve k*phi = epsilon*pi mod 2*pi with 0<phi<pi."""
    odd = next((i for i,(_,_,s) in enumerate(relators) if s),None)
    if odd is not None:
        return dict(status='NONE', obstruction='odd A parity', index=odd)
    impossible = next((i for i,(e,k,_) in enumerate(relators) if not k and e),None)
    if impossible is not None:
        return dict(status='NONE', obstruction='central minus identity', index=impossible)
    d = reduce(gcd,(abs(k) for _,k,_ in relators),0)
    if not d:
        return dict(status='EXISTS', gcd=0, phase_parity=0, phase=[1,2],
                    count='continuum')
    # The normalized exponents have gcd 1, so at least one is odd.
    e = next(e for e,k,_ in relators if (k//d)&1)
    bad = next((i for i,(f,k,_) in enumerate(relators) if f != (((k//d)&1)*e)),None)
    if bad is not None:
        return dict(status='NONE', obstruction='incompatible central parity',
                    index=bad, gcd=d, phase_parity=e)
    count = (d-1+e)//2
    if count == 0:
        return dict(status='NONE', obstruction='only commuting endpoint phases',
                    gcd=d, phase_parity=e, count=0)
    return dict(status='EXISTS', gcd=d, phase_parity=e, count=count,
                phase=[1 if e else 2,d])


def solve(p: Presentation, **limits):
    if not p.meridian_generators or p.rank != 2:
        raise ValueError('two declared meridian generators required; declaration is not a proof')
    try:
        forms, bits, nodes = normal_forms(p, **limits)
        answer = analyze(forms)
        return dict(answer, presentation_digest=p.digest(),
                    relator_normal_forms=[list(x) for x in forms],
                    peak_exponent_bits=bits, live_nodes=nodes,
                    scope='two-generator meridian-traceless representation feasibility; '
                          'knot/meridian provenance must be independently verified')
    except LimitExceeded as exc:
        return dict(status='UNKNOWN', reason=str(exc), presentation_digest=p.digest(),
                    scope='no mathematical conclusion')


def verify(p: Presentation, certificate: dict, **limits) -> bool:
    """Replay integer arithmetic from the source; shared arithmetic, not a
    separately implemented proof assistant. Extra timing fields are irrelevant.
    """
    if certificate.get('status') not in ('EXISTS','NONE'):
        return False
    fresh = solve(p, **limits)
    return all(certificate.get(k) == value for k,value in fresh.items())
