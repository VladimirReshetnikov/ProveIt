"""Checked two-seed Wirtinger recognition with exact integer SU(2) arithmetic.

The input is revalidated as a spherical one-component PD. Seed generators are
actual Wirtinger meridians; each other generator is derived by one original
crossing conjugation. Every original relation is then imposed on the derived
values. No arbitrary group-search endpoint or meridian declaration is trusted.

Kronheimer--Mrowka, Knots, sutures and excision, Corollary 7.17, supplies the
traceless nonabelian representation criterion. For two meridians all word
values have binary-dihedral normal forms, so a gcd/parity test is complete.
Search failure or any resource limit is inconclusive. The seed search and its
search-independent replay share the original time/work allowance.
"""
from collections import deque
from hashlib import sha256
from itertools import combinations
import json
from math import gcd, isfinite
from time import monotonic

from .diagram import Diagram, DisjointSet
from .integer_codec import certificate_equal, json_safe


class TwoMeridianLimit(RuntimeError):
    """Local exhaustion, never a knot verdict."""


def validate_limits(seconds, max_work, max_attempts):
    for name, value in (('max_work', max_work), ('max_attempts', max_attempts)):
        if value is not None and (type(value) is not int or value < 0):
            raise ValueError(name+' must be a nonnegative integer or None')
    if seconds is not None and (type(seconds) not in (int, float)
            or not isfinite(seconds) or seconds < 0):
        raise ValueError('two-meridian seconds must be finite and nonnegative, or None')


class _Budget:
    def __init__(self, check, seconds, max_work):
        self.check, self.max_work, self.work = check, max_work, 0
        self.expires = None if seconds is None else monotonic()+seconds

    def tick(self, amount=1):
        self.check()
        if self.expires is not None and monotonic() >= self.expires:
            raise TwoMeridianLimit('two-meridian local time allowance exhausted')
        if self.max_work is not None and self.work+amount > self.max_work:
            raise TwoMeridianLimit('two-meridian shared work allowance exhausted')
        self.work += amount


def _model(diagram, budget):
    """Build signed Wirtinger crossings from revalidated PD port orientations."""
    budget.tick(4*diagram.crossings+1)
    diagram = Diagram.from_pd(diagram.pd)
    n = diagram.crossings
    digest = sha256(json.dumps(diagram.pd, separators=(',', ':')).encode('ascii')).hexdigest()
    if not n:
        return diagram, digest, 0, []
    dsu = DisjointSet(2*n)
    for _, b, _, d in diagram.pd:
        budget.tick()
        dsu.union(b, d)
    names, owner = {}, []
    for edge in range(2*n):
        budget.tick()
        root = dsu.find(edge)
        owner.append(names.setdefault(root, len(names)))
    crossings = []
    for row, (incoming, _), sign in zip(diagram.pd, diagram.incoming_slots(), diagram.signs()):
        budget.tick()
        crossings.append((owner[row[1]], owner[row[incoming]],
                          owner[row[(incoming+2) % 4]], sign))
    budget.tick()
    return diagram, digest, len(names), crossings


def _rules(n, crossings, budget):
    rules, incident = [], [[] for _ in range(n)]
    for i, (over, under_in, under_out, _) in enumerate(crossings):
        for source, target, direction in ((under_in, under_out, 1), (under_out, under_in, -1)):
            budget.tick()
            index = len(rules)
            rules.append((over, source, target, i, direction))
            for v in {over, source}:
                incident[v].append(index)
    return rules, incident


def _propagate(n, rules, incident, seeds, budget):
    budget.tick(n+len(rules))
    remaining = [1 if over == source else 2 for over, source, *_ in rules]
    reached = set(seeds)
    queue, trace = deque(seeds), []
    while queue and len(reached) < n:
        v = queue.popleft()
        budget.tick()
        for index in incident[v]:
            budget.tick()
            remaining[index] -= 1
            if remaining[index]:
                continue
            over, source, target, crossing, direction = rules[index]
            if target not in reached:
                reached.add(target)
                trace.append([target, crossing, direction])
                queue.append(target)
    return trace, len(reached)


def _multiply(x, y, budget):
    e, k, s = x
    f, ell, t = y
    budget.tick(1+abs(k).bit_length()+abs(ell).bit_length())
    return ((e+f+s*t) & 1, k-ell if s else k+ell, s ^ t)


def _inverse(x):
    e, k, s = x
    return (e ^ s, k if s else -k, s)


def _conjugate(over, source, sign, budget):
    c = over if sign == 1 else _inverse(over)
    return _multiply(_multiply(c, source, budget), _inverse(c), budget)


def _replay_values(n, crossings, seeds, trace, budget):
    """Replay a strict acyclic derivation without rerunning seed search."""
    if (type(seeds) is not list or type(trace) is not list
            or len(seeds) not in ((0,) if n == 0 else (1, 2))
            or any(type(v) is not int or not 0 <= v < n for v in seeds)
            or seeds != sorted(set(seeds)) or len(trace) != n-len(seeds)):
        return None
    values = {seed: value for seed, value in zip(seeds, ((0, 0, 1), (1, -1, 1)))}
    for step in trace:
        budget.tick()
        if (type(step) is not list or len(step) != 3
                or any(type(v) is not int for v in step)):
            return None
        target, index, direction = step
        if (not 0 <= target < n or target in values or not 0 <= index < len(crossings)
                or direction not in (-1, 1)):
            return None
        over, under_in, under_out, sign = crossings[index]
        source, dest = (under_in, under_out) if direction == 1 else (under_out, under_in)
        if target != dest or source not in values or over not in values:
            return None
        values[target] = _conjugate(values[over], values[source], sign*direction, budget)
    return values if len(values) == n else None


def _phase(forms, budget):
    for i, (e, k, s) in enumerate(forms):
        budget.tick()
        if s:
            return dict(status='NONE', obstruction='odd meridian parity', index=i)
        if not k and e:
            return dict(status='NONE', obstruction='central minus identity', index=i)
    d = 0
    for _, k, _ in forms:
        budget.tick(1+abs(k).bit_length()+d.bit_length())
        d = gcd(d, abs(k))
    if not d:
        return dict(status='EXISTS', gcd=0, phase=[1, 2], count='continuum')
    for e, k, _ in forms:
        budget.tick(1+abs(k).bit_length()+d.bit_length())
        if (k//d) & 1:
            parity = e
            break
    for i, (e, k, _) in enumerate(forms):
        budget.tick(1+abs(k).bit_length()+d.bit_length())
        if e != (((k//d) & 1)*parity):
            return dict(status='NONE', obstruction='incompatible central parity',
                        index=i, gcd=d, phase_parity=parity)
    count = (d-1+parity)//2
    if not count:
        return dict(status='NONE', obstruction='only commuting endpoint phases',
                    gcd=d, phase_parity=parity, count=0)
    return dict(status='EXISTS', gcd=d, phase_parity=parity, count=count,
                phase=[1 if parity else 2, d])


def _certificate(digest, n, crossings, seeds, trace, budget):
    values = _replay_values(n, crossings, seeds, trace, budget)
    if values is None:
        return None
    forms = []
    for over, under_in, under_out, sign in crossings:
        budget.tick()
        lhs = _conjugate(values[over], values[under_in], sign, budget)
        forms.append(_multiply(lhs, _inverse(values[under_out]), budget))
    if len(seeds) < 2:
        # Every derived arc is the same meridian as a formal group word.
        # All original conjugation relations are then identities in Z.
        if any(form != (0, 0, 0) for form in forms):
            raise ArithmeticError('one-seed propagation failed cyclic consistency')
        phase, status = dict(status='CYCLIC'), 'UNKNOT'
    else:
        phase = _phase(forms, budget)
        status = 'KNOTTED' if phase['status'] == 'EXISTS' else 'UNKNOT'
    budget.tick()
    return dict(version=1, method='wirtinger-two-seed', input_sha256=digest,
                arc_count=n, seeds=list(seeds), derivations=trace,
                relator_normal_forms=[list(form) for form in forms], phase=phase, status=status)


def _verify(diagram, certificate, budget):
    _, digest, n, crossings = _model(diagram, budget)
    if type(certificate) is not dict or 'seeds' not in certificate or 'derivations' not in certificate:
        return False
    expected = _certificate(digest, n, crossings, certificate['seeds'], certificate['derivations'], budget)
    budget.tick()
    return expected is not None and certificate_equal(certificate, expected)


def verify_two_meridian_certificate(diagram, certificate, *, max_work=2_000_000,
                                    check=lambda: None):
    """Rebuild the PD presentation and replay; local/global exhaustion propagates.

    Search is independent of replay. Integer arithmetic is shared and is tested
    separately against expanded words and rational quaternion calculations.
    """
    validate_limits(None, max_work, None)
    return _verify(diagram, certificate, _Budget(check, None, max_work))


def two_meridian_decide(diagram, *, seconds=0.05, max_work=2_000_000,
                        max_attempts=10_000, check=lambda: None):
    """Sound partial recognizer, complete on two-seed derivable diagrams uncapped.

    All preparation, every attempted seed set, arithmetic and replay share one
    work/time allowance. Set all three local caps to None for exhaustive search.
    The integer ledger is a cooperative work measure, not a hard bit-time bound.
    """
    validate_limits(seconds, max_work, max_attempts)
    start = monotonic()
    budget = _Budget(check, seconds, max_work)
    stats = dict(attempts=0, work=0, replay_work=0, max_reached=0)
    replay_start = None
    try:
        checked, digest, n, crossings = _model(diagram, budget)
        stats['arc_count'] = n
        found = None
        if not n:
            found = [], []
        else:
            rules, incident = _rules(n, crossings, budget)
            for rank in (1, 2):
                for seeds in combinations(range(n), rank):
                    budget.tick()
                    if max_attempts is not None and stats['attempts'] >= max_attempts:
                        raise TwoMeridianLimit('two-meridian seed-attempt allowance exhausted')
                    stats['attempts'] += 1
                    trace, reached = _propagate(n, rules, incident, seeds, budget)
                    stats['max_reached'] = max(stats['max_reached'], reached)
                    if reached == n:
                        found = list(seeds), trace
                        break
                if found is not None:
                    break
        if found is None:
            budget.tick()
            reason = 'no complete derivation from one or two seed meridians'
        else:
            certificate = _certificate(digest, n, crossings, *found, budget)
            if certificate is None:
                raise ArithmeticError('produced seed derivation failed replay')
            replay_start = budget.work
            if not _verify(checked, certificate, budget):
                raise ArithmeticError('produced two-meridian certificate failed verification')
            stats['replay_work'] = budget.work-replay_start
            budget.tick()
            stats['work'] = budget.work
            return dict(status=certificate['status'], method='wirtinger-two-seed',
                        certificate=json_safe(certificate), statistics=stats, seconds=monotonic()-start)
    except TwoMeridianLimit as exc:
        check()
        reason = str(exc)
    check()
    stats['work'] = budget.work
    if replay_start is not None:
        stats['replay_work'] = budget.work-replay_start
    return dict(status='INCONCLUSIVE', reason=reason, statistics=stats, seconds=monotonic()-start)
