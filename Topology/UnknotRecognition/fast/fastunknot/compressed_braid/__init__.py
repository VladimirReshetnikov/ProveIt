"""Source-bound recognition of compressed braid closures using the native kernel.

The binary Artin grammar describes its own braid closure, not a PD diagram.
Three-strand input is completely decided given sufficient resources. Singleton
forests use the same complete leaf backend and a bounded exact homology fallback
for wider factors. Public recognition replays every verdict before publication.

Adapted from the MIT-0 compressed-braid-certificates research delivery (2026-10-08).
No copy of its source-derived string kernel is used: all exact string operations
come from fastunknot.compressed_words.WordArena.
"""
import json
import math
from time import monotonic

from ..compressed_words import CompressedLimit, WordArena
from .grammar import Builder, validate
from .engine import recognize as _produce_three
from .forest import recognize_forest as _produce_forest, verify_forest as _verify_forest
from .verify import InvalidCertificate, verify as _verify_three


class _Budget:
    def __init__(self, max_work, max_nodes, seconds, check, max_cube_generators=200000):
        for name, value in (('max_work', max_work), ('max_nodes', max_nodes)):
            if type(value) is not int or value < 0:
                raise ValueError(name + ' must be a nonnegative integer')
        if seconds is not None and (type(seconds) not in (int, float)
                                     or not math.isfinite(seconds) or seconds < 0):
            raise ValueError('seconds must be finite and nonnegative or None')
        self.max_work, self.max_nodes = max_work, max_nodes
        self.work = self.nodes = self.arenas = 0
        self.cube_generators = 0
        self.max_cube_generators = max_cube_generators
        self.check = check
        self.expires = None if seconds is None else monotonic() + seconds

    def poll(self):
        self.check()
        if self.expires is not None and monotonic() >= self.expires:
            raise CompressedLimit('compressed-braid time allowance exhausted')

    def charge(self, amount=1):
        if self.work + amount > self.max_work:
            raise CompressedLimit('shared compressed-braid work allowance exhausted')
        self.work += amount

    def step(self):
        self.poll()
        self.charge()

    def reserve_generators(self, amount):
        self.poll()
        if self.cube_generators + amount > self.max_cube_generators:
            raise CompressedLimit('shared exceptional cube generator allowance exhausted')
        self.cube_generators += amount

    def factory(self, **options):
        budget = self
        options.update(max_nodes=self.max_nodes, max_work=self.max_work, check=self.poll)
        class SharedArena(WordArena):
            def tick(self, amount=1):
                budget.charge(amount)
                super().tick(amount)

            def _intern(self, rule, length, first, last):
                if rule not in self._interned and budget.nodes >= budget.max_nodes:
                    raise CompressedLimit('shared compressed-braid node allowance exhausted')
                before = len(self.rules)
                result = super()._intern(rule, length, first, last)
                budget.nodes += len(self.rules) - before
                return result
        self.arenas += 1
        return SharedArena(**options)

    def stats(self):
        return dict(work=self.work, allocated_nodes=self.nodes, arenas=self.arenas,
                    cube_generators=self.cube_generators)


def _cap(value, label):
    if type(value) is not int or value < 0:
        raise ValueError(label + ' must be a nonnegative integer')
    return value


def _encoded_size(value, limit, budget):
    """Bound exact canonical JSON transport without building one large string."""
    used = 0
    for piece in json.JSONEncoder(sort_keys=True, separators=(',', ':')).iterencode(value):
        budget.step()
        used += len(piece.encode('utf-8'))
        if used > limit:
            raise CompressedLimit('compressed-braid serialized byte allowance exhausted')
    return used


def _source(data, max_input_rules, max_input_bytes, budget):
    budget.poll()
    if not isinstance(data, dict) or not isinstance(data.get('rules'), list):
        raise ValueError('expected a compressed Artin braid grammar')
    if len(data['rules']) > max_input_rules + 1:
        raise CompressedLimit('compressed-braid input rule allowance exhausted')
    _encoded_size(data, max_input_bytes, budget)


def _replay(data, certificate, options, fallback_options):
    if not isinstance(certificate, dict):
        raise InvalidCertificate('certificate must be an object')
    version = certificate.get('version')
    if version == 'compressed-three-braid-v1':
        return _verify_three(data, certificate, **options)
    if version in ('compressed-singleton-forest-v1', 'compressed-singleton-forest-v2',
                   'compressed-singleton-forest-v3'):
        return _verify_forest(data, certificate, **options, **fallback_options)
    raise InvalidCertificate('unknown compressed-braid certificate version')


def recognize(data, *, max_nodes=100000, max_work=10000000, max_input_rules=100000,
              max_input_bytes=16000000, max_certificate_bytes=64000000,
              seconds=None, check=lambda: None, equality_probe_steps=64,
              prefix_probe_steps=64, fallback_max_crossings=12,
              fallback_max_generators=200000, use_fallback_reduction=True):
    """Produce and independently replay a compressed braid-closure certificate.

    The work and allocated-node ceilings are shared across producer and verifier
    arenas, including every singleton leaf. Metadata and JSON chunks also charge
    work; these are cooperative abstract operations, not bit or CPU instructions.
    Byte ceilings refer to canonical JSON transport, not a hard process-memory cap.
    Invalid input and implementation errors propagate. Only known resource limits
    yield INCONCLUSIVE, with no partial certificate. External cancellation propagates.
    """
    if type(use_fallback_reduction) is not bool:
        raise ValueError('use_fallback_reduction must be Boolean')
    for label, value in (('max_input_rules', max_input_rules), ('max_input_bytes', max_input_bytes),
                         ('max_certificate_bytes', max_certificate_bytes),
                         ('equality_probe_steps', equality_probe_steps), ('prefix_probe_steps', prefix_probe_steps),
                         ('fallback_max_crossings', fallback_max_crossings),
                         ('fallback_max_generators', fallback_max_generators)):
        _cap(value, label)
    budget = _Budget(max_work, max_nodes, seconds, check, fallback_max_generators)
    options = dict(arena_factory=budget.factory, check=budget.step,
                   equality_probe_steps=equality_probe_steps, prefix_probe_steps=prefix_probe_steps)
    fallback_options = dict(fallback_max_crossings=fallback_max_crossings,
                            fallback_reserve=budget.reserve_generators)
    try:
        _source(data, max_input_rules, max_input_bytes, budget)
        result = (_produce_three(data, **options) if data.get('strands') == 3 else
                  _produce_forest(data, **options, **fallback_options,
                                  use_fallback_reduction=use_fallback_reduction))
        certificate = result['certificate']
        size = _encoded_size(certificate, max_certificate_bytes, budget)
        verdict = _replay(data, certificate, options, fallback_options)
        if verdict != result['status']:
            raise ArithmeticError('compressed braid producer and replay disagree')
        budget.poll()
        return dict(result, verified=True, certificate_bytes=size, resources=budget.stats())
    except CompressedLimit as exc:
        return dict(status='INCONCLUSIVE', reason=str(exc), resources=budget.stats())


def verify(data, certificate, *, max_nodes=100000, max_work=10000000,
           max_input_rules=100000, max_input_bytes=16000000, max_certificate_bytes=64000000,
           seconds=None, check=lambda: None, equality_probe_steps=64, prefix_probe_steps=64,
           fallback_max_crossings=12, fallback_max_generators=200000):
    """Return the independently certified status; invalid proofs and limits raise.

    Fresh replay has one shared work/node/time budget across all leaves. It never
    invokes producer reduction or longest-common-prefix search. INCONCLUSIVE may
    be certified for an unsupported wider leaf, but is never an unknot verdict.
    """
    for label, value in (('max_input_rules', max_input_rules), ('max_input_bytes', max_input_bytes),
                         ('max_certificate_bytes', max_certificate_bytes),
                         ('equality_probe_steps', equality_probe_steps), ('prefix_probe_steps', prefix_probe_steps),
                         ('fallback_max_crossings', fallback_max_crossings),
                         ('fallback_max_generators', fallback_max_generators)):
        _cap(value, label)
    budget = _Budget(max_work, max_nodes, seconds, check, fallback_max_generators)
    _source(data, max_input_rules, max_input_bytes, budget)
    _encoded_size(certificate, max_certificate_bytes, budget)
    answer = _replay(data, certificate, dict(arena_factory=budget.factory, check=budget.step,
        equality_probe_steps=equality_probe_steps, prefix_probe_steps=prefix_probe_steps),
        dict(fallback_max_crossings=fallback_max_crossings, fallback_reserve=budget.reserve_generators))
    budget.poll()
    return answer


__all__ = ['Builder', 'validate', 'recognize', 'verify', 'InvalidCertificate', 'CompressedLimit']
