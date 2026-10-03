#!/usr/bin/env python3
"""Radius-one time dilation for a completed weighted Boolean-channel CA.

A channel integer r*t+p represents (base_type=t, phase=p). Cell states are
subsets of channels. The old local permutation acts on the phase-zero subset,
including its own cardinality sector, while every other subset is untouched.
The frozen base permutation is applied once per block of r steps on synchronized
phase-zero inputs, with no added particles or non-vacuum background.

Public inputs are validated with ValueError, also under ``python -O``. Integer
parameters must be exact Python ints, excluding bool, float and int subclasses.
Particle inputs are finite iterables of two-item tuple/list lanes; each call
snapshots them before validation and use. Transition descriptors are immutable
copies, independent of subsequent mutations to the supplied base.
"""
from collections import defaultdict
from collections.abc import Mapping
from types import MappingProxyType


def _items(value, name):
    if isinstance(value, (str, bytes, bytearray, Mapping)):
        raise ValueError(f'{name} must be a finite iterable')
    try:
        return tuple(value)
    except TypeError as exc:
        raise ValueError(f'{name} must be a finite iterable') from exc


def _index(value, limit, name):
    if type(value) is not int or not 0 <= value < limit:
        raise ValueError(f'{name} must be an exact int in [0, {limit})')
    return value


def _pair(value, limit, name):
    if not isinstance(value, (tuple, list)) or len(value) != 2:
        raise ValueError(f'{name} must be a two-item tuple/list')
    a, b = value
    _index(a, limit, name)
    _index(b, limit, name)
    if a >= b:
        raise ValueError(f'{name} must contain two distinct increasing IDs')
    return a, b


class RadiusOneCA:
    def __init__(self, base, r=None):
        try:
            names, velocity = base.names, base.velocity
            single, pairs = base.single, base.pairs
        except AttributeError as exc:
            raise ValueError('base must provide names, velocity, single and pairs') from exc
        self.base_type_count = len(_items(names, 'base.names'))
        self.base_velocity = _items(velocity, 'base.velocity')
        if (len(self.base_velocity) != self.base_type_count
                or any(type(v) is not int for v in self.base_velocity)):
            raise ValueError('base.velocity must contain one exact int per base type')
        maximum = max(map(abs, self.base_velocity), default=0)
        self.r = max(1, maximum) if r is None else r
        if type(self.r) is not int or self.r < max(1, maximum):
            raise ValueError('r must be an exact int at least max(1, max(abs(velocity)))')
        self.channel_count = self.r * self.base_type_count
        if not isinstance(single, Mapping) or not isinstance(pairs, Mapping):
            raise ValueError('base.single and base.pairs must be mappings')
        single_copy = {}
        for a, b in single.items():
            _index(a, self.base_type_count, 'singleton source ID')
            _index(b, self.base_type_count, 'singleton target ID')
            if a in single_copy:
                raise ValueError('duplicate singleton source ID')
            single_copy[a] = b
        if (set(single_copy) != set(range(self.base_type_count))
                or set(single_copy.values()) != set(single_copy)):
            raise ValueError('base.single must be a permutation of every base type')
        pairs_copy = {}
        for a, b in pairs.items():
            a = _pair(a, self.base_type_count, 'pair source')
            b = _pair(b, self.base_type_count, 'pair target')
            if a in pairs_copy:
                raise ValueError('duplicate pair source')
            pairs_copy[a] = b
        if set(pairs_copy) != set(pairs_copy.values()):
            raise ValueError('base.pairs must permute its supported pair set')
        self.single = MappingProxyType(single_copy)
        self.pairs = MappingProxyType(pairs_copy)
        self.inverse_single = MappingProxyType({b: a for a, b in self.single.items()})
        self.inverse_pairs = MappingProxyType({b: a for a, b in self.pairs.items()})
        self.displacement = tuple(self.epsilon(t, (p - 1) % self.r)
                                  for t in range(self.base_type_count)
                                  for p in range(self.r))
        assert max(map(abs, self.displacement), default=0) <= 1

    def epsilon(self, t, old_phase):
        _index(t, self.base_type_count, 'base type ID')
        _index(old_phase, self.r, 'old phase')
        velocity = self.base_velocity[t]
        return ((velocity > 0) - (velocity < 0)) if old_phase < abs(velocity) else 0

    def encode_channel(self, t, phase=0):
        _index(t, self.base_type_count, 'base type ID')
        _index(phase, self.r, 'phase')
        return self.r*t + phase

    def embed(self, particles):
        particles = self._check_base(particles)
        return tuple(sorted((x, self.encode_channel(t)) for x, t in particles))

    def project(self, particles, phase=0):
        """Decode only synchronized states, rejecting accidental phase loss."""
        _index(phase, self.r, 'phase')
        particles = self._check(particles)
        if any(k % self.r != phase for x, k in particles):
            raise ValueError('all particles must have the requested phase')
        return tuple((x, k // self.r) for x, k in particles)

    def _lanes(self, particles, limit):
        result, seen = [], set()
        for lane in _items(particles, 'particles'):
            if not isinstance(lane, (tuple, list)) or len(lane) != 2:
                raise ValueError('each particle must be a two-item tuple/list lane')
            x, k = lane
            if type(x) is not int:
                raise ValueError('position must be an exact int')
            _index(k, limit, 'lane ID')
            lane = (x, k)
            if lane in seen:
                raise ValueError('duplicate Boolean lane occupancy')
            seen.add(lane)
            result.append(lane)
        return tuple(result)

    def _check_base(self, particles):
        return self._lanes(particles, self.base_type_count)

    def _check(self, particles):
        return self._lanes(particles, self.channel_count)

    def _base_local(self, present, inverse=False):
        present = tuple(sorted(present))
        if len(present) == 1:
            return ((self.inverse_single if inverse else self.single)[present[0]],)
        if len(present) == 2:
            return (self.inverse_pairs if inverse else self.pairs).get(present, present)
        return present  # Includes vacuum and every cardinality >= 3.

    def local_zero(self, present, inverse=False):
        """Π_0 or Π_0^{-1}; cardinality means phase-zero cardinality only."""
        if type(inverse) is not bool:
            raise ValueError('inverse must be a bool')
        present = _items(present, 'present channels')
        for k in present:
            _index(k, self.channel_count, 'channel ID')
        if len(set(present)) != len(present):
            raise ValueError('duplicate Boolean lane occupancy')
        zero = tuple(k // self.r for k in present if k % self.r == 0)
        other = tuple(k for k in present if k % self.r != 0)
        return tuple(sorted(other + tuple(self.encode_channel(t)
                                         for t in self._base_local(zero, inverse))))

    def step(self, particles):
        particles = self._check(particles)
        cells = defaultdict(list)
        for x, k in particles:
            cells[x].append(k)
        result = []
        for x, present in cells.items():
            for k in self.local_zero(present):
                t, p = divmod(k, self.r)
                rotated = self.encode_channel(t, (p+1) % self.r)
                result.append((x + self.displacement[rotated], rotated))
        self._check(result)
        assert len(result) == len(particles)
        return tuple(sorted(result))

    def inverse_step(self, particles):
        particles = self._check(particles)
        cells = defaultdict(list)
        # Undo streaming and then the local phase rotation, before Π_0^{-1}.
        for x, k in particles:
            t, p = divmod(k, self.r)
            old_k = self.encode_channel(t, (p-1) % self.r)
            cells[x - self.displacement[k]].append(old_k)
        result = [(x, k) for x, present in cells.items()
                  for k in self.local_zero(present, inverse=True)]
        self._check(result)
        assert len(result) == len(particles)
        return tuple(sorted(result))

    def committed_halt(self, particles, base):
        """Occurrence of the exact two-channel phase-zero committed-halt cell.

        The explicit base argument supplies the halt descriptor for this query;
        it does not alter this wrapper's immutable transition descriptors.
        """
        particles = self._check(particles)
        try:
            type_ids, halt = base.type_ids, base.halt
            if not isinstance(type_ids, Mapping):
                raise ValueError('base.type_ids must be a mapping')
            left = type_ids[('L', 0, (halt, 0, 0))]
            stationary = type_ids[('S', 0)]
        except (AttributeError, KeyError, TypeError) as exc:
            raise ValueError('base must provide both committed-halt type IDs') from exc
        wanted = {self.encode_channel(left), self.encode_channel(stationary)}
        if len(wanted) != 2:
            raise ValueError('committed-halt type IDs must be distinct')
        cells = defaultdict(set)
        for x, k in particles:
            cells[x].add(k)
        return any(wanted == present for present in cells.values())
