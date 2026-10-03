#!/usr/bin/env python3
"""Exact spatial blocking of a completed Boolean-channel collision/stream CA.

This is spatial recoding, with no temporal phase or time dilation. Old site
x = width*z + a, 0 <= a < width, becomes lane width*t+a at block site z.
The local collision is width independent copies of the old local permutation,
followed by the lane permutation (t,a) -> (t,(a+v(t)) mod width). Streaming
then uses a displacement determined by the OUTPUT lane. All configurations,
including arbitrary mixed-offset states, are in the image of this encoding.

The base convention is: a singleton permutation, a supported-pair permutation,
identity on unsupported pairs, vacuum, and every cardinality >= 3. This compact
description is retained; native pair-row counts are not flattened block counts.
Only Python's standard library is required. Public validation survives -O.
"""
from collections import defaultdict
from collections.abc import Mapping
from types import MappingProxyType


def _items(value, label):
    if isinstance(value, (str, bytes, bytearray, Mapping)):
        raise ValueError(f'{label} must be a finite iterable')
    try:
        return tuple(value)
    except TypeError as exc:
        raise ValueError(f'{label} must be a finite iterable') from exc


def _index(value, limit, label):
    if type(value) is not int or not 0 <= value < limit:
        raise ValueError(f'{label} must be an exact int in [0,{limit})')
    return value


class SpatialRadiusOneCA:
    def __init__(self, base, width=4):
        try:
            names = _items(base.names, 'base.names')
            velocity = _items(base.velocity, 'base.velocity')
            single, pairs = base.single, base.pairs
        except AttributeError as exc:
            raise ValueError('base must supply names, velocity, single, and pairs') from exc
        self.base_type_count = len(names)
        if len(velocity) != len(names) or any(type(v) is not int for v in velocity):
            raise ValueError('one exact integer velocity is required per type')
        if (type(width) is not int or width < 1
                or width < max(map(abs, velocity), default=0)):
            raise ValueError('width must be an exact positive int at least max |v|')
        self.width = width
        self.base_velocity = velocity
        self.channel_count = width * self.base_type_count
        if not isinstance(single, Mapping) or not isinstance(pairs, Mapping):
            raise ValueError('singleton and pair rules must be mappings')
        single_copy = {}
        for a, b in single.items():
            _index(a, self.base_type_count, 'singleton source')
            _index(b, self.base_type_count, 'singleton target')
            single_copy[a] = b
        if (set(single_copy) != set(range(self.base_type_count))
                or set(single_copy.values()) != set(single_copy)):
            raise ValueError('singleton rule must permute all types')

        def pair(value):
            if not isinstance(value, (tuple, list)) or len(value) != 2:
                raise ValueError('pair must be a two-item tuple/list')
            a, b = value
            _index(a, self.base_type_count, 'pair type')
            _index(b, self.base_type_count, 'pair type')
            if a >= b:
                raise ValueError('pair must have distinct increasing types')
            return a, b

        pairs_copy = {pair(a): pair(b) for a, b in pairs.items()}
        if set(pairs_copy) != set(pairs_copy.values()):
            raise ValueError('pair rule must permute its finite support')
        self.single = MappingProxyType(single_copy)
        self.pairs = MappingProxyType(pairs_copy)
        self.inverse_single = MappingProxyType({b: a for a, b in single_copy.items()})
        self.inverse_pairs = MappingProxyType({b: a for a, b in pairs_copy.items()})
        self.lane_permutation = tuple(
            width*t + (a+velocity[t]) % width
            for t in range(self.base_type_count) for a in range(width))
        self.inverse_lane_permutation = tuple(
            width*t + (b-velocity[t]) % width
            for t in range(self.base_type_count) for b in range(width))
        self.displacement = tuple(
            (((b-velocity[t]) % width) + velocity[t]) // width
            for t in range(self.base_type_count) for b in range(width))
        if any(abs(d) > 1 for d in self.displacement):
            raise ValueError('internal displacement exceeds radius one')

    def encode_channel(self, t, offset=0):
        _index(t, self.base_type_count, 'base type')
        _index(offset, self.width, 'offset')
        return self.width*t + offset

    def _lanes(self, particles, limit):
        result, seen = [], set()
        for particle in _items(particles, 'particles'):
            if not isinstance(particle, (tuple, list)) or len(particle) != 2:
                raise ValueError('particle must be a two-item tuple/list')
            x, k = particle
            if type(x) is not int:
                raise ValueError('position must be an exact int')
            _index(k, limit, 'channel')
            if (x, k) in seen:
                raise ValueError('duplicate Boolean lane occupancy')
            seen.add((x, k))
            result.append((x, k))
        return tuple(result)

    def embed(self, particles):
        """B: all old configurations to all blocked configurations, using floor."""
        result = []
        for x, t in self._lanes(particles, self.base_type_count):
            z, a = divmod(x, self.width)
            result.append((z, self.encode_channel(t, a)))
        return tuple(sorted(result))

    def project(self, particles):
        """B^{-1}: decode every blocked configuration; no synchronization test."""
        return tuple(sorted((self.width*z + k % self.width, k // self.width)
                            for z, k in self._lanes(particles, self.channel_count)))

    def _base_local(self, present, inverse=False):
        present = tuple(sorted(present))
        if len(present) == 1:
            return ((self.inverse_single if inverse else self.single)[present[0]],)
        if len(present) == 2:
            return (self.inverse_pairs if inverse else self.pairs).get(present, present)
        return present

    def local_collision(self, present, inverse=False):
        """Lambda Pi_block, or Pi_block^{-1} Lambda^{-1}, on a whole block."""
        if type(inverse) is not bool:
            raise ValueError('inverse must be a bool')
        present = _items(present, 'present channels')
        for k in present:
            _index(k, self.channel_count, 'channel')
        if len(set(present)) != len(present):
            raise ValueError('duplicate Boolean lane occupancy')
        if inverse:
            present = tuple(self.inverse_lane_permutation[k] for k in present)
        by_offset = defaultdict(list)
        for k in present:
            t, a = divmod(k, self.width)
            by_offset[a].append(t)
        output = tuple(self.encode_channel(t, a)
                       for a, types in by_offset.items()
                       for t in self._base_local(types, inverse))
        if not inverse:
            output = tuple(self.lane_permutation[k] for k in output)
        return tuple(sorted(output))

    def step(self, particles):
        particles = self._lanes(particles, self.channel_count)
        cells = defaultdict(list)
        for z, k in particles:
            cells[z].append(k)
        return tuple(sorted((z+self.displacement[k], k)
                            for z, present in cells.items()
                            for k in self.local_collision(present)))

    def inverse_step(self, particles):
        cells = defaultdict(list)
        for z, k in self._lanes(particles, self.channel_count):
            cells[z-self.displacement[k]].append(k)
        return tuple(sorted((z, k) for z, present in cells.items()
                            for k in self.local_collision(present, inverse=True)))

    def committed_halt(self, particles, base):
        """Exact halt pair at offset zero; the other offsets must be empty."""
        particles = self._lanes(particles, self.channel_count)
        try:
            left = base.type_ids[('L', 0, (base.halt, 0, 0))]
            stationary = base.type_ids[('S', 0)]
        except (AttributeError, KeyError, TypeError) as exc:
            raise ValueError('base must provide committed-halt type IDs') from exc
        wanted = {self.encode_channel(left), self.encode_channel(stationary)}
        if len(wanted) != 2:
            raise ValueError('committed-halt types must be distinct')
        cells = defaultdict(set)
        for z, k in particles:
            cells[z].add(k)
        return any(present == wanted for present in cells.values())
