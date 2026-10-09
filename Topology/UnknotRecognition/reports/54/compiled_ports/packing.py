"""Capacity-aware, carry-free additive encoding of source profiles.
SPDX-License-Identifier: MIT-0
"""
from __future__ import annotations
from .profiles import Profiles, exact_int


class ProfileCodec:
    def __init__(self, lengths, mode='binary'):
        self.lengths = tuple(lengths)
        if any(type(x) is not int or x <= 0 for x in self.lengths):
            raise ValueError('positive atom capacities required')
        if mode not in ('binary', 'mixed'):
            raise ValueError('mode must be binary or mixed')
        self.mode = mode
        self.radices = tuple((1 << x.bit_length()) if mode == 'binary' else x + 1
                             for x in self.lengths)
        unit = 1
        units = []
        for radix in self.radices:
            units.append(unit)
            unit *= radix
        self.units = tuple(units)
        self.limit = unit

    def encode(self, counts):
        if (len(counts) != len(self.lengths)
                or any(type(x) is not int or not 0 <= x <= cap
                       for x, cap in zip(counts, self.lengths))):
            raise ValueError('profile exceeds its atom capacities')
        return sum(x * unit for x, unit in zip(counts, self.units))

    def decode(self, code):
        code = exact_int(code)
        if not 0 <= code < self.limit:
            raise ValueError('packed code is out of range')
        counts = []
        for cap, radix in zip(self.lengths, self.radices):
            code, digit = divmod(code, radix)
            if digit > cap:
                raise ValueError('packed digit exceeds its atom capacity')
            counts.append(digit)
        return tuple(counts)

    def table_from_native_histogram(self, histogram):
        out = {}
        for row in histogram:
            if (not isinstance(row, dict) or set(row) != {'weight', 'orbits'}
                    or not isinstance(row['weight'], (list, tuple)) or len(row['weight']) != 1):
                raise ValueError('expected scalar weighted-orbit histogram')
            a = self.decode(row['weight'][0])
            c = exact_int(row['orbits'])
            if c < 1 or a in out:
                raise ValueError('duplicate profile or nonpositive multiplicity')
            out[a] = c
        return Profiles.from_histogram(self.lengths, out)
