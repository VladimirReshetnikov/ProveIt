"""Finite source-atom profiles. No implicit expansion of orbit multiplicities.

A validated table is an algebraically valid census, not automatically a
certificate for a particular interval-pairing source. See native.py.
SPDX-License-Identifier: MIT-0
"""
from __future__ import annotations
from dataclasses import dataclass
from collections import defaultdict
from collections.abc import Iterable, Sequence
import re


def exact_int(value: object) -> int:
    if type(value) is int:
        return value
    if isinstance(value, str) and re.fullmatch(r'[+-]?0[xX][0-9a-fA-F]+', value):
        return int(value, 16)
    raise ValueError('expected an exact integer or hexadecimal string')


def json_safe(value):
    """Encode large integers without changing Python's global decimal limit."""
    if type(value) is int:
        return hex(value) if value.bit_length() > 1024 else value
    if isinstance(value, (list, tuple)):
        return [json_safe(x) for x in value]
    if isinstance(value, dict):
        return {k: json_safe(v) for k, v in value.items()}
    return value


@dataclass(frozen=True)
class ProfileRow:
    counts: tuple[int, ...]
    multiplicity: int


@dataclass(frozen=True)
class Profiles:
    lengths: tuple[int, ...]
    rows: tuple[ProfileRow, ...]

    def __post_init__(self):
        if type(self.lengths) is not tuple or type(self.rows) is not tuple:
            raise ValueError('lengths and rows must be immutable tuples')
        m = len(self.lengths)
        if any(type(x) is not int or x <= 0 for x in self.lengths):
            raise ValueError('atoms must have positive integer length')
        mass = [0] * m
        previous = None
        for row in self.rows:
            if not isinstance(row, ProfileRow) or type(row.counts) is not tuple:
                raise ValueError('malformed profile row')
            if (len(row.counts) != m or not any(row.counts)
                    or any(type(x) is not int or x < 0 for x in row.counts)
                    or type(row.multiplicity) is not int or row.multiplicity < 1):
                raise ValueError('profiles are nonzero, nonnegative, with positive multiplicity')
            if previous is not None and row.counts <= previous:
                raise ValueError('profiles must be sorted and unique')
            for j, x in enumerate(row.counts):
                mass[j] += x * row.multiplicity
            previous = row.counts
        if tuple(mass) != self.lengths:
            raise ValueError('per-atom mass does not match the source partition')

    @classmethod
    def from_histogram(cls, lengths: Sequence[int], histogram: dict[tuple[int, ...], int]):
        return cls(tuple(lengths), tuple(ProfileRow(tuple(a), c)
                    for a, c in sorted(histogram.items()) if c))

    @classmethod
    def from_dict(cls, data: dict):
        if not isinstance(data, dict) or set(data) != {'lengths', 'rows'}:
            raise ValueError('malformed profile table')
        rows = []
        for record in data['rows']:
            if not isinstance(record, dict) or set(record) != {'counts', 'multiplicity'}:
                raise ValueError('malformed profile row')
            rows.append(ProfileRow(tuple(exact_int(x) for x in record['counts']),
                                   exact_int(record['multiplicity'])))
        return cls(tuple(exact_int(x) for x in data['lengths']), tuple(rows))

    def to_dict(self):
        return {'lengths': list(self.lengths), 'rows': [
            {'counts': list(row.counts), 'multiplicity': row.multiplicity}
            for row in self.rows]}

    @property
    def size(self):
        return sum(self.lengths)

    @property
    def orbit_count(self):
        return sum(row.multiplicity for row in self.rows)

    @property
    def edges(self):
        return sum(sum(x > 0 for x in row.counts) for row in self.rows)

    def observe(self, weights: Sequence[Sequence[int]]) -> dict[tuple[int, ...], int]:
        """Histogram of additive observations constant on each source atom."""
        if len(weights) != len(self.lengths):
            raise ValueError('one weight vector per atom is required')
        d = len(weights[0]) if weights else 0
        if any(len(v) != d or any(type(x) is not int for x in v) for v in weights):
            raise ValueError('weight vectors must have a common dimension and exact integers')
        out = defaultdict(int)
        for row in self.rows:
            value = tuple(sum(row.counts[j] * weights[j][i]
                              for j in range(len(weights))) for i in range(d))
            out[value] += row.multiplicity
        return dict(sorted(out.items()))


def cuts_and_lengths(size: int, cuts: Iterable[int]):
    if type(size) is not int or size < 0:
        raise ValueError('size must be a nonnegative integer')
    cuts = tuple(cuts)
    if (not cuts or any(type(x) is not int for x in cuts)
            or cuts[0] != 0 or cuts[-1] != size
            or any(a >= b for a, b in zip(cuts, cuts[1:]))):
        raise ValueError('cuts must strictly partition [0,size), or be (0,) for size zero')
    return cuts, tuple(b - a for a, b in zip(cuts, cuts[1:]))
