"""Exact singleton-cut kernels for explicit Artin braid knot closures.

This module does not search over braid representatives.  It preserves closures,
not equality in the original braid group.  A CORE status is not a verdict.
"""
from __future__ import annotations
from dataclasses import dataclass
from bisect import bisect_right
from typing import Iterable


@dataclass(frozen=True)
class Braid:
    strands: int
    word: tuple[int, ...]

    @classmethod
    def checked(cls, strands: int, word: Iterable[int]) -> 'Braid':
        if type(strands) is not int or strands < 1:
            raise ValueError('strands must be a positive integer')
        word = tuple(word)
        if strands > len(word) + 1:
            raise ValueError('too few letters for a knot closure')
        p = list(range(strands))
        for g in word:
            if type(g) is not int or not 1 <= abs(g) < strands:
                raise ValueError('invalid Artin generator')
            j = abs(g) - 1
            p[j], p[j+1] = p[j+1], p[j]
        visited = [False]*strands
        j = length = 0
        while not visited[j]:
            visited[j] = True
            length += 1
            j = p[j]
        if length != strands:
            raise ValueError('closure is a link, not a knot')
        return cls(strands, word)

    @property
    def exponent(self) -> int:
        return sum(1 if g > 0 else -1 for g in self.word)

    @property
    def minority(self) -> int:
        return (len(self.word) - abs(self.exponent)) // 2

    @property
    def canonical_genus(self) -> int:
        return (len(self.word) - self.strands + 1) // 2

    def to_json(self) -> dict:
        return {'strands': self.strands, 'word': list(self.word)}


def singleton_certificate(braid: Braid) -> dict:
    """Linear word-RAM production, including every singleton cut.

    Factor intervals use 0-based strand indices [start, stop).  The generator
    a separates strands a-1 and a.  Positions in cuts are 0-based word indices.
    """
    braid = Braid.checked(braid.strands, braid.word)
    b, w = braid.strands, braid.word
    counts, positions = [0]*b, [-1]*b
    for p, g in enumerate(w):
        counts[abs(g)] += 1
        positions[abs(g)] = p
    cuts = [a for a in range(1, b) if counts[a] == 1]
    boundaries = [0] + cuts + [b]
    owner = [-1]*b
    factors = []
    for j, (lo, hi) in enumerate(zip(boundaries, boundaries[1:])):
        factors.append({'start': lo, 'stop': hi, 'strands': hi-lo, 'word': []})
        for a in range(lo+1, hi):
            owner[a] = j
    for g in w:
        j = owner[abs(g)]
        if j >= 0:
            lo = factors[j]['start']
            factors[j]['word'].append((1 if g > 0 else -1)*(abs(g)-lo))
    return {'schema': 'artin-singleton-cuts-v1', 'input_strands': b,
            'input_length': len(w),
            'cuts': [{'generator': a, 'position': positions[a],
                      'letter': w[positions[a]]} for a in cuts],
            'factors': factors}


def verify_certificate(braid: Braid, certificate: dict) -> tuple[Braid, ...]:
    """Independent replay; no producer call, no digest trusted as proof.

    Uses occurrence lists and binary search rather than the producer's owner
    table.  Completeness of the singleton set is checked, not only soundness.
    """
    braid = Braid.checked(braid.strands, braid.word)
    if not isinstance(certificate, dict):
        raise ValueError('certificate must be a dictionary')
    if certificate.get('schema') != 'artin-singleton-cuts-v1':
        raise ValueError('unknown certificate schema')
    if certificate.get('input_strands') != braid.strands or certificate.get('input_length') != len(braid.word):
        raise ValueError('wrong input dimensions')
    occurrences: list[list[int]] = [[] for _ in range(braid.strands)]
    for p, g in enumerate(braid.word):
        occurrences[abs(g)].append(p)
    cuts = [a for a in range(1, braid.strands) if len(occurrences[a]) == 1]
    expected = [{'generator': a, 'position': occurrences[a][0],
                 'letter': braid.word[occurrences[a][0]]} for a in cuts]
    if certificate.get('cuts') != expected:
        raise ValueError('cuts are invalid or incomplete')
    boundaries = [0] + cuts + [braid.strands]
    projections = [[] for _ in range(len(boundaries)-1)]
    is_cut = [False]*braid.strands
    for a in cuts:
        is_cut[a] = True
    for g in braid.word:
        a = abs(g)
        if is_cut[a]:
            continue
        j = bisect_right(boundaries, a)-1
        projections[j].append((1 if g > 0 else -1)*(a-boundaries[j]))
    claimed = certificate.get('factors')
    if not isinstance(claimed, list) or len(claimed) != len(projections):
        raise ValueError('wrong factor list')
    result = []
    for j, word in enumerate(projections):
        lo, hi = boundaries[j:j+2]
        record = {'start': lo, 'stop': hi, 'strands': hi-lo, 'word': word}
        if claimed[j] != record:
            raise ValueError('factor does not match its source projection')
        factor = Braid.checked(hi-lo, word)
        local_counts = [0]*factor.strands
        for g in word:
            local_counts[abs(g)] += 1
        if any(v < 2 for v in local_counts[1:]):
            raise ValueError('a core factor still has a singleton')
        result.append(factor)
    if sum(len(x.word) for x in result) + len(cuts) != len(braid.word):
        raise ValueError('letter accounting failed')
    if sum(x.canonical_genus for x in result) != braid.canonical_genus:
        raise ValueError('genus accounting failed')
    return tuple(result)


def connected_sum_braid(factors: Iterable[Braid]) -> Braid:
    """Closure-preserving connected sum with one shared strand, no new letters."""
    offset, word = 0, []
    for factor in factors:
        factor = Braid.checked(factor.strands, factor.word)
        word.extend((1 if g > 0 else -1)*(abs(g)+offset) for g in factor.word)
        offset += factor.strands-1
    return Braid.checked(offset+1, word)


def kernelize(braid: Braid, *, verify: bool = True) -> dict:
    """Return KNOTTED, UNKNOT, or a certified CORE, never a guessed verdict."""
    braid = Braid.checked(braid.strands, braid.word)
    certificate = singleton_certificate(braid)
    if verify:
        factors = verify_certificate(braid, certificate)
    else:
        factors = tuple(Braid.checked(f['strands'], f['word']) for f in certificate['factors'])
    nonempty = tuple(f for f in factors if f.word)
    failures = [j for j, f in enumerate(nonempty) if abs(f.exponent) > f.strands-1]
    stats = {'input_letters': len(braid.word), 'input_strands': braid.strands,
             'input_minority': braid.minority, 'input_canonical_genus': braid.canonical_genus,
             'singleton_cuts': len(certificate['cuts']),
             'nonempty_factors': len(nonempty), 'core_letters': sum(len(f.word) for f in nonempty),
             'core_minority_sum': sum(f.minority for f in nonempty),
             'core_minority_max': max((f.minority for f in nonempty), default=0),
             'core_genus_max': max((f.canonical_genus for f in nonempty), default=0)}
    out = {'status': 'CORE', 'method': 'singleton-cut-kernel', 'certificate': certificate,
           'factors': [f.to_json() for f in nonempty], 'stats': stats,
           'general_quasipolynomial_guarantee': False}
    if failures:
        j = failures[0]
        f = nonempty[j]
        out.update(status='KNOTTED', method='factor-bennequin',
                   obstruction={'factor': j, 'exponent_sum': f.exponent,
                                'bound_for_unknot': f.strands-1})
    elif not nonempty:
        out.update(status='UNKNOT', method='singleton-tree')
        out['merged_kernel'] = Braid.checked(1, []).to_json()
    else:
        merged = connected_sum_braid(nonempty)
        out['merged_kernel'] = merged.to_json()
        if len(merged.word) > 4*stats['core_minority_sum']:
            raise ArithmeticError('minority kernel bound failed')
        if merged.strands > 2*stats['core_minority_sum']+1:
            raise ArithmeticError('strand kernel bound failed')
    if stats['core_letters'] > 4*braid.canonical_genus:
        raise ArithmeticError('genus kernel bound failed')
    return out
