"""Total exact recognition, or explicit UNKNOWN under user-selected limits.

The complete backend has an exponential, not quasi-polynomial, bound.
A successful short certificate can avoid computing the Khovanov complex.
"""
from __future__ import annotations
from dataclasses import dataclass
from typing import Any
from .diagram import Diagram, InvalidDiagram, braid_closure
from .algebra import fox_determinant
from .khovanov import ResourceLimit, reduced_khovanov


@dataclass(frozen=True)
class RecognitionResult:
    status: str
    method: str
    crossings: int
    evidence: dict[str, Any]

    def as_json(self) -> dict[str, Any]:
        return {
            'status': self.status,
            'method': self.method,
            'crossings': self.crossings,
            'evidence': self.evidence,
            'quasipolynomial_guarantee': False,
            'complete_backend_bound': '2^O(n) bit operations; NOT n^O(log n)',
        }


def parse_input(data: Any) -> Diagram:
    """Accept {"pd": [...]} or {"braid": {"strands": m, "word": [...]}}.

    An optional "description" field is ignored. Arbitrary executable input
    (eval/pickle) is deliberately not supported.
    """
    if not isinstance(data, dict):
        raise InvalidDiagram('The input must be a JSON object')
    kinds = [key for key in ('pd', 'braid') if key in data]
    if len(kinds) != 1:
        raise InvalidDiagram('Specify exactly one of "pd" and "braid"')
    if kinds[0] == 'pd':
        return Diagram.from_pd(data['pd'])
    braid = data['braid']
    if not isinstance(braid, dict) or set(braid) != {'strands', 'word'}:
        raise InvalidDiagram('"braid" must have exactly "strands" and "word" fields')
    if not isinstance(braid['word'], list):
        raise InvalidDiagram('"word" must be a list of integer braid generators')
    try:
        return braid_closure(braid['strands'], braid['word'])
    except ValueError as exc:
        raise InvalidDiagram(str(exc)) from exc


def recognize(diagram: Diagram, *, force_homology: bool = False,
              fast_only: bool = False, check_d_squared: bool = False,
              max_generators: int | None = None,
              max_states: int | None = None) -> RecognitionResult:
    """Decide the unknot exactly, with explicit non-verdicts under resource guards.

    With default arguments this is a total algorithm in the usual unlimited-
    memory mathematical model. It is not a feasible large-diagram solver.
    """
    if force_homology and fast_only:
        raise ValueError('force_homology and fast_only are mutually exclusive')
    for name, limit in [('max_generators', max_generators), ('max_states', max_states)]:
        if limit is not None and (type(limit) is not int or limit < 1):
            raise ValueError(f'{name} must be a positive integer or None')
    n, evidence = diagram.crossings, {}
    if not force_homology:
        start = diagram.descending_start()
        if start is not None:
            return RecognitionResult('unknot', 'descending-diagram', n,
                                     {'starting_incoming_dart': start,
                                      'canonical_pd': diagram.as_json()['pd']})
        determinant = fox_determinant(diagram)
        evidence['determinant'] = determinant
        if determinant != 1:
            return RecognitionResult('knotted', 'Fox-determinant', n, evidence)
        if fast_only:
            evidence['reason'] = 'No fast certificate found; determinant 1 is inconclusive'
            return RecognitionResult('unknown', 'fast-certificates-only', n, evidence)
    try:
        homology = reduced_khovanov(diagram, check_d_squared=check_d_squared,
                                   max_generators=max_generators, max_states=max_states)
    except ResourceLimit as exc:
        evidence['reason'] = str(exc)
        return RecognitionResult('unknown', 'resource-limit', n, evidence)
    evidence['reduced_khovanov'] = homology.as_json()
    return RecognitionResult('unknot' if homology.is_unknot else 'knotted',
                             'reduced-Khovanov-F2', n, evidence)
