"""Optional fastunknot adapter; not integrated or executed against upstream here.

Call only after existing cheap certificates. The caller owns global deadlines,
process limits, restart policy, and its full proof/provenance graph.
"""
from __future__ import annotations
from dataclasses import dataclass
from typing import Any
from cyclic_garside import Budget, LimitExceeded, preprocess, verify, verify_radius

@dataclass
class Proposal:
    status: str
    candidate: Any = None
    evidence: dict | None = None
    reason: str | None = None


def propose(diagram, *, radius: int = 1, max_ticks: int | None = 100000,
            max_targets: int | None = 100000) -> Proposal:
    """Return an independently checked shorter source-derived diagram, or skip.

    Local resource failures skip the probe. Invalid certificates and unexpected
    code errors propagate; they are never treated as an unknot/knot verdict.
    A tick cap is cooperative, NOT a wall-clock or hard memory bound.
    """
    from fastunknot import Diagram  # defer optional upstream dependency
    if not isinstance(diagram, Diagram):
        raise TypeError('expected a validated fastunknot Diagram')
    source = diagram.braid_source
    if source is None:
        return Proposal('skipped', reason='no checked braid-source provenance')
    b, word = source
    try:
        result = preprocess(b, word, radius=radius, max_targets=max_targets,
                            budget=Budget(max_ticks=max_ticks))
        checker = verify if result['certificate']['schema'].endswith('v1') else verify_radius
        output = checker(b, word, result['certificate'])
        if len(output) >= diagram.crossings:
            return Proposal('no-improvement', reason='not shorter than the current simplified diagram')
        candidate = Diagram.from_braid(b, output)
    except (LimitExceeded, MemoryError) as exc:
        return Proposal('skipped', reason=str(exc))
    evidence = {
        'kind': 'source-braid-garside-proposal-v1',
        'original_source': {'strands': b, 'word': list(word)},
        'source_certificate': result['certificate'],
        'candidate_source': {'strands': b, 'word': list(output)},
        'scope': 'closure-preserving source branch; not a concatenated PD move trace',
        'statistics': result['stats'],
    }
    return Proposal('candidate', candidate=candidate, evidence=evidence)
