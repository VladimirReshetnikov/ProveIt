"""Bounded, independently replayed source-braid proposals for recognition."""
from dataclasses import dataclass
from time import monotonic

from .diagram import Diagram
from .cyclic_garside import Budget, LimitExceeded, preprocess, verify, verify_radius


@dataclass
class Proposal:
    candidate: Diagram | None
    evidence: dict


def propose(original, current_crossings, *, radius=1, seconds=0.1,
            max_ticks=100000, max_targets=100000, check=lambda: None):
    """Build a shorter checked source branch within local and global allowances.

    The host validates options before early recognition certificates. This
    internal adapter consumes the original Diagram's checked braid source and
    compares against the current simplified PD size. It returns no knot verdict.
    A local limit preserves the host's current diagram; global limits propagate.
    """
    check()
    source = original.braid_source
    if source is None:
        return Proposal(None, dict(status='skipped', reason='no checked braid source'))
    strands, word = source
    start = monotonic()
    local_deadline = None if seconds is None else start + seconds

    def probe_check():
        check()
        if local_deadline is not None and monotonic() >= local_deadline:
            raise LimitExceeded('Garside local time allowance exhausted')

    budget = Budget(max_ticks=max_ticks, hook=probe_check)
    try:
        budget.check()
        result = preprocess(strands, word, radius=radius, max_targets=max_targets,
                            budget=budget)
        checker = verify if result['certificate']['schema'] == 'cyclic-garside-kernel-v1' else verify_radius
        output = checker(strands, word, result['certificate'], check=budget.check)
        budget.check()
        used = len(output) < current_crossings
        candidate = Diagram.from_braid(strands, output) if used else None
        budget.check()
    except (LimitExceeded, MemoryError) as exc:
        check()  # A global expiry never becomes a local fallback.
        return Proposal(None, dict(status='skipped', reason=str(exc) or 'memory allocation failed',
                                   ticks=budget.ticks, seconds=monotonic()-start))
    evidence = dict(status='verified', source_strands=strands, source_word=list(word),
                    certificate=result['certificate'], statistics=result['stats'],
                    candidate_word=list(output), current_crossings=current_crossings,
                    used=used, ticks=budget.ticks, seconds=monotonic()-start,
                    scope='closure-preserving source branch; separate from the PD move trace')
    check()
    return Proposal(candidate, evidence)
