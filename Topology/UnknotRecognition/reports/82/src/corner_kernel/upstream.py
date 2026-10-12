"""Optional adapter to ProveIt's existing count_orbits API. MIT-0.

Source contract inspected at ed166080d7db14dd7a91d07788996f02947dd92a.
This adapter is not dispatched by recognize. It requires source-constructed
V/R/F systems; that geometry adapter is not supplied in this research package.
"""
from dataclasses import dataclass, field
from .compiler import Incomplete


@dataclass
class SharedBudget:
    max_cycles: int | None = None
    max_queries: int | None = None
    cycles: int = 0
    queries: int = 0
    proofs: list = field(default_factory=list)

    def __post_init__(self):
        for x in (self.max_cycles, self.max_queries):
            if x is not None and (type(x) is not int or x < 0):
                raise ValueError('invalid budget')


def upstream_oracle(size, pairings, budget=None, *, record_certificate=True,
                    check=None):
    """Factory with shared cumulative caps and no partial-result coercion."""
    from fastunknot.interval_orbits import IntervalPairing, count_orbits
    budget = budget if budget is not None else SharedBudget()
    pairs = tuple(pairings)
    poll = check if check is not None else (lambda: None)
    def count(extra=()):
        poll()
        if budget.max_queries is not None and budget.queries >= budget.max_queries:
            raise Incomplete('shared upstream query cap exhausted')
        rest = None if budget.max_cycles is None else budget.max_cycles-budget.cycles
        augmented = pairs + tuple(IntervalPairing(x, x, y, y) for x, y in extra)
        result = count_orbits(size, augmented, max_cycles=rest, check=poll,
                              record_certificate=record_certificate)
        budget.queries += 1
        budget.cycles += result.cycles
        if not result.complete:
            raise Incomplete('shared upstream AHT cycle cap exhausted')
        if record_certificate:
            budget.proofs.append({'extra': tuple(extra), 'count': result.orbits,
                                  'certificate': result.certificate})
        return result.orbits
    return count
