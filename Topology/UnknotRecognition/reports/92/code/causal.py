"""Certified local-version accounting for a fixed acyclic dependency graph.

This is an executable mathematical scheduler model, not a production hierarchy.
Task IDs must be in topological order. Geometry and correctness of dependency
edges are obligations of the caller, not assumptions validated by the model.
"""
from __future__ import annotations
from dataclasses import dataclass
from typing import Sequence


def validate(caps: Sequence[int], parents: Sequence[Sequence[int]]) -> None:
    if len(caps) != len(parents) or any(type(g) is not int or g < 0 for g in caps):
        raise ValueError('nonnegative caps and matching parent lists required')
    for i, ps in enumerate(parents):
        if len(set(ps)) != len(ps) or any(type(j) is not int or j < 0 or j >= i for j in ps):
            raise ValueError('parent IDs must be distinct and earlier than child')


def initial_budget(caps: Sequence[int], initial: Sequence[int] | None = None) -> tuple[int, ...]:
    initial = tuple(caps if initial is None else initial)
    if len(initial) != len(caps) or any(type(d) is not int or d < 0 or d > g for d,g in zip(initial,caps)):
        raise ValueError('initial budgets must be integers between zero and their caps')
    return initial


def path_bounds(caps: Sequence[int], parents: Sequence[Sequence[int]],
                initial: Sequence[int] | None = None) -> tuple[int, ...]:
    validate(caps, parents)
    initial = initial_budget(caps, initial)
    bounds = []
    for d, g, ps in zip(initial, caps, parents):
        bounds.append(d + (g+1)*sum(bounds[j] for j in ps))
    return tuple(bounds)


def dependency_height(parents: Sequence[Sequence[int]]) -> int:
    validate([0]*len(parents), parents)
    heights = []
    for ps in parents:
        heights.append(0 if not ps else 1+max(heights[p] for p in ps))
    return max(heights, default=0)


def path_sum_reference(caps: Sequence[int], parents: Sequence[Sequence[int]],
                       initial: Sequence[int] | None = None) -> tuple[int, ...]:
    """Exponential literal-path oracle, for small tests only."""
    validate(caps, parents)
    initial = initial_budget(caps, initial)
    def visit(i, suffix):
        yield initial[i]*suffix
        for p in parents[i]:
            yield from visit(p, suffix*(caps[i]+1))
    return tuple(sum(visit(i, 1)) for i in range(len(caps)))


def amplification(caps: Sequence[int], parents: Sequence[Sequence[int]],
                  costs: Sequence[int] | None = None) -> tuple[int, ...]:
    """Reverse path sum: weighted total bound is dot(initial, amplification).

    Scores are upper-bound sensitivities, not predictions of actual run times.
    Dependencies and rebuild caps must be kept fixed when comparing budgets.
    """
    validate(caps, parents)
    costs = tuple([1]*len(caps) if costs is None else costs)
    if len(costs) != len(caps) or any(type(c) is not int or c < 0 for c in costs):
        raise ValueError('one nonnegative integer event cost per task required')
    scores = list(costs)
    for j in range(len(caps)-1, -1, -1):
        for i in parents[j]:
            scores[i] += (caps[j]+1)*scores[j]
    return tuple(scores)


@dataclass
class PersistentCounters:
    caps: tuple[int, ...]
    parents: tuple[tuple[int, ...], ...]
    initial: tuple[int, ...] | None = None

    def __post_init__(self):
        validate(self.caps, self.parents)
        self.versions = [0]*len(self.caps)
        self.remaining = list(initial_budget(self.caps, self.initial))
        self.snapshots = [tuple(0 for _ in ps) for ps in self.parents]
        self.events: list[tuple[str, int]] = []

    def clean_flags(self):
        clean = []
        for i, ps in enumerate(self.parents):
            clean.append(all(clean[p] for p in ps) and
                         self.snapshots[i] == tuple(self.versions[p] for p in ps))
        return clean

    def legal_events(self):
        clean = self.clean_flags()
        result = []
        for i, ps in enumerate(self.parents):
            if clean[i] and self.remaining[i] > 0:
                result.append(('repair', i))
            elif not clean[i] and all(clean[p] for p in ps):
                result.append(('rebuild', i))
        return result

    def apply(self, op: str, task: int):
        if (op, task) not in self.legal_events():
            raise ValueError('illegal, redundant, stale, or exhausted event')
        if op == 'repair':
            self.remaining[task] -= 1
        else:
            self.remaining[task] = self.caps[task]
            self.snapshots[task] = tuple(self.versions[p] for p in self.parents[task])
        self.versions[task] += 1
        self.events.append((op, task))

    def finish(self, limit: int = 100000, prefer_later: bool = True):
        for _ in range(limit):
            legal = self.legal_events()
            if not legal:
                return self
            event = max(legal, key=lambda e: e[1]) if prefer_later else legal[0]
            self.apply(*event)
        if self.legal_events():
            raise RuntimeError('trace limit reached; no completion claimed')
        return self


@dataclass(frozen=True)
class Range:
    """Authenticated callers may use these half-open source-support ranges."""
    namespace: str
    lo: int
    hi: int

    def __post_init__(self):
        if not isinstance(self.namespace, str) or not self.namespace or type(self.lo) is not int or type(self.hi) is not int or self.lo < 0 or self.hi <= self.lo:
            raise ValueError('nonempty named half-open interval required')


def supports_overlap(first: Sequence[Range], second: Sequence[Range]) -> bool:
    # Conservative exact test in the caller's common source namespace.
    return any(a.namespace == b.namespace and max(a.lo,b.lo) < min(a.hi,b.hi)
               for a in first for b in second)


def invalidate(writes: Sequence[Range], reads: Sequence[Sequence[Range]]) -> tuple[int, ...]:
    """Read sets must include witness loops AND all used incidence/chart records."""
    return tuple(i for i, support in enumerate(reads) if supports_overlap(writes, support))


def causal_potential(caps: Sequence[int], parents: Sequence[Sequence[int]],
                     remaining: Sequence[int], versions: Sequence[int],
                     snapshots: Sequence[Sequence[int]],
                     costs: Sequence[int] | None = None) -> int:
    """Nonnegative amortized potential including unobserved parent versions.

    Each legal event lowers this quantity by at least its charged event cost.
    Computing this value does not authenticate the underlying geometry.
    """
    validate(caps, parents)
    remaining=initial_budget(caps,remaining)
    n=len(caps)
    if len(versions)!=n or len(snapshots)!=n or any(type(v) is not int or v<0 for v in versions):
        raise ValueError('invalid version or snapshot dimensions')
    a=amplification(caps,parents,costs)
    total=0
    for i,ps in enumerate(parents):
        if len(snapshots[i])!=len(ps):
            raise ValueError('snapshot must contain every direct parent')
        pending=0
        for j,s in zip(ps,snapshots[i]):
            if type(s) is not int or s<0 or s>versions[j]:
                raise ValueError('snapshot version is outside the observed history')
            pending+=versions[j]-s
        total+=a[i]*(remaining[i]+(caps[i]+1)*pending)
    return total
