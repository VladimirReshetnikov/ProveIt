"""Finite reference algorithms for the iPRA complexity report.

The algorithms expose finite bounds. They are executable mathematical models,
not proofs that this Python implementation has Turing-machine space O(log N)
or that the theorems have been derived in iPRA. In particular, the transcript
objects and the independent Floyd-Warshall oracle are deliberately materialized.
All nondeterministic choices in the counting construction are supplied as a
finite transcript and then checked deterministically.
"""
from __future__ import annotations

from dataclasses import dataclass
from itertools import product
from typing import Optional


@dataclass(frozen=True)
class Graph:
    """An N-vertex directed graph, including optional loops, in N*N bits."""

    n: int
    mask: int

    def __post_init__(self) -> None:
        if self.n < 1:
            raise ValueError("the vertex set must be nonempty")
        if not 0 <= self.mask < (1 << (self.n * self.n)):
            raise ValueError("adjacency mask is outside its declared bit width")

    def edge(self, u: int, v: int) -> bool:
        return (
            0 <= u < self.n
            and 0 <= v < self.n
            and bool((self.mask >> (u * self.n + v)) & 1)
        )

    def vertex(self, u: int) -> None:
        if not 0 <= u < self.n:
            raise ValueError("vertex outside graph")


def closure(graph: Graph) -> tuple[tuple[bool, ...], ...]:
    """Independent reflexive transitive closure by Floyd-Warshall."""
    r = [[u == v or graph.edge(u, v) for v in range(graph.n)]
         for u in range(graph.n)]
    for k in range(graph.n):
        for u in range(graph.n):
            for v in range(graph.n):
                r[u][v] = r[u][v] or (r[u][k] and r[k][v])
    return tuple(tuple(row) for row in r)


def linear_reach(graph: Graph, source: int, steps: int) -> tuple[bool, ...]:
    """Vertices reachable in at most the declared number of steps."""
    graph.vertex(source)
    if steps < 0:
        raise ValueError("negative step bound")
    r = tuple(v == source for v in range(graph.n))
    for _ in range(steps):
        r = tuple(
            r[v] or any(r[u] and graph.edge(u, v) for u in range(graph.n))
            for v in range(graph.n)
        )
    return r


@dataclass
class SavitchStats:
    nodes: int = 0
    max_frames: int = 0


def savitch_node_bound(n: int, level: int) -> int:
    if n < 1 or level < 0:
        raise ValueError("invalid recurrence parameters")
    return (2 * n + 1) ** (level + 1)


def savitch(graph: Graph, source: int, target: int,
            level: Optional[int] = None,
            stats: Optional[SavitchStats] = None) -> bool:
    """Depth-first H_j; no memoization and no full reachability table.

    H_0 is equality-or-edge. H_(j+1) tries all midpoints and recursively
    checks both halves. The default j=ceil(log2 N) is enough for reachability.
    """
    graph.vertex(source)
    graph.vertex(target)
    if level is None:
        level = (graph.n - 1).bit_length()
    if level < 0:
        raise ValueError("negative level")
    if stats is None:
        stats = SavitchStats()

    def visit(a: int, b: int, j: int, frames: int) -> bool:
        stats.nodes += 1
        stats.max_frames = max(stats.max_frames, frames)
        if j == 0:
            return a == b or graph.edge(a, b)
        for mid in range(graph.n):
            if visit(a, mid, j - 1, frames + 1):
                if visit(mid, b, j - 1, frames + 1):
                    return True
        return False

    return visit(source, target, level, 1)


Path = tuple[int, ...]


def valid_path(graph: Graph, source: int, target: int,
               max_steps: int, path: Path) -> bool:
    if not isinstance(path, tuple) or not path:
        return False
    if len(path) > max_steps + 1:
        return False
    if path[0] != source or path[-1] != target:
        return False
    if any(not isinstance(v, int) or not 0 <= v < graph.n for v in path):
        return False
    return all(graph.edge(u, v) for u, v in zip(path, path[1:]))


def least_path(graph: Graph, source: int, target: int,
               max_steps: int) -> Optional[Path]:
    """Literal bounded search, by length and then lexicographic interiors.

    The search inspects at most sum(N**r for r in range(max_steps+1))
    candidates. Its cost is irrelevant to the small-space branch verifier;
    it is a concrete primitive-recursive-style witness constructor.
    """
    graph.vertex(source)
    graph.vertex(target)
    if max_steps < 0:
        raise ValueError("negative path bound")
    if source == target:
        return (source,)
    for length in range(1, max_steps + 1):
        for interior in product(range(graph.n), repeat=length - 1):
            path = (source,) + interior + (target,)
            if valid_path(graph, source, target, max_steps, path):
                return path
    return None


@dataclass(frozen=True)
class EnumerationTranscript:
    """Entry u is None (not marked), or a checked path witnessing the mark."""

    entries: tuple[Optional[Path], ...]


@dataclass(frozen=True)
class CountRound:
    """One fresh exact enumeration for each prospective next-layer target."""

    targets: tuple[EnumerationTranscript, ...]


@dataclass(frozen=True)
class NonReachTranscript:
    rounds: tuple[CountRound, ...]
    final: EnumerationTranscript


def verify_enumeration(graph: Graph, source: int, depth: int,
                       expected_count: int, target: int,
                       transcript: EnumerationTranscript,
                       successor_query: bool) -> tuple[bool, bool]:
    """Return (accepted transcript, hit bit).

    A successor query computes source==target OR existence of a marked
    predecessor. A direct query computes whether target itself was marked.
    The returned bit is semantically reliable only if accepted is True
    and the supplied expected count really is the reachable-set size.
    """
    if not 0 <= source < graph.n or not 0 <= target < graph.n:
        return False, False
    if not isinstance(transcript, EnumerationTranscript):
        return False, False
    if not isinstance(transcript.entries, tuple) or len(transcript.entries) != graph.n:
        return False, False
    if not 0 <= expected_count <= graph.n or not 0 <= depth < graph.n:
        return False, False
    count = 0
    hit = successor_query and target == source
    for vertex, path in enumerate(transcript.entries):
        if path is None:
            continue
        if not valid_path(graph, source, vertex, depth, path):
            return False, False
        count += 1
        if successor_query:
            hit = hit or graph.edge(vertex, target)
        else:
            hit = hit or vertex == target
    if count != expected_count:
        return False, False
    return True, hit


def verify_nonreach(graph: Graph, source: int, target: int,
                    transcript: NonReachTranscript) -> bool:
    """Deterministically verify a proposed inductive-counting branch.

    A valid accepting transcript exists exactly when target is unreachable.
    This reference representation stores the full transcript. The theoretical
    nondeterministic machine streams its choices and retains O(log N) bits.
    """
    graph.vertex(source)
    graph.vertex(target)
    if not isinstance(transcript, NonReachTranscript):
        return False
    if not isinstance(transcript.rounds, tuple) or len(transcript.rounds) != graph.n - 1:
        return False
    count = 1
    for depth, round_ in enumerate(transcript.rounds):
        if not isinstance(round_, CountRound):
            return False
        if not isinstance(round_.targets, tuple) or len(round_.targets) != graph.n:
            return False
        next_count = 0
        for vertex, enumeration in enumerate(round_.targets):
            ok, hit = verify_enumeration(
                graph, source, depth, count, vertex, enumeration, True
            )
            if not ok:
                return False
            next_count += int(hit)
        count = next_count
    ok, hit = verify_enumeration(
        graph, source, graph.n - 1, count, target, transcript.final, False
    )
    return ok and not hit


def canonical_nonreach_transcript(graph: Graph, source: int) -> NonReachTranscript:
    """A bounded-search canonical transcript, generated even for yes targets.

    This depends only on the graph and source. Its final verification accepts
    each target that is not reachable, and rejects each reachable target.
    """
    graph.vertex(source)

    def enumeration(depth: int) -> EnumerationTranscript:
        return EnumerationTranscript(tuple(
            least_path(graph, source, v, depth) for v in range(graph.n)
        ))

    rounds = tuple(
        CountRound(tuple(enumeration(depth) for _ in range(graph.n)))
        for depth in range(graph.n - 1)
    )
    return NonReachTranscript(rounds, enumeration(graph.n - 1))


def transcript_bit_bound(n: int) -> int:
    """A fixed-width PR upper bound for a serialized bounded transcript.

    Each vertex entry uses one mark bit, a length field, and N vertex fields.
    Padding makes all transcripts have a common bound and enables bounded
    quantification over transcript codes in the arithmetic proof.
    """
    if n < 1:
        raise ValueError("empty graph")
    width = (n + 1).bit_length()
    enumeration_count = n * (n - 1) + 1
    return enumeration_count * n * (1 + width + n * width)
