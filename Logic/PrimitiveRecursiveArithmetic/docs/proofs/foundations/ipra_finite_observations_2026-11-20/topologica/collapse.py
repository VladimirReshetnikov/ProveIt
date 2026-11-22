"""Elementary collapse to a vertex, with checkable success or failure evidence.

A face is a nonempty vertex bit mask. A search state is a bit mask selecting
faces from the original s-face table. There are at most 2**s states and s*s
ordered candidates per state. A successful sequence has at most (s-1)//2
steps. Failure concerns collapse by these elementary moves on this complex.
"""
from dataclasses import dataclass
from itertools import combinations


def complex_from_facets(facets):
    faces = set()
    for facet in facets:
        if facet <= 0:
            raise ValueError("facets must be nonempty")
        f = facet
        while f:
            faces.add(f)
            f = (f - 1) & facet
    return frozenset(faces)


def face(*vertices):
    return sum(1 << i for i in set(vertices))


@dataclass(frozen=True)
class Sequence:
    pairs: tuple  # removed (free facet, unique coface) in vertex-bit notation


@dataclass(frozen=True)
class ClosedFamily:
    states: frozenset  # forward-closed family containing the start, no point


class CollapseSearch:
    def __init__(self, source):
        self.faces = sorted(source)
        if any(f <= 0 for f in self.faces) or len(self.faces) != len(set(self.faces)):
            raise ValueError("nonempty faces must be listed once")
        self.index = {f: i for i, f in enumerate(self.faces)}
        for f in self.faces:
            for b in range(f.bit_length()):
                sub = f & ~(1 << b)
                if sub and sub not in self.index:
                    raise ValueError("not downward closed")
        self.start = (1 << len(self.faces)) - 1
        self.above = [sum(1 << j for j, g in enumerate(self.faces)
                          if g != f and (f & g) == f) for f in self.faces]

    def point(self, state):
        return (state.bit_count() == 1 and
                self.faces[state.bit_length() - 1].bit_count() == 1)

    def moves(self, state):
        for i, f in enumerate(self.faces):
            if not (state >> i) & 1:
                continue
            strict = self.above[i] & state
            if strict.bit_count() != 1:
                continue
            j = strict.bit_length() - 1
            g = self.faces[j]
            if g.bit_count() == f.bit_count() + 1:
                yield (f, g), state ^ (1 << i) ^ (1 << j)

    def search(self):
        seen = {self.start: None}
        queue = [self.start]
        for state in queue:
            if self.point(state):
                pairs = []
                while seen[state] is not None:
                    state, pair = seen[state]
                    pairs.append(pair)
                return Sequence(tuple(reversed(pairs)))
            for pair, child in self.moves(state):
                if child not in seen:
                    seen[child] = state, pair
                    queue.append(child)
        return ClosedFamily(frozenset(seen))

    def verify(self, certificate):
        if isinstance(certificate, Sequence):
            current = set(self.faces)
            for f, g in certificate.pairs:
                if f not in current or g not in current or g.bit_count() != f.bit_count() + 1:
                    return False
                if {h for h in current if h != f and (h & f) == f} != {g}:
                    return False
                current.difference_update((f, g))
            return len(current) == 1 and next(iter(current)).bit_count() == 1
        if isinstance(certificate, ClosedFamily):
            states = certificate.states
            return self.start in states and all(
                0 <= state <= self.start and not self.point(state)
                and all(child in states for _, child in self.moves(state)) for state in states)
        return False


def check_examples():
    cover = [complex_from_facets([face(a, b), face(b, c)])
             for a, b, c in [(0, 1, 2), (2, 3, 4), (4, 5, 0)]]
    nerve = set()
    for size in range(1, 4):
        for indices in combinations(range(3), size):
            intersection = frozenset.intersection(*(cover[i] for i in indices))
            if not intersection:
                continue
            nerve.add(face(*indices))
            finder = CollapseSearch(intersection)
            cert = finder.search()
            assert isinstance(cert, Sequence) and finder.verify(cert)
            assert len(cert.pairs) == (2 if size == 1 else 0)
            print(f"intersection {indices}: {len(cert.pairs)} collapses")
    assert nerve == complex_from_facets([face(0, 1), face(1, 2), face(2, 0)])
    cycle = CollapseSearch(frozenset.union(*cover))
    obstruction = cycle.search()
    assert isinstance(obstruction, ClosedFamily) and cycle.verify(obstruction)
    assert len(obstruction.states) == 1
    print("hexagon boundary: exhausted a closed family of 1 state with no point")
    assert not cycle.verify(Sequence(((face(0), face(0, 1)),)))
    assert not cycle.verify(ClosedFamily(frozenset()))
    branched = CollapseSearch(complex_from_facets(
        [face(0, 1, 2), face(2, 3), face(2, 4)]))
    witness = branched.search()
    assert isinstance(witness, Sequence) and branched.verify(witness)
    assert len(witness.pairs) == 5 and any(g.bit_count() == 3 for _, g in witness.pairs)
    assert not branched.verify(ClosedFamily(frozenset({branched.start})))
    print(f"filled triangle and two branches: {len(witness.pairs)} verified collapses")
    print(f"free face / coface masks: {witness.pairs}")


if __name__ == "__main__":
    check_examples()
