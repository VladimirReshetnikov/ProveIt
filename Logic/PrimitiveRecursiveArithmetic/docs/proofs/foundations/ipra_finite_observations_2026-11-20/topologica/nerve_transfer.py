"""Finite homological nerve comparison over F2. Python 3.10+, standard library."""
from itertools import combinations
from functools import reduce
from operator import xor


def bits(mask):
    return [j for j in range(mask.bit_length()) if mask & (1 << j)]


def mask(*vertices):
    return sum(1 << j for j in set(vertices))


def subsets(face):
    vertices = bits(face)
    for size in range(1, len(vertices) + 1):
        for choice in combinations(vertices, size):
            yield mask(*choice)


def complex_of(*facets):
    return {s for f in facets for s in subsets(f)}


def boundary(simplex):
    return {simplex ^ (1 << j) for j in bits(simplex)}


def parity_sum(rows):
    return reduce(xor, rows, set())


class Filler:
    """Boundary reduction and a preimage for each pivot row."""
    def __init__(self, domain):
        self.rows = {}
        for simplex in sorted(domain):
            residue, used = self.reduce(boundary(simplex))
            if residue:
                lead = max(residue)
                self.rows[lead] = residue, used ^ {simplex}

    def reduce(self, vector):
        residue, used = set(vector), set()
        for lead in sorted(self.rows, reverse=True):
            if lead in residue:
                row, preimage = self.rows[lead]
                residue ^= row
                used ^= preimage
        return residue, used


def contract(complex_):
    """Return a linear augmented contraction or a cycle and dual obstruction."""
    simplex_set = set(complex_) | {0}
    contraction = {}
    ranks = max(s.bit_count() for s in simplex_set)
    for rank in range(ranks + 1):
        target = [s for s in simplex_set if s.bit_count() == rank]
        domain = [s for s in simplex_set if s.bit_count() == rank + 1]
        fillers = Filler(domain)
        for s in sorted(target):
            z = {s} ^ parity_sum(contraction[t] for t in boundary(s))
            residue, preimage = fillers.reduce(z)
            if residue:
                coord = min(residue)
                dual = {t for t in target if coord in fillers.reduce({t})[0]}
                assert not parity_sum(boundary(t) for t in z)
                assert len(z & dual) % 2 == 1
                assert all(len(boundary(t) & dual) % 2 == 0 for t in domain)
                return None, (z, dual)
            contraction[s] = preimage
            assert parity_sum(boundary(t) for t in preimage) == z
    return contraction, None


class Cover:
    def __init__(self, space, members):
        self.space = set(space)
        self.members = [set(member) for member in members]
        if any(not s or not (boundary(s) - {0}) <= part
               for part in [self.space] + self.members for s in part):
            raise ValueError("expected a complex of nonempty simplices")
        if set().union(*self.members) != self.space:
            raise ValueError("members must cover the entire complex")
        self.intersections = {}
        self.contractions = {}
        for index in range(1, 1 << len(self.members)):
            common = set.intersection(*(self.members[i] for i in bits(index)))
            if common:
                self.intersections[index] = common
                contraction, failure = contract(common)
                if failure is not None:
                    raise ValueError(f"intersection {index}, cycle and dual {failure}")
                self.contractions[index] = contraction

    def augmented_boundary(self, vector, side):
        def faces(index, simplex):
            from_index = {(i, simplex) for i in boundary(index) if i or side == "space"}
            from_simplex = {(index, s) for s in boundary(simplex) if s or side == "nerve"}
            return from_index ^ from_simplex
        return parity_sum(faces(i, s) for i, s in vector)

    def fill_augmented(self, cycle, side):
        if self.augmented_boundary(cycle, side):
            raise ValueError("input must be a cycle")
        current, filler = set(cycle), set()
        # rank 1 represents dimension 0 on the unaugmented axis
        max_rank = (len(self.members) if side == "nerve"
                    else max((s.bit_count() for s in self.space), default=0))
        for rank in range(max_rank, 0, -1):
            lifted = set()
            for i, s in current:
                if side == "nerve" and i.bit_count() == rank:
                    lifted ^= {(i, t) for t in self.contractions[i][s]}
                if side == "space" and s.bit_count() == rank:
                    apex = next(j for j, member in enumerate(self.members) if s in member)
                    if not (i & (1 << apex)):
                        lifted ^= {(i | (1 << apex), s)}
            current ^= self.augmented_boundary(lifted, side)
            filler ^= lifted
        assert not current
        assert self.augmented_boundary(filler, side) == cycle
        return filler

    def transfer(self, cycle, source):
        if source not in {"space", "nerve"}:
            raise ValueError("source must be space or nerve")
        source_simplices = self.space if source == "space" else self.intersections.keys()
        if any(s not in source_simplices for s in cycle):
            raise ValueError("unknown simplex")
        terminal = {(0, s) if source == "space" else (s, 0) for s in cycle}
        filler = self.fill_augmented(terminal, source)
        total_chain = {(i, s) for i, s in filler if i and s}
        if source == "space":
            return parity_sum({i} for i, s in total_chain if s.bit_count() == 1)
        return parity_sum({s} for i, s in total_chain if i.bit_count() == 1)


def demo():
    edges = [mask(i, (i+1) % 6) for i in range(6)]
    circle = complex_of(*edges)
    members = [complex_of(edges[i], edges[i+1]) for i in (0, 2, 4)]
    cover = Cover(circle, members)
    triangle = {mask(0, 1), mask(1, 2), mask(0, 2)}
    assert cover.transfer(set(edges), "space") == triangle
    assert cover.transfer(triangle, "nerve") == set(edges)
    print("The six-edge cycle transfers to the three-edge nerve cycle and back.")
    failure = contract(circle)[1]
    assert failure and failure[0] == set(edges)
    print(f"One-member cover fails: cycle has {len(failure[0])} edges; "
          f"dual has {len(failure[1])} edge(s).")
    # Test a filled triangle. Two cycle representatives may differ by a boundary.
    disk = complex_of(mask(0, 1, 2))
    one = Cover(disk, [disk])
    assert one.transfer(triangle, "space") == set()
    assert one.transfer({mask(1)}, "space") == {mask(0)}
    twice = one.transfer(one.transfer({mask(1)}, "space"), "nerve")
    assert not Filler([s for s in disk if s.bit_count() == 2]).reduce(twice ^ {mask(1)})[0]
    print("Filled triangle, H0 representative, and boundary reflection checks pass.")


if __name__ == "__main__":
    demo()
