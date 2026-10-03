"""Explicit binary mass-five CA compiler; no external code is imported.

State is ordinary occupancy {0,1}.  A finite source ADD/SUB/optional NOP
table fixes every geometric code and hence one fixed CA on the full shift.
This module uses sparse occupancy to evaluate that CA exactly.  See proof.md.
"""
from dataclasses import dataclass
from collections.abc import Mapping
from types import MappingProxyType
from typing import Callable


def natural(value):
    return type(value) is int and value >= 0


def lattice_sites(values):
    """Validate before set conversion, so duplicates and bools are not erased."""
    try:
        sites = tuple(values)
    except TypeError as exc:
        raise ValueError("occupied sites must be a finite iterable") from exc
    if any(type(x) is not int for x in sites):
        raise ValueError("lattice coordinates must be exact integers, not bool/float")
    if len(set(sites)) != len(sites):
        raise ValueError("duplicate occupied coordinates")
    return sites


@dataclass(frozen=True, slots=True)
class Machine:
    rows: Mapping
    entry: str
    halt: str

    def __post_init__(self):
        if not isinstance(self.rows, Mapping):
            raise ValueError("source rows must be a mapping")
        if any(type(q) is not str or not q for q in (self.entry, self.halt)):
            raise ValueError("entry and halt must be nonempty string labels")
        rows = dict(self.rows)
        if any(type(q) is not str or not q for q in rows):
            raise ValueError("source labels must be nonempty strings")
        if self.halt in rows or self.entry not in rows and self.entry != self.halt:
            raise ValueError("bad entry/halt")
        snapshot = {}
        for q, r in rows.items():
            if type(r) not in (list, tuple) or not r or type(r[0]) is not str or r[0] not in ("ADD", "SUB", "NOP"):
                raise ValueError((q, r))
            expected = {"ADD": 3, "SUB": 4, "NOP": 2}[r[0]]
            if len(r) != expected:
                raise ValueError((q, "wrong instruction length"))
            if r[0] == "NOP":
                dst = [r[1]]
            else:
                if type(r[1]) is not int or r[1] not in (0, 1):
                    raise ValueError((q, r))
                dst = r[2:]
            if any(type(t) is not str or not t or t not in rows and t != self.halt for t in dst):
                raise ValueError((q, "undefined destination"))
            snapshot[q] = tuple(r)
        object.__setattr__(self, "rows", MappingProxyType(snapshot))

    def validate_configuration(self, q, a, b):
        if type(q) is not str or q not in self.rows and q != self.halt:
            raise ValueError("unknown source control")
        if not natural(a) or not natural(b):
            raise ValueError("source counters must be exact natural integers")

    def step(self, q, a, b):
        self.validate_configuration(q, a, b)
        if q == self.halt:
            return q, a, b
        r = self.rows[q]
        if r[0] == "NOP":
            return r[1], a, b
        c = [a, b]
        if r[0] == "ADD":
            c[r[1]] += 1
            q = r[2]
        elif c[r[1]]:
            c[r[1]] -= 1
            q = r[2]
        else:
            q = r[3]
        return q, *c


class BinaryCA:
    __slots__ = ('machine', 'states', 'moving', 'codes', 'decode', 'D', 'C',
                 'E', 'K', 'Z', 'radius', '_frozen')

    def __setattr__(self, name, value):
        if getattr(self, "_frozen", False):
            raise AttributeError("a compiled BinaryCA is immutable")
        object.__setattr__(self, name, value)

    def __delattr__(self, name):
        raise AttributeError("a compiled BinaryCA is immutable")

    def __init__(self, machine: Machine):
        if not isinstance(machine, Machine):
            raise ValueError("compiler requires a validated Machine")
        self.machine = machine
        self.states = tuple(sorted(machine.rows)) + (machine.halt,)
        self.moving = tuple(q for q in self.states if q in machine.rows and machine.rows[q][0] != "NOP")
        codes = {}
        for role, states in (("H", self.states), ("O", self.moving), ("I", self.moving)):
            for q in states:
                codes[role, q] = len(codes) + 1
        self.codes = MappingProxyType(codes)
        self.decode = MappingProxyType({d: rq for rq, d in codes.items()})
        self.D = len(self.codes)
        self.C = self.D + 1
        self.E = 2 * self.D + 2
        self.K = 4 * self.D + 5
        self.Z = 4 * self.K
        self.radius = self.Z + 3 * self.K + self.E
        self._frozen = True

    def components(self, occupied):
        out = []
        for x in sorted(lattice_sites(occupied)):
            if not out or x - out[-1][-1] > self.K:
                out.append([x])
            else:
                out[-1].append(x)
        return out

    def direction(self, role, q):
        if type(role) is not str or role not in ("O", "I") or type(q) is not str or q not in self.machine.rows or self.machine.rows[q][0] == "NOP":
            raise ValueError("direction requires a moving packet code")
        sign = -1 if self.machine.rows[q][1] == 0 else 1
        return sign if role == "O" else -sign

    def pair(self, marker, side, gap):
        if type(marker) is not int or type(side) is not int or side not in (-1, 1) or type(gap) is not int or not 1 <= gap <= self.D:
            raise ValueError("invalid packet geometry")
        return {marker + side * self.C, marker + side * (self.C + gap)}

    def rewrite(self, comp, occupied: Callable[[int], bool]):
        """Equal-cardinality component replacement, with read-only context."""
        comp = lattice_sites(comp)
        if not comp or tuple(sorted(comp)) != comp or any(b-a > self.K for a,b in zip(comp,comp[1:])):
            raise ValueError("rewrite requires one sorted nonempty component")
        if not callable(occupied):
            raise ValueError("context must be an occupancy predicate")
        old = set(comp)
        if len(comp) not in (2, 3):
            return old
        if len(comp) == 2:
            d = comp[1] - comp[0]
            if d not in self.decode:
                return old
            role, q = self.decode[d]
            if role == "H":
                return old
            sign = self.direction(role, q)
            return {x + sign for x in comp}
        small = [i for i in (0, 1) if 1 <= comp[i+1] - comp[i] <= self.D]
        if len(small) != 1:
            return old
        j = small[0]
        pair = set(comp[j:j+2])
        marker = comp[2] if j == 0 else comp[0]
        d = max(pair) - min(pair)
        role, q = self.decode[d]
        distance = min(abs(x-marker) for x in pair)
        if not self.C <= distance <= self.K:
            return old
        if role == "H":
            if marker != comp[0] or min(pair) != marker + self.C:
                return old
            if q == self.machine.halt:
                return old
            r = self.machine.rows[q]
            if r[0] == "NOP":
                return {marker} | self.pair(marker, 1, self.codes["H", r[1]])
            sign = -1 if r[1] == 0 else 1
            if r[0] == "SUB":
                sensed = occupied(marker + sign*self.Z)
                if type(sensed) is not bool:
                    raise ValueError("occupancy predicate must return a Boolean")
                if sensed:
                    return {marker} | self.pair(marker, 1, self.codes["H", r[3]])
            return {marker} | self.pair(marker, sign, self.codes["O", q])
        sign = self.direction(role, q)
        behind = marker < min(pair) if sign == 1 else marker > max(pair)
        if behind:
            return {marker} | {x + sign for x in pair}
        if distance != self.K:
            return old
        r = self.machine.rows[q]
        if role == "O":
            delta = 1 if r[0] == "ADD" else -1
            new_marker = marker + sign*delta
            return {new_marker} | self.pair(new_marker, -sign, self.codes["I", q])
        return {marker} | self.pair(marker, 1, self.codes["H", r[2]])

    def step(self, occupied):
        occupied = set(lattice_sites(occupied))
        out = set()
        for comp in self.components(occupied):
            new = self.rewrite(comp, occupied.__contains__)
            assert len(new) == len(comp)
            assert min(new) >= comp[0]-self.E and max(new) <= comp[-1]+self.E
            assert out.isdisjoint(new)
            out.update(new)
        return out

    def local(self, neighborhood):
        """The radius-R Boolean local rule, supplied as occupied offsets.

        Offsets outside [-R,R] are rejected; absence means an exact zero.
        Evaluating on a finite word and reading the center is valid because
        components that can affect the center and their boundary/context
        guards lie wholly inside this window (see locality proof).
        """
        n = set(lattice_sites(neighborhood))
        if any(abs(x) > self.radius for x in n):
            raise ValueError("invalid local neighborhood")
        return int(0 in self.step(n))

    def encode(self, q, a, b):
        self.machine.validate_configuration(q, a, b)
        return {-(self.Z+a), 0, self.Z+b} | self.pair(0, 1, self.codes["H", q])

    def duration(self, q, a, b):
        self.machine.validate_configuration(q, a, b)
        if q == self.machine.halt:
            return 0
        r = self.machine.rows[q]
        if r[0] == "NOP":
            return 1
        c = (a, b)[r[1]]
        if r[0] == "SUB" and c == 0:
            return 1
        delta = 1 if r[0] == "ADD" else -1
        return 3 + 2*(self.Z+c) + delta - 2*self.K - 2*self.C - self.codes["O", q] - self.codes["I", q]

    def halt_pattern(self):
        return tuple(int(i in {0, self.C, self.C+self.codes["H", self.machine.halt]})
                     for i in range(self.C+self.D+1))

    def ledger(self):
        m, p = len(self.states), len(self.moving)
        # Contextual home SUB splits into two guarded rows.
        z = sum(r[0] == "SUB" for r in self.machine.rows.values())
        return dict(alphabet_size=2, mass=5, states=m, moving_states=p,
                    pair_codes=self.D, C=self.C, E=self.E, K=self.K, Z=self.Z,
                    radius=self.radius, truth_table_entries_exponent=2*self.radius+1,
                    free_pair_rows=2*p,
                    departure_triple_rows=2*p*(self.K-self.C+1),
                    contact_triple_rows=2*p,
                    home_guarded_rows=len(self.machine.rows)+z,
                    listed_schema_rows_before_identity_simplification=4*p+2*p*(self.K-self.C+1)+len(self.machine.rows)+z,
                    halt_pattern_length=len(self.halt_pattern()))
