"""Exact gluing equivalence for regular cyclic and dihedral surface covers.

Each block is a connected regular cover with fibre the GROUP C_m or D_m
(respectively m or 2m sheets). Monodromy acts on the left. Each edge glues
the entire preimage of two compatible base boundary circles by a right
multiplication, over a boundary-orientation-reversing base gluing.

Equivalence is over a fixed labelled base decomposition. This is neither
unmarked surface homeomorphism nor a general per-lift attachment solver.
The module does not extract structures from knots or give knot verdicts.
"""

from __future__ import annotations

from dataclasses import dataclass
from math import gcd
from typing import Any

from .integer_codec import encoded_integer
from .surface_cover import canonical_schema


Element = tuple[int, int]  # T**shift R**parity


def _poll(check):
    if check is not None:
        check()


def _integer(value: Any, name: str, minimum: int = 0) -> int:
    try:
        result = encoded_integer(value)
    except ValueError as exc:
        raise ValueError(f"{name} must be an integer or signed hexadecimal string") from exc
    if result < minimum:
        raise ValueError(f"{name} must be at least {minimum}")
    return result


def _fields(raw, names, description):
    if not isinstance(raw, dict) or set(raw) != set(names):
        raise ValueError(f"{description} requires exactly {sorted(names)}")


@dataclass(frozen=True)
class FiniteGroup:
    kind: str
    modulus: int

    def __post_init__(self):
        if self.kind not in ("cyclic", "dihedral"):
            raise ValueError("group kind must be cyclic or dihedral")
        if type(self.modulus) is not int or self.modulus < 1:
            raise ValueError("group modulus must be a positive integer")

    @property
    def degree(self):
        return self.modulus * (2 if self.kind == "dihedral" else 1)

    def multiply(self, left: Element, right: Element) -> Element:
        e, t = left
        f, u = right
        return e ^ f, (t + (-u if e else u)) % self.modulus

    def inverse(self, value: Element) -> Element:
        e, t = value
        return e, (t if e else -t) % self.modulus

    def parse(self, raw, name="group element") -> Element:
        _fields(raw, {"parity", "shift"}, name)
        parity = _integer(raw["parity"], name + ".parity")
        if parity not in (0, 1) or (self.kind == "cyclic" and parity):
            raise ValueError(f"invalid parity for {self.kind} group")
        try:
            shift = encoded_integer(raw["shift"])
        except ValueError as exc:
            raise ValueError(name + ".shift must be an integer") from exc
        return parity, shift % self.modulus

    def order(self, value: Element) -> int:
        return 2 if value[0] else self.modulus // gcd(self.modulus, value[1])

    def generated_by(self, values: tuple[Element, ...]) -> bool:
        reflections = [t for e, t in values if e]
        if self.kind == "dihedral" and not reflections:
            return False
        divisor = self.modulus
        for parity, shift in values:
            if parity:
                shift -= reflections[0]
            divisor = gcd(divisor, shift)
        return divisor == 1

    def in_cyclic_subgroup(self, value: Element, generator: Element) -> bool:
        if generator[0]:
            return value == (0, 0) or value == generator
        return value[0] == 0 and value[1] % gcd(self.modulus, generator[1]) == 0


def _element_json(value: Element):
    return {"parity": value[0], "shift": value[1]}


@dataclass(frozen=True)
class Block:
    genus: int
    boundary_count: int
    monodromy: tuple[Element, ...]
    peripheral: tuple[Element, ...]
    euler: int


@dataclass(frozen=True)
class Edge:
    source: tuple[int, int]
    target: tuple[int, int]
    phase: Element


@dataclass(frozen=True)
class Mark:
    kind: str
    block: int
    boundary: int | None
    source: Element
    target: Element


@dataclass(frozen=True, init=False)
class RegularCoverAssembly:
    """Checked regular-cover input; block and boundary indices are zero based.

    Only orientable bordered bases are accepted. Signed peripheral words are
    followed in their listed order, using the existing canonical schema.
    """

    group: FiniteGroup
    blocks: tuple[Block, ...]
    edges: tuple[Edge, ...]
    occupied_ports: frozenset[tuple[int, int]]

    def __init__(self, raw: dict, *, check=None):
        _fields(raw, {"group", "blocks", "edges"}, "assembly")
        _fields(raw["group"], {"kind", "modulus"}, "group")
        kind = raw["group"]["kind"]
        if kind not in ("cyclic", "dihedral"):
            raise ValueError("group.kind must be cyclic or dihedral")
        object.__setattr__(self, "group", FiniteGroup(
            kind, _integer(raw["group"]["modulus"], "modulus", 1)))
        if not isinstance(raw["blocks"], list) or not raw["blocks"]:
            raise ValueError("blocks must be a nonempty list")
        blocks = []
        for index, item in enumerate(raw["blocks"]):
            _poll(check)
            _fields(item, {"surface", "monodromy"}, f"block {index}")
            surface = item["surface"]
            _fields(surface, {"orientable", "genus", "boundary_components"}, "surface")
            if surface["orientable"] is not True:
                raise ValueError("only orientable bordered base surfaces are supported")
            genus = _integer(surface["genus"], "surface.genus")
            boundaries = _integer(surface["boundary_components"], "boundary_components", 1)
            rank = 2 * genus + boundaries - 1
            if not isinstance(item["monodromy"], list) or len(item["monodromy"]) != rank:
                raise ValueError(f"block {index} requires exactly {rank} monodromy elements")
            maps = tuple(self.group.parse(g, "monodromy") for g in item["monodromy"])
            if not self.group.generated_by(maps):
                raise ValueError(f"block {index} is not a connected regular cover of the group")
            _, _, words, euler = canonical_schema(True, genus, boundaries, check=check)
            peripheral = []
            for word in words:
                result = (0, 0)
                for letter in word:
                    _poll(check)
                    step = maps[abs(letter) - 1]
                    if letter < 0:
                        step = self.group.inverse(step)
                    result = self.group.multiply(step, result)
                peripheral.append(result)
            blocks.append(Block(genus, boundaries, maps, tuple(peripheral), euler))
        object.__setattr__(self, "blocks", tuple(blocks))
        if not isinstance(raw["edges"], list):
            raise ValueError("edges must be a list")
        occupied = set()
        edges = []
        for index, item in enumerate(raw["edges"]):
            _poll(check)
            _fields(item, {"source", "target", "phase"}, f"edge {index}")
            source = self._port(item["source"])
            target = self._port(item["target"])
            if source == target or source in occupied or target in occupied:
                raise ValueError("every boundary port can occur in at most one gluing")
            occupied.update((source, target))
            a = self.blocks[source[0]].peripheral[source[1]]
            b = self.blocks[target[0]].peripheral[target[1]]
            if a != self.group.inverse(b):
                raise ValueError("glued boundary monodromies must be exact inverses")
            edges.append(Edge(source, target, self.group.parse(item["phase"], "phase")))
        object.__setattr__(self, "edges", tuple(edges))
        object.__setattr__(self, "occupied_ports", frozenset(occupied))

    def _port(self, raw):
        _fields(raw, {"block", "boundary"}, "boundary port")
        block = _integer(raw["block"], "port.block")
        boundary = _integer(raw["boundary"], "port.boundary")
        if block >= len(self.blocks) or boundary >= self.blocks[block].boundary_count:
            raise ValueError("boundary port is out of range")
        return block, boundary

    def topology(self, *, check=None):
        """Euler data for assembled surfaces without enumerating sheets/lifts."""
        adjacency = [[] for _ in self.blocks]
        for edge in self.edges:
            u, v = edge.source[0], edge.target[0]
            adjacency[u].append(v)
            adjacency[v].append(u)
        seen = set()
        result = []
        for root in range(len(self.blocks)):
            if root in seen:
                continue
            seen.add(root)
            stack, vertices = [root], []
            while stack:
                _poll(check)
                u = stack.pop()
                vertices.append(u)
                for v in adjacency[u]:
                    if v not in seen:
                        seen.add(v)
                        stack.append(v)
            chi = self.group.degree * sum(self.blocks[v].euler for v in vertices)
            boundaries = 0
            for v in vertices:
                for index, peripheral in enumerate(self.blocks[v].peripheral):
                    _poll(check)
                    if (v, index) not in self.occupied_ports:
                        boundaries += self.group.degree // self.group.order(peripheral)
            numerator = 2 - boundaries - chi
            if numerator < 0 or numerator % 2:
                raise ArithmeticError("inconsistent orientable surface Euler data")
            result.append({"blocks": sorted(vertices), "euler_characteristic": chi,
                           "boundary_components": boundaries, "genus": numerator // 2})
        return result


def _prepare(source, target, raw_marks, check=None):
    if not isinstance(source, RegularCoverAssembly):
        source = RegularCoverAssembly(source, check=check)
    if not isinstance(target, RegularCoverAssembly):
        target = RegularCoverAssembly(target, check=check)
    if (source.group != target.group or source.blocks != target.blocks
            or tuple((e.source, e.target) for e in source.edges)
            != tuple((e.source, e.target) for e in target.edges)):
        raise ValueError("comparison requires identical labelled bases and local monodromies")
    if not isinstance(raw_marks, list):
        raise ValueError("marks must be a list")
    marks = []
    for item in raw_marks:
        _poll(check)
        if not isinstance(item, dict) or item.get("kind") not in ("point", "boundary"):
            raise ValueError("mark.kind must be point or boundary")
        kind = item["kind"]
        fields = {"kind", "block", "source", "target"}
        if kind == "boundary":
            fields.add("boundary")
        _fields(item, fields, "mark")
        block = _integer(item["block"], "mark.block")
        if block >= len(source.blocks):
            raise ValueError("mark.block is out of range")
        boundary = None
        if kind == "boundary":
            boundary = _integer(item["boundary"], "mark.boundary")
            if boundary >= source.blocks[block].boundary_count:
                raise ValueError("mark.boundary is out of range")
        marks.append(Mark(kind, block, boundary, source.group.parse(item["source"]),
                          source.group.parse(item["target"])))
    return source, target, tuple(marks)


def _forest(source, target, check=None):
    group = source.group
    adjacency = [[] for _ in source.blocks]
    for i, edge in enumerate(source.edges):
        adjacency[edge.source[0]].append((edge.target[0], i, False))
        adjacency[edge.target[0]].append((edge.source[0], i, True))
    component = [-1] * len(source.blocks)
    paths = [(0, 0)] * len(source.blocks)
    target_paths = [(0, 0)] * len(source.blocks)
    roots, trees = [], set()
    for root in range(len(source.blocks)):
        if component[root] >= 0:
            continue
        comp = len(roots)
        roots.append(root)
        component[root] = comp
        stack = [root]
        while stack:
            _poll(check)
            u = stack.pop()
            for v, index, reverse in adjacency[u]:
                if component[v] >= 0:
                    continue
                component[v] = comp
                trees.add(index)
                a, b = source.edges[index].phase, target.edges[index].phase
                if reverse:
                    a, b = group.inverse(a), group.inverse(b)
                paths[v] = group.multiply(paths[u], a)
                target_paths[v] = group.multiply(target_paths[u], b)
                stack.append(v)
    return component, paths, target_paths, roots, trees


def _constraint_indices(source, marks, forest, check=None):
    component, _, _, roots, trees = forest
    result = [([], []) for _ in roots]
    for index, edge in enumerate(source.edges):
        _poll(check)
        if index not in trees:
            result[component[edge.source[0]]][0].append(index)
    for index, mark in enumerate(marks):
        _poll(check)
        result[component[mark.block]][1].append(index)
    return result


def _constraints(source, target, marks, forest, parity, indices, check=None):
    """Reduce group and coset equations to unary contradictions/congruences."""
    group = source.group
    m = group.modulus
    _, paths, target_paths, _, _ = forest
    result = []

    def impossible(reference, reason):
        result.append({"reference": reference, "impossible": reason})

    def congruence(reference, residue, modulus):
        result.append({"reference": reference, "residue": residue % modulus,
                       "modulus": modulus})

    for index in indices[0]:
        _poll(check)
        edge, other = source.edges[index], target.edges[index]
        u, v = edge.source[0], edge.target[0]
        c = group.multiply(group.multiply(paths[u], edge.phase), group.inverse(paths[v]))
        d = group.multiply(group.multiply(target_paths[u], other.phase),
                           group.inverse(target_paths[v]))
        ref = {"kind": "cycle", "index": index}
        if c[0] != d[0]:
            impossible(ref, "cycle parities differ")
            continue
        rhs = (c[1] - (-d[1] if parity else d[1])) % m
        if not c[0]:
            if rhs:
                impossible(ref, "rotation holonomies disagree under this root parity")
            continue
        common = gcd(2, m)
        if rhs % common:
            impossible(ref, "reflection congruence fails gcd divisibility")
        else:
            modulus = m // common
            residue = 0 if modulus == 1 else (rhs // common) * pow(2 // common, -1, modulus)
            congruence(ref, residue, modulus)
    for index in indices[1]:
        _poll(check)
        mark = marks[index]
        ref = {"kind": "mark", "index": index}
        left = group.multiply(paths[mark.block], group.inverse(mark.source))
        right = group.multiply(mark.target, group.inverse(target_paths[mark.block]))
        base = group.multiply(left, right)
        if mark.kind == "point":
            if parity != base[0]:
                impossible(ref, "point mark forces the other root parity")
            else:
                congruence(ref, base[1], m)
            continue
        peripheral = source.blocks[mark.block].peripheral[mark.boundary]
        if not peripheral[0]:
            if parity != base[0]:
                impossible(ref, "rotation boundary coset forces the other root parity")
            else:
                congruence(ref, base[1], gcd(m, peripheral[1]))
        else:
            value = base if parity == base[0] else group.multiply(
                group.multiply(left, peripheral), right)
            congruence(ref, value[1], m)
    return result


def _solve_constraints(constraints, check=None):
    residue, modulus = 0, 1
    previous = []
    for index, item in enumerate(constraints):
        _poll(check)
        if "impossible" in item:
            return {"obstruction": {"kind": "unary", "constraint": index}}
        a, q = item["residue"], item["modulus"]
        common = gcd(modulus, q)
        if (a - residue) % common:
            # Pairwise congruence consistency is equivalent to CRT consistency.
            # Scan once, at the first failure of this parity branch.
            for prior in previous:
                other = constraints[prior]
                if (a - other["residue"]) % gcd(q, other["modulus"]):
                    return {"obstruction": {"kind": "pair", "constraints": [prior, index]}}
            raise ArithmeticError("CRT contradiction had no incompatible pair")
        reduced = q // common
        if reduced > 1:
            step = ((a - residue) // common) * pow(modulus // common, -1, reduced)
            residue += modulus * (step % reduced)
        modulus *= reduced
        residue %= modulus
        previous.append(index)
    return {"residue": residue, "modulus": modulus}


def compare_assemblies(source, target, marks=None, *, check=None):
    """Return exact equivalence, all root families, and arithmetic certificates.

    A successful parity branch means the root is T**(residue+k*modulus)
    R**parity for 0 <= k < m/modulus. Different graph components vary freely.
    """
    source, target, marks = _prepare(source, target, [] if marks is None else marks, check)
    forest = _forest(source, target, check)
    component, paths, target_paths, roots, _ = forest
    indices = _constraint_indices(source, marks, forest, check)
    records = []
    total = 1
    parities = range(2 if source.group.kind == "dihedral" else 1)
    for comp, root in enumerate(roots):
        branches = []
        count = 0
        for parity in parities:
            _poll(check)
            constraints = _constraints(source, target, marks, forest, parity, indices[comp], check)
            solution = _solve_constraints(constraints, check)
            branch = {"parity": parity, **solution}
            if "obstruction" not in solution:
                count += source.group.modulus // solution["modulus"]
            branches.append(branch)
        records.append({"root": root, "branches": branches, "count": count})
        total *= count
    return {"equivalent": total != 0, "isomorphism_count": total,
            "components": records, "block_components": component,
            "source_paths": [_element_json(x) for x in paths],
            "target_paths": [_element_json(x) for x in target_paths]}


def verify_certificate(source, target, marks, certificate, *, check=None):
    """Verify complete residue families or short incompatibility proofs.

    No CRT is run. A positive branch supplies a common residue and the least
    common multiple of the constraint moduli. A negative branch supplies an
    impossible equation or a pair of incompatible congruences. Geometric
    group/coset reductions are recomputed. Cancellation exceptions propagate.
    """
    source, target, marks = _prepare(source, target, marks, check)
    forest = _forest(source, target, check)
    component, paths, target_paths, roots, _ = forest
    indices = _constraint_indices(source, marks, forest, check)
    try:
        if (certificate["block_components"] != component
                or certificate["source_paths"] != [_element_json(x) for x in paths]
                or certificate["target_paths"] != [_element_json(x) for x in target_paths]
                or len(certificate["components"]) != len(roots)):
            return False
        total = 1
        expected_parities = list(range(2 if source.group.kind == "dihedral" else 1))
        for comp, root in enumerate(roots):
            record = certificate["components"][comp]
            if (record["root"] != root
                    or [b["parity"] for b in record["branches"]] != expected_parities):
                return False
            count = 0
            for branch in record["branches"]:
                constraints = _constraints(
                    source, target, marks, forest, branch["parity"], indices[comp], check)
                if "obstruction" in branch:
                    obstruction = branch["obstruction"]
                    if obstruction["kind"] == "unary":
                        index = obstruction["constraint"]
                        if type(index) is not int or not 0 <= index < len(constraints):
                            return False
                        if "impossible" not in constraints[index]:
                            return False
                    elif obstruction["kind"] == "pair":
                        pair = obstruction["constraints"]
                        if len(pair) != 2 or any(
                                type(i) is not int or not 0 <= i < len(constraints) for i in pair):
                            return False
                        a, b = (constraints[i] for i in pair)
                        if "impossible" in a or "impossible" in b:
                            return False
                        if (a["residue"] - b["residue"]) % gcd(a["modulus"], b["modulus"]) == 0:
                            return False
                    else:
                        return False
                else:
                    r, q = branch["residue"], branch["modulus"]
                    if type(r) is not int or type(q) is not int or q < 1 or not 0 <= r < q:
                        return False
                    lcm = 1
                    for item in constraints:
                        _poll(check)
                        if "impossible" in item or (r - item["residue"]) % item["modulus"]:
                            return False
                        lcm = lcm // gcd(lcm, item["modulus"]) * item["modulus"]
                    if q != lcm or source.group.modulus % q:
                        return False
                    count += source.group.modulus // q
            if record["count"] != count:
                return False
            total *= count
        return (certificate["isomorphism_count"] == total
                and type(certificate["equivalent"]) is bool
                and certificate["equivalent"] == (total != 0))
    except (KeyError, IndexError, TypeError, ZeroDivisionError):
        return False


def transport_witness(source, target, certificate, roots=None, *, check=None):
    """Evaluate selected root families, returning one right gauge per block.

    Verify imported certificates with their marks first. Default roots choose
    the first nonempty branch. Supplied roots use group-element JSON objects.
    """
    source, target, _ = _prepare(source, target, [], check)
    forest = _forest(source, target, check)
    component, paths, target_paths, graph_roots, _ = forest
    if not certificate.get("equivalent"):
        raise ValueError("there is no transport for an inequivalent comparison")
    if roots is not None and (not isinstance(roots, list) or len(roots) != len(graph_roots)):
        raise ValueError("one root element is required for every graph component")
    selected = []
    for comp, _ in enumerate(graph_roots):
        branches = certificate["components"][comp]["branches"]
        if roots is None:
            branch = next(b for b in branches if "obstruction" not in b)
            value = (branch["parity"], branch["residue"])
        else:
            value = source.group.parse(roots[comp], "root choice")
        if not any("obstruction" not in b and value[0] == b["parity"]
                   and (value[1] - b["residue"]) % b["modulus"] == 0 for b in branches):
            raise ValueError("root choice is outside the certified families")
        selected.append(value)
    gauges = []
    for v, comp in enumerate(component):
        _poll(check)
        value = source.group.multiply(source.group.inverse(paths[v]), selected[comp])
        gauges.append(_element_json(source.group.multiply(value, target_paths[v])))
    return gauges


def verify_transport(source, target, marks, gauges, *, check=None):
    """Directly verify gluing and mark equations, without a forest or CRT."""
    source, target, marks = _prepare(source, target, marks, check)
    if not isinstance(gauges, list) or len(gauges) != len(source.blocks):
        return False
    try:
        values = [source.group.parse(x, "gauge") for x in gauges]
    except ValueError:
        return False
    group = source.group
    for edge, other in zip(source.edges, target.edges):
        _poll(check)
        u, v = edge.source[0], edge.target[0]
        if group.multiply(edge.phase, values[v]) != group.multiply(values[u], other.phase):
            return False
    for mark in marks:
        _poll(check)
        image = group.multiply(mark.source, values[mark.block])
        if mark.kind == "point":
            if image != mark.target:
                return False
        else:
            difference = group.multiply(image, group.inverse(mark.target))
            peripheral = source.blocks[mark.block].peripheral[mark.boundary]
            if not group.in_cyclic_subgroup(difference, peripheral):
                return False
    return True


def phase_orbit_count(kind, modulus, cycle_rank):
    """Number of unmarked phase classes on a connected fixed labelled graph.

    The graph has first Betti number cycle_rank. For D_m this is the Burnside
    count of simultaneous conjugacy classes in D_m**cycle_rank. This counts
    possible assemblies, not maps between one source and target assembly.
    """
    group = FiniteGroup(kind, _integer(modulus, "modulus", 1))
    beta = _integer(cycle_rank, "cycle_rank")
    m = group.modulus
    if kind == "cyclic":
        return m ** beta
    if m % 2:
        numerator = (2 * m) ** beta + (m - 1) * m ** beta + m * 2 ** beta
    else:
        numerator = 2 * (2 * m) ** beta + (m - 2) * m ** beta + m * 4 ** beta
    return numerator // (2 * m)


def canonicalize_assembly(source, *, check=None):
    """Unmarked canonical cache key and a verified-form transport candidate.

    The key includes the whole labelled base model and all canonical phases.
    It is complete for THIS restricted unmarked equivalence. Do not use it
    to erase named points, boundary lifts, port framings, or arbitrary
    attachment maps; such structures require the marked comparison API.

    Every graph component needs at most two candidate root conjugations.
    A first reflection, if present, is normalized to shift zero for odd m,
    and to its shift parity for even m. Any remaining half-turn ambiguity
    is central. Returned gauges map source to the returned edge phases.
    """
    if not isinstance(source, RegularCoverAssembly):
        source = RegularCoverAssembly(source, check=check)
    group = source.group
    m = group.modulus
    forest = _forest(source, source, check)
    component, paths, _, roots, trees = forest
    holonomies = [[] for _ in roots]
    for index, edge in enumerate(source.edges):
        _poll(check)
        if index in trees:
            continue
        u, v = edge.source[0], edge.target[0]
        value = group.multiply(group.multiply(paths[u], edge.phase), group.inverse(paths[v]))
        holonomies[component[u]].append((index, value))
    chosen = []
    for entries in holonomies:
        first_reflection = next((value[1] for _, value in entries if value[0]), None)
        candidates = []
        for parity in range(2 if group.kind == "dihedral" else 1):
            shift = 0
            if first_reflection is not None:
                common = gcd(2, m)
                least = first_reflection % common
                rhs = first_reflection - (-least if parity else least)
                reduced = m // common
                if reduced != 1:
                    shift = ((rhs // common) * pow(2 // common, -1, reduced)) % reduced
            root = (parity, shift)
            inverse_root = group.inverse(root)
            key = tuple((index, *group.multiply(group.multiply(inverse_root, value), root))
                        for index, value in entries)
            candidates.append((key, root))
        chosen.append(min(candidates)[1])
    gauges = [group.multiply(group.inverse(paths[v]), chosen[comp])
              for v, comp in enumerate(component)]
    phases = []
    for edge in source.edges:
        _poll(check)
        u, v = edge.source[0], edge.target[0]
        phases.append(group.multiply(
            group.multiply(group.inverse(gauges[u]), edge.phase), gauges[v]))
    header = (
        (group.kind, m),
        tuple((b.genus, b.boundary_count, b.monodromy) for b in source.blocks),
        tuple((edge.source, edge.target) for edge in source.edges),
    )
    return {"key": (header, tuple(phases)),
            "phases": [_element_json(value) for value in phases],
            "gauges": [_element_json(value) for value in gauges]}
