"""Exact marked small-cut responses for boundary-gluing graph DAGs.

Positive integral edge weights; fresh edge/interior occurrences at every use.
No knot verdict or geometric embedding claim is made by this module.
Python 3.10+, standard library only.  License: MIT-0.
"""
from __future__ import annotations

from dataclasses import dataclass
from itertools import combinations
from math import comb
from typing import Any, Iterable
import hashlib
import json

Key = tuple[int, int]  # ordered terminal-color mask, two monochromatic-edge flags


class InputError(ValueError):
    """The graph grammar violates the documented input contract."""


class BudgetExceeded(RuntimeError):
    """No result is returned when an explicit operation/state budget is exhausted."""


@dataclass
class Budget:
    limit: int | None = None
    states: int | None = None
    used: int = 0

    def tick(self, amount: int = 1) -> None:
        self.used += amount
        if self.limit is not None and self.used > self.limit:
            raise BudgetExceeded("operation budget exhausted; query is inconclusive")

    def check_states(self, amount: int) -> None:
        if self.states is not None and amount > self.states:
            raise BudgetExceeded("state budget exhausted; query is inconclusive")


@dataclass(frozen=True)
class Entry:
    cost: int
    witness: Any


@dataclass(frozen=True)
class Meta:
    vertices: int
    edges: int
    partition: tuple[int, ...]  # connected-component labels of terminals
    hidden: int                # components having no current terminal
    degrees: tuple[int, ...]   # saturated at 4; enough for cubic certification
    interior_cubic: bool

    @property
    def terminal_components(self) -> int:
        return len(set(self.partition))

    @property
    def components(self) -> int:
        return self.hidden + self.terminal_components

    def record(self) -> dict[str, Any]:
        return {"vertices_hex": hex(self.vertices), "edges_hex": hex(self.edges),
                "partition": list(self.partition), "hidden_components_hex": hex(self.hidden),
                "degrees_capped_at_four": list(self.degrees),
                "interior_cubic": self.interior_cubic}


@dataclass
class Result:
    grammar: dict[str, Any]
    k: int
    tables: list[dict[Key, Entry]]
    metadata: list[Meta]
    operations: int

    @property
    def root(self) -> int:
        return self.grammar.get("root", len(self.tables) - 1)

    def response(self) -> dict[Key, int]:
        return {key: ent.cost for key, ent in self.tables[self.root].items()}

    def has_marked_cut(self) -> bool:
        if terminal_count(self.grammar["nodes"][self.root]) != 0:
            raise InputError("forget root terminals before asking an unrestricted cut query")
        return (0, 3) in self.tables[self.root]

    def certificate(self) -> dict[str, Any]:
        rows = []
        for table in self.tables:
            rows.append([[mask, flags, ent.cost, ent.witness]
                         for (mask, flags), ent in sorted(table.items())])
        return {"schema": "proveit.sparse-cut-certificate.v1", "threshold": self.k,
                "grammar_sha256": grammar_digest(self.grammar), "tables": rows,
                "metadata": [m.record() for m in self.metadata]}


class DSU:
    def __init__(self, n: int):
        self.p = list(range(n))

    def find(self, a: int) -> int:
        while a != self.p[a]:
            self.p[a] = self.p[self.p[a]]
            a = self.p[a]
        return a

    def union(self, a: int, b: int) -> None:
        a, b = self.find(a), self.find(b)
        if a != b:
            self.p[b] = a


def _int(value: Any, low: int = 0) -> bool:
    return type(value) is int and value >= low


def terminal_count(node: dict[str, Any]) -> int:
    return len(node["terminals"])


def grammar_digest(grammar: dict[str, Any]) -> str:
    return hashlib.sha256(json.dumps(grammar, sort_keys=True, separators=(",", ":"))
                          .encode("utf-8")).hexdigest()


def validate(grammar: dict[str, Any], k: int) -> None:
    if not _int(k):
        raise InputError("threshold must be a nonnegative integer, not a boolean")
    if not isinstance(grammar, dict) or grammar.get("schema") != "proveit.graph-grammar.v1":
        raise InputError("unsupported grammar schema")
    nodes = grammar.get("nodes")
    if not isinstance(nodes, list) or not nodes:
        raise InputError("nodes must be a nonempty list")
    for i, node in enumerate(nodes):
        if not isinstance(node, dict):
            raise InputError(f"node {i}: expected an object")
        terms = node.get("terminals")
        if not isinstance(terms, list) or not all(_int(t) for t in terms) or len(set(terms)) != len(terms):
            raise InputError(f"node {i}: terminal indices must be distinct nonnegative integers")
        kind = node.get("kind")
        if kind == "leaf":
            n, edges = node.get("vertices"), node.get("edges")
            if not _int(n, 1) or not isinstance(edges, list) or any(t >= n for t in terms):
                raise InputError(f"node {i}: bad leaf size or terminals")
            for edge in edges:
                if (not isinstance(edge, list) or len(edge) != 3 or
                    not all(_int(x) for x in edge[:2]) or
                    max(edge[:2]) >= n or not _int(edge[2], 1)):
                    raise InputError(f"node {i}: each edge is [u,v,positive integer weight]")
            isolated = node.get("isolated_vertices", [])
            visible = set(terms) | {v for edge in edges for v in edge[:2]}
            if (not isinstance(isolated, list) or not all(_int(v) and v < n for v in isolated)
                    or len(set(isolated)) != len(isolated) or set(isolated) & visible):
                raise InputError(f"node {i}: invalid private isolated-vertex inventory")
            if n > 1 and len(visible | set(isolated)) != n:
                raise InputError(f"node {i}: list every private isolated vertex explicitly")
        elif kind in ("join", "map"):
            children = [node.get("child")] if kind == "map" else [node.get("left"), node.get("right")]
            maps = [node.get("mapping")] if kind == "map" else [node.get("left_map"), node.get("right_map")]
            labels = []
            for child, mapping in zip(children, maps):
                if not _int(child) or child >= i:
                    raise InputError(f"node {i}: children must precede their parent")
                if (not isinstance(mapping, list) or len(mapping) != terminal_count(nodes[child]) or
                    not all(_int(x) for x in mapping)):
                    raise InputError(f"node {i}: bad boundary map")
                labels.extend(mapping)
            groups = sorted(set(labels))
            if groups != list(range(len(groups))) or any(t >= len(groups) for t in terms):
                raise InputError(f"node {i}: quotient classes must be contiguous and terminals must exist")
        else:
            raise InputError(f"node {i}: unsupported kind {kind!r}")
    root = grammar.get("root", len(nodes)-1)
    if not _int(root) or root >= len(nodes):
        raise InputError("bad root")


def connected_support_bound(r: int, k: int) -> int:
    """Upper bound for boundary colorings, before multiplication by four flags."""
    if r == 0:
        return 1
    if r == 1:
        return 2
    d = 2*r-3
    return min(1 << r, 2 * sum(comb(d, j) for j in range(min(d, k)+1)))


def support_bound(r: int, c: int, k: int) -> int:
    """General marked-entry bound; c counts terminal-bearing components only."""
    return 4 * min(1 << r, (1 << c) * sum(comb(2*r, j) for j in range(min(2*r, k)+1)))


def _put(table: dict[Key, Entry], key: Key, cost: int, witness: Any, budget: Budget) -> None:
    old = table.get(key)
    if old is None or cost < old.cost:
        table[key] = Entry(cost, witness)
        budget.check_states(len(table))


def _leaf(node: dict[str, Any], k: int, budget: Budget) -> tuple[dict[Key, Entry], Meta]:
    n, edges, terms = node["vertices"], node["edges"], node["terminals"]
    adjacency = [[] for _ in range(n)]
    degrees = [0]*n
    for u, v, _ in edges:
        adjacency[u].append(v)
        adjacency[v].append(u)
        degrees[u] += 1
        degrees[v] += 1
    seen = set()
    comps = []
    vertex_comp = [-1]*n
    for root in range(n):
        if root in seen:
            continue
        seen.add(root)
        order, parent = [root], {root: -1}
        for v in order:
            vertex_comp[v] = len(comps)
            for w in adjacency[v]:
                if w not in seen:
                    seen.add(w)
                    parent[w] = v
                    order.append(w)
        comps.append((root, order, parent))
    total: dict[Key, Entry] = {(0, 0): Entry(0, 0)}
    for ci, (root, order, parent) in enumerate(comps):
        comp_edges = [(u, v, w) for u, v, w in edges if vertex_comp[u] == ci]
        comp_terms = [(j, t) for j, t in enumerate(terms) if vertex_comp[t] == ci]
        sub = {v: 1 << v for v in order}
        for v in reversed(order[1:]):
            sub[parent[v]] |= sub[v]
        switches = [sub[v] for v in order[1:]]
        universe = sub[root]
        local: dict[Key, Entry] = {}
        for j in range(min(k, len(switches))+1):
            for chosen in combinations(switches, j):
                base = 0
                for block in chosen:
                    base ^= block
                for coloring in (base, universe ^ base):
                    budget.tick()
                    cost, flags = 0, 0
                    for u, v, weight in comp_edges:
                        a, b = (coloring >> u) & 1, (coloring >> v) & 1
                        if a != b:
                            cost += weight
                            if cost > k:
                                break
                        else:
                            flags |= 1 << a
                    if cost <= k:
                        mask = sum(((coloring >> t) & 1) << j for j, t in comp_terms)
                        _put(local, (mask, flags), cost, coloring, budget)
        merged: dict[Key, Entry] = {}
        cost_buckets: dict[int, list[tuple[Key, Entry]]] = {}
        for key2, e2 in local.items():
            cost_buckets.setdefault(e2.cost, []).append((key2, e2))
        for (mask1, flags1), e1 in total.items():
            for c2 in range(k-e1.cost+1):
                for (mask2, flags2), e2 in cost_buckets.get(c2, []):
                    budget.tick()
                    _put(merged, (mask1 | mask2, flags1 | flags2), e1.cost+e2.cost,
                         e1.witness | e2.witness, budget)
        total = merged
    canon = {}
    part = tuple(canon.setdefault(vertex_comp[t], len(canon)) for t in terms)
    hidden = len(comps)-len(canon)
    ts = set(terms)
    meta = Meta(n, len(edges), part, hidden, tuple(min(4, degrees[t]) for t in terms),
                all(degrees[v] == 3 for v in range(n) if v not in ts))
    return total, meta


def _mapped(mask: int, mapping: list[int]) -> tuple[int, int] | None:
    assigned = ones = 0
    for i, group in enumerate(mapping):
        bit = 1 << group
        value = (mask >> i) & 1
        if assigned & bit:
            if bool(ones & bit) != bool(value):
                return None
        else:
            assigned |= bit
            if value:
                ones |= bit
    return assigned, ones


def _project(ones: int, terminals: list[int]) -> int:
    return sum(((ones >> t) & 1) << i for i, t in enumerate(terminals))


def _metadata(children: list[Meta], maps: list[list[int]], terminals: list[int]) -> Meta:
    q = len(set(x for mapping in maps for x in mapping))
    dsu = DSU(q)
    degree = [0]*q
    for child, mapping in zip(children, maps):
        roots = {}
        for t, group in enumerate(mapping):
            comp = child.partition[t]
            if comp in roots:
                dsu.union(group, roots[comp])
            else:
                roots[comp] = group
            degree[group] = min(4, degree[group] + child.degrees[t])
    old_components = {dsu.find(i) for i in range(q)}
    kept_components = {dsu.find(i) for i in terminals}
    canon = {}
    partition = tuple(canon.setdefault(dsu.find(t), len(canon)) for t in terminals)
    ts = set(terminals)
    return Meta(sum(c.vertices for c in children)-sum(len(m) for m in maps)+q,
                sum(c.edges for c in children), partition,
                sum(c.hidden for c in children)+len(old_components-kept_components),
                tuple(degree[t] for t in terminals),
                all(c.interior_cubic for c in children) and
                all(degree[t] == 3 for t in range(q) if t not in ts))


def solve(grammar: dict[str, Any], k: int = 3, *, operation_limit: int | None = None,
          state_limit: int | None = None, cost_indexed: bool = True) -> Result:
    """Compute every finite exact-flag response up to k, or raise on exhaustion.

    Tables retain only minima for a fixed (boundary coloring, exact flags).
    The meaning of an absent key is 'no realization with cost <= k'.
    """
    validate(grammar, k)
    if any(x is not None and not _int(x) for x in (operation_limit, state_limit)):
        raise InputError("budgets must be nonnegative integers or None")
    budget = Budget(operation_limit, state_limit)
    tables: list[dict[Key, Entry]] = []
    metadata: list[Meta] = []
    for node in grammar["nodes"]:
        kind = node["kind"]
        if kind == "leaf":
            table, meta = _leaf(node, k, budget)
        elif kind == "map":
            child = node["child"]
            table = {}
            for key, ent in tables[child].items():
                budget.tick()
                image = _mapped(key[0], node["mapping"])
                if image is not None:
                    _put(table, (_project(image[1], node["terminals"]), key[1]),
                         ent.cost, [list(key)], budget)
            meta = _metadata([metadata[child]], [node["mapping"]], node["terminals"])
        else:
            left, right = node["left"], node["right"]
            lm, rm = node["left_map"], node["right_map"]
            shared = sum(1 << x for x in set(lm) & set(rm))
            # Join on interface color instead of trying all incompatible pairs.
            buckets: dict[Any, list[tuple[Key, Entry, int]]] = {}
            for key, ent in tables[right].items():
                budget.tick()
                image = _mapped(key[0], rm)
                if image is not None:
                    bucket_key = (image[1] & shared, ent.cost) if cost_indexed else image[1] & shared
                    buckets.setdefault(bucket_key, []).append((key, ent, image[1]))
            table = {}
            for key1, e1 in tables[left].items():
                image = _mapped(key1[0], lm)
                if image is None:
                    continue
                if cost_indexed:
                    candidates = (row for bcost in range(k-e1.cost+1)
                                  for row in buckets.get((image[1] & shared, bcost), []))
                else:
                    candidates = iter(buckets.get(image[1] & shared, []))
                for key2, e2, ones2 in candidates:
                    budget.tick()
                    cost = e1.cost + e2.cost
                    if cost <= k:
                        key = (_project(image[1] | ones2, node["terminals"]), key1[1] | key2[1])
                        _put(table, key, cost, [list(key1), list(key2)], budget)
            meta = _metadata([metadata[left], metadata[right]], [lm, rm], node["terminals"])
        assert len(table) <= support_bound(terminal_count(node), meta.terminal_components, k)
        tables.append(table)
        metadata.append(meta)
    return Result(grammar, k, tables, metadata, budget.used)


def _children(node: dict[str, Any]) -> list[int]:
    if node["kind"] == "map":
        return [node["child"]]
    if node["kind"] == "join":
        return [node["left"], node["right"]]
    return []


def witness_dag(result: Result, key: Key = (0, 3)) -> dict[str, Any]:
    """Extract an occurrence-independent acyclic witness, without expansion."""
    root = result.root
    if key not in result.tables[root]:
        raise InputError("requested response has no low-cost witness")
    pending, seen = [(root, key)], set()
    records = []
    while pending:
        index, state = pending.pop()
        if (index, state) in seen:
            continue
        seen.add((index, state))
        ent = result.tables[index][state]
        node = result.grammar["nodes"][index]
        records.append({"node": index, "state": list(state), "cost": ent.cost,
                        "witness": ent.witness})
        for child, child_state in zip(_children(node), ent.witness if node["kind"] != "leaf" else []):
            pending.append((child, tuple(child_state)))
    records.sort(key=lambda r: (r["node"], r["state"]))
    return {"schema": "proveit.sparse-cut-witness.v1", "grammar_sha256": grammar_digest(result.grammar),
            "threshold": result.k, "root_state": list(key), "records": records}


def cut_addresses(result: Result, key: Key = (0, 3)) -> list[dict[str, Any]]:
    """At most k original edge-occurrence addresses; paths choose child copies."""
    if key not in result.tables[result.root]:
        raise InputError("no such witness")
    answer = []
    stack = [(result.root, key, ())]
    while stack:
        index, state, path = stack.pop()
        ent = result.tables[index][state]
        if ent.cost == 0:
            continue
        node = result.grammar["nodes"][index]
        if node["kind"] == "leaf":
            for e, (u, v, weight) in enumerate(node["edges"]):
                if ((ent.witness >> u) ^ (ent.witness >> v)) & 1:
                    answer.append({"path": list(path), "leaf": index, "edge": e, "weight": weight})
        else:
            for side, (child, child_state) in enumerate(zip(_children(node), ent.witness)):
                stack.append((child, tuple(child_state), path+(side,)))
    assert len(answer) <= result.k
    return answer


def mark_address(result: Result, color: int, key: Key = (0, 3)) -> dict[str, Any]:
    if color not in (0, 1) or key not in result.tables[result.root] or not key[1] & (1 << color):
        raise InputError("the requested color has no monochromatic-edge flag")
    index, state, path = result.root, key, []
    while True:
        node, ent = result.grammar["nodes"][index], result.tables[index][state]
        if node["kind"] == "leaf":
            for e, (u, v, weight) in enumerate(node["edges"]):
                if ((ent.witness >> u) & 1) == color == ((ent.witness >> v) & 1):
                    return {"path": path, "leaf": index, "edge": e, "weight": weight, "color": color}
            raise AssertionError("invalid leaf flag")
        for side, (child, child_state) in enumerate(zip(_children(node), ent.witness)):
            if child_state[1] & (1 << color):
                index, state = child, tuple(child_state)
                path.append(side)
                break
        else:
            raise AssertionError("invalid composed flag")


def serial_node(left: int, right: int, width: int) -> dict[str, Any]:
    if not _int(width, 1):
        raise InputError("serial width must be positive")
    return {"kind": "join", "left": left, "right": right,
            "left_map": list(range(2*width)),
            "right_map": list(range(width, 3*width)),
            "terminals": list(range(width))+list(range(2*width, 3*width))}


def append_power(nodes: list[dict[str, Any]], base: int, exponent: int, width: int) -> int:
    """Binary powers are expanded into O(log exponent) *rules*, not graph copies."""
    if not _int(exponent, 1):
        raise InputError("power exponent must be positive; zero needs an identity interface")
    acc = None
    cur = base
    while exponent:
        if exponent & 1:
            if acc is None:
                acc = cur
            else:
                nodes.append(serial_node(acc, cur, width))
                acc = len(nodes)-1
        exponent >>= 1
        if exponent:
            nodes.append(serial_node(cur, cur, width))
            cur = len(nodes)-1
    assert acc is not None
    return acc


def circular_ladder(exponent: int) -> dict[str, Any]:
    """2*exponent vertices, 3*exponent edges; loops/parallel edges when small."""
    nodes = [{"kind": "leaf", "vertices": 4,
              "edges": [[0, 1, 1], [0, 2, 1], [1, 3, 1]], "terminals": [0, 1, 2, 3]}]
    root = append_power(nodes, 0, exponent, 2)
    nodes.append({"kind": "map", "child": root, "mapping": [0, 1, 0, 1], "terminals": []})
    return {"schema": "proveit.graph-grammar.v1", "nodes": nodes, "root": len(nodes)-1}


def thue_morse(depth: int) -> dict[str, Any]:
    """Nonuniform, nested connected production rules A'=AB and B'=BA."""
    if not _int(depth):
        raise InputError("nonnegative depth required")
    a = {"kind": "leaf", "vertices": 4,
         "edges": [[0, 1, 1], [0, 2, 1], [1, 3, 1]], "terminals": [0, 1, 2, 3]}
    b = {"kind": "leaf", "vertices": 8,
         "edges": [[0, 2, 1], [1, 3, 1], [0, 4, 1], [1, 5, 1]]+
                  [[u, v, 1] for u in range(4, 8) for v in range(u+1, 8) if (u, v) != (4, 5)],
         "terminals": [0, 1, 2, 3]}
    nodes = [a, b]
    x, y = 0, 1
    for _ in range(depth):
        nodes.append(serial_node(x, y, 2))
        nodes.append(serial_node(y, x, 2))
        x, y = len(nodes)-2, len(nodes)-1
    nodes.append({"kind": "map", "child": x, "mapping": [0, 1, 0, 1], "terminals": []})
    return {"schema": "proveit.graph-grammar.v1", "nodes": nodes, "root": len(nodes)-1}
