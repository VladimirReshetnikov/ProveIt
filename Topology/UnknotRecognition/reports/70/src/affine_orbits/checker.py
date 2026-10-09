"""Independent arithmetic certificate checker.

No BulkIndex, StepProfile, SparseOverlay, gcd, or certificate-producer calls.
Shares only strict schema/transport utilities with the producer. Histogram
validation uses direct residue counting on endpoint cells, not an event sweep.
Defects are verified by graph traversal, not the producer's disjoint-set code.
"""
from __future__ import annotations
from collections import Counter
from typing import Any
from .core import Model, Defect, digest, integer, parse_defect


def _hist(rows: Any, dimension: int) -> Counter:
    if not isinstance(rows, list):
        raise ValueError("histogram is not a list")
    out = Counter()
    for row in rows:
        if not isinstance(row, dict) or set(row) != {"weight", "multiplicity"}:
            raise ValueError("invalid histogram fields")
        val = tuple(integer(x) for x in row["weight"])
        n = integer(row["multiplicity"])
        if len(val) != dimension or n < 1 or val in out:
            raise ValueError("invalid or duplicate histogram entry")
        out[val] = n
    return out


def verify(model: Model | dict[str, Any], defects: list[Defect | dict[str, Any]],
           cert: dict[str, Any]) -> bool:
    """Return True or raise ValueError; no failure is interpreted as a verdict."""
    m = Model.parse(model.as_dict() if isinstance(model, Model) else model)
    dd = [parse_defect(vars(d) if isinstance(d, Defect) else d, m) for d in defects]
    required = {"schema", "source_sha256", "roots", "signs", "shifts", "parent_edges",
                "components", "histogram", "component_count"}
    if not isinstance(cert, dict) or set(cert) != required:
        raise ValueError("invalid certificate fields")
    source = {"model": m.as_dict(), "defects": [vars(d) for d in dd]}
    if cert["schema"] != "affine-orbit-profile-v1" or cert["source_sha256"] != digest(source):
        raise ValueError("certificate source binding failed")
    arrays = [tuple(integer(x) for x in cert[name]) for name in
              ("roots", "signs", "shifts", "parent_edges")]
    root, sign, shift, parent_edge = arrays
    if any(len(a) != m.vertices for a in arrays):
        raise ValueError("forest array length mismatch")
    if any(not 0 <= r < m.vertices for r in root) or any(s not in (-1, 1) for s in sign):
        raise ValueError("invalid root or sign")
    if any(not 0 <= a < m.sheets for a in shift):
        raise ValueError("noncanonical gauge shift")
    children = [[] for _ in range(m.vertices)]
    forest_roots = []
    for v in range(m.vertices):
        eid = parent_edge[v]
        if eid == -1:
            if root[v] != v or sign[v] != 1 or shift[v] != 0:
                raise ValueError("invalid root gauge")
            forest_roots.append(v)
            continue
        if not 0 <= eid < len(m.edges):
            raise ValueError("parent edge out of range")
        e = m.edges[eid]
        if e.v == v and e.u != v:
            u, s, a = e.u, e.sign, e.shift
        elif e.u == v and e.v != v:
            u, s, a = e.v, e.sign, (-e.sign * e.shift) % m.sheets
        else:
            raise ValueError("parent edge does not join a distinct parent")
        if root[u] != root[v] or sign[v] != s * sign[u] or shift[v] != (s * shift[u] + a) % m.sheets:
            raise ValueError("parent gauge equation failed")
        children[u].append(v)
    seen = set()
    for r in forest_roots:
        stack = [r]
        while stack:
            v = stack.pop()
            if v in seen or root[v] != r:
                raise ValueError("invalid rooted spanning forest")
            seen.add(v)
            stack.extend(children[v])
    if len(seen) != m.vertices:
        raise ValueError("cyclic or disconnected parent certificate")
    monos = {r: [] for r in forest_roots}
    for e in m.edges:
        if root[e.u] != root[e.v]:
            raise ValueError("forest does not span a base component")
        s = sign[e.v] * e.sign * sign[e.u]
        a = sign[e.v] * (e.sign * shift[e.u] + e.shift - shift[e.v]) % m.sheets
        monos[root[e.u]].append((s, a))
    records = {r: [] for r in forest_roots}
    for w in m.weights:
        a = (w.start - shift[w.v] if sign[w.v] == 1 else shift[w.v] - w.stop + 1) % m.sheets
        records[root[w.v]].append((a, w.stop - w.start, w.value))
    claims = cert["components"]
    if not isinstance(claims, list) or len(claims) != len(forest_roots):
        raise ValueError("component record count mismatch")
    component_data = {}
    total = Counter()
    for row in claims:
        if set(row) != {"root", "divisor", "reflection", "gcd_witnesses", "histogram"}:
            raise ValueError("invalid component claim")
        r = integer(row["root"])
        if r not in monos or r in component_data:
            raise ValueError("duplicate or unknown base root")
        maps = monos[r]
        reflect = next((a for s, a in maps if s == -1), None)
        witnesses = row["gcd_witnesses"]
        if not isinstance(witnesses, list) or len(witnesses) != len(maps):
            raise ValueError("gcd witness count mismatch")
        d = m.sheets
        for (s, a), witness in zip(maps, witnesses):
            if not isinstance(witness, (list, tuple)) or len(witness) != 3:
                raise ValueError("invalid gcd witness")
            b = (a if s == 1 else a - reflect) % m.sheets
            g, x, y = (integer(z) for z in witness)
            if g <= 0 or d % g or b % g or x * d + y * b != g:
                raise ValueError("Bezout/divisibility proof failed")
            d = g
        c = None if reflect is None else reflect % d
        stated_c = None if row["reflection"] is None else integer(row["reflection"])
        if integer(row["divisor"]) != d or stated_c != c:
            raise ValueError("wrong affine subgroup claim")

        def eval_f(x: int) -> tuple[int, ...]:
            x %= d
            out = [0] * m.dimension
            for a, length, val in records[r]:
                q, rem = divmod(length, d)
                n = q + int((x - a) % d < rem)
                for j in range(m.dimension):
                    out[j] += n * val[j]
            return tuple(out)

        # Independent direct counting at each candidate endpoint cell.
        endpoints = {0, d}
        for a, length, _ in records[r]:
            rem = length % d
            if rem:
                endpoints.update((a % d, (a + rem) % d))
                if c is not None:
                    endpoints.update(((c - a - rem + 1) % d, (c - a + 1) % d))
        fixed = []
        if c is not None:
            if d & 1:
                fixed = [(c * ((d + 1) // 2)) % d]
            elif not c & 1:
                fixed = [c // 2, c // 2 + d // 2]
        found = Counter()
        ep = sorted(endpoints)
        for a, b in zip(ep, ep[1:]):
            fa = eval_f(a)
            if c is None:
                found[fa] += b - a
            else:
                fb = eval_f(c - a)
                weight = tuple(x + y for x, y in zip(fa, fb))
                found[weight] += b - a - sum(a <= x < b for x in fixed)
        if c is not None:
            if any(n & 1 for n in found.values()):
                raise ValueError("odd reflection pair histogram")
            found = Counter({w: n // 2 for w, n in found.items() if n})
            for x in fixed:
                found[eval_f(x)] += 1
        found = Counter({w: n for w, n in found.items() if n})
        if found != _hist(row["histogram"], m.dimension):
            raise ValueError("component histogram failed direct counting")
        total.update(found)
        component_data[r] = (d, c)

    def point_key(v: int, x: int) -> tuple[int, int]:
        rr = root[v]
        d, c = component_data[rr]
        a = (sign[v] * (x - shift[v])) % d
        return rr, a if c is None else min(a, (c - a) % d)

    def orbit_weight(key: tuple[int, int]) -> tuple[int, ...]:
        rr, x = key
        d, c = component_data[rr]
        residues = {x} if c is None else {x, (c - x) % d}
        out = [0] * m.dimension
        for a, length, val in records[rr]:
            q, rem = divmod(length, d)
            n = sum(q + int((z - a) % d < rem) for z in residues)
            for j in range(m.dimension):
                out[j] += n * val[j]
        return tuple(out)

    # Independently traverse the graph on touched bulk orbits.
    adjacency = {}
    pairs = []
    for e in dd:
        a, b = point_key(e.u, e.x), point_key(e.v, e.y)
        adjacency.setdefault(a, set()).add(b)
        adjacency.setdefault(b, set()).add(a)
        pairs.append((a, b, e.payload))
    for a in adjacency:
        w = orbit_weight(a)
        total[w] -= 1
        if total[w] < 0:
            raise ValueError("too many removed bulk components")
        if total[w] == 0:
            del total[w]
    block_of = {}
    blocks = []
    for a in adjacency:
        if a in block_of:
            continue
        index = len(blocks)
        vertices = []
        stack = [a]
        block_of[a] = index
        while stack:
            z = stack.pop()
            vertices.append(z)
            for t in adjacency[z]:
                if t not in block_of:
                    block_of[t] = index
                    stack.append(t)
        weight = [0] * m.dimension
        for z in vertices:
            wz = orbit_weight(z)
            for j in range(m.dimension):
                weight[j] += wz[j]
        blocks.append(weight)
    for a, _, payload in pairs:
        out = blocks[block_of[a]]
        for j in range(m.dimension):
            out[j] += payload[j]
    for out in blocks:
        total[tuple(out)] += 1
    if total != _hist(cert["histogram"], m.dimension):
        raise ValueError("final attachment histogram mismatch")
    if sum(total.values()) != integer(cert["component_count"]):
        raise ValueError("wrong final component count")
    return True
