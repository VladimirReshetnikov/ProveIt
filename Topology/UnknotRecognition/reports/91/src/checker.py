"""Independent certificate replay.  Does not import the producer.

Completeness at explicit leaves is checked by deleting at most k edges,
then coloring the resulting components.  Internal rules are replayed by
literal dictionaries of quotient-class colors, not the producer's bit joins.
"""
from __future__ import annotations
from itertools import combinations, product
from typing import Any
import hashlib
import json


def digest(g: dict) -> str:
    return hashlib.sha256(json.dumps(g, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def natural(v: Any, minimum: int = 0) -> bool:
    return type(v) is int and v >= minimum


def validate(g: dict, k: int) -> None:
    require(isinstance(g, dict) and g.get("schema") == "proveit.graph-grammar.v1", "grammar schema")
    require(natural(k), "threshold")
    nodes = g.get("nodes")
    require(isinstance(nodes, list) and len(nodes) > 0, "nodes")
    for i, n in enumerate(nodes):
        require(isinstance(n, dict), "node object")
        ts = n.get("terminals")
        require(isinstance(ts, list) and all(natural(v) for v in ts) and len(set(ts)) == len(ts), "terminals")
        if n.get("kind") == "leaf":
            require(natural(n.get("vertices"), 1), "leaf vertices")
            require(all(t < n["vertices"] for t in ts) and isinstance(n.get("edges"), list), "leaf data")
            for e in n["edges"]:
                require(isinstance(e, list) and len(e) == 3 and all(natural(v) for v in e[:2])
                        and max(e[:2]) < n["vertices"] and natural(e[2], 1), "edge data")
            isolated = n.get("isolated_vertices", [])
            named = set(ts) | {v for e in n["edges"] for v in e[:2]}
            require(isinstance(isolated, list) and all(natural(v) and v < n["vertices"] for v in isolated)
                    and len(set(isolated)) == len(isolated) and not set(isolated) & named,
                    "isolated vertex inventory")
            require(n["vertices"] == 1 or len(named | set(isolated)) == n["vertices"],
                    "implicit large leaf vertex universe")
        else:
            require(n.get("kind") in ("map", "join"), "operation kind")
            cs, maps = child_data(n)
            labels = []
            for c, mp in zip(cs, maps):
                require(natural(c) and c < i, "acyclic child")
                require(isinstance(mp, list) and len(mp) == len(nodes[c]["terminals"])
                        and all(natural(v) for v in mp), "map data")
                labels += mp
            q = len(set(labels))
            require(set(labels) == set(range(q)) and all(t < q for t in ts), "quotient classes")
    require(natural(g.get("root", len(nodes)-1)) and g.get("root", len(nodes)-1) < len(nodes), "root")


def child_data(node: dict) -> tuple[list[int], list[list[int]]]:
    if node["kind"] == "map":
        return [node["child"]], [node["mapping"]]
    if node["kind"] == "join":
        return [node["left"], node["right"]], [node["left_map"], node["right_map"]]
    return [], []


def components(vertices: list[int], edges: list[tuple[int, int]]) -> list[list[int]]:
    adjacency = {v: set() for v in vertices}
    for u, v in edges:
        adjacency[u].add(v)
        adjacency[v].add(u)
    unseen, out = set(vertices), []
    while unseen:
        root = min(unseen)
        unseen.remove(root)
        todo, block = [root], []
        while todo:
            v = todo.pop()
            block.append(v)
            for w in adjacency[v]:
                if w in unseen:
                    unseen.remove(w)
                    todo.append(w)
        out.append(block)
    return out


def color_key(node: dict, coloring: int) -> tuple[tuple[int, int], int]:
    cost, flags = 0, 0
    for u, v, w in node["edges"]:
        a, b = (coloring >> u) & 1, (coloring >> v) & 1
        if a == b:
            flags |= 1 << a
        else:
            cost += w
    mask = sum(((coloring >> t) & 1) << i for i, t in enumerate(node["terminals"]))
    return (mask, flags), cost


def leaf_complete(node: dict, k: int) -> dict[tuple[int, int], int]:
    """Polynomial for fixed k; no spanning-tree state enumeration is used."""
    n, es, ts = node["vertices"], node["edges"], node["terminals"]
    blocks = components(list(range(n)), [(u, v) for u, v, _ in es])
    total = {(0, 0): 0}
    for block in blocks:
        bs = set(block)
        local_edges = [e for e in es if e[0] in bs]
        local = {}
        for size in range(min(k, len(local_edges))+1):
            for removed in combinations(range(len(local_edges)), size):
                if sum(local_edges[e][2] for e in removed) > k:
                    continue
                gone = set(removed)
                parts = components(block, [(u, v) for i, (u, v, _) in enumerate(local_edges) if i not in gone])
                for values in product((0, 1), repeat=len(parts)):
                    coloring = 0
                    for part, value in zip(parts, values):
                        if value:
                            for v in part:
                                coloring |= 1 << v
                    flags, cost = 0, 0
                    for u, v, w in local_edges:
                        a, b = (coloring >> u) & 1, (coloring >> v) & 1
                        if a == b:
                            flags |= 1 << a
                        else:
                            cost += w
                    if cost <= k:
                        mask = sum(((coloring >> t) & 1) << j for j, t in enumerate(ts) if t in bs)
                        key = (mask, flags)
                        local[key] = min(local.get(key, k+1), cost)
        updated = {}
        for (x, a), ca in total.items():
            for (y, b), cb in local.items():
                if ca+cb <= k:
                    key = (x | y, a | b)
                    updated[key] = min(updated.get(key, k+1), ca+cb)
        total = updated
    return total


def combine(node: dict, keys: list[tuple[int, int]], costs: list[int]) -> tuple[tuple[int, int], int] | None:
    _, maps = child_data(node)
    values: dict[int, int] = {}
    flags = 0
    for state, mp in zip(keys, maps):
        flags |= state[1]
        for j, group in enumerate(mp):
            val = (state[0] >> j) & 1
            if group in values and values[group] != val:
                return None
            values[group] = val
    mask = sum(values[t] << j for j, t in enumerate(node["terminals"]))
    return (mask, flags), sum(costs)


def metadata(g: dict) -> list[dict]:
    """Independent boundary component graph and saturated-degree replay."""
    internal = []
    output = []
    for node in g["nodes"]:
        ts = node["terminals"]
        if node["kind"] == "leaf":
            vertices, ne = node["vertices"], len(node["edges"])
            parts = components(list(range(vertices)), [(u, v) for u, v, _ in node["edges"]])
            owners = {v: j for j, b in enumerate(parts) for v in b}
            ds = [0]*vertices
            for u, v, _ in node["edges"]:
                ds[u] += 1
                ds[v] += 1
            hidden = len(parts)-len({owners[t] for t in ts})
            canonical = {}
            partition = [canonical.setdefault(owners[t], len(canonical)) for t in ts]
            degrees = [min(4, ds[t]) for t in ts]
            ok = all(ds[v] == 3 for v in range(vertices) if v not in set(ts))
        else:
            children, maps = child_data(node)
            q = len(set(v for mp in maps for v in mp))
            links = []
            ds = [0]*q
            vertices = ne = hidden = 0
            ok = True
            for c, mp in zip(children, maps):
                cm = internal[c]
                vertices += cm[0]-len(mp)
                ne += cm[1]
                hidden += cm[3]
                ok &= cm[5]
                grouped = {}
                for i, group in enumerate(mp):
                    grouped.setdefault(cm[2][i], []).append(group)
                    ds[group] = min(4, ds[group]+cm[4][i])
                for block in grouped.values():
                    links += [(block[0], v) for v in block[1:]]
            vertices += q
            parts = components(list(range(q)), links)
            owners = {v: j for j, b in enumerate(parts) for v in b}
            hidden += len(parts)-len({owners[t] for t in ts})
            canonical = {}
            partition = [canonical.setdefault(owners[t], len(canonical)) for t in ts]
            degrees = [ds[t] for t in ts]
            ok &= all(ds[v] == 3 for v in range(q) if v not in set(ts))
        internal.append((vertices, ne, partition, hidden, degrees, bool(ok)))
        output.append({"vertices_hex": hex(vertices), "edges_hex": hex(ne), "partition": partition,
                       "hidden_components_hex": hex(hidden), "degrees_capped_at_four": degrees,
                       "interior_cubic": bool(ok)})
    return output


def read_table(rows: list, r: int, k: int) -> tuple[dict, dict]:
    table, witnesses = {}, {}
    require(isinstance(rows, list), "table rows")
    for row in rows:
        require(isinstance(row, list) and len(row) == 4, "table record")
        mask, flags, cost, wit = row
        require(natural(mask) and mask < (1 << r) and natural(flags) and flags < 4
                and natural(cost) and cost <= k, "state/cost range")
        key = (mask, flags)
        require(key not in table, "duplicate state")
        table[key], witnesses[key] = cost, wit
    return table, witnesses


def check_realization(node: dict, key: tuple, cost: int, wit: Any, get_child) -> None:
    if node["kind"] == "leaf":
        require(natural(wit) and wit < (1 << node["vertices"]), "leaf coloring range")
        require(color_key(node, wit) == (key, cost), "leaf realization")
        return
    children, _ = child_data(node)
    require(isinstance(wit, list) and len(wit) == len(children), "child references")
    keys, costs = [], []
    for child, state in zip(children, wit):
        require(isinstance(state, list) and len(state) == 2 and all(natural(x) for x in state), "child state")
        ck = tuple(state)
        cc = get_child(child, ck)
        keys.append(ck)
        costs.append(cc)
    require(combine(node, keys, costs) == (key, cost), "composed realization")


def verify_certificate(g: dict, cert: dict) -> dict:
    require(isinstance(cert, dict) and cert.get("schema") == "proveit.sparse-cut-certificate.v1", "certificate schema")
    k = cert.get("threshold")
    validate(g, k)
    require(cert.get("grammar_sha256") == digest(g), "source digest")
    nodes = g["nodes"]
    require(isinstance(cert.get("tables"), list) and len(cert["tables"]) == len(nodes), "table count")
    require(cert.get("metadata") == metadata(g), "metadata mismatch")
    tables = []
    for i, node in enumerate(nodes):
        given, witnesses = read_table(cert["tables"][i], len(node["terminals"]), k)
        if node["kind"] == "leaf":
            expected = leaf_complete(node, k)
        else:
            children, _ = child_data(node)
            expected = {}
            for combination in product(*[list(tables[c].items()) for c in children]):
                keys = [key for key, cost in combination]
                costs = [cost for key, cost in combination]
                value = combine(node, keys, costs)
                if value is not None and value[1] <= k:
                    key, cost = value
                    expected[key] = min(expected.get(key, k+1), cost)
        require(given == expected, f"incomplete/incorrect response at node {i}")
        for key, cost in given.items():
            check_realization(node, key, cost, witnesses[key], lambda c, s: tables[c][s])
        tables.append(given)
    root = g.get("root", len(nodes)-1)
    return {"verified": True, "states": sum(len(t) for t in tables),
            "root_response": [[*key, cost] for key, cost in sorted(tables[root].items())]}


def verify_witness(g: dict, witness: dict) -> dict:
    require(isinstance(witness, dict) and witness.get("schema") == "proveit.sparse-cut-witness.v1", "witness schema")
    k = witness.get("threshold")
    validate(g, k)
    require(witness.get("grammar_sha256") == digest(g), "witness digest")
    nodes, known = g["nodes"], {}
    records = witness.get("records")
    require(isinstance(records, list), "witness records")
    for row in records:
        i, state, cost, wit = row.get("node"), row.get("state"), row.get("cost"), row.get("witness")
        require(natural(i) and i < len(nodes) and isinstance(state, list) and len(state) == 2, "witness index")
        key = tuple(state)
        read_table([[*key, cost, wit]], len(nodes[i]["terminals"]), k)
        require((i, key) not in known, "duplicate witness record")
        check_realization(nodes[i], key, cost, wit, lambda c, s: known[(c, s)][0])
        known[(i, key)] = (cost, wit)
    root, state = g.get("root", len(nodes)-1), tuple(witness["root_state"])
    require((root, state) in known, "missing root witness")
    return {"verified": True, "cost": known[(root, state)][0], "flags": state[1],
            "terminal_mask": state[0], "records": len(known)}


def verify_addresses(g: dict, witness: dict, cuts: list[dict], marks: list[dict]) -> dict:
    summary = verify_witness(g, witness)
    known = {(row["node"], tuple(row["state"])): row for row in witness["records"]}
    require(isinstance(cuts, list) and isinstance(marks, list), "address lists")
    require(all(isinstance(a, dict) and "color" not in a for a in cuts), "cut address role")
    require(all(isinstance(a, dict) and natural(a.get("color")) and a["color"] < 2 for a in marks), "mark address role")
    seen, weight_sum = set(), 0
    for address in cuts + marks:
        i = g.get("root", len(g["nodes"])-1)
        key = tuple(witness["root_state"])
        for side in address["path"]:
            node = g["nodes"][i]
            children, _ = child_data(node)
            require(natural(side) and side < len(children), "address side")
            record = known[(i, key)]
            i, key = children[side], tuple(record["witness"][side])
        node = g["nodes"][i]
        require(node["kind"] == "leaf" and i == address["leaf"], "address leaf")
        e = address["edge"]
        require(natural(e) and e < len(node["edges"]), "edge index")
        u, v, w = node["edges"][e]
        require(w == address["weight"], "edge weight")
        coloring = known[(i, key)]["witness"]
        a, b = (coloring >> u) & 1, (coloring >> v) & 1
        if "color" in address:
            require(address["color"] in (0, 1) and a == b == address["color"], "mark edge")
        else:
            identity = (tuple(address["path"]), e)
            require(identity not in seen and a != b, "cut edge/duplicate")
            seen.add(identity)
            weight_sum += w
    require(weight_sum == summary["cost"], "incomplete cut addresses")
    require({m["color"] for m in marks} == {c for c in (0, 1) if summary["flags"] & (1 << c)}, "mark coverage")
    return {"verified": True, "cut_edges": len(cuts), "marks": len(marks), "cost": weight_sum}
