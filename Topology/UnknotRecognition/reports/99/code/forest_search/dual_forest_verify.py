"""Independent finite verifier for dual forest / unsigned peeling certificates.

Imports no producer code.  Successful verification concerns the supplied
graph and incidence matrix only; source geometry is a separate obligation.
"""


class Rejected(ValueError):
    pass


def _int(value):
    return type(value) is int


def _require(condition, message):
    if not condition:
        raise Rejected(message)


def _read(problem):
    _require(type(problem) is dict and set(problem) == {"vertices", "columns", "edges", "rows"},
             "invalid problem fields")
    vertices, columns = problem["vertices"], problem["columns"]
    _require(_int(vertices) and vertices >= 1, "invalid vertices")
    _require(_int(columns) and columns >= 0, "invalid columns")
    edge_input, row_input = problem["edges"], problem["rows"]
    _require(isinstance(edge_input, (list, tuple)) and isinstance(row_input, (list, tuple)),
             "invalid source lists")
    _require(len(edge_input) == len(row_input), "edge/row count mismatch")
    edges, rows = [], []
    for edge in edge_input:
        if edge is None:
            edges.append(None)
        else:
            _require(isinstance(edge, (list, tuple)) and len(edge) == 2, "invalid source edge")
            _require(all(_int(x) and 0 <= x < vertices for x in edge), "invalid source endpoint")
            edges.append((edge[0], edge[1]))
    for record in row_input:
        _require(isinstance(record, (list, tuple)), "invalid source row")
        row = {}
        for pair in record:
            _require(isinstance(pair, (list, tuple)) and len(pair) == 2, "invalid source pair")
            c, a = pair
            _require(_int(c) and 0 <= c < columns and _int(a) and a > 0,
                     "invalid source incidence")
            _require(c not in row, "duplicate source incidence")
            row[c] = 1 if a == 1 else 2
        rows.append(row)
    return vertices, columns, edges, rows


def _row_set(record, number, label, nonempty=False):
    _require(isinstance(record, (list, tuple)), "invalid " + label)
    _require(all(_int(r) and 0 <= r < number for r in record), "out of range " + label)
    result = set(record)
    _require(len(result) == len(record), "duplicate " + label)
    _require(bool(result) or not nonempty, "empty " + label)
    return result


def _partition_after(edges, chosen):
    # This checker uses explicit set-of-vertices blocks, deliberately separate
    # from the producer's union-find and all of its search routines.
    blocks = []
    rank = 0
    for e in chosen:
        edge = edges[e]
        _require(edge is not None, "selected ineligible edge")
        u, v = edge
        ui = next((i for i, block in enumerate(blocks) if u in block), None)
        vi = next((i for i, block in enumerate(blocks) if v in block), None)
        if u == v or (ui is not None and ui == vi):
            continue
        rank += 1
        if ui is None and vi is None:
            blocks.append({u, v})
        elif ui is None:
            blocks[vi].add(u)
        elif vi is None:
            blocks[ui].add(v)
        else:
            blocks[ui].update(blocks[vi])
            del blocks[vi]
    return blocks, rank


def _same_component(blocks, u, v):
    return u == v or any(u in block and v in block for block in blocks)


def _stopping(rows, witness, deleted):
    selected = _row_set(witness, len(rows), "stopping witness", nonempty=True)
    _require(selected.isdisjoint(deleted), "stopping witness contains a deleted row")
    totals = {}
    for r in selected:
        for c, a in rows[r].items():
            totals[c] = min(2, totals.get(c, 0) + a)
    _require(all(a != 1 for a in totals.values()), "witness is not a stopping set")
    return selected


def _success(data, certificate):
    vertices, columns, edges, rows = data
    _require(set(certificate) == {"kind", "tree", "peeling"}, "invalid success fields")
    tree = _row_set(certificate["tree"], len(rows), "tree")
    _require(len(tree) == vertices - 1, "incorrect spanning tree cardinality")
    _, rank = _partition_after(edges, sorted(tree))
    _require(rank == vertices - 1, "tree is cyclic or disconnected")
    moves = certificate["peeling"]
    _require(isinstance(moves, (list, tuple)), "invalid peeling sequence")
    times, pivots = {}, set()
    for t, move in enumerate(moves):
        _require(isinstance(move, (list, tuple)) and len(move) == 2, "invalid peeling move")
        r, c = move
        _require(_int(r) and 0 <= r < len(rows) and r not in tree and r not in times,
                 "invalid peeling row")
        _require(_int(c) and 0 <= c < columns and c not in pivots, "invalid pivot column")
        _require(rows[r].get(c, 0) == 1, "pivot is not a unit source incidence")
        times[r] = t
        pivots.add(c)
    _require(set(times) == set(range(len(rows))) - tree, "peeling does not cover surviving rows")
    pivot_time = {c: (t, r) for r, c in moves for t in [times[r]]}
    for r, row in enumerate(rows):
        if r in tree:
            continue
        for c in row:
            if c in pivot_time:
                t, owner = pivot_time[c]
                if r != owner:
                    _require(times[r] < t, "source incidence survives at a claimed leaf pivot")


def _negative(data, certificate):
    vertices, _, edges, rows = data
    pending = [(certificate, frozenset())]
    while pending:
        node, deleted = pending.pop()
        _require(type(node) is dict and type(node.get("kind")) is str, "invalid proof node")
        blocks, rank = _partition_after(edges, sorted(deleted))
        _require(rank == len(deleted), "proof path is not an independent forest")
        kind = node["kind"]
        if kind == "unrooted":
            _require(not deleted and set(node) == {"kind", "vertices"}, "invalid unrooted fields")
            cut = _row_set(node["vertices"], vertices, "unrooted vertex cut", nonempty=True)
            _require(0 not in cut, "unrooted cut contains root")
            for edge in edges:
                if edge is not None:
                    _require((edge[0] in cut) == (edge[1] in cut), "source edge crosses unrooted cut")
        elif kind == "rank_obstruction":
            _require(set(node) == {"kind", "stopping_sets", "rank"}, "invalid rank proof fields")
            family = node["stopping_sets"]
            _require(isinstance(family, (list, tuple)) and family, "empty stopping family")
            used, ground = set(), set()
            for record in family:
                stop = _stopping(rows, record, deleted)
                _require(used.isdisjoint(stop), "rank witnesses overlap")
                used.update(stop)
                ground.update(r for r in stop if edges[r] is not None)
            _, extended_rank = _partition_after(edges, sorted(set(deleted) | ground))
            relative_rank = extended_rank - rank
            _require(_int(node["rank"]) and node["rank"] == relative_rank, "incorrect rank value")
            _require(relative_rank < len(family), "no rank defect")
        elif kind in ("split", "blocked"):
            required = {"kind", "witness", "children"} if kind == "split" else {"kind", "witness"}
            _require(set(node) == required, "invalid stopping node fields")
            witness = _stopping(rows, node["witness"], deleted)
            possible = {r for r in witness if edges[r] is not None
                        and not _same_component(blocks, *edges[r])}
            if kind == "blocked":
                _require(not possible, "blocked node has an independent candidate")
                continue
            children = node["children"]
            _require(isinstance(children, (list, tuple)) and possible, "invalid split children")
            seen = set()
            for child in children:
                _require(type(child) is dict and set(child) == {"row", "proof"}, "invalid child")
                e = child["row"]
                _require(_int(e) and e in possible and e not in seen, "incorrect or repeated branch")
                seen.add(e)
                pending.append((child["proof"], deleted | {e}))
            _require(seen == possible, "split omits an independent candidate")
        else:
            raise Rejected("unknown negative proof node")


def check_result(problem, result):
    """Return (accepted, explanation); INCONCLUSIVE has no affirmative proof."""
    try:
        data = _read(problem)
        _require(type(result) is dict, "invalid result")
        status = result.get("status")
        proof = result.get("certificate")
        _require(type(proof) is dict, "no complete certificate")
        if status == "SUCCESS":
            _require(proof.get("kind") == "success", "wrong positive certificate type")
            _success(data, proof)
        elif status == "NO_FOREST":
            _negative(data, proof)
        else:
            raise Rejected("result makes no completed certificate claim")
        return True, "verified for supplied graph and unsigned incidence"
    except (Rejected, KeyError, TypeError, IndexError, ValueError) as error:
        return False, str(error)


def verify(problem, result):
    return check_result(problem, result)[0]


def main():
    import argparse
    import json
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("problem")
    parser.add_argument("result")
    args = parser.parse_args()
    with open(args.problem, encoding="utf-8") as stream:
        problem = json.load(stream)
    with open(args.result, encoding="utf-8") as stream:
        result = json.load(stream)
    good, reason = check_result(problem, result)
    print(json.dumps({"accepted": good, "reason": reason}, indent=2))
    raise SystemExit(0 if good else 1)


if __name__ == "__main__":
    main()
