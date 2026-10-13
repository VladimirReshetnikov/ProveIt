"""Exact dual-forest selection with immutable unsigned row incidence.

This is a finite graph/matrix operator.  It does not authenticate a manifold
and does not issue knot or nonball verdicts.  All integers are exact.

Input: {'vertices': positive int, 'columns': nonnegative int,
        'edges': [[u,v] or None, ...],
        'rows': [[[column, positive_count], ...], ...]}.
Vertex 0 is the distinguished boundary root.  An edge is associated with
one matrix row; None marks a row unavailable for top-handle cancellation.
Counts are capped at two on input, preserving all decisions below.
"""

from collections import deque


class InvalidProblem(ValueError):
    pass


class BudgetExhausted(RuntimeError):
    pass


def _integer(x):
    return isinstance(x, int) and not isinstance(x, bool)


def normalize(problem):
    if not isinstance(problem, dict):
        raise InvalidProblem("problem must be a dictionary")
    if set(problem) != {"vertices", "columns", "edges", "rows"}:
        raise InvalidProblem("unexpected or missing problem fields")
    v, h = problem["vertices"], problem["columns"]
    if not _integer(v) or v < 1 or not _integer(h) or h < 0:
        raise InvalidProblem("invalid vertex or column count")
    edges, rows = problem["edges"], problem["rows"]
    if not isinstance(edges, (tuple, list)) or not isinstance(rows, (tuple, list)):
        raise InvalidProblem("edges and rows must be sequences")
    if len(edges) != len(rows):
        raise InvalidProblem("exactly one edge record per row is required")
    ee, aa = [], []
    for edge, row in zip(edges, rows):
        if edge is None:
            ee.append(None)
        else:
            if not isinstance(edge, (tuple, list)) or len(edge) != 2:
                raise InvalidProblem("invalid edge")
            if any(not _integer(x) or not 0 <= x < v for x in edge):
                raise InvalidProblem("edge endpoint outside namespace")
            ee.append(tuple(edge))
        if not isinstance(row, (tuple, list)):
            raise InvalidProblem("invalid sparse row")
        values = {}
        for item in row:
            if not isinstance(item, (tuple, list)) or len(item) != 2:
                raise InvalidProblem("invalid sparse incidence")
            c, a = item
            if not _integer(c) or not 0 <= c < h or not _integer(a) or a < 1:
                raise InvalidProblem("invalid column or count")
            if c in values:
                raise InvalidProblem("duplicate sparse column")
            values[c] = min(2, a)
        aa.append(tuple(sorted(values.items())))
    return v, h, tuple(ee), tuple(aa)


class Work:
    def __init__(self, max_work=None, max_nodes=None):
        for name, value in (("max_work", max_work), ("max_nodes", max_nodes)):
            if value is not None and (not _integer(value) or value < 0):
                raise InvalidProblem("invalid " + name)
        self.maximum = max_work
        self.max_nodes = max_nodes
        self.counts = {}
        self.total = 0

    def tick(self, label, amount=1):
        self.counts[label] = self.counts.get(label, 0) + amount
        self.total += amount
        if self.maximum is not None and self.total > self.maximum:
            raise BudgetExhausted("structural work budget exhausted")
        if label == "search_nodes" and self.max_nodes is not None:
            if self.counts[label] > self.max_nodes:
                raise BudgetExhausted("search node budget exhausted")

    def export(self):
        return dict(self.counts, structural_work=self.total)


class DSU:
    def __init__(self):
        self.parent = {}
        self.size = {}

    def find(self, x):
        if x not in self.parent:
            self.parent[x] = x
            self.size[x] = 1
        root = x
        while self.parent[root] != root:
            root = self.parent[root]
        while self.parent[x] != x:
            previous = x
            x = self.parent[x]
            self.parent[previous] = root
        return root

    def join(self, u, v):
        u, v = self.find(u), self.find(v)
        if u == v:
            return False
        if self.size[u] < self.size[v]:
            u, v = v, u
        self.parent[v] = u
        self.size[u] += self.size[v]
        return True


def _source_connectivity(data, work):
    v, _, edges, _ = data
    adjacency = {0: []}
    for edge in edges:
        work.tick("graph_edge_visits")
        if edge is not None:
            a, b = edge
            adjacency.setdefault(a, []).append(b)
            adjacency.setdefault(b, []).append(a)
    # A huge binary namespace with omitted vertices is rejected without a
    # huge array allocation; its least omitted vertex is a one-vertex cut.
    if len(adjacency) < v:
        absent = 0
        for x in sorted(adjacency):
            if x != absent:
                break
            absent += 1
        return {"kind": "unrooted", "vertices": [absent]}
    reached, queue = {0}, deque([0])
    while queue:
        for y in adjacency[queue.popleft()]:
            work.tick("graph_arc_visits")
            if y not in reached:
                reached.add(y)
                queue.append(y)
    if len(reached) != v:
        return {"kind": "unrooted", "vertices": sorted(set(adjacency) - reached)}
    return None


def _forest(data, selected, work):
    dsu = DSU()
    for e in selected:
        work.tick("forest_edge_visits")
        edge = data[2][e]
        if edge is None or not dsu.join(*edge):
            raise AssertionError("internal selected set is not a forest")
    return dsu


def _extend_tree(data, selected, work):
    dsu = _forest(data, selected, work)
    chosen = set(selected)
    for e, edge in enumerate(data[2]):
        work.tick("extension_edge_visits")
        if edge is not None and e not in chosen and dsu.join(*edge):
            chosen.add(e)
    if len(chosen) != data[0] - 1:
        raise AssertionError("connected graph forest failed to extend")
    return sorted(chosen)


def _peel(data, row_ids, work):
    rows = data[3]
    live = set(row_ids)
    totals, owner = {}, {}
    for r in sorted(live):
        work.tick("peel_row_visits")
        for c, a in rows[r]:
            work.tick("peel_incidence_visits")
            totals[c] = totals.get(c, 0) + a
            owner[c] = owner.get(c, 0) ^ r
    queue = deque(sorted(c for c, a in totals.items() if a == 1))
    schedule = []
    work.tick("peel_calls")
    while queue:
        c = queue.popleft()
        work.tick("peel_queue_pops")
        if totals[c] != 1:
            continue
        r = owner[c]
        if r not in live:
            raise AssertionError("stale sole owner")
        live.remove(r)
        schedule.append([r, c])
        for h, a in rows[r]:
            work.tick("peel_removal_visits")
            totals[h] -= a
            owner[h] ^= r
            if totals[h] == 1:
                queue.append(h)
    return schedule, sorted(live)


def _minimize_stop(data, stop, work):
    current = set(stop)
    for row in stop:
        if row not in current:
            continue
        work.tick("witness_minimization_calls")
        _, residual = _peel(data, current - {row}, work)
        if residual:
            current = set(residual)
    return sorted(current)


def _positive(data, selected, work):
    tree = _extend_tree(data, selected, work)
    schedule, residual = _peel(data, set(range(len(data[3]))) - set(tree), work)
    if residual:
        raise AssertionError("claimed success did not survive tree extension")
    return {"kind": "success", "tree": tree, "peeling": schedule}


def solve_by_stopping(problem, *, minimize_witness=True, max_work=None, max_nodes=None):
    """Complete obstruction-guided search; exhaustion is class-specific."""
    data = normalize(problem)
    work = Work(max_work, max_nodes)
    if not isinstance(minimize_witness, bool):
        raise InvalidProblem("minimize_witness must be Boolean")
    try:
        failure = _source_connectivity(data, work)
        if failure:
            return {"status": "NO_FOREST", "certificate": failure,
                    "method": "stopping_search", "stats": work.export()}

        def search(selected):
            work.tick("search_nodes")
            dsu = _forest(data, selected, work)
            _, residual = _peel(data, set(range(len(data[3]))) - set(selected), work)
            if not residual:
                work.tick("success_leaves")
                return True, _positive(data, selected, work)
            witness = _minimize_stop(data, residual, work) if minimize_witness else residual
            eligible = []
            for e in witness:
                work.tick("candidate_edge_tests")
                edge = data[2][e]
                if edge is not None and dsu.find(edge[0]) != dsu.find(edge[1]):
                    eligible.append(e)
            if not eligible:
                work.tick("blocked_leaves")
                return False, {"kind": "blocked", "witness": witness}
            children = []
            if len(eligible) == 1:
                work.tick("forced_choices")
            for e in eligible:
                work.tick("branch_edges")
                yes, proof = search(tuple(sorted((*selected, e))))
                if yes:
                    return True, proof
                children.append({"row": e, "proof": proof})
            return False, {"kind": "split", "witness": witness, "children": children}

        yes, proof = search(())
        return {"status": "SUCCESS" if yes else "NO_FOREST", "certificate": proof,
                "method": "stopping_search", "stats": work.export()}
    except (BudgetExhausted, RecursionError) as error:
        return {"status": "INCONCLUSIVE", "reason": str(error),
                "method": "stopping_search", "stats": work.export()}


def _degree_two_groups(data, work):
    """Return seed-free source SCC row groups, or None outside the regime."""
    rows = data[3]
    owners = {}
    for r, row in enumerate(rows):
        for c, a in row:
            work.tick("dependency_incidence_visits")
            owners.setdefault(c, []).append((r, a))
    outgoing = [[] for _ in rows]
    incoming = [[] for _ in rows]
    seeds = set()
    for occupants in owners.values():
        if not any(a == 1 for _, a in occupants):
            continue  # An inert column can never offer a raw unit pivot.
        if len(occupants) > 2:
            return None
        if len(occupants) == 1:
            seeds.add(occupants[0][0])
        else:
            for target, a in occupants:
                if a == 1:
                    source = occupants[1][0] if target == occupants[0][0] else occupants[0][0]
                    outgoing[source].append(target)
                    incoming[target].append(source)
                    work.tick("dependency_arcs")
    # Iterative Kosaraju keeps recursion depth independent of source size.
    seen, finish = set(), []
    for initial in range(len(rows)):
        if initial in seen:
            continue
        seen.add(initial)
        stack = [(initial, 0)]
        while stack:
            u, index = stack[-1]
            work.tick("scc_stack_steps")
            if index < len(outgoing[u]):
                v = outgoing[u][index]
                stack[-1] = (u, index + 1)
                if v not in seen:
                    seen.add(v)
                    stack.append((v, 0))
            else:
                finish.append(u)
                stack.pop()
    component = [-1] * len(rows)
    groups = []
    for initial in reversed(finish):
        if component[initial] != -1:
            continue
        label = len(groups)
        group, stack = [], [initial]
        component[initial] = label
        while stack:
            u = stack.pop()
            group.append(u)
            work.tick("scc_vertex_visits")
            for v in incoming[u]:
                if component[v] == -1:
                    component[v] = label
                    stack.append(v)
        groups.append(sorted(group))
    source = [True] * len(groups)
    for u, targets in enumerate(outgoing):
        for v in targets:
            if component[u] != component[v]:
                source[component[v]] = False
    return sorted((group for i, group in enumerate(groups)
                   if source[i] and seeds.isdisjoint(group)), key=lambda group: group[0])


def _graphic_independent(data, members, work):
    dsu = DSU()
    work.tick("graphic_oracle_calls")
    for e in sorted(members):
        work.tick("graphic_oracle_edge_visits")
        if data[2][e] is None or not dsu.join(*data[2][e]):
            return False
    return True


def _rainbow_forest(data, groups, work):
    """Standard shortest augmenting paths for graphic/partition intersection."""
    color = {e: i for i, group in enumerate(groups) for e in group if data[2][e] is not None}
    ground = sorted(color)
    chosen = set()
    while len(chosen) < len(groups):
        work.tick("matroid_augmentation_rounds")
        outside = [e for e in ground if e not in chosen]
        used = {color[e] for e in chosen}
        sources = [e for e in outside if _graphic_independent(data, chosen | {e}, work)]
        parent = {e: None for e in sources}
        queue = deque(sources)
        terminal = None
        while queue:
            u = queue.popleft()
            work.tick("exchange_queue_pops")
            if u not in chosen and color[u] not in used:
                terminal = u
                break
            if u not in chosen:
                # Exchange in the partition matroid: same color, or a color
                # not yet present (the latter case was already a terminal).
                neighbors = [f for f in sorted(chosen)
                             if color[u] == color[f] or color[u] not in used]
                work.tick("partition_exchange_tests", len(chosen))
            else:
                neighbors = [e for e in outside
                             if _graphic_independent(data, (chosen - {u}) | {e}, work)]
            for v in neighbors:
                if v not in parent:
                    parent[v] = u
                    queue.append(v)
        if terminal is None:
            represented = {color[e] for e in parent}
            missing = [i for i in range(len(groups)) if i not in represented]
            obstruction = [groups[i] for i in missing]
            # The standard matroid-intersection min-max witness yields a
            # Rado defect.  Check it again before emitting a negative result.
            dsu, rank = DSU(), 0
            for group in obstruction:
                for e in group:
                    edge = data[2][e]
                    work.tick("rado_rank_edge_visits")
                    if edge is not None and dsu.join(*edge):
                        rank += 1
            if not obstruction or rank >= len(obstruction):
                raise AssertionError("invalid matroid-intersection Rado witness")
            return None, {"kind": "rank_obstruction", "stopping_sets": obstruction, "rank": rank}
        path = []
        while terminal is not None:
            path.append(terminal)
            terminal = parent[terminal]
        work.tick("matroid_path_vertices", len(path))
        chosen.symmetric_difference_update(path)
        if len({color[e] for e in chosen}) != len(chosen):
            raise AssertionError("augmenting path lost partition independence")
        if not _graphic_independent(data, chosen, work):
            raise AssertionError("augmenting path lost graphic independence")
        work.tick("matroid_augmentations")
    return sorted(chosen), None


def solve_degree_two(problem, *, max_work=None):
    """Polynomial exact solver when every non-inert column has support <= 2."""
    data = normalize(problem)
    work = Work(max_work)
    try:
        failure = _source_connectivity(data, work)
        if failure:
            return {"status": "NO_FOREST", "certificate": failure,
                    "method": "degree_two", "stats": work.export()}
        groups = _degree_two_groups(data, work)
        if groups is None:
            return {"status": "INCONCLUSIVE", "reason": "non-inert column support exceeds two",
                    "method": "degree_two", "stats": work.export()}
        work.tick("source_scc_groups", len(groups))
        selected, failure = _rainbow_forest(data, groups, work)
        proof = failure if failure is not None else _positive(data, selected, work)
        return {"status": "NO_FOREST" if failure else "SUCCESS", "certificate": proof,
                "method": "degree_two", "stats": work.export()}
    except BudgetExhausted as error:
        return {"status": "INCONCLUSIVE", "reason": str(error),
                "method": "degree_two", "stats": work.export()}


def from_dense(vertices, edges, matrix, columns=None):
    """Convenience encoder; the solver itself remains sparse."""
    width = columns if columns is not None else (len(matrix[0]) if matrix else 0)
    if any(len(row) != width for row in matrix):
        raise InvalidProblem("dense row widths disagree")
    return {"vertices": vertices, "columns": width, "edges": edges,
            "rows": [[[c, a] for c, a in enumerate(row) if a] for row in matrix]}


def main():
    import argparse
    import json
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input")
    parser.add_argument("--method", choices=("degree-two", "search"), default="degree-two")
    parser.add_argument("--max-work", type=int)
    parser.add_argument("--max-nodes", type=int)
    parser.add_argument("--no-minimize", action="store_true")
    args = parser.parse_args()
    with open(args.input, encoding="utf-8") as stream:
        problem = json.load(stream)
    if args.method == "degree-two":
        result = solve_degree_two(problem, max_work=args.max_work)
    else:
        result = solve_by_stopping(problem, minimize_witness=not args.no_minimize,
                                  max_work=args.max_work, max_nodes=args.max_nodes)
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
