"""Independent standard-library replay of the abstract triangle witness.

Imports no forest selector, peeling implementation, or topology library.
"""

import json
from pathlib import Path


def check(path):
    packet = json.loads(Path(path).read_text(encoding="utf-8"))
    problem = packet["problem"]
    n, columns = problem["vertices"], problem["columns"]
    edges = problem["edges"]
    rows = [dict(row) for row in problem["rows"]]
    supports = packet["triangle_columns"]
    assert len(supports) == columns
    assert len(rows) == len(edges)
    for c, support in enumerate(supports):
        assert len(support) == len(set(support)) == 3
        assert {r for r, row in enumerate(rows) if row.get(c, 0)} == set(support)
        degree = [0] * n
        for r in support:
            assert rows[r][c] == 1
            a, b = edges[r]
            assert a != b
            degree[a] += 1
            degree[b] += 1
        assert sorted(d for d in degree if d) == [2, 2, 2]
    assert all(a == 1 for row in rows for a in row.values())

    def replay(witness):
        tree = witness["tree"]
        assert len(tree) == len(set(tree)) == n - 1
        adjacency = [[] for _ in range(n)]
        for r in tree:
            a, b = edges[r]
            assert a != b
            adjacency[a].append(b)
            adjacency[b].append(a)
        seen, frontier = {0}, [0]
        while frontier:
            for v in adjacency[frontier.pop()]:
                if v not in seen:
                    seen.add(v)
                    frontier.append(v)
        assert len(seen) == n  # Connected with n-1 edges is a tree.
        live = set(range(len(rows))) - set(tree)
        used_columns = set()
        for r, c in witness["peeling"]:
            assert r in live and c not in used_columns
            assert rows[r].get(c, 0) == 1
            assert sum(rows[s].get(c, 0) for s in live) == 1
            live.remove(r)
            used_columns.add(c)
        return live

    assert not replay(packet["successful"])
    residual = replay(packet["failing"])
    assert residual and sorted(residual) == packet["failing"]["stopping_residual"]
    totals = [sum(rows[r].get(c, 0) for r in residual) for c in range(columns)]
    assert totals == packet["failing"]["column_totals"]
    assert all(total != 1 for total in totals)
    return dict(status="VERIFIED", vertices=n, rows=len(rows), columns=columns,
                successful_peels=len(packet["successful"]["peeling"]),
                failing_peels=len(packet["failing"]["peeling"]),
                stopping_rows=len(residual), parity_compatible_columns=columns,
                scope="abstract graph/matrix witness; no native realization")


if __name__ == "__main__":
    import sys
    path = (sys.argv[1] if len(sys.argv) > 1 else
            Path(__file__).with_name("triangle_tree_sensitivity.json"))
    print(json.dumps(check(path), indent=2))
