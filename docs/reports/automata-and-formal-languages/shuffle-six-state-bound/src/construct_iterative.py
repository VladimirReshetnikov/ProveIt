#!/usr/bin/env python3
"""Construct and independently replay a reaching word for a valid <=6-row subset.

Python 3.10+, standard library only. No SMT solver is needed.
Input JSON: {"m":6,"n":7,"cells":[[0,0],...],"root":[0,0]}.
The root is optional. Output includes the complete word and its subset trace.
"""
from __future__ import annotations
import argparse
from itertools import permutations
import json
from pathlib import Path
from typing import Iterable

Cell = tuple[int, int]
Letter = tuple[list[int], list[int]]
DEFAULT_DATA = Path(__file__).resolve().parents[1] / "data" / "certificates_masks.jsonl"


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def step(cells: set[Cell], letter: Letter) -> set[Cell]:
    f, g = letter
    return {(f[i], j) for i, j in cells} | {(i, g[j]) for i, j in cells}


def replay(m: int, n: int, root: Cell, word: list[Letter]) -> list[set[Cell]]:
    states = [{root}]
    for f, g in word:
        require(len(f) == m and len(g) == n, "letter has wrong dimensions")
        require(all(0 <= x < m for x in f), "invalid row transformation")
        require(all(0 <= x < n for x in g), "invalid column transformation")
        states.append(step(states[-1], (f, g)))
    return states


def validate_data(path: Path) -> dict[tuple[int, int], dict]:
    """Check each local certificate, independently of the C++ implementation.

    This checks the stored representatives, not exhaustive orbit coverage.
    Run verify_all.cpp for the complete finite verification.
    """
    database: dict[tuple[int, int], dict] = {}
    with path.open(encoding="utf-8") as source:
        for number, line in enumerate(source, 1):
            d = json.loads(line)
            m, n = d["m"], d["n"]
            require(1 <= m <= 6 and 1 <= n <= 64, f"bad dimensions on line {number}")
            require(len(d["columns"]) == n, "wrong target column count")
            require(d["columns"] == sorted(set(d["columns"])), "columns not distinct/sorted")
            require(d["key"] == sum(1 << a for a in d["columns"]), "bad family key")
            require(all(0 <= a < (1 << m) for a in d["columns"]), "bad target mask")
            require(len(d["predecessor"]) == n, "wrong predecessor column count")
            require(all(0 < a < (1 << m) for a in d["predecessor"]), "empty/invalid column")
            target = {(i, j) for j, a in enumerate(d["columns"])
                      for i in range(m) if a & (1 << i)}
            before = {(i, j) for j, a in enumerate(d["predecessor"])
                      for i in range(m) if a & (1 << i)}
            require({i for i, _ in before} == set(range(m)), "empty predecessor row")
            require(len(before) < len(target), "nondecreasing certificate")
            # replay also validates transformation domains.
            require(len(d["f"]) == m and len(d["g"]) == n, "bad map dimensions")
            require(all(0 <= i < m for i in d["f"]), "bad f")
            require(all(0 <= j < n for j in d["g"]), "bad g")
            require(step(before, (d["f"], d["g"])) == target, "incorrect image")
            identity = (m, d["key"])
            require(identity not in database, "duplicate certificate")
            database[identity] = d
    return database


def remove_axes(cells: set[Cell], m: int, n: int,
                row: int | None, col: int | None, root: Cell):
    rows = [i for i in range(m) if i != row]
    cols = [j for j in range(n) if j != col]
    ri = {x: i for i, x in enumerate(rows)}
    ci = {x: j for j, x in enumerate(cols)}
    smaller = {(ri[i], ci[j]) for i, j in cells if i != row and j != col}
    return smaller, rows, cols, (ri[root[0]], ci[root[1]])


def lift(word: list[Letter], m: int, n: int,
         rows: list[int], cols: list[int]) -> list[Letter]:
    answer: list[Letter] = []
    for f, g in word:
        ff, gg = list(range(m)), list(range(n))
        for i, old in enumerate(rows):
            ff[old] = rows[f[i]]
        for j, old in enumerate(cols):
            gg[old] = cols[g[j]]
        answer.append((ff, gg))
    return answer


def table_predecessor(cells: set[Cell], m: int, n: int, database: dict):
    original_columns = [sum(1 << i for i in range(m) if (i, j) in cells)
                        for j in range(n)]
    require(len(set(original_columns)) == n, "hard target has repeated columns")
    for p_tuple in permutations(range(m)):
        p = list(p_tuple)  # old row -> new row
        transformed = [sum(1 << p[i] for i in range(m) if a & (1 << i))
                       for a in original_columns]
        key = sum(1 << a for a in transformed)
        d = database.get((m, key))
        if d is None:
            continue
        ordered = sorted(transformed)
        q = [ordered.index(a) for a in transformed]  # old column -> new column
        ip, iq = [0] * m, [0] * n
        for i, x in enumerate(p):
            ip[x] = i
        for j, x in enumerate(q):
            iq[x] = j
        before = {(ip[i], iq[j]) for j, a in enumerate(d["predecessor"])
                  for i in range(m) if a & (1 << i)}
        f = [ip[d["f"][p[i]]] for i in range(m)]
        g = [iq[d["g"][q[j]]] for j in range(n)]
        require(step(before, (f, g)) == cells, "conjugation error")
        require(len(before) < len(cells), "nondecreasing conjugate")
        return before, (f, g), key
    raise ValueError("no certificate for hard case; database incomplete or input outside scope")


def construct(m: int, n: int, cells: Iterable[Cell], database: dict,
              root: Cell = (0, 0)) -> tuple[list[Letter], list[dict]]:
    require(1 <= m <= 6 and n >= 1, "requires 1 <= m <= 6 and n >= 1")
    cells = set(cells)
    require(0 <= root[0] < m and 0 <= root[1] < n, "root outside grid")
    require(all(0 <= i < m and 0 <= j < n for i, j in cells), "cell outside grid")
    require(any(i == root[0] for i, _ in cells), "target misses initial row")
    require(any(j == root[1] for _, j in cells), "target misses initial column")
    original_m, original_n, original_root, target = m, n, root, set(cells)
    frames: list[tuple] = []
    reductions: list[dict] = []
    while cells != {root}:
        require(cells, "empty intermediate state")
        rows = [{j for ii, j in cells if ii == i} for i in range(m)]
        cols = [{i for i, jj in cells if jj == j} for j in range(n)]
        empty_row = next((i for i, s in enumerate(rows) if not s), None)
        empty_col = next((j for j, s in enumerate(cols) if not s), None)
        if empty_row is not None or empty_col is not None:
            er = empty_row
            ec = empty_col if er is None else None
            small, rr, cc, newroot = remove_axes(cells, m, n, er, ec, root)
            frames.append(("lift", m, n, rr, cc))
            reductions.append({"kind": "empty-axis", "m": m, "n": n,
                               "row": er, "column": ec})
            cells, m, n, root = small, len(rr), len(cc), newroot
            continue
        found = None
        for a in range(m):
            for b in range(m):
                if a != b and rows[a] <= rows[b] and not (rows[a] == rows[b] and b == root[0]):
                    before = cells - {(b, j) for j in rows[a]}
                    f, g = list(range(m)), list(range(n))
                    f[a] = b
                    found = before, (f, g), "row-copy", a, b
                    break
            if found:
                break
        if found is None:
            for a in range(n):
                for b in range(n):
                    if a != b and cols[a] <= cols[b] and not (cols[a] == cols[b] and b == root[1]):
                        before = cells - {(i, b) for i in cols[a]}
                        f, g = list(range(m)), list(range(n))
                        g[a] = b
                        found = before, (f, g), "column-copy", a, b
                        break
                if found:
                    break
        if found is not None:
            before, letter, kind, a, b = found
            require(len(before) < len(cells) and step(before, letter) == cells, "copy error")
            require(any(i == root[0] for i, _ in before), "copy loses root row")
            require(any(j == root[1] for _, j in before), "copy loses root column")
            frames.append(("append", letter))
            reductions.append({"kind": kind, "m": m, "n": n,
                               "from": a, "to": b, "size": len(cells),
                               "predecessor_size": len(before)})
            cells = before
            continue
        isolated = next(((i, next(iter(r))) for i, r in enumerate(rows) if len(r) == 1), None)
        if isolated is not None:
            i, j = isolated
            require(cols[j] == {i}, "degree-one cell not isolated after reductions")
            rr0 = root[0] if root[0] != i else next(r for r in range(m) if r != i)
            cc0 = root[1] if root[1] != j else next(c for c in range(n) if c != j)
            f, g = list(range(m)), list(range(n))
            f[i], f[rr0] = rr0, i
            g[j], g[cc0] = cc0, j
            count = 2 if root in {(i, j), (rr0, cc0)} else 1
            prefix = [(f, g) for _ in range(count)]
            require(replay(m, n, root, prefix)[-1] == {(i, j), (rr0, cc0)}, "seed error")
            small, rr, cc, newroot = remove_axes(cells, m, n, i, j, (rr0, cc0))
            frames.append(("isolate", m, n, rr, cc, prefix))
            reductions.append({"kind": "isolated-cell", "m": m, "n": n,
                               "cell": [i, j], "seed_length": count})
            cells, m, n, root = small, len(rr), len(cc), newroot
            continue
        before, letter, key = table_predecessor(cells, m, n, database)
        frames.append(("append", letter))
        reductions.append({"kind": "table", "m": m, "n": n, "key": key,
                           "size": len(cells), "predecessor_size": len(before)})
        cells = before
    word: list[Letter] = []
    for frame in reversed(frames):
        if frame[0] == "append":
            word.append(frame[1])
        elif frame[0] == "lift":
            _, mm, nn, rr, cc = frame
            word = lift(word, mm, nn, rr, cc)
        else:
            _, mm, nn, rr, cc, prefix = frame
            word = prefix + lift(word, mm, nn, rr, cc)
    states = replay(original_m, original_n, original_root, word)
    require(states[-1] == target, "final replay failed")
    bound = len(target) + min(len({i for i, _ in target}), len({j for _, j in target})) - 2
    require(len(word) <= bound, "word-length bound failed")
    return word, reductions


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--data", type=Path, default=DEFAULT_DATA)
    args = parser.parse_args()
    database = validate_data(args.data)
    d = json.loads(args.input.read_text(encoding="utf-8"))
    root = tuple(d.get("root", [0, 0]))
    cells = {tuple(c) for c in d["cells"]}
    word, reductions = construct(d["m"], d["n"], cells, database, root)
    states = replay(d["m"], d["n"], root, word)
    result = {"m": d["m"], "n": d["n"], "root": root,
              "target": sorted(cells), "length": len(word),
              "word": [{"f": f, "g": g} for f, g in word],
              "trace": [sorted(s) for s in states], "reductions": reductions}
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(f"Verified word of length {len(word)}; output: {args.output}")


if __name__ == "__main__":
    main()
