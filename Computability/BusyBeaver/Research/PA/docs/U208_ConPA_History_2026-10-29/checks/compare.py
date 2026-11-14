#!/usr/bin/env python3
"""Independent comparison of the five frozen U209 packets."""
import collections
import hashlib
import json
import argparse
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = Path(__file__).resolve().parent


def digest(data):
    return hashlib.sha256(data).hexdigest()


def encode(value):
    return json.dumps(value, separators=(",", ":")).encode()


def table(path):
    result = {}
    for line in path.read_text().splitlines():
        if not line or line.startswith("#"):
            continue
        q, b, w, d, r = line.split()
        q, b, w, r = map(int, (q, b, w, r))
        if (q, b) in result or b not in (0, 1) or w not in (0, 1) or d not in ("L", "R"):
            raise ValueError("Malformed table")
        result[q, b] = (w, d, r)
    return result


def canonical(t):
    states = {q for q, b in t}
    if set(t) != {(q, b) for q in states for b in (0, 1)}:
        raise ValueError("Incomplete table")
    halts = {r for w, d, r in t.values()} - states
    if len(halts) != 1:
        raise ValueError("Expected one halt")
    halt = next(iter(halts))
    ids = {0: 0}
    words = {0: ""}
    queue = [0]
    result = []
    for q in queue:
        for b in (0, 1):
            w, d, r = t[q, b]
            if r == halt:
                target = "H"
            else:
                if r not in ids:
                    ids[r] = len(ids)
                    words[r] = words[q] + str(b)
                    queue.append(r)
                target = ids[r]
            result.append([ids[q], b, w, d, target])
    if set(ids) != states:
        raise ValueError("Graph-unreachable working states")
    return result, ids, words, halt


def source(rows):
    paths = [p for p, _, _ in rows]
    if paths != sorted(paths) or len(set(paths)) != len(paths):
        raise ValueError("Invalid leaf order")
    intervals = {}
    subtrees = {}
    leaves = {p: (op, arg) for p, op, arg in rows}
    def visit(p, index):
        first = index
        if p in leaves:
            value = leaves[p]
            index += 1
        else:
            if not any(x.startswith(p) for x in paths):
                raise ValueError("Incomplete source tree")
            left, index = visit(p + "0", index)
            right, index = visit(p + "1", index)
            value = (left, right)
        intervals[p] = (first, index)
        subtrees[p] = value
        return value, index
    _, size = visit("", 0)
    if size != len(rows):
        raise ValueError("Invalid source size")
    graph = []
    for index, (p, op, arg) in enumerate(rows):
        if op == "CH":
            succ = []
        elif op == "CI":
            succ = [(index + 1) % size]
        else:
            bit = "1" if op == "CC" else "0"
            count = 1 if op == "CD" else arg
            positions = [i for i, x in enumerate(p) if x == bit]
            if count <= 0 or count > len(positions):
                raise ValueError("Unbound control branch")
            ancestor = p[:positions[-count]]
            endpoint = intervals[ancestor][0 if bit == "1" else 1] % size
            succ = [endpoint, (index + 1) % size] if op == "CD" else [endpoint]
        graph.append([op, arg, succ])
    return graph, {
        "primitives": size,
        "distinct_subtrees": len(set(subtrees.values())),
        "maximum_depth": max(map(len, paths)),
        "maximum_zero_run": max(len(x) for p in paths for x in p.split("1")),
        "control_edges": sum(len(x[2]) for x in graph),
    }


def main():
    records = []
    models = {}
    for p in sorted((ROOT / "comparison").glob("U209*/u209.tm")):
        package = p.parent
        short = p.parent.name
        source_path = package / "sites.json"
        if not source_path.exists():
            source_path = package / "source/u209.sites.json"
        rows = json.loads(source_path.read_text())
        graph, metrics = source(rows)
        t = table(package / "u209.native.tm")
        c, ids, words, halt = canonical(t)
        models[short] = (t, c, ids, halt)
        record = {
            "package": str(package.relative_to(ROOT)),
            "dense_sha256": digest(p.read_bytes()),
            "native_sha256": digest((package / "u209.native.tm").read_bytes()),
            "source_sha256": digest(source_path.read_bytes()),
            "source_word_sha256": digest(encode([[op, arg] for _, op, arg in rows])),
            "source_cfg_sha256": digest(encode(graph)),
            "canonical_graph_sha256": digest(encode(c)),
            "working_states": len(ids),
            "literal_rows": len(t),
            "graph_reachable_working_states": len(ids),
            **metrics,
        }
        records.append(record)
    isomorphisms = []
    names = list(models)
    for i, x in enumerate(names):
        tx, cx, ix, hx = models[x]
        for y in names[i + 1:]:
            ty, cy, iy, hy = models[y]
            same = cx == cy
            record = {"first": x, "second": y, "rooted_isomorphic": same}
            if same:
                inverse = {v: q for q, v in iy.items()}
                rename = {q: inverse[v] for q, v in ix.items()}
                rename[hx] = hy
                converted = {(rename[q], b): (w, d, rename[r]) for (q, b), (w, d, r) in tx.items()}
                if converted != ty or rename[0] != 0:
                    raise ValueError("Isomorphism failed direct replay")
                record["nonidentity_native_map"] = {str(q): r for q, r in rename.items() if q != r}
            else:
                record["first_canonical_row_difference"] = next([a, b] for a, b in zip(cx, cy) if a != b)
            isomorphisms.append(record)
    result = {
        "status": "FIVE_PACKETS_TWO_ROOTED_ISOMORPHISM_CLASSES",
        "proposals": records,
        "same_primitive_word": len({r["source_word_sha256"] for r in records}) == 1,
        "same_ordinal_control_graph": len({r["source_cfg_sha256"] for r in records}) == 1,
        "isomorphisms": isomorphisms,
        "scope": "Literal-state graph identity and source semantics; not end-to-end proof-assistant certification.",
    }
    parser = argparse.ArgumentParser()
    parser.add_argument("--output",type=Path,default=ROOT / "build/comparison.json")
    args=parser.parse_args()
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
