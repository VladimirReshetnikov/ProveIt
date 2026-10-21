"""Build dag219: dag222 with the equality test (node 123) replaced by Source 140's routine.

  python make_dag219.py DAG222_NODES_JSON OUT_DIR

The new routine (candidate-k219/new_equality_macro.json), with D_i = decnz i, C_j = cont j,
B = brk 1:

  P = (D6, C2)   U = (P, B)   A = (D5, U)   L = (A, D6)
  Z = (D5, C1)   R = (Z, U)   E = (L, R)

Node 123 becomes E = (L, R); P, U, A, L, Z, R are appended as nodes 461..466 (U is shared by A
and R, the open-subtree sharing of Source 140). Every other node of dag222 keeps its number,
so the program-level proofs about dag222 carry over textually; only the equality test's two
lemmas are proved anew. Writes OUT_DIR/dag219_nodes.json (same format as dag222_nodes.json)
and OUT_DIR/dag219_sites.json (the leaves of ptree, as [bits, op, arg]).
"""
import json, sys
from pathlib import Path

sys.setrecursionlimit(100000)


def sites(nodes, root, nn):
    out = []

    def go(n, fuel, path):
        if fuel == 0:
            return
        a, b = nodes[n]
        for bit, e in (("0", a), ("1", b)):
            if e[0] == "N":
                if fuel - 1 == 0:
                    continue
                go(e[1], fuel - 1, path + bit)
            else:
                out.append([path + bit, e[0], e[1]])

    go(root, nn + 1, "")
    return out


def main(src, outdir):
    d = json.load(open(src))
    nn = d["nnodes"]
    assert nn == 461
    nodes = {int(k): (tuple(v[0]), tuple(v[1])) for k, v in d["nodes"].items()}
    P, U, A, L, Z, R = range(461, 467)
    nodes[P] = (("EDecnz", 6), ("EContinue", 2))
    nodes[U] = (("N", P), ("EBreak", 1))
    nodes[A] = (("EDecnz", 5), ("N", U))
    nodes[L] = (("N", A), ("EDecnz", 6))
    nodes[Z] = (("EDecnz", 5), ("EContinue", 1))
    nodes[R] = (("N", Z), ("N", U))
    nodes[123] = (("N", L), ("N", R))
    nn = 467
    out = Path(outdir)
    json.dump({"nnodes": nn, "nodes": {str(k): [list(v[0]), list(v[1])] for k, v in sorted(nodes.items())}},
              open(out / "dag219_nodes.json", "w"))
    s = sites(nodes, 0, nn)
    json.dump(s, open(out / "dag219_sites.json", "w"))
    print(f"dag219: {nn} nodes, {len(s)} leaves, max depth {max(len(x[0]) for x in s)}")


if __name__ == "__main__":
    main(*sys.argv[1:])
