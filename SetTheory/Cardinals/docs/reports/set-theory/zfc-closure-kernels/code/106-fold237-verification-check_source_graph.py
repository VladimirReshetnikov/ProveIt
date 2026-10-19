#!/usr/bin/env python3
"""Independent finite source-graph audit using integer path arithmetic.

The checked implication is source bisimulation, not binary-machine correctness.
All source leaves, both decrement outcomes, and every successor's zero-tail
canonicality are checked.  No register values are sampled.
"""
import argparse
import hashlib
import json
from pathlib import Path


def graph(rows):
    ordered = sorted(tuple(r) for r in rows)
    if len({r[0] for r in ordered}) != len(ordered):
        raise ValueError("duplicate path")
    terminals = {p: i for i, (p, _, _) in enumerate(ordered)}
    prefixes = {p[:k] for p in terminals for k in range(len(p))}
    if set(terminals) & prefixes:
        raise ValueError("non-prefix-free tree")
    if not terminals or "" not in prefixes:
        raise ValueError("missing root")
    for p in prefixes:
        if any(p + c not in prefixes and p + c not in terminals for c in "01"):
            raise ValueError("non-full tree")
    maximum = max(map(len, terminals))

    def locate(word):
        padded = word + "0" * maximum
        for depth in range(1, maximum + 1):
            prefix = padded[:depth]
            if prefix in terminals:
                if "1" in word[depth:]:
                    raise ValueError("nonzero consumed-path tail")
                return terminals[prefix]
        raise ValueError("decoder exhausted")

    def inc(word):
        if not word:
            return ""
        n = (int(word, 2) + 1) % (1 << len(word))
        return format(n, "0" + str(len(word)) + "b")

    def cut(word, bit, k):
        if k == 0:
            return word
        positions = [i for i, c in enumerate(word) if c == bit]
        return word[:positions[-k]] if len(positions) >= k else ""

    def jump(word, k, kind):
        return inc(cut(word, "0", k)) if kind == "CB" else cut(word, "1", k)

    out = []
    for p, op, arg in ordered:
        if not p or set(p) - set("01"):
            raise ValueError("path alphabet")
        if op in ("CI", "CD"):
            if type(arg) is not int or not 0 <= arg < 9:
                raise ValueError("invalid register")
            successor = locate(inc(p))
            if op == "CI":
                out.append(("INC", arg, successor))
            else:
                out.append(("DEC", arg, successor, locate(jump(p, 1, "CB"))))
        elif op in ("CB", "CC"):
            if type(arg) is not int or arg < 0:
                raise ValueError("invalid jump operand")
            out.append(("JUMP", locate(jump(p, arg, op))))
        elif op == "CH" and arg is None:
            out.append(("HALT",))
        else:
            raise ValueError("invalid instruction")
    return ordered, out, locate(""), maximum


def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("baseline", type=Path)
    ap.add_argument("candidate", type=Path)
    ap.add_argument("--output", type=Path)
    args = ap.parse_args()
    b = json.loads(args.baseline.read_text())
    c = json.loads(args.candidate.read_text())
    bo, bg, bi, bm = graph(b)
    co, cg, ci, cm = graph(c)
    if [r[1:] for r in bo] != [r[1:] for r in co]:
        raise ValueError("ordered instructions differ")
    if bg != cg or bi != ci:
        raise ValueError("complete control graphs differ")
    if sum(r[0] == "HALT" for r in bg) != 1:
        raise ValueError("halt descriptor count")

    controls = []
    changed = [list(r) for r in c]
    j = next(i for i, row in enumerate(changed) if row[1] == "CD")
    changed[j][2] = (changed[j][2] + 1) % 9
    controls.append({"name": "changed_decrement_register",
                     "rejected": graph(changed)[1] != bg})
    incomplete = [list(r) for r in c[:-1]]
    try:
        graph(incomplete)
        rejects_incomplete = False
    except ValueError:
        rejects_incomplete = True
    controls.append({"name": "removed_leaf", "rejected": rejects_incomplete})
    duplicate = [list(r) for r in c] + [list(c[0])]
    try:
        graph(duplicate)
        rejects_duplicate = False
    except ValueError:
        rejects_duplicate = True
    controls.append({"name": "duplicate_leaf", "rejected": rejects_duplicate})
    if not all(x["rejected"] for x in controls):
        raise ValueError("negative control accepted")

    r = {"status": "PASS_INDEPENDENT_SOURCE_GRAPH",
         "scope": "Every source step, all natural register files; no binary runtime claim",
         "baseline": str(args.baseline), "candidate": str(args.candidate),
         "baseline_sha256": digest(args.baseline),
         "candidate_sha256": digest(args.candidate),
         "leaf_occurrences": len(bg),
         "guard_edges": sum(2 if x[0] == "DEC" else 0 if x[0] == "HALT" else 1 for x in bg),
         "halt_descriptors": sum(x[0] == "HALT" for x in bg),
         "initial_leaf": bi, "baseline_max_depth": bm, "candidate_max_depth": cm,
         "all_successor_paths_have_only_zero_unused_tail": True,
         "negative_controls": controls}
    txt = json.dumps(r, indent=2) + "\n"
    if args.output:
        args.output.write_text(txt)
    print(txt, end="")


if __name__ == "__main__":
    main()
