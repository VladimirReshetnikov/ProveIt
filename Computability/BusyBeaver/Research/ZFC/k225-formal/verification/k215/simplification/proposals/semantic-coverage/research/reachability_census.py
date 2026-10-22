#!/usr/bin/env python3
"""Source-register abstract reachability: finite evidence, not a kernel proof.

Read exact K215 leaf data, reconstruct its control flow independently, then
compute a finite product-domain inductive invariant. No machine is modified.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from collections import Counter, deque
from pathlib import Path

if not __debug__:
    raise SystemExit("Run this finite validator without Python -O/-OO.")


def increment(path):
    p = list(path)
    for j in range(len(p) - 1, -1, -1):
        p[j] = 1 - p[j]
        if p[j]:
            break
    return tuple(p)


def strip(path, bit, count):
    p = list(path)
    while p and count:
        count -= p.pop() == bit
    return tuple(p)


def flatten(rows):
    tree = {}
    leaves = []
    for ordinal, (bits, op, arg) in enumerate(rows):
        p = tuple(map(int, bits))
        node = tree
        for b in p:
            if "leaf" in node:
                raise ValueError("Overlapping source leaves")
            node = node.setdefault(b, {})
        if node:
            raise ValueError("Repeated or overlapping source leaf")
        node["leaf"] = (ordinal, p, op, arg)
        leaves.append((ordinal, p, op, arg))

    def check_full(node):
        if "leaf" in node:
            if len(node) != 1:
                raise ValueError("Malformed leaf")
            return
        if set(node) != {0, 1}:
            raise ValueError("Incomplete binary source tree")
        for child in node.values():
            check_full(child)
    check_full(tree)

    def resolve(path):
        node = tree
        depth = 0
        while "leaf" not in node:
            node = node[path[depth] if depth < len(path) else 0]
            depth += 1
        return node["leaf"]

    def nexts(leaf):
        _, p, op, arg = leaf
        if op == "CI":
            return (increment(p),)
        if op == "CD":
            return increment(p), increment(strip(p, 0, 1))
        if op == "CB":
            return (increment(strip(p, 0, arg)),)
        if op == "CC":
            return (strip(p, 1, arg),)
        if op == "CH":
            return ()
        raise ValueError(op)

    transitions = [(op, arg, tuple(resolve(p)[0] for p in nexts(leaf)))
                   for leaf in leaves for _, _, op, arg in [leaf]]
    initial = resolve(())[0]

    prim = [i for i, (op, _, _) in enumerate(transitions) if op in ("CI", "CD", "CH")]
    number = {q: i for i, q in enumerate(prim)}
    def epsilon(i):
        seen = set()
        while transitions[i][0] in ("CB", "CC"):
            if i in seen:
                raise ValueError("Control-only loop")
            seen.add(i)
            i = transitions[i][2][0]
        return number[i]
    normalized = [(op[1:], arg, tuple(epsilon(j) for j in succ))
                  for i in prim for op, arg, succ in [transitions[i]]]
    return transitions, initial, {"initial": epsilon(initial), "transitions": normalized}


def analyze(transitions, initial, cap, counter_mode):
    # Bit k means exact k for k < cap; bit cap means >= cap.
    top = (1 << (cap + 1)) - 1
    initial_state = [1] * 9
    initial_state[0] = (top if counter_mode == "arbitrary" else
                        top & ~1 if counter_mode == "positive" else
                        1 << min(4, cap))
    inv = [None] * len(transitions)
    inv[initial] = tuple(initial_state)
    queue = deque([initial]); queued = {initial}

    def transfer(i, state):
        op, reg, successors = transitions[i]
        if op in ("CB", "CC"):
            return [(successors[0], state)]
        if op == "CH":
            return []
        def setreg(mask):
            t = list(state); t[reg] = mask
            return tuple(t)
        if op == "CI":
            mask = 0
            for k in range(cap + 1):
                if state[reg] & (1 << k):
                    mask |= 1 << min(k + 1, cap)
            return [(successors[0], setreg(mask))]
        if op == "CD":
            out = []
            if state[reg] & 1:
                out.append((successors[1], setreg(1)))
            mask = 0
            for k in range(1, cap + 1):
                if state[reg] & (1 << k):
                    mask |= 1 << (k - 1)
                    if k == cap:
                        mask |= 1 << cap
            if mask:
                out.append((successors[0], setreg(mask)))
            return out
        raise ValueError(op)

    while queue:
        i = queue.popleft(); queued.remove(i)
        for j, state in transfer(i, inv[i]):
            old = inv[j]
            merged = state if old is None else tuple(a | b for a, b in zip(old, state))
            if merged != old:
                inv[j] = merged
                if j not in queued:
                    queued.add(j); queue.append(j)

    # Separate post-fixpoint check; do not accept the worklist's own claim.
    assert all((a & b) == a for a, b in zip(initial_state, inv[initial]))
    checked_edges = 0
    for i, state in enumerate(inv):
        if state is None:
            continue
        for j, out in transfer(i, state):
            target = inv[j]
            assert target is not None
            assert all((a & b) == a for a, b in zip(out, target))
            checked_edges += 1
    eliminated = []
    for i, (op, reg, succ) in enumerate(transitions):
        if op != "CD":
            continue
        for branch, allowed in [("positive", top & ~1), ("zero", 1)]:
            if inv[i] is None or not (inv[i][reg] & allowed):
                eliminated.append({"site": i, "branch": branch, "register": reg})
    unreachable = [i for i, x in enumerate(inv) if x is None]
    live_obligations = sum(len(transfer(i, state)) if transitions[i][0] != "CH" else 1
                           for i, state in enumerate(inv) if state is not None)
    return {"cap": cap, "counter_mode": counter_mode, "total_sites": len(inv),
            "reachable_abstract_sites": len(inv) - len(unreachable),
            "unreachable_sites": unreachable,
            "decrement_outcomes_excluded": eliminated,
            "live_site_obligations": live_obligations,
            "postfixpoint_edges_checked": checked_edges,
            "invariant": inv}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--sites", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--compare-cfg", type=Path)
    args = parser.parse_args()
    raw = args.sites.read_bytes(); rows = json.loads(raw)
    transitions, initial, cfg = flatten(rows)
    if args.compare_cfg:
        other = json.loads(args.compare_cfg.read_text())
        assert json.loads(json.dumps(cfg)) == other
    runs = [analyze(transitions, initial, cap, mode)
            for cap in (1, 2, 4, 8, 16)
            for mode in ("arbitrary", "positive", "exact4")]
    # The three-class domain is the smallest one attaining the best count.
    best = next(x for x in runs if x["cap"] == 2 and x["counter_mode"] == "exact4")
    report = {"status": "FINITE_ABSTRACT_INTERPRETATION_NOT_KERNEL_PROOF",
              "input_sha256": hashlib.sha256(raw).hexdigest(),
              "source_site_count": len(rows),
              "primitive_count": len(cfg["transitions"]),
              "input_control_cfg_matches_prior": bool(args.compare_cfg),
              "initial_site": initial,
              "all_register_site_obligations": sum(2 if op == "CD" else 1
                                                   for op, _, _ in transitions),
              "runs": [{k: v for k, v in run.items()
                        if k not in ("invariant", "unreachable_sites", "decrement_outcomes_excluded")}
                       | {"unreachable_count": len(run["unreachable_sites"]),
                          "excluded_decrement_outcomes": len(run["decrement_outcomes_excluded"])}
                       for run in runs],
              "best_invariant": best,
              "scope": "Product-register invariant from R=[4,0,...,0]; other runs vary counter. No concrete TM contract, source-to-CFG theorem, or endpoint rebuild is established."}
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: v for k, v in report.items() if k != "best_invariant"}, indent=2))


if __name__ == "__main__":
    main()
