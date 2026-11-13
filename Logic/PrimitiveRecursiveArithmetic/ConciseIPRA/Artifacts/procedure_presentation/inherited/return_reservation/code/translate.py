"""Translate canonical shared-leaf AST streams to return-reservation streams.

This is an untrusted certificate producer. No proof checker imports it.
The root theorem (first JSON line) is preserved literally.
"""
import json
from pathlib import Path
import sys


def translate(text):
    records = iter(json.loads(line) for line in text.splitlines() if line.strip())
    goal = next(records)
    emitted = [goal]
    old_floor = 0
    new_floor = 0
    names = {}
    allocations = []
    calls = 0
    rules = {"computation": 0, "hypothesis": 0, "use": 0,
             "open": 0, "progress": 0, "cases": 0}
    used_hypotheses = {}

    def rename(tree):
        if isinstance(tree, list):
            return [rename(x) for x in tree]
        if type(tree) is not int:
            raise ValueError("The translator accepts integer/list certificates only")
        if tree >= 0:
            return tree
        if tree in names:
            return names[tree]
        if tree < old_floor:
            # Preserve an out-of-scope hole without capturing a current name.
            return new_floor + tree - old_floor
        raise ValueError("Missing allocation in the old name ledger")

    def opening(a, t=0j, d=0):
        try:
            return [opening(b, t, d + 5 - len(a)) for b in a]
        except Exception:
            return a if old_floor <= a < d else d % 2 and opening(t, d=3)

    def check(g, a, kinds):
        nonlocal old_floor, new_floor, calls
        calls += 1
        s, u, t = r = next(records)
        emitted.append(rename(r))
        computation = [[s and [s], u, t], opening(t, r, 3) if s else u]
        entry = opening(a)
        if entry not in (*g, computation):
            elimination = False
            if opening(t, u) == a:
                elimination = True
                rules["use"] += 1
                a = opening(t, s)
                s = r[:2] if s else [t] * 3
            check(g, s, kinds)
            h = s * 3
            if not h:
                a = opening(*a, t, 2)
                h = a
                kind = "progress" if len(a) == 2 else "cases"
                rules[kind] += 1
            elif elimination:
                kind = "use-padding"
            else:
                kind = "open"
                rules[kind] += 1
            old_floor -= 1
            names[old_floor] = new_floor
            allocations.append([old_floor, new_floor])
            added = opening(h, old_floor * (1 if s else len(a) == 2))
            check([*g, added], opening(a, [old_floor]), [*kinds, kind])
        elif entry in tuple(g):
            rules["hypothesis"] += 1
            position = next(j for j in range(len(g) - 1, -1, -1) if g[j] == entry)
            kind = kinds[position]
            used_hypotheses[kind] = used_hypotheses.get(kind, 0) + 1
        else:
            rules["computation"] += 1
        # The new checker reserves one name after every successful call.
        new_floor -= 1

    check(b"\x00", goal, ["neutral"])
    return "".join(json.dumps(record, separators=(",", ":")) + "\n"
                   for record in emitted), {
                       "calls": calls,
                       "allocations": allocations,
                       "old_final_floor": old_floor,
                       "new_final_floor": new_floor,
                       "rule_counts": rules,
                       "used_hypotheses": used_hypotheses,
                   }


if __name__ == "__main__":
    source, destination = map(Path, sys.argv[1:])
    compiled, receipt = translate(source.read_text())
    destination.write_text(compiled)
    print(json.dumps(receipt, indent=2))
