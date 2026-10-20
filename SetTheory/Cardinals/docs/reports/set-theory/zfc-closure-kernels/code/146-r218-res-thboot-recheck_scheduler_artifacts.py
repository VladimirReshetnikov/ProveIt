#!/usr/bin/env python3
"""Recheck retained scheduler source shapes and exact failed blank prefixes.

No search or state-count success is claimed. This driver uses only files in
its own directory. The protected-cost numbers are retained search receipts;
they are not independently recomputed by this standard-library checker.
"""
from pathlib import Path
import hashlib
import json

HERE = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def tree(rows):
    root = {}
    for path, op, arg in rows:
        at = root
        for bit in path:
            at = at.setdefault(bit, {})
        assert not at
        at["leaf"] = (op, arg)

    def visit(at):
        if "leaf" in at:
            assert set(at) == {"leaf"}
            return at["leaf"]
        assert set(at) == {"0", "1"}
        return visit(at["0"]), visit(at["1"])

    return visit(root)


def leaf(t):
    return isinstance(t[0], str)


def sites(t, p=""):
    return [[p, *t]] if leaf(t) else sites(t[0], p + "0") + sites(t[1], p + "1")


def metrics(t):
    seen = set()

    def visit(n):
        seen.add(n)
        if not leaf(n):
            visit(n[0])
            visit(n[1])

    visit(t)
    rows = sites(t)
    return dict(dag_nodes=len(seen), leaf_occurrences=len(rows),
                maximum_depth=max(len(p) for p, _, _ in rows),
                maximum_zero_run=max(len(z) for p, _, _ in rows for z in p.split("1")))


def read_table(path):
    result = {}
    for line in path.read_text().splitlines():
        if not line or line.startswith("#"):
            continue
        q, bit, written, direction, target = line.split()
        result[int(q), int(bit)] = (int(written), 1 if direction == "R" else -1, int(target))
    return result


def failed_blank_prefix(path):
    table = read_table(path)
    q, head, ones = 0, 0, set()
    for tick in range(1000):
        bit = int(head in ones)
        written, direction, target = table[q, bit]
        # An exact outward self-loop on an entirely blank ray is divergence.
        if target == q and bit == 0:
            outward = ((direction == 1 and (not ones or head > max(ones))) or
                       (direction == -1 and (not ones or head < min(ones))))
            if outward:
                return dict(status="EXACT_BLANK_RAY_DIVERGENCE", steps=tick,
                            state=q, head=head, ones=sorted(ones),
                            loop_row=[q, bit, written, direction, target],
                            table_sha256=sha(path), working_states=len(table) // 2)
        if written:
            ones.add(head)
        else:
            ones.discard(head)
        q, head = target, head + direction
    raise AssertionError("Retained failed startup did not reach its recorded ray loop")


def main():
    after = tree(json.loads((HERE / "load_after_body/sites.json").read_text()))
    body, load = after[0][1][0], after[1]
    copy, restore = load
    p6 = (("CD", 6), ("CC", 2))
    assert copy == (("CD", 0), (("CI", 8), (("CI", 6), ("CC", 3))))
    assert restore == (("CI", 0), p6)
    guard = (("CD", 8), ("CB", 1))
    a = (guard, load)
    published = (a, body)
    variants = {
        "load_after_body": ((("CD", 8), (body, ("CB", 1))), load),
        "leading_wrapper": (("CI", 0), (a, (("CD", 0), body))),
        "shared_restore": (("CI", 0), (p6, ((("CD", 8), ((("CD", 0), body), ("CB", 1))), copy))),
        "stride2": (("CI", 0), (load, (("CD", 8), (body, ("CC", 2))))),
        "rotated_restore": (restore, (body, ((("CD", 8), ("CC", 2)), copy))),
        "rotated_restore_ci": (("CI", 0), (p6, (body, ((("CD", 8), ("CC", 2)), copy)))),
    }
    records = []
    for name, expected in variants.items():
        folder = HERE / name
        source = folder / "sites.json"
        assert tree(json.loads(source.read_text())) == expected, name
        record = dict(name=name, source_sha256=sha(source), metrics=metrics(expected))
        screen = folder / "screen.json"
        if screen.exists():
            cost = json.loads(screen.read_text())
        else:
            cost = json.loads((folder / "allocation.json").read_text())["objective"]
        assert cost["metrics"] == record["metrics"], name
        record["retained_cost_receipt"] = cost
        candidate = folder / "candidate.tm"
        if candidate.exists():
            record["failed_startup"] = failed_blank_prefix(candidate)
        records.append(record)
    reference_rows = sites(published)
    compact = (json.dumps(reference_rows, separators=(",", ":")) + "\n").encode("ascii")
    result = dict(
        status="SIX_RETAINED_SOURCE_SHAPES_AND_FAILED_STARTUP_PREFIXES_RECHECKED",
        reconstructed_reference_source_sha256=hashlib.sha256(compact).hexdigest(),
        reference_metrics=metrics(published),
        variants=records,
        np_pl_transport_failed_startup=failed_blank_prefix(HERE / "np_pl_swap/candidate.tm"),
        scope=("Source shapes, source metrics, and retained literal blank-ray divergences "
               "are rechecked. The protected allocation costs are inherited receipts, "
               "not independently validated machine counts. No listed changed table "
               "has a complete source-wide runtime proof and successful blank initialization."),
    )
    (HERE / "scheduler_probe_report.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: v for k, v in result.items() if k != "variants"}, indent=2))
    for record in records:
        print(record["name"], record["metrics"],
              record["retained_cost_receipt"]["cost_lower_bound"],
              record.get("failed_startup", {}).get("steps"))


if __name__ == "__main__":
    main()
