#!/usr/bin/env python3
"""Independent source audit, not a binary-machine runtime certificate.

No search, optimizer, novelty checker, or source-language module is imported.
All ordinals in this file are zero based.
"""
from collections import deque
from pathlib import Path
import hashlib
import json

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
BASE = ROOT / "research_sub222/delivery/K221_Construction_2026-10-20"
NOVEL = ROOT / "research_sub221/novel"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def resolve(rows):
    """Interval ancestry resolver; also cross-check every edge arithmetically."""
    leaf = {p: i for i, (p, _, _) in enumerate(rows)}
    assert len(leaf) == len(rows)
    intervals = {}

    def visit(p):
        if p in leaf:
            a = (leaf[p], leaf[p] + 1)
        else:
            assert any(q.startswith(p) for q in leaf), ("missing child", p)
            x, y = visit(p + "0"), visit(p + "1")
            assert x[1] == y[0]
            a = (x[0], y[1])
        intervals[p] = a
        return a

    assert visit("") == (0, len(rows))

    def unwind(p, bit, k):
        while p:
            end, p = p[-1], p[:-1]
            if end == bit:
                k -= 1
                if k == 0:
                    return intervals[p][bit == "0"] % len(rows)
        return 0

    def direct(p):
        # The prefix must not leave a nonzero suffix behind its selected leaf.
        q = p + "0" * (max(map(len, leaf)) + 1)
        for k in range(1, len(q) + 1):
            if q[:k] in leaf:
                assert "1" not in p[k:]
                return leaf[q[:k]]
        raise AssertionError(p)

    def inc(p):
        return (
            format((int(p, 2) + 1) % 2 ** len(p), f"0{len(p)}b")
            if p
            else ""
        )

    def cut(p, bit, k):
        places = [j for j, x in enumerate(p) if x == bit]
        return p[: places[-k]] if len(places) >= k else ""

    result = []
    for i, (p, op, reg) in enumerate(rows):
        after = (i + 1) % len(rows)
        if op == "CI":
            result.append(("I", reg, (after,)))
            targets = (direct(inc(p)),)
        elif op == "CD":
            result.append(("D", reg, (unwind(p, "0", 1), after)))
            targets = (direct(inc(cut(p, "0", 1))), direct(inc(p)))
        elif op == "CB":
            result.append(("J", None, (unwind(p, "0", reg),)))
            targets = (direct(inc(cut(p, "0", reg))),)
        elif op == "CC":
            result.append(("J", None, (unwind(p, "1", reg),)))
            targets = (direct(cut(p, "1", reg)),)
        else:
            assert op == "CH" and reg is None
            result.append(("H", None, ()))
            targets = ()
        assert result[-1][2] == targets, (i, result[-1], targets)
    assert direct("") == 0
    return result


def transfer(g, i, value, limit=8):
    """Each component is a subset of {0,...,limit}, limit means >=limit."""
    op, reg, targets = g[i]
    if op == "H":
        return []
    if op == "J":
        return [(targets[0], value)]

    def changed(vals):
        out = list(value)
        out[reg] = frozenset(vals)
        return tuple(out)

    if op == "I":
        return [(targets[0], changed(min(x + 1, limit) for x in value[reg]))]
    results = []
    if 0 in value[reg]:
        results.append((targets[0], changed([0])))
    positives = value[reg] - {0}
    if positives:
        vals = set()
        for x in positives:
            vals.update([limit - 1, limit] if x == limit else [x - 1])
        results.append((targets[1], changed(vals)))
    return results


def invariant(g, seed):
    fs = [None] * len(g)
    fs[0] = tuple(frozenset([min(x, 8)]) for x in seed)
    todo, pending, updates = deque([0]), {0}, 0
    while todo:
        i = todo.popleft()
        pending.remove(i)
        for j, image in transfer(g, i, fs[i]):
            joined = image if fs[j] is None else tuple(a | b for a, b in zip(image, fs[j]))
            if joined != fs[j]:
                fs[j] = joined
                updates += 1
                if j not in pending:
                    todo.append(j)
                    pending.add(j)
    assert all(min(x, 8) in f for x, f in zip(seed, fs[0]))
    edges = 0
    for i, value in enumerate(fs):
        if value is not None:
            for j, image in transfer(g, i, value):
                assert fs[j] is not None
                assert all(a <= b for a, b in zip(image, fs[j]))
                edges += 1
    return fs, {"updates": updates, "inductive_guarded_edges": edges}


def local_step(g, pc, regs):
    op, r, ts = g[pc]
    if op == "H":
        return None
    if op == "I":
        regs[r] += 1
        return ts[0]
    if op == "J":
        return ts[0]
    if regs[r]:
        regs[r] -= 1
        return ts[1]
    return ts[0]


def run_local(g, entry, exit_, regs):
    pc, regs, steps = entry, list(regs), 0
    while pc != exit_:
        pc = local_step(g, pc, regs)
        steps += 1
        if pc is None:
            return "halt", regs, steps
        assert steps <= 100000
    return "return", regs, steps


def audit():
    source = BASE / "machine/sites221.json"
    assert digest(source) == "691684ec948c972bf67727d6d4cd1181a90a9203644ee3db3eae363280e3fac9"
    rows = json.loads(source.read_text())
    g = resolve(rows)
    seeds = {
        "baseline": [3, 0, 0, 0, 3, 0, 0, 0, 0],
        "shortened_startup": [4, 3, 0, 0, 3, 0, 0, 0, 0],
    }
    receipts = {}
    all_facts = {}
    for name, seed in seeds.items():
        fs, receipt = invariant(g, seed)
        assert fs[4598][6] == fs[4603][6] == fs[4718][1] == frozenset([0])
        assert [i for i, f in enumerate(fs) if f is None] == [4604, 4719, 4720]
        receipt.update(
            seed=seed,
            zero_facts=[[4598, 6], [4603, 6], [4718, 1]],
            unreachable=[4604, 4719, 4720],
            facts_at_entries={
                str(i): [sorted(x) for x in fs[i]] for i in (0, 4598, 4603, 4718)
            },
        )
        receipts[name] = receipt
        all_facts[name] = [None if f is None else [sorted(x) for x in f] for f in fs]

    old_local = [
        ("I", 6, (4599,)),
        ("D", 6, (4605, 4600)),
        ("D", 5, (4602, 4601)),
        ("J", None, (4599,)),
        ("I", 5, (4603,)),
        ("D", 6, (4605, 4604)),
        ("J", None, (4602,)),
        ("D", 5, (4609, 4606)),
        ("D", 5, (4608, 4607)),
        ("J", None, (4606,)),
        ("J", None, (4610,)),
        ("H", None, ()),
    ]
    assert g[4598:4610] == old_local
    incoming = [
        (i, t) for i, (_, _, ts) in enumerate(g) if not 4598 <= i < 4610
        for t in ts if 4598 <= t < 4610
    ]
    assert incoming == [(39, 4598)]
    assert {(i, t) for i in range(4598, 4610) for t in g[i][2] if not 4598 <= t < 4610} == {(4608, 4610)}

    new_source = NOVEL / "specialize_halt_test/sites.json"
    new_rows = json.loads(new_source.read_text())
    ng = resolve(new_rows)
    assert ng[4598:4604] == [
        ("D", 5, (4604, 4599)),
        ("D", 5, (4603, 4600)),
        ("D", 5, (4602, 4601)),
        ("J", None, (4600,)),
        ("J", None, (4604,)),
        ("H", None, ()),
    ]
    assert len(new_rows) == len(rows) - 6
    mapping = {i: i if i < 4598 else i - 6 for i in range(len(rows)) if not 4598 <= i < 4610}
    mapping[4598] = 4598
    for oi, ni in mapping.items():
        if oi == 4598:
            continue
        assert rows[oi][1:] == new_rows[ni][1:]
        op, r, ts = g[oi]
        assert ng[ni] == (op, r, tuple(mapping[t] for t in ts))

    # Supplementary tests only. Universal proof is the graph case analysis
    # with the decreasing clear-loop rank, stated in AUDIT.md.
    for n in range(513):
        value = [17, 19, 23, 29, 31, n, 0, 37, 41]
        old, new = run_local(g, 4598, 4610, value), run_local(ng, 4598, 4604, value)
        expected_regs = value.copy()
        expected_regs[5] = 0
        assert old[:2] == new[:2] == ("halt" if n == 1 else "return", expected_regs)
        assert old[2] == (8 if n == 0 else 7 if n == 1 else 2 * n + 4)
        assert new[2] == (1 if n == 0 else 3 if n == 1 else 2 * n)
    bad = [0] * 9
    bad[5] = 2
    bad[6] = 1
    assert run_local(g, 4598, 4610, bad)[0] == "halt"
    assert run_local(ng, 4598, 4604, bad)[0] == "return"

    deletion_receipts = []
    for mask in (1, 2, 3):
        removed = ({4603, 4604} if mask & 1 else set()) | ({4718, 4719, 4720} if mask & 2 else set())
        retained = [i for i in range(len(rows)) if i not in removed]
        m = {i: j for j, i in enumerate(retained)}
        deletion_file = NOVEL / f"drop_seed_noops/{mask}/sites.json"
        drows = json.loads(deletion_file.read_text())
        dg = resolve(drows)
        assert len(drows) == len(retained)

        def collapse(i):
            skipped = []
            while i in removed:
                assert i not in skipped
                skipped.append(i)
                assert i in (4603, 4718)
                assert g[i][0] == "D"
                for fs in all_facts.values():
                    assert fs[i][g[i][1]] == [0]
                i = g[i][2][0]
            assert len(skipped) <= 1
            return m[i]

        for j, i in enumerate(retained):
            assert drows[j][1:] == rows[i][1:]
            op, r, ts = g[i]
            assert dg[j] == (op, r, tuple(collapse(t) for t in ts))
        assert collapse(0) == 0
        deletion_receipts.append({
            "mask": mask, "source_sha256": digest(deletion_file),
            "removed": sorted(removed), "retained": len(retained),
            "maximum_removed_reachable_steps": 1,
        })

    facts_file = HERE / "inductive_facts.json"
    facts_file.write_text(json.dumps(all_facts, separators=(",", ":")) + "\n")
    receipt = {
        "status": "SOURCE_SEED_SPECIALIZATION_AUDIT_PASS_NOT_TM_RUNTIME",
        "baseline_source_sha256": digest(source),
        "source_resolvers": "independent interval ancestry and binary arithmetic",
        "invariants": receipts,
        "inductive_facts_sha256": digest(facts_file),
        "threshold": 8,
        "threshold_meaning": "The final bucket contains every natural >=8, not just 8.",
        "halt_specialization": {
            "source_sha256": digest(new_source), "old_interval": [4598, 4610],
            "new_interval": [4598, 4604], "old_entry_precondition": "R6=0",
            "single_external_entry": incoming, "all_other_operations_and_successors_preserved": True,
            "universal_contract": "Halt iff initial R5=1; otherwise return. All outputs have R5=R6=0; other registers unchanged.",
            "proof": "Exact graph case split n=0, n=1, n>=2; clear-loop induction on n-2. See AUDIT.md.",
            "unrestricted_equivalence_negative_control": "Rejected: R5=2,R6=1 makes old halt and new return.",
            "supplementary_sample_values": 513,
        },
        "noop_deletions": deletion_receipts,
        "not_established": [
            "A <=220-state correct transition table",
            "Candidate-specific binary runtime or blank startup for the specialized source",
            "A new Rocq/Lean proof of the inherited calculus-to-ZFC calibration",
        ],
    }
    (HERE / "audit.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps(receipt, indent=2))


if __name__ == "__main__":
    audit()
