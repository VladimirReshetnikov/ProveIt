#!/usr/bin/env python3
"""Reconstruct PA194NS/SUMS and replay construction-level certificates.

Python 3.10+, standard library. The supplied runtime uses unchanged inherited
register-box lemmas. This is not an end-to-end proof-assistant verification.
This integration wrapper and independent V8 ports were executed successfully;
their receipts are included.
"""
from pathlib import Path
import hashlib
import json
import compiler as c

HERE = Path(__file__).resolve().parent
START, HALT = 74, 254
BASE_NODES = c.raw_nodes
BASE_HASH = "e0a7397cf2134e8e7f58a8b1de2f7ff90b74ededd54c912f6ba5b7db48dabe54"
EXPECTED = {
    False: ("pa194sums", 3670, 4776, 1485452,
        "b81a833dc99bcc2204ba513260e2e4fa07981b018228eef2f0bcc188e977f9c2",
        "f7c8799c86847a4aeb85f078015f159a6fabbc94d5e26cbd84f337c4f8789fa8"),
    True: ("pa194ns", 3651, 4751, 1479348,
        "db2ce84a0e883b44e348b60c834382245a9f55623de675ffdacb1e8b3c18bf75",
        "eef9329b9a7e1f2810eddcf3e99fc0184b073ea266d658ebe473f7d11d68ecd7"),
}

def digest(s):
    return hashlib.sha256(s.encode("utf-8")).hexdigest()

def read_table(path):
    rows = {}
    for line in path.read_text().splitlines():
        q, b, w, d, n = line.split()
        q, b, w, n = map(int, (q, b, w, n))
        assert b in (0, 1) and w in (0, 1) and d in ("L", "R")
        assert (q, b) not in rows
        rows[q, b] = (w, d == "R", n)
    return rows

def table_text(rows):
    return "".join(
        f'{q} {b} {w} {"R" if d else "L"} {n}\n'
        for (q, b), (w, d, n) in sorted(rows.items())
    )

def nodes(nopush, symmetric):
    out = BASE_NODES()
    if nopush:
        out["node163"] = ("node6", "node54")
    if symmetric:
        out["node168"] = ("node37", "node56")
        out["node171"] = (
            "node170", (("leaf", "inc", 5), ("leaf", "continueTo", 3)))
    return out

def source(grammar, nopush=False, symmetric=False):
    c.raw_nodes = lambda: nodes(nopush, symmetric)
    return c.source(grammar)

def raw_table(nopush):
    rows = read_table(HERE / "baseline/unfolded201.native.tm")
    rows[38, 1] = (1, True, 30)
    rows[310, 1] = (1, True, 330)
    rows[330, 0] = (0, True, 63)
    rows[330, 1] = (1, False, 73)
    if nopush:
        rows[164, 1] = (1, True, 114)
    assert len(rows) == 404
    return rows

def fold_table(raw, folds):
    aliases = {a: b for a, b, actions in folds}
    changes = {b: actions for a, b, actions in folds}
    assert len({q for a, b, actions in folds for q in (a, b)}) == 2 * len(folds)
    rows = {}
    for (q, bit), act in raw.items():
        if q in aliases:
            continue
        w, d, n = changes[q][bit] if q in changes else act
        rows[q, bit] = (w, bool(d), aliases.get(n, n))
    return rows, aliases

def check_folds(raw, folded, folds, aliases):
    incoming = {}
    for (q, bit), (w, d, n) in raw.items():
        incoming.setdefault(n, []).append((q, bit, w, d))
    cases = []
    for a, b, actions in folds:
        assert START not in (a, b)
        for old, history in ((a, 0), (b, 1)):
            assert incoming[old]
            assert all((w, d) == (history, True)
                       for q, bit, w, d in incoming[old])
            for bit in (0, 1):
                w, d, n = raw[old, bit]
                expected = (aliases.get(n, n), 1 if d else -1,
                            {-1: history, 0: w})
                q, x, tape = b, 0, {-1: history, 0: bit}
                for steps in range(1, 21):
                    assert x in (-1, 0)
                    wr, dr, q = folded[q, tape[x]]
                    tape[x] = wr
                    x += 1 if dr else -1
                    if (q, x, tape) == expected:
                        break
                else:
                    raise AssertionError(("local fold failure", old, bit))
                cases.append(dict(old=old, history=history, read=bit, steps=steps))
    assert len(cases) == 32
    assert sum(len(incoming[q]) for a, b, _ in folds for q in (a, b)) == 26
    return cases

def dense(rows):
    controls = {q for q, _ in rows}
    assert len(controls) == 194 and len(rows) == 388
    assert HALT not in controls
    assert all((q, b) in rows for q in controls for b in (0, 1))
    assert {n for w, d, n in rows.values()} - controls == {HALT}
    order, index = [START], {START: 0}
    for q in order:
        for bit in (0, 1):
            n = rows[q, bit][2]
            if n != HALT and n not in index:
                index[n] = len(order)
                order.append(n)
    assert len(order) == 194
    out = {(index[q], b): (w, d, 194 if n == HALT else index[n])
           for (q, b), (w, d, n) in rows.items()}
    return out, order + [HALT]

def startup(rows, address):
    head = -2
    expected = {head - 1, head + 48}
    expected.update(head + i for i, bit in enumerate(address) if bit)
    file = [0, 0, 0, 0, 0, 0, 2, 0, 0] + [1] * 26
    p = head + 49
    for value in file:
        p += 1
        expected.update(range(p, p + value + 1))
        p += value + 1
    q, x, ones = START, 0, set()
    for steps in range(1, 100001):
        w, d, q = rows[q, int(x in ones)]
        (ones.add if w else ones.discard)(x)
        x += 1 if d else -1
        assert q != HALT
        if (q, x, ones) == (84, head, expected):
            assert steps == 58004 and len(ones) == 66
            return dict(steps=steps, state=q, head=x, support=sorted(ones),
                        physical_file=file, complete_tape_equality=True)
    raise AssertionError("clean startup frame not reached")

def main():
    if not __debug__:
        raise SystemExit("Do not use Python -O; assertions check certificates.")
    base = read_table(HERE / "baseline/pa194.native.tm")
    assert digest(table_text(base)) == BASE_HASH
    grammar = c.read_grammar(HERE / "baseline/grammar.json")
    original_sites, original_ins, original_contracts = source(grammar)
    original_check = c.validate(base, original_contracts)
    assert original_check == dict(ok=True, contracts=4780,
                                  max_steps=497, total_steps=1479348)
    folds = json.loads((HERE / "baseline/folds.json").read_text())
    folds.append([41, 330, [[0, False, 31], [1, False, 46]]])
    results = {"positive_control": original_check}
    for nopush in (False, True):
        name, count, outcomes, total, native_hash, dense_hash = EXPECTED[nopush]
        parent_sites, parent_ins, parent_cs = source(grammar, nopush, False)
        sites, ins, cs = source(grammar, nopush, True)
        prefix = 3649 if nopush else 3668
        assert ins[:prefix] == parent_ins[:prefix]
        assert ins[prefix:] == [("inc", 5, prefix + 1), ("jump", 0)]
        assert len(sites) == count and len(cs) == outcomes
        assert tuple(sites[25][0]) == (1, 0, 0, 0, 0, 0)
        assert max(map(lambda s: len(s[0]), sites)) == 36
        raw = raw_table(nopush)
        rows, aliases = fold_table(raw, folds)
        local = check_folds(raw, rows, folds, aliases)
        dense_rows, labels = dense(rows)
        assert digest(table_text(rows)) == native_hash
        assert digest(table_text(dense_rows)) == dense_hash
        assert (HERE / f"{name}.native.tm").read_text() == table_text(rows)
        assert (HERE / f"{name}.tm").read_text() == table_text(dense_rows)
        assert json.loads((HERE / f"{name}.labels.json").read_text()) == labels
        assert all(rows[q, b] == base[q, b] for q in c.BOXSTATES for b in (0, 1))
        symbolic = c.validate(rows, cs)
        assert symbolic == dict(ok=True, contracts=outcomes,
                                max_steps=499, total_steps=total)
        start = startup(rows, sites[25][0])
        results[name] = dict(working_states=194, rows=388, raw_states=202,
            source_sites=count, primitive_outcomes=outcomes,
            symbolic=symbolic, local_fold_cases=local, startup=start,
            sha256_native=native_hash, sha256_dense=dense_hash,
            proof_scope="Inherited register-box lemmas; no new Lean endpoint")
    c.raw_nodes = BASE_NODES
    out = HERE / "evidence/replayed_verification.json"
    out.parent.mkdir(exist_ok=True)
    out.write_text(json.dumps(results, indent=2) + "\n")
    print(json.dumps({k: v.get("symbolic", v) for k, v in results.items()}, indent=2))

if __name__ == "__main__":
    main()
