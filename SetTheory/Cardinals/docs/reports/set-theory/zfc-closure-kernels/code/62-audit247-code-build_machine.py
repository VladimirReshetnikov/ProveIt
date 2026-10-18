#!/usr/bin/env python3
"""Reconstruct the exact 247-state machine from the pinned 252-state table.

The prefix-carry rewrite is prior work in the incoming prefix250 packages.
This contribution redirects the marking edge 60/0 to 20 and removes 0,1,3.
All artifacts and reference inputs are relative to this file; no network is used.
"""
from __future__ import annotations
import argparse
from hashlib import sha256
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
PROVEIT_COMMIT = "e0b512a63e2c1ca6a1698fa437b8568f1643ff6b"
BASE_SHA256 = "939f99d602c8f7057517c4369279de99e30827050fc743581df83f26aaf1b713"
PRIOR250_SHA256 = "fd455304bad82a6da7ab83149352d0b1db27557582c4cc6312de003c96ff4e43"
PROGRAM_SHA256 = "1fbc30fcf82a1442ed88d1a1dde412630a431d32a7265d22bdf8517bffe01746"
LEAN_PROGRAM_SHA256 = "6e564bd1ba179b2d39fccc3b8c86a681ec0dd6529df9cfa2522500eef140cfde"
OLD_FINAL_SHA256 = "0d37614f3caf37139b0be127837630539224acd1c45d748cf5704abfc3230b42"
CANONICAL_SHA256 = "58bbbda620daf6d4d62f486db05f54d0dccb8373c080c1b5a0b26533e7a3a669"
PHYSICAL = (6, 2, 0, 4, 3, 7, 8, 5, 1)
REMOVED = {0, 1, 3, 43, 59, 85}
PATCH = {
    (30, 1): (0, "R", 95),
    (60, 0): (0, "R", 20),
    (75, 0): (1, "R", 255),
    (75, 1): (1, "L", 63),
    (97, 0): (1, "R", 83),
    (97, 1): (1, "L", 131),
    (109, 0): (0, "R", 75),
    (131, 0): (0, "L", 48),
    (255, 0): (1, "L", 97),
    (255, 1): (1, "L", 131),
}

def digest(path):
    return sha256(Path(path).read_bytes()).hexdigest()

def read_table(path):
    table = {}
    start = None
    for line in Path(path).read_text(encoding="ascii").splitlines():
        if line.startswith("#! start "):
            assert start is None
            start = int(line.split()[-1])
        if not line.strip() or line.startswith("#"):
            continue
        q, b, w, d, t = line.split()
        q, b, w, t = map(int, (q, b, w, t))
        assert b in (0, 1) and w in (0, 1) and d in ("L", "R")
        assert (q, b) not in table
        table[q, b] = w, d, t
    states = {q for q, b in table}
    assert start in states
    assert set(table) == {(q, b) for q in states for b in (0, 1)}
    return table, start

def encode(table, start):
    return f"#! start {start}\n" + "".join(
        f"{q} {b} {w} {d} {t}\n"
        for (q, b), (w, d, t) in sorted(table.items()))

def build(check_existing=True):
    path = ROOT / "reference/baseline252_old.tm"
    assert digest(path) == BASE_SHA256
    baseline, start = read_table(path)
    assert start == 64 and len(baseline) == 504
    assert {q for q, b in baseline} == set(range(254)) - {5, 8}
    table = {key: row for key, row in baseline.items() if key[0] not in REMOVED}
    for key, row in PATCH.items():
        assert baseline.get(key) != row
        table[key] = row
    states = {q for q, b in table}
    assert states == (set(range(254)) - {0, 1, 3, 5, 8, 43, 59, 85}) | {255}
    assert len(states) == 247 and len(table) == 494
    assert set(table) == {(q, b) for q in states for b in (0, 1)}
    assert {t for w, d, t in table.values()} - states == {254}
    assert [(key, row) for key, row in table.items() if row[2] == 254] == [((77, 1), (1, "R", 254))]
    assert sha256(encode(table, 97).encode("ascii")).hexdigest() == OLD_FINAL_SHA256
    if check_existing:
        assert encode(table, 97) == (ROOT / "machine/zfc_prefix247_old.tm").read_text()
    return table

def program_rows():
    path = ROOT / "reference/Prog254.v"
    assert digest(path) == PROGRAM_SHA256
    source = path.read_text(encoding="ascii").split("Definition p254_tab", 1)[1]
    body = source.split("[", 1)[1].split("].", 1)[0]
    edge = r"(?:CN \d+|CI \d+|CD \d+|CB \d+|CC \d+|CH)"
    pattern = r"\((" + edge + r"),\s*(" + edge + r")\)"
    rows = re.findall(pattern, body)
    assert len(rows) == 6459
    assert not re.sub(r"[\s;]", "", re.sub(pattern, "", body))
    check_lean_program_port(rows)
    return rows

def check_lean_program_port(coq_rows):
    """Check all rows AND the balanced-tree flattening used by the Lean endpoint."""
    path = ROOT / "reference/lean/Prog254.lean"
    assert digest(path) == LEAN_PROGRAM_SHA256
    source = path.read_text(encoding="utf-8")
    edge = r"\.(?:node \d+|inc \d+|decnz \d+|brk \d+|cont \d+|halt)"
    row_pattern = r"\((" + edge + r"),\s*(" + edge + r")\),?\s*-- (\d+)"
    tags = {"node": "CN", "inc": "CI", "decnz": "CD",
            "brk": "CB", "cont": "CC", "halt": "CH"}
    def convert(term):
        op, *arg = term[1:].split()
        return tags[op] + (" " + arg[0] if arg else "")
    blocks = {}
    for number, body in re.findall(
            r"private def block(\d+) : List Row := \[(.*?)\n\]", source, re.S):
        rows = re.findall(row_pattern, body)
        assert rows and not re.sub(r"\s", "", re.sub(row_pattern, "", body))
        assert int(number) not in blocks
        blocks[int(number)] = [(convert(a), convert(b), int(i)) for a, b, i in rows]
    assert set(blocks) == set(range(101))
    tree = source.split("def literalTree : RowTree :=", 1)[1].split("/--", 1)[0]
    token_pattern = r"\(|\)|\.branch|\.leaf|block\d+|\d+"
    tokens = re.findall(token_pattern, tree)
    assert not re.sub(r"\s", "", re.sub(token_pattern, "", tree))
    cursor = 0
    def parse():
        nonlocal cursor
        token = tokens[cursor]
        cursor += 1
        if token == "(":
            out = parse()
            assert tokens[cursor] == ")"
            cursor += 1
            return out
        if token == ".leaf":
            name = tokens[cursor]
            cursor += 1
            assert name.startswith("block")
            return blocks[int(name[5:])]
        assert token == ".branch"
        cut = int(tokens[cursor])
        cursor += 1
        left, right = parse(), parse()
        assert len(left) == cut
        return left + right
    flat = parse()
    assert cursor == len(tokens)
    assert [i for a, b, i in flat] == list(range(6459))
    assert [(a, b) for a, b, i in flat] == coq_rows

def program_sites():
    """Parse all nodes and traverse the entire source tree, with no site cache."""
    rows = program_rows()
    seen, sites = set(), []
    def visit(node, prefix, active):
        assert node not in active and 0 <= node < len(rows)
        seen.add(node)
        for bit, term in enumerate(rows[node]):
            kind, *arg = term.split()
            value = int(arg[0]) if arg else None
            pc = prefix + str(bit)
            if kind == "CN":
                visit(value, pc, active | {node})
            else:
                if kind in ("CI", "CD"):
                    assert value in range(9)
                sites.append((pc, kind, value))
    visit(0, "", set())
    assert seen == set(range(6459)) and len(sites) == 6460
    assert len({pc for pc, kind, value in sites}) == 6460
    assert max(len(pc) for pc, op, r in sites) == 34
    return sites

def canonical(table):
    order = [97] + sorted({q for q, b in table} - {97})
    mapping = {old: new for new, old in enumerate(order)} | {254: 247}
    result = {(mapping[q], b): (w, d, mapping[t])
              for (q, b), (w, d, t) in table.items()}
    assert sha256(encode(result, 0).encode("ascii")).hexdigest() == CANONICAL_SHA256
    return result, order, mapping

def graph_reachable(table, start, halt):
    pending, seen = [start], set()
    while pending:
        q = pending.pop()
        if q == halt or q in seen:
            continue
        seen.add(q)
        pending.extend(table[q, b][2] for b in (0, 1))
    return seen

def latex_table(table):
    """Produce the full printable table from the same canonical transition map."""
    prelude = r"""\section{Complete canonical transition table}
\label{app:table}
The initial state is 0, the working states are $0,\ldots,246$, and the separate halt label is 247. Every entry is $(\text{write},\text{move},\text{next})$. The final write and move are executed. State numbers run down each half of the table.
\begingroup\small
\setlength{\tabcolsep}{9pt}
\renewcommand{\arraystretch}{1.02}
\begin{longtable}{rcc@{\qquad}rcc}
\toprule
$q$ & Read 0 & Read 1 & $q$ & Read 0 & Read 1\\
\midrule\endfirsthead
\toprule
$q$ & Read 0 & Read 1 & $q$ & Read 0 & Read 1\\
\midrule\endhead
\bottomrule\endfoot
"""
    def half(q):
        cells = [str(q)]
        for b in (0, 1):
            w, d, t = table[q, b]
            cells.append(r"\texttt{" + f"{w} {d} {t}" + "}")
        return " & ".join(cells)
    rows = []
    for q in range(124):
        right = " & " + half(q + 124) if q + 124 < 247 else " & & &"
        rows.append(half(q) + right + r"\\")
    return prelude + "\n".join(rows) + "\n" + r"\end{longtable}" + "\n" + r"\endgroup" + "\n"

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--check", action="store_true")
    args = ap.parse_args()
    if not __debug__:
        ap.error("Assertions are part of the certificates; do not use -O.")
    table = build(check_existing=args.check)
    canon, order, mapping = canonical(table)
    assert digest(ROOT / "reference/prefix250_old.tm") == PRIOR250_SHA256
    prior, prior_start = read_table(ROOT / "reference/prefix250_old.tm")
    assert prior_start == 97 and len(prior) == 500
    reduced = {key: value for key, value in prior.items() if key[0] not in {0, 1, 3}}
    reduced[60, 0] = (0, "R", 20)
    assert reduced == table
    assert graph_reachable(table, 97, 254) == {q for q, b in table}
    files = {
        "machine/zfc_prefix247_old.tm": encode(table, 97),
        "machine/zfc_prefix247.tm": encode(canon, 0),
        "machine/canonical_table.tex": latex_table(canon),
        "machine/renumbering.json": json.dumps(dict(
            start_old=97, start_canonical=0, dispatch_old=96,
            dispatch_canonical=mapping[96], halt_old=254, halt_canonical=247,
            canonical_to_old=order, old_to_canonical=mapping), indent=2) + "\n",
    }
    for name, data in files.items():
        if args.check:
            assert (ROOT / name).read_text(encoding="ascii") == data, name
        else:
            (ROOT / name).parent.mkdir(parents=True, exist_ok=True)
            (ROOT / name).write_text(data, encoding="ascii")
    sites = program_sites()
    out = dict(status="PASS", working_states=247, binary_rows=494,
        start=0, halt=247, dispatcher=mapping[96],
        baseline_commit=PROVEIT_COMMIT, removed_from252=sorted(REMOVED),
        added_states=[255], changed_surviving_rows_from252=8,
        removed_from250=[0, 1, 3], changed_surviving_rows_from250=[
            dict(state=60, read=0, before=[0, "R", 0], after=[0, "R", 20])],
        graph_reachable_working_states=247, unique_halt_row=[mapping[77], 1, 1, "R", 247],
        source_decoder_nodes=6459, source_leaves=len(sites),
        lean_literal_port_rows_identical=6459,
        printable_table_matches_canonical=True,
        guarded_cases=sum(2 if op == "CD" else 1 for pc, op, r in sites),
        old_table_sha256=OLD_FINAL_SHA256, canonical_table_sha256=CANONICAL_SHA256)
    (ROOT / "results").mkdir(parents=True, exist_ok=True)
    (ROOT / "results/rebuild.json").write_text(json.dumps(out, indent=2)+"\n")
    print(json.dumps(out, indent=2))

if __name__ == "__main__":
    main()
