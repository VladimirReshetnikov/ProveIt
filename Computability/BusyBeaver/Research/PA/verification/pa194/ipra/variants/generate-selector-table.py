"""Generate pinned tables and native caches for primary-source register permutations."""

import json
import sys
from hashlib import sha256
from pathlib import Path


PRIMARY_HASH = "4bfea62b17aad7d8c8c5e682fe8942e0a86b93e4351f8e675e32705bdaae007f"
LABEL_HASH = "b8c234a0c757cd1885f8fe8ecefc8198767b6d2c15ce0a01443a1e915fded964"
variants = {
    "PA194P5": {
        "folder": "pa194p5_research_2026-11-14",
        "table": "machine/pa194p5.tm",
        "labels": "reference/pa194.labels.json",
        "table_hash": "cf3a2c2d3ba8e95d5c0ea825c3f279ae529b6591cc1280264b0ba3793e77d026",
        "label_hash": LABEL_HASH,
        "native_hash": "a9d3a13786b6a0018713d8803865860b5e9e26692fde34975545c3bb0f09501c",
        "native_output": "pa194p5.native.tm",
        "source": ("reference/pa194.instructions.json", "reference/pa194.sites.json"),
        "routes": {17: (32, 25), 21: (60, 55), 41: (25, 48), 45: (55, 60),
                   61: (25, 48), 144: (48, 32), 161: (32, 25)},
    },
    "PA194TDY": {
        "folder": "pa194_tdy_2026-11-14",
        "table": "artifacts/pa194_tdy.tm",
        "labels": "artifacts/labels.json",
        "table_hash": "84bfe1368312c7c71c9e4706de7cb65923310e25f8d472997c9c57c5aedd7934",
        "label_hash": "8f977a69162d3622d83588c242a7b67456c623df4c0d06cc6582db2b71b906bd",
        "native_hash": "2f6e2342151be7c9f7fb8025f81063525c5d276605d2fa87535a9c7d1498755d",
        "native_output": "pa194_tdy.native.tm",
        "source": ("source/instructions.json", "source/sites.json"),
        "routes": {41: (25, 48), 61: (25, 48), 82: (33, 25), 144: (48, 33)},
    },
    "PA194C32": {
        "folder": "pa194_ax11hc4_c32_research_2026-11-15/construction",
        "table": "cycle32/pa194_cycle32.tm",
        "labels": "cycle32/labels.json",
        "table_hash": "3af42ea9d430e5df22b69e6fc540e3530f87263372580c7c554bae37ba524ac8",
        "label_hash": "45ed8d4ce00769058326ca2563d122afd809385c77b2f551f038016b9f79cb6a",
        "native_hash": "7a83339f95624c0d9b3935f081f226b17461dac6c4660e03a400ce04be8e0a9e",
        "native_output": "pa194_cycle32.native.tm",
        "grammar": ("source/source_grammar.json", "e162ee72042f671edcaf99d5aa4d0173e867c636719f9fb3fd254c83f84ebb4e"),
        "routes": {17: (32, 48), 21: (60, 55), 41: (25, 32), 45: (55, 60),
                   61: (25, 32), 144: (48, 25), 161: (32, 48)},
    },
}


def pinned(path, digest):
    raw = path.read_bytes()
    assert sha256(raw).hexdigest() == digest
    return raw


def dense_table(raw):
    rows = {}
    for line in raw.decode("ascii").splitlines():
        q, b, w, d, dest = line.split()
        key = int(q), int(b)
        dest = int(dest)
        assert key not in rows and w in ("0", "1") and d in ("L", "R") and 0 <= dest <= 194
        rows[key] = int(w), d, dest
    assert set(rows) == {(q, b) for q in range(194) for b in range(2)}
    return rows


def native_table(rows, labels):
    return {(labels[q], b): (w, d, labels[dest])
            for (q, b), (w, d, dest) in rows.items()}


def lean_list(items, cols):
    return ",\n".join("  " + ",".join(items[i:i + cols])
                      for i in range(0, len(items), cols))


def lean_tree(rows, keys):
    if not keys:
        return ".empty"
    mid = len(keys) // 2
    q = keys[mid]

    def arm(b):
        w, d, t = rows[q, b]
        return f"(some ({str(bool(w)).lower()},{str(d == 'R').lower()},{t}))"

    return (f"(.node {q} {arm(0)} {arm(1)}\n"
            f"{lean_tree(rows, keys[:mid])}\n"
            f"{lean_tree(rows, keys[mid + 1:])})")


def grammar_sites(grammar):
    """Expand the packet's compact tree to its path/operator/operand triples."""
    entries = grammar["entries"]
    opcodes = {"i": "inc", "d": "dec", "b": "breakTo", "c": "continueTo", "h": "halt"}

    def expand(index, path):
        entry = entries[index]
        if isinstance(entry, str):
            yield [path, opcodes[entry[0]], int(entry[1:]) if len(entry) > 1 else None]
        else:
            yield from expand(entry[0], path + "0")
            yield from expand(entry[1], path + "1")

    return list(expand(grammar["root"], ""))


def check_source(spec, folder, primary):
    if "grammar" in spec:
        filename, digest = spec["grammar"]
        grammar = json.loads(pinned(folder / filename, digest))
        assert grammar_sites(grammar) == json.loads((primary / "source/pa194.sites.json").read_bytes())
    else:
        for name, source in zip(("instructions", "sites"), spec["source"]):
            assert json.loads((folder / source).read_bytes()) == \
                json.loads((primary / "source" / f"pa194.{name}.json").read_bytes())


def main():
    if len(sys.argv) != 4 or sys.argv[1] not in variants:
        raise SystemExit("usage: generate-selector-table.py {PA194P5,PA194TDY,PA194C32} REPO OUTPUT")
    variant = sys.argv[1]
    repo, out = map(Path, sys.argv[2:])
    spec = variants[variant]
    docs = repo / "Computability/BusyBeaver/Research/PA/docs"
    primary = docs / "pa194_conpa_2026-11-13/construction"
    folder = docs / spec["folder"]
    parent = dense_table(pinned(primary / "tables/pa194.tm", PRIMARY_HASH))
    child = dense_table(pinned(folder / spec["table"], spec["table_hash"]))
    primary_labels = json.loads(pinned(primary / "tables/pa194.labels.json", LABEL_HASH))
    labels = json.loads(pinned(folder / spec["labels"], spec["label_hash"]))
    assert len(set(labels)) == len(labels) == 195 and (labels[0], labels[-1]) == (74, 254)
    check_source(spec, folder, primary)
    native = native_table(child, labels)
    expected = native_table(parent, primary_labels)
    for q, (old, new) in spec["routes"].items():
        assert expected[q, 1] == (0, "R", old)
        expected[q, 1] = 0, "R", new
    assert native == expected
    raw_native = "".join(f"{q} {b} {w} {d} {dest}\n"
                         for (q, b), (w, d, dest) in sorted(native.items())).encode("ascii")
    assert sha256(raw_native).hexdigest() == spec["native_hash"]
    out.mkdir(parents=True, exist_ok=True)
    (out / spec["native_output"]).write_bytes(raw_native)
    row_code = lean_list([f"({w},{int(d == 'R')},{t})"
                          for _, (w, d, t) in sorted(child.items())], 12)
    (out / f"{variant}Data.lean").write_text(f"""import PA194FoldedCache
import PA194BModelSteps

set_option autoImplicit false
set_option maxRecDepth 65536

namespace {variant}Data

/-- {variant.removeprefix('PA194')}'s pinned dense rows, in increasing state/read order. -/
def rows : List PA194BRows.Action := [
{row_code}
]

def labels : List Nat := [
{lean_list(list(map(str, labels)), 14)}
]

def nativeTree : PA194FoldedCache.Tree := {lean_tree(native, sorted(labels[:-1]))}

abbrev table := PA194BModelSteps.table rows
abbrev machine : M6.Zip.TMN := nativeTree.read
abbrev denseControl := labels.idxOf

theorem rowCount : rows.length = 388 := by decide +kernel
theorem labelCount : labels.length = 195 := by decide +kernel

end {variant}Data
""")


if __name__ == "__main__":
    main()
