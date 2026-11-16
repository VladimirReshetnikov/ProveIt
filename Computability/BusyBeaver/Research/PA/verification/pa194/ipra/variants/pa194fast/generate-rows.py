"""Generate Lean certificates for the three pinned two-shortcut tables."""

import json
import sys
from hashlib import sha256
from pathlib import Path


# Reference table stem and archive SHA-256 pins for each literal variant.
CANDIDATES = {
    "": (
        "pa194_conpa_2026-11-13/construction/tables/pa194",
        "4bfea62b17aad7d8c8c5e682fe8942e0a86b93e4351f8e675e32705bdaae007f",
        "b8c234a0c757cd1885f8fe8ecefc8198767b6d2c15ce0a01443a1e915fded964",
        "d8f3b1b8e994cccb0ce2ce0950ff1ea0e1729570501538b6f0a6c110c8794233",
    ),
    "B": (
        "PA194B_PA194G_research_2026-11-14/machine/pa194B",
        "b2bcdb6c3816a1fbade699a79e431e4b530ec341aaf516c911920d43f9995397",
        "e30b9614e7d105cdb50d1c9fdb82c4051b58e4d46b7bb7602714094f4e3c64b5",
        "3310f1106c0d431cc7b56a8229cafa120f6030388cf8af4297cfd987136f5bc5",
    ),
    "SEL": (
        "pa194_sel_ax11gh_research_2026-11-14/machines/SEL/machine/pa194sel",
        "5121f0b417ea025af140804b59e50a9d2fc3c461612e98b2f0ac86742c76a75b",
        "e9ff4746563f97efc655b1b3b5261d3fb87e5f62aeee3d2fc83cd8be6817d990",
        "e93b8634951bf934569e43e418b4b2bfcb329d61c3720f6880bf05003b112be1",
    ),
}
CONTROLS = {
    26: "firstSource",
    42: "firstNext",
    13: "firstTurn",
    91: "firstDestination",
    101: "secondSource",
    194: "secondReturn",
    17: "secondDestination",
    11: "neighborControl",
}


def generate(docs, out, candidate, pins):
    path, table_hash, labels_hash, fast_hash = pins
    stem = docs / path
    base = stem.with_suffix(".tm").read_bytes()
    label_bytes = stem.with_suffix(".labels.json").read_bytes()
    assert sha256(base).hexdigest() == table_hash
    assert sha256(label_bytes).hexdigest() == labels_hash
    labels = json.loads(label_bytes)
    dense = {q: i for i, q in enumerate(labels)}
    assert len(labels) == len(dense) == 195 and (labels[0], labels[-1]) == (74, 254)

    native = {}
    for line in base.decode("ascii").splitlines():
        q, b, write, move, target = line.split()
        native[labels[int(q)], int(b)] = int(write), move, labels[int(target)]
    assert set(native) == {(q, b) for q in labels[:-1] for b in (0, 1)}
    assert native[26, 1] == (1, "R", 42)
    assert native[101, 0] == (0, "L", 26)
    native[26, 1] = 1, "R", 91
    native[101, 0] = 0, "R", 17

    literal = "".join(
        f"{q} {b} {w} {move} {target}\n"
        for (q, b), (w, move, target) in sorted(native.items())
    ).encode("ascii")
    assert sha256(literal).hexdigest() == fast_hash
    basename = f"PA194{candidate}Fast" if candidate else "primary_fast"
    (out / f"{basename}.native.tm").write_bytes(literal)

    rows = []
    for q in labels[:-1]:
        for b in (0, 1):
            write, direction, target = native[q, b]
            rows.append(f'({write},{int(direction == "R")},{dense[target]})')
    chunks = ",\n".join(
        "  " + ",".join(rows[i:i + 12]) for i in range(0, len(rows), 12)
    )
    settings = "\n".join(
        f"  {role} := ⟨{dense[q]},by decide⟩" for q, role in CONTROLS.items()
    )

    reference = f"PA194{candidate}Rows"
    actions = "actions" if candidate else "rows"
    module = f"PA194{candidate}FastRows"
    (out / f"{module}.lean").write_text(f"""import PA194GuardedShortcuts
import {reference}

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0

namespace {module}
open PA194GuardedShortcuts

/-- Dense rows obtained from the pinned native bytes using the reference
    native-to-dense map. -/
def rows : List Action := [
{chunks}
]

def certificate : Certificate where
  original := {reference}.{actions}
  accelerated := rows
  originalCount := by decide +kernel
  acceleratedCount := by decide +kernel
{settings}
  firstOriginal := rfl
  firstMiddle := rfl
  firstLast := rfl
  firstFast := rfl
  secondOriginal := rfl
  secondMiddle := rfl
  secondLast := rfl
  secondFast := rfl
  ordinary := by decide +kernel
  incoming := by decide +kernel

abbrev table := acceleratedTable certificate
#print axioms certificate
end {module}
""")


def main():
    repo, out = map(Path, sys.argv[1:3])
    flags = sys.argv[3:]
    if flags not in ([], ["--companions"]):
        raise SystemExit("usage: generate-rows.py REPO OUTPUT [--companions]")
    docs = repo / "Computability/BusyBeaver/Research/PA/docs"
    catalogue = (docs / "MACHINE_FILES.tsv").read_text()
    core = docs / "pa194_ax11gdh_research_2026-11-15/research/core_reductions"
    manifest = json.loads((core / "input_sha256.json").read_bytes())
    assert CANDIDATES[""][1:] == (
        manifest["inputs/primary.tm"],
        manifest["inputs/labels.json"],
        manifest["inputs/primary_fast.native.tm"],
    )
    out.mkdir(parents=True, exist_ok=True)
    for candidate, pins in CANDIDATES.items():
        if candidate and not flags:
            continue
        assert f"\t{pins[-1]}\t" in catalogue
        generate(docs, out, candidate, pins)


if __name__ == "__main__":
    main()
