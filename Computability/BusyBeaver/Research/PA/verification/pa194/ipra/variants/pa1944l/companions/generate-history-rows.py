"""Check the four exact b4l archive tables and emit their history-fold certificates."""

from hashlib import sha256
from pathlib import Path
import json
import sys


repo, out = map(Path, sys.argv[1:])
docs = repo / "Computability/BusyBeaver/Research/PA/docs"
four = docs / "pa1944l_research_2026-11-14/machine"
local = docs / "pa194_ax11qh4_research_2026-11-14/research/local"
corpus = docs / "pa194_comparison_and_new_designs_2026-11-15/research/physical"
metadata = json.loads((corpus / "receipts/corpus_meta.json").read_bytes())
assert "All runs use native state labels and start 74" in (local / "README.txt").read_text()
labels_raw = (four / "labels.json").read_bytes()
assert sha256(labels_raw).hexdigest() == "2890771c2db5c598d5f3f833feecf2903e01d69bdf626782e34196c34bfcb13b"
labels = json.loads(labels_raw)
dense = {q: i for i, q in enumerate(labels)}
assert len(labels) == len(dense) == 195 and (labels[0], labels[-1]) == (74, 254)

# Each child is delivered as native rows, with the base start at 74.
pins = {
    "": ("0867349f173d1a98287e5727114e0f210ed36e47f9e927cdf845b978c2ec72b5",
         "0ccf69e31825f78b3be1769f9227f2ffcd81dedc8072f5edbbbcbab3170e8bbd",
         local / "b4l.native.tm", []),
    "Fast": ("481796e5f6b88cb73c35cf2c7cde543a1d9afa4b87c5b1e6f267ffd21cdc2f90",
             "c591bfe12a6a650ead6efa3b589bacd6476a90fd4a90d90cf8cf864cf16eaca8", None, ["f"]),
    "SEL": ("59b64faa9b5a0cd2facfc8676aeca9d2ecb87f50cdc8445a2c7b64d84072e5d3",
            "b3ea2ac01a206d4f82daa959d3d05b44b47185e1c591dbbecf4d94fd445b7a04", None, ["sel"]),
    "FastSEL": ("2f02da57c72d820825a7b86e656d7c11ad86219ac0bdb3e46b5e4458e3962acc",
                "5bbf9c34d11beaeadc31a1a2e5c5332e513b4c1d7cf9553b6374ace05a42e5ad", None, ["f", "sel"]),
}


def rows_of(raw, decode):
    rows = {}
    for line in raw.decode("ascii").splitlines():
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        q, bit, write, direction, target = line.split()
        key = decode(int(q)), int(bit)
        assert key not in rows
        assert write in ("0", "1") and direction in ("L", "R")
        rows[key] = int(write), direction, decode(int(target))
    assert set(rows) == {(q, b) for q in labels[:-1] for b in (0, 1)}
    assert {t for _, _, t in rows.values()} - set(labels[:-1]) == {254}
    return rows


def native_bytes(rows):
    return "".join(f"{q} {b} {w} {d} {t}\n"
                   for (q, b), (w, d, t) in sorted(rows.items())).encode("ascii")


def verify_one(kind, parent_pin, pin, path, patches):
    parent_path = corpus / "inputs/corpus" / f"{parent_pin}.tm"
    if kind:
        parent_raw = parent_path.read_bytes()
        base = rows_of(parent_raw, lambda state: state)
        assert metadata[pin] == {"base": pins[""][1], "patches": patches}
    else:
        raw = (four / "machine.tm").read_bytes()
        assert sha256(raw).hexdigest() == "c5787c6f2350e77183ca0d3ff25d2733ba87e8bb52cd54092d7fa26fcf4d5253"
        base = rows_of(raw, lambda state: labels[state])
        parent_raw = native_bytes(base)
    assert sha256(parent_raw).hexdigest() == parent_pin
    archive = path if path is not None else corpus / "inputs/corpus" / f"{pin}.tm"
    literal = archive.read_bytes()
    assert not any(line.startswith(b"#") for line in literal.splitlines())
    assert sha256(literal).hexdigest() == pin
    child = rows_of(literal, lambda state: state)
    overlay = {(q, b): (w, d, 88 if t == 301 else t)
               for (q, b), (w, d, t) in base.items() if q != 301}
    overlay.update({(88, 0): (0, "L", 301), (301, 0): (0, "R", 122), (301, 1): (1, "R", 301)})
    assert literal == native_bytes(overlay)
    assert base[88, 0] == (0, "R", 122) and base[301, 0] == (0, "R", 45)
    for q in (88, 301):
        inbound = [(src, w, d) for src, (w, d, t) in base.items() if t == q]
        assert inbound and all((w, d) == (int(q == 88), "R") for _, w, d in inbound)
    for q, left in ((88, 1), (301, 0)):
        for bit in (0, 1):
            w, move, end = base[q, bit]
            duration = 1 if bit else (3 if left else 5)
            tape = {-1: left, 0: bit}
            control, head = 88, 0
            for _ in range(duration):
                write, heading, control = child[control, tape[head]]
                tape[head] = write
                head += (1 if heading == "R" else -1)
            assert (head, control, tape) == (
                1 if move == "R" else -1, 88 if end == 301 else end, {-1: left, 0: w})
    return literal, child


def emit(kind, literal, child):
    prior_rows = "PA1944LData" if not kind else f"PA1944L{kind}Rows"
    stem = f"PA1944L{kind}History"
    module = stem + "Rows"
    rows = [f"({w},{int(d == 'R')},{dense[t]})"
            for q in labels[:-1] for b in (0, 1) for w, d, t in [child[q, b]]]
    chunks = ",\n".join("  " + ",".join(rows[i:i + 12]) for i in range(0, len(rows), 12))
    (out / f"{stem}.native.tm").write_bytes(literal)
    (out / f"{module}.lean").write_text(f"""import PA194GuardedHistory
import {prior_rows}

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0

namespace {module}
open PA194GuardedHistory
open PA194BRows (Action)

def rows : List Action := [
{chunks}
]

def rho (q : Nat) : Nat := if q = {dense[301]} then {dense[88]} else q

def certificate : Certificate where
  original := {prior_rows}.rows
  candidate := rows
  rho := rho
  folds := [⟨{dense[88]},1,{dense[301]},{dense[301]}⟩,⟨{dense[301]},0,{dense[301]},{dense[122]}⟩]
  extra := fun q => if q = {dense[301]} then some ({dense[137]},{dense[30]}) else none
  originalCount := by decide +kernel
  candidateCount := by decide +kernel
  start := rfl
  halt := rfl
  live := by decide +kernel
  target := by decide +kernel
  registered := by decide +kernel
  ordinary := by decide +kernel
  exceptional := by decide +kernel
  incoming := by decide +kernel

abbrev table := candidateTable certificate
#print axioms certificate
end {module}
""")


out.mkdir(parents=True, exist_ok=True)
for kind, values in pins.items():
    emit(kind, *verify_one(kind, *values))
