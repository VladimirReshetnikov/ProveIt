"""Check the archived selector literals before emitting finite row certificates."""

import json
import sys
from hashlib import sha256
from pathlib import Path


# Each tuple gives the reference table, labels, their pins, the optional
# already-calibrated fast overlay pin, and the two selector pins.
PARENTS = {
    "LCC": (
        "pa194_loop_continuation_research_2026-11-14/machines/PA194LC_C/machine.tm",
        "pa194_loop_continuation_research_2026-11-14/machines/PA194LC_C/labels.json",
        "7de80d804e5994db6008687421b0c5b4e96c9c87097fb293269406e9009a5753",
        "dedb6297f4e43a0b6b1a3867be950ce9ca8ba8cc72c2a0297ce99fe071f11112",
        "6f06fbe5a10834d0da06d35bf0ebfa16702f07f5cc6c7965d8bc3f30c98c7c47",
        "cba995e86e6e3efee5c74bca2ade7b98adcc8be052d728c69484f4a01a23e9a6",
        "786a71dd5ff25030ec243035b35f9f61eac466139180767c90d2ef4bd9feadba",
        "PA194LCCData", "rows",
    ),
    "LC": (
        "pa194_loop_continuation_research_2026-11-14/machines/PA194LC/machine.tm",
        "pa194_loop_continuation_research_2026-11-14/machines/PA194LC/labels.json",
        "9cb620ba1b869fb793fd9ba0a99e90dcc85d9a6d62a42f48109743a7fbeda3c8",
        "86a4619d85d97849d0169c8c9773a37bcc8d1d05356451e6c761ab3bfcdda691",
        "dc03de52a78d09f016c6b16346fd4b93f20c87a44dc1e9efb6b7c6a8e6f5fc9f",
        "eed3f48e464b2ac3bbf17260732d1bac0dce0e086da6ea6eb6a5143d528b4c51",
        "c5b776372d8535aef2382b1a51d68ca529bbc0c05be75e5575fa43fbc7e48ac3",
        "PA194LCData", "rows",
    ),
    "AD": (
        "pa194_conpa_2026-11-13/construction/tables/pa194_AD.tm",
        "pa194_conpa_2026-11-13/construction/tables/pa194_AD.labels.json",
        "27613aa92da79ba2ec6e2e88e0ac909fda218e06495ecc0af27201eac0e26c8f",
        "b8c234a0c757cd1885f8fe8ecefc8198767b6d2c15ce0a01443a1e915fded964",
        "d13760e39edeac19cb3312635b22aa29c3182668fac6fb97256e08a9ce626332",
        "c16787eab6a8ec39d0964e2ccc1c052b4f2f5210b54720530463a295d3ab1fb6",
        "fc959c310d118ecbbe2fa76be58f85c7adb9b179fb264b0dea5fa7b450ba7c7f",
        "PA194ADCompressedData", "rows",
    ),
    "HX": (
        "pa194_research_2026-11-14/hx194/machine/pa194hx.tm",
        "pa194_research_2026-11-14/hx194/machine/pa194hx.labels.json",
        "3242a613d328d17c979ce3675a154733ea16a1949b4391cb824711b5aa46399a",
        "3188b59b6479f9664074bb5371bcf2c5c0943f529be1496df35f5cbd2cb77d6c",
        "88015058bd168c277130c7d804193f41302a6e031647da7fc39065458577c75c",
        "5d360c04ea9023cb9894cacc163959016c3927cccfa41cff16c239ea7db452e5",
        "a3957dbab299a65bb3a2f0d27cda9e28d57c218ea3c1121b522b38d3fa323008",
        "PA194HXRows", "rows",
    ),
    "B": (
        "PA194B_PA194G_research_2026-11-14/machine/pa194B.tm",
        "PA194B_PA194G_research_2026-11-14/machine/pa194B.labels.json",
        "b2bcdb6c3816a1fbade699a79e431e4b530ec341aaf516c911920d43f9995397",
        "e30b9614e7d105cdb50d1c9fdb82c4051b58e4d46b7bb7602714094f4e3c64b5",
        "3310f1106c0d431cc7b56a8229cafa120f6030388cf8af4297cfd987136f5bc5",
        "da905776f4ee249c5a0f695d53d57f6ba77a009c117639b7b110f8358982dcc9",
        "359e581cb13b0ccc40ff6fb4de0b849e065b9c1ee18f39a38d2a6356b02e16f9",
        "PA194BRows", "actions",
    ),
}

SELECTOR = {
    (12,0):(0,"L",38),
    (38,0):(0,"R",98),
    (38,1):(1,"R",19),
    (104,1):(1,"R",127),
    (124,0):(0,"R",8),
    (124,1):(1,"R",59),
    (127,0):(0,"L",124),
    (312,1):(1,"R",12),
}
ROLES = [(12,0,38,98),(38,1,38,19),(127,0,124,8),(124,1,124,59)]


def pinned(path, digest):
    data = path.read_bytes()
    assert sha256(data).hexdigest() == digest
    return data


def bytes_of(rows):
    return "".join(
        f"{q} {b} {w} {d} {t}\n" for (q,b),(w,d,t) in sorted(rows.items())
    ).encode("ascii")


def generate(repo, out, parent, fast):
    docs = repo / "Computability/BusyBeaver/Research/PA/docs"
    table, labels_path, table_pin, labels_pin, fast_pin, sel_pin, combined_pin, old_module, old_rows = PARENTS[parent]
    corpus = docs / "pa194_comparison_and_new_designs_2026-11-15/research/physical"
    metadata = json.loads((corpus / "receipts/corpus_meta.json").read_bytes())
    labels = json.loads(pinned(docs / labels_path, labels_pin))
    dense = {q:i for i,q in enumerate(labels)}
    assert len(labels) == len(dense) == 195 and (labels[0],labels[-1]) == (74,254)
    base = {}
    for line in pinned(docs / table, table_pin).decode("ascii").splitlines():
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        q,b,w,d,t = line.split()
        base[labels[int(q)],int(b)] = (int(w),d,labels[int(t)])
    assert set(base) == {(q,b) for q in labels[:-1] for b in (0,1)}
    if fast:
        assert base[26,1] == (1,"R",42) and base[101,0] == (0,"L",26)
        base[26,1] = (1,"R",91)
        base[101,0] = (0,"R",17)
        assert sha256(bytes_of(base)).hexdigest() == fast_pin
        old_module, old_rows = f"PA194{parent}FastRows", "rows"
    digest = combined_pin if fast else sel_pin
    assert digest in metadata
    rows = base | SELECTOR
    raw = bytes_of(rows)
    assert sha256(raw).hexdigest() == digest
    retained = corpus / "inputs/corpus" / f"{digest}.tm"
    if retained.is_file():
        assert raw == retained.read_bytes()
    out.mkdir(parents=True,exist_ok=True)
    mod = f"PA194{parent}{'Fast' if fast else ''}SELRows"
    (out / f"{mod}.native.tm").write_bytes(raw)
    vals = [f"({w},{int(d == 'R')},{dense[t]})"
            for q in labels[:-1] for b in (0,1) for w,d,t in [rows[q,b]]]
    chunks = ",\n".join("  "+",".join(vals[i:i+12]) for i in range(0,388,12))
    folds = ",".join(f"⟨{dense[q]},{b},{dense[s]},{dense[t]}⟩" for q,b,s,t in ROLES)
    (out / f"{mod}.lean").write_text(f"""import PA194GuardedSelectors
import {old_module}

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0

namespace {mod}
open PA194GuardedSelectors
open PA194BRows (Action)

def rows : List Action := [
{chunks}
]

def rho (q : Nat) : Nat := if q = {dense[38]} then {dense[12]}
  else if q = {dense[124]} then {dense[127]} else q

def certificate : Certificate where
  original := {old_module}.{old_rows}
  candidate := rows
  rho := rho
  folds := [{folds}]
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
end {mod}
""")


if __name__ == "__main__":
    candidates = sys.argv[3:]
    if not candidates or any(name.removesuffix("Fast") not in PARENTS for name in candidates):
        raise SystemExit("usage: generate-rows.py REPO OUTPUT {AD,B,HX,LC,LCC,ADFast,BFast,HXFast,LCFast,LCCFast} ...")
    repo, out = map(Path, sys.argv[1:3])
    for name in candidates:
        generate(repo, out, name.removesuffix("Fast"), name.endswith("Fast"))
