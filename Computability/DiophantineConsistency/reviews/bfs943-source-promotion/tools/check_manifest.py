#!/usr/bin/env python3
"""Check `manifest.tsv` against the research sources and the BFS943 copies.

Usage: py -I -X utf8 -B check_manifest.py [--allow-drift]

For every copied module: the research source has the recorded SHA-256, the
promoted file `Lean/DiophantineConsistency/BFS943/<module>.lean` has the
recorded SHA-256, and the relation holds:

* `identical`: the two files are byte-identical;
* `imports-only`: they have the same number of `import` lines, and are
  byte-identical once those lines are removed; every promoted import names
  a tree module (`DiophantineConsistency.BFS943.*`, `DiophantineConsistency.*`,
  another tree library, Mathlib or Foundation) whose source file exists.

Rows `reconstructed` and `authored` have no research source; only their
promoted hash is checked. `--allow-drift` reports, instead of failing on, a
promoted hash that has changed (the promotion record lists such fixes).
Also checks that the BFS943 folder contains exactly the manifest's modules.
"""
from hashlib import sha256
from pathlib import Path
import re
import sys

D = Path(__file__).resolve().parents[1]
DC = D.parents[1]                       # Computability/DiophantineConsistency
ROOT = DC.parents[1]                    # repository root
B = DC / "Lean/DiophantineConsistency/BFS943"
IMPORT = re.compile(rb"(?m)^[ \t]*import[ \t]+(\S+)[ \t]*\r?$")
LIBS = {}
for m in re.finditer(r'(?ms)^\[\[lean_lib\]\]\s*\nname\s*=\s*"([^"]+)"\s*\nsrcDir\s*=\s*"([^"]+)"',
                     (ROOT / "lakefile.toml").read_text(encoding="utf-8")):
    LIBS[m.group(1)] = ROOT / m.group(2)
EXTERNAL = ("Mathlib", "Foundation", "Init", "Lean", "Std")


def strip(data):
    return IMPORT.sub(b"", data)


def resolves(name):
    top = name.split(".")[0]
    if top in EXTERNAL:
        return True
    return top in LIBS and (LIBS[top] / (name.replace(".", "/") + ".lean")).exists()


def main():
    drift_ok = "--allow-drift" in sys.argv
    rows = [l.split("\t") for l in (D / "manifest.tsv").read_text(encoding="utf-8").splitlines()[1:]]
    bad, drift, counts = [], [], {}
    for mod, src, ssha, psha, rel in rows:
        counts[rel] = counts.get(rel, 0) + 1
        pdata = (B / f"{mod}.lean").read_bytes()
        if sha256(pdata).hexdigest() != psha:
            drift.append(mod)
        for name in IMPORT.findall(pdata):
            if not resolves(name.decode()):
                bad.append(f"{mod}: unresolved import {name.decode()}")
        if rel in ("reconstructed", "authored"):
            continue
        sdata = (DC / src).read_bytes()
        if sha256(sdata).hexdigest() != ssha:
            bad.append(f"{mod}: source hash")
        if rel == "identical":
            ok = sdata == pdata
        elif rel == "imports-only":
            ok = (len(IMPORT.findall(sdata)) == len(IMPORT.findall(pdata))
                  and strip(sdata) == strip(pdata))
        else:
            ok = False
        if not ok and mod not in drift:
            bad.append(f"{mod}: relation {rel} fails")
    on_disk = {p.stem for p in B.glob("*.lean")}
    listed = {r[0] for r in rows}
    # Modules authored in BFS943/ after the promotion are not promotion rows;
    # they must be declared in post_promotion.tsv (module, record folder).
    post = {}
    post_file = D / "post_promotion.tsv"
    if post_file.exists():
        for line in post_file.read_text(encoding="utf-8").splitlines():
            if line and not line.startswith("#"):
                m, rec = line.split("	")
                post[m] = rec
    clash = sorted(set(post) & listed)
    if clash:
        bad.append(f"post-promotion modules shadow manifest rows: {clash}")
    extra = on_disk - listed - set(post)
    missing = (listed | set(post)) - on_disk
    if extra or missing:
        bad.append(f"folder/manifest mismatch: extra {sorted(extra)}, missing {sorted(missing)}")
    if post:
        print("post-promotion modules", len(post))
    print("rows", len(rows), counts)
    if drift:
        print("promoted hash changed:", ", ".join(drift))
        if not drift_ok:
            bad.append(f"{len(drift)} promoted hashes changed")
    for b in bad:
        print("FAIL", b)
    print("ok" if not bad else "MISMATCH")
    sys.exit(0 if not bad else 1)


if __name__ == "__main__":
    main()
