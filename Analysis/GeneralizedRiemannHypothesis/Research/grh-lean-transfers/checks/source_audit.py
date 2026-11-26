"""Check the source lock and selected public declarations in a local grh-lean clone."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys

PIN = "72fead102f663d5c7a407964a13dc0cf9d977207"
MATHLIB = "56a005855ea17e0b0958f73ec801ae140b0a1679"
root = Path(sys.argv[1]).resolve()
rev = subprocess.check_output(["git", "-C", str(root), "rev-parse", "HEAD"], text=True).strip()
if rev != PIN:
    raise SystemExit(f"Expected {PIN}, found {rev}")

# A clean tracked tree is essential before treating the file digests as pinned.
subprocess.run(["git", "-C", str(root), "diff", "--exit-code", "HEAD"], check=True)
print("Repository", rev)
statements = []
for edition in ("grh", "grh-compact"):
    project = root / edition
    sources = sorted((project / "src").rglob("*.lean"))
    lock = json.loads((project / "lake-manifest.json").read_text())
    assert next(item["rev"] for item in lock["packages"] if item["name"]=="mathlib") == MATHLIB
    assert (project/"lean-toolchain").read_text().strip()=="leanprover/lean4:v4.35.0"
    config = json.loads((project/"comparator.json").read_text())
    main = (project/"src/Main.lean").read_text()
    assert all("theorem "+name+" " in main for name in config["theorem_names"])
    assert set(config["permitted_axioms"])=={"propext","Quot.sound","Classical.choice"}
    body=(project/"src/Statements.lean").read_bytes()
    assert [l for l in body.decode().splitlines() if l.startswith("import ")]==["import Mathlib"]
    statements.append(body)
    print(edition, len(sources), "source modules")
    for path in ("src/Statements.lean","src/Main.lean","comparator.json"):
        print(hashlib.sha256((project/path).read_bytes()).hexdigest(), edition+"/"+path)
assert statements[0]==statements[1]
print("Public statement files agree byte for byte.")
print("These are source checks. Kernel replay is documented in the cited independent audit.")
