"""Reproduce distributed checker measurements and finite numerical evidence."""
from pathlib import Path
import gzip
import hashlib
import json
import subprocess
import sys
import tempfile
import measure

ROOT=Path(__file__).resolve().parent
manifest=ROOT/"MANIFEST.json"
if manifest.exists():
    for name,item in json.loads(manifest.read_text())["files"].items():
        raw=(ROOT/name).read_bytes()
        if len(raw)!=item["bytes"] or hashlib.sha256(raw).hexdigest()!=item["sha256"]:
            raise SystemExit("Manifest mismatch: "+name)
recorded=json.loads((ROOT/"evidence/measurements.json").read_text())
current=measure.run()
if (current["python"] == recorded["python"]
        and current["zlib"] == recorded["zlib"]
        and current["zlib_runtime"] == recorded.get("zlib_runtime")):
    if current["rows"] != recorded["rows"]:
        raise SystemExit("Measurement mismatch")
else:
    print("Runtime version differs; reported normalization/compression sizes may change.")
for source in (ROOT/"code").glob("*.py"):
    compressed=source.with_suffix(source.suffix+".gz")
    if compressed.exists() and gzip.decompress(compressed.read_bytes())!=source.read_bytes():
        raise SystemExit("Compressed source mismatch: "+source.name)
subprocess.run([sys.executable,str(ROOT/"tests/check_checkers.py")],check=True)
subprocess.run([sys.executable,str(ROOT/"tests/check_baseline.py")],check=True)
subprocess.run([sys.executable,str(ROOT/"tests/review_ast_profile.py")],check=True)
with tempfile.TemporaryDirectory() as temporary:
    destination=Path(temporary)/"bounded.json"
    subprocess.run([sys.executable,str(ROOT/"tests/bounded_simulation.py"),
                    "--output",str(destination)],check=True)
    result=json.loads(destination.read_text())
    if result["failed"] or result["skipped"]:
        raise SystemExit("Numerical audit failed or skipped a case")
print("All reproduction checks passed. Universal claims remain written proofs.")
