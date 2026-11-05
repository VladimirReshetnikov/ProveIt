#!/usr/bin/env python3
"""Read-only independent check of a retained captured-provider replay."""
import hashlib
import json
import pathlib
import re
import subprocess

HERE = pathlib.Path(__file__).resolve().parent
ROOT = pathlib.Path(subprocess.check_output(["git", "-C", str(HERE), "rev-parse", "--show-toplevel"], text=True).strip())
PACKET = ROOT / "Computability/DiophantineConsistency/research/fourteen-p64-independent-replay"
records = json.loads((PACKET / "results.json").read_text())
result = json.loads((PACKET / "result.json").read_text())
terminal = json.loads((PACKET / "terminal-observation.json").read_text())
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
assert terminal["outer_observed_exit"] == 0 and terminal["read_only_audit_observed_exit"] == 0
assert terminal["runner_sha256"] == sha(PACKET / "run.py")
assert terminal["records_sha256"] == sha(PACKET / "results.json")
assert terminal["result_sha256"] == sha(PACKET / "result.json")
assert terminal["read_only_audit_sha256"] == sha(PACKET / "audit.py")
expected = ["P64Graph", "P64Root", "P64Norm", "P64Early", "P64Facts", "P64ConvZero", "P64Converse", "IPRAPositive64"]
assert [r["module"] for r in records] == expected
assert result["status"] == "PASS" and result["modules"] == len(records) == 8
paths = [pathlib.Path(p) for p in result["lean_path"]]
objects = {}
num_imports = 0
for i, rec in enumerate(records):
    assert rec["exit"] == 0
    src, shim, obj = (pathlib.Path(rec[k]) for k in ("source", "shim", "object"))
    assert sha(src) == rec["source_sha256"] and sha(shim) == rec["shim_sha256"]
    assert obj.is_file() and not obj.is_symlink() and sha(obj) == rec["object_sha256"]
    raw, built = src.read_text(), shim.read_text()
    if i == 0:
        header = "import DiophantineConsistency.Compact44.FreeJSumSquares\n"
        assert raw.startswith(header) and built == "import P65GraphShim\n" + raw[len(header):]
    else:
        assert raw == built
    log = PACKET / "logs" / (rec["module"]+".txt")
    assert sha(log) == rec["log_sha256"] == sha(pathlib.Path(rec["log"]))
    assert not any(s in log.read_text() for s in ("sorryAx", "error:", "warning:"))
    actual_imports = re.findall(r"^import\s+(\S+)", built, re.MULTILINE)
    assert actual_imports == list(rec["imports"])
    for module in actual_imports:
        rel = module.replace(".", "/")+".olean"
        resolved = next((p / rel for p in paths if (p / rel).exists()), None)
        dep = rec["imports"][module]
        assert resolved is not None and str(resolved) == dep["path"] and sha(resolved) == dep["sha256"]
        if module.startswith("DiophantineConsistency.Compact44.") and module.rsplit(".", 1)[-1] in expected:
            prior = module.rsplit(".", 1)[-1]
            assert prior in objects and resolved == objects[prior]
        num_imports += 1
    objects[rec["module"]] = obj
for path, digest in result["direct_provider_guards"].items():
    assert sha(pathlib.Path(path)) == digest
lean = pathlib.Path("/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean")
assert sha(lean) == result["lean_sha256"]
endpoint = (PACKET / "logs/IPRAPositive64.txt").read_text()
for name in ("positiveBridge", "native_equivalence", "standard_equivalence", "reference_equivalence"):
    assert f"'DiophantineConsistency.IPRAPositive64.{name}' depends on axioms: [propext, Classical.choice, Quot.sound]" in endpoint
print(json.dumps({"status": "RETAINED_CAPTURED_PROVIDER_CHECKS_PASS", "modules": len(records),
    "recorded_imports": num_imports, "provider_guards": len(result["direct_provider_guards"]),
    "results_sha256": sha(PACKET / "results.json"), "result_sha256": sha(PACKET / "result.json"),
    "runner_sha256": sha(PACKET / "run.py"), "outer_reported_exit": terminal["outer_observed_exit"],
    "scope": "Read-only hashes, recorded exits, source/import/log checks; no Lean replay or transitive provenance authentication."
}, indent=2, sort_keys=True))
