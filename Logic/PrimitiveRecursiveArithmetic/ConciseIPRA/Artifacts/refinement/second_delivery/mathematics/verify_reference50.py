"""Verify the frozen current control and its local AST transcription."""

import hashlib
import importlib.util
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parent


def load_module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def canonical(term, binders=()):
    tag = term[0]
    if tag in ("zero", "0"):
        return ("0",)
    if tag in ("var", "v"):
        name = term[1]
        return ("bound", binders.index(name)) if name in binders else ("free", name)
    if tag in ("suc", "S"):
        return ("S", canonical(term[1], binders))
    return ("I", canonical(term[1], binders), canonical(term[2], binders),
            canonical(term[4], (term[3],) + binders))


def main():
    reference = ROOT / "reference50"
    provenance = json.loads((reference / "PROVENANCE.json").read_text())
    for entry in provenance["files"]:
        actual = hashlib.sha256((reference / entry["saved_name"]).read_bytes()).hexdigest()
        if actual != entry["sha256"]:
            raise AssertionError((entry["saved_name"], "source hash mismatch"))
    old = load_module("frozen_current50", reference / "predecessor50.py")
    new = load_module("candidate47", ROOT / "predecessor47.py")
    left = canonical(old.predecessor50(old.var("n")))
    right = canonical(new.current_predecessor50(new.variable("n")))
    if left != right:
        raise AssertionError("Current control transcription is not alpha-equivalent.")
    digest = hashlib.sha256(repr(left).encode()).hexdigest()
    if digest != provenance["control_canonical_ast_sha256"]:
        raise AssertionError("Canonical AST hash mismatch.")
    report = {"status": "passed", "frozen_file_hashes": len(provenance["files"]),
              "control_alpha_equivalent": True, "current_control_nodes": 50,
              "canonical_ast_sha256": digest}
    (ROOT / "reference50_verification.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
