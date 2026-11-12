"""Remeasure the controls discovered in the thirteen incoming archives."""
from pathlib import Path
import ast
import hashlib
import io
import json
import tokenize

ROOT = Path(__file__).resolve().parent
SKIP = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.COMMENT,
        tokenize.NEWLINE, tokenize.NL, tokenize.INDENT, tokenize.DEDENT}

def metric(path):
    raw = path.read_bytes()
    tree = ast.parse(raw)
    text = ast.unparse(tree) + "\n"
    return dict(
        tokens=sum(t.type not in SKIP for t in
                   tokenize.generate_tokens(io.StringIO(text).readline)),
        ast_nodes=sum(1 for _ in ast.walk(tree)),
        normalized_bytes=len(text.encode()),
        sha256=hashlib.sha256(raw).hexdigest())

def main():
    audit = json.loads((ROOT / "evidence/incoming_audit.json").read_text())
    controls = []
    rows = []
    for archive in audit["archives"]:
        for source in archive["selected_measured_sources"]:
            result = metric(ROOT / source["local_path"])
            for key, value in result.items():
                if source[key] != value:
                    raise AssertionError((source["local_path"], key))
            rows.append(dict(file=source["local_path"], **result))
            if Path(source["local_path"]).name in ("native_strict_checker.py",
                                                   "ast386.py"):
                controls.append(result)
    controls.append(metric(ROOT / "implementation/ref/verified_refinements/strict/checker.py"))
    coordinates = ("tokens", "ast_nodes", "normalized_bytes")
    envelope = tuple(min(c[k] for c in controls) for k in coordinates)
    candidate = metric(ROOT / "implementation/alias_inverted.py")
    candidate_vector = tuple(candidate[k] for k in coordinates)
    assert envelope == (334, 386, 628), envelope
    assert candidate_vector == (331, 373, 625), candidate_vector
    assert all(a < b for a, b in zip(candidate_vector, envelope))
    print(json.dumps(dict(incoming_archives=13,
                          remeasured_incoming_sources=len(rows),
                          prior_typed_envelope=envelope,
                          candidate=candidate_vector,
                          strict_improvement_all_coordinates=True), indent=2))

if __name__ == "__main__":
    main()

