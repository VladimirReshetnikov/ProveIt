#!/usr/bin/env python3
"""Remeasure the five exact incoming archives, without executing their code."""
import argparse
import ast
import gzip
import hashlib
import io
import json
from pathlib import Path
import platform
import urllib.request
import zipfile

from reproduce import measure, ROOT

COMMIT = "798856e4ef2d02b7f9c0f1660828c5ce58f277f2"
ARCHIVES = {
    "ipra_conditional_image_2026-11-13.zip": "07386aa7848e2ac2eaec468ac9ea7abbb0cf19b7",
    "ipra_coverage_constancy_2026-11-13.zip": "798a8049de46be95e8c1f79fda35807290d5c647",
    "ipra_coverage_obstruction_2026-11-13.zip": "0a4fbbfec4aa07ec826894a5980dccaf4323e22f",
    "ipra_homogeneous_discharge_2026-11-13.zip": "18291833c07ff39d9de5d5d0b6160def4f5afffa",
    "ipra_validated_arity_refinement_2026-11-13.zip": "691f6aa73cb49c426e662716238149866275f493",
}
BASE = ("https://raw.githubusercontent.com/VladimirReshetnikov/ProveIt/" + COMMIT
        + "/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/docs/incoming/")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--archives", type=Path, help="Directory containing the five ZIPs; otherwise download the pinned versions.")
    args = parser.parse_args()
    rows = []
    archives = []
    for name, expected in ARCHIVES.items():
        if args.archives:
            data = (args.archives / name).read_bytes()
        else:
            with urllib.request.urlopen(BASE + name, timeout=60) as response:
                data = response.read()
        blob = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
        if blob != expected:
            raise ValueError("Git blob mismatch: " + name)
        archives.append({"archive": name, "git_blob_sha1": blob, "size_bytes": len(data)})
        with zipfile.ZipFile(io.BytesIO(data)) as archive:
            for member in sorted(archive.namelist()):
                if not member.endswith((".py", ".py.gz")):
                    continue
                code = archive.read(member)
                if member.endswith(".gz"):
                    code = gzip.decompress(code)
                try:
                    measurements = measure(code)
                except (UnicodeDecodeError, SyntaxError) as exc:
                    rows.append({"archive": name, "path": member, "error": str(exc)})
                    continue
                tree = ast.parse(code.decode("utf-8"))
                dynamic = any(isinstance(n, ast.Call) and isinstance(n.func, ast.Name)
                              and n.func.id in {"exec", "eval"} for n in ast.walk(tree))
                rows.append({"archive": name, "path": member, **measurements,
                             "contains_exec_or_eval_call": dynamic})
    result = {
        "commit": COMMIT, "python": platform.python_version(),
        "archives": archives, "member_count": len(rows), "files": rows,
        "qualification": "Includes utilities and invalid experiments. A size census is not a soundness audit.",
    }
    destination = ROOT / "evidence/survey_reproduced.json"
    destination.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"archives_verified": len(archives), "members_measured": len(rows),
                      "parse_errors": sum("error" in r for r in rows),
                      "output": str(destination)}, indent=2))


if __name__ == "__main__":
    main()
