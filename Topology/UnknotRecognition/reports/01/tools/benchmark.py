"""Reproduce the bundled examples and independently replay every certificate.

Run: python -m tools.benchmark
The examples are not a representative performance study or a complexity proof.
"""
from datetime import datetime, timezone
import json
from pathlib import Path
import platform
from time import monotonic

from unknot import Grid, recognize, verify_certificate
from unknot.determinant import determinant

ROOT = Path(__file__).resolve().parents[1]
NAMES = ("unknot", "trefoil", "torus_2_5", "determinant_one_knot",
         "scrambled_unknot", "scrambled_trefoil", "scrambled_determinant_one_knot")


def main():
    out = ROOT / "examples" / "certificates"
    out.mkdir(exist_ok=True)
    rows = []
    for name in NAMES:
        grid = Grid.from_json(json.loads((ROOT / "examples" / (name + ".json")).read_text()))
        result = recognize(grid, max_states=100000, timeout=30, use_determinant=False)
        certificate = result.pop("certificate", None)
        if certificate is not None:
            start = monotonic()
            verified = verify_certificate(certificate, grid)
            result["verification_seconds"] = monotonic() - start
            if verified["verdict"] != result["verdict"]:
                raise AssertionError("certificate disagrees with result")
            (out / (name + ".json")).write_text(json.dumps(certificate, indent=2) + "\n")
            result["certificate_verified"] = True
        result["name"] = name
        result["determinant"] = determinant(grid)
        rows.append(result)
        print(json.dumps(result), flush=True)
    # Deliberately exercise an incomplete, resource-bounded run.
    grid = Grid.from_json(json.loads((ROOT / "examples/scrambled_unknot.json").read_text()))
    limited = recognize(grid, max_states=1, use_determinant=False)
    if limited["verdict"] != "UNKNOWN" or "certificate" in limited:
        raise AssertionError("state limit produced an unsound conclusion")
    report = {"timestamp_utc": datetime.now(timezone.utc).isoformat(),
              "python": platform.python_version(), "platform": platform.platform(),
              "determinant_shortcut_enabled": False, "results": rows,
              "resource_limit_check": limited}
    (ROOT / "docs/benchmark-results.json").write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
