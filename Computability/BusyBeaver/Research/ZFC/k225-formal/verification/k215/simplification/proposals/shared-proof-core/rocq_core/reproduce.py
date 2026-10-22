#!/usr/bin/env python3
"""Compile baseline and candidate in isolated trees; kernel-recheck typed clients.

Requires Python 3.10+, coqc and coqchk. Tested on Coq 8.18.0.
Only the library namespace Stdlib is normalized to Coq in inherited sources.
No endpoint beyond ThmDom is claimed to have been rebuilt by this driver.
"""
from pathlib import Path
import argparse
import hashlib
import json
import shutil
import subprocess
import time

HERE = Path(__file__).resolve().parent
PREFIXES = ["K230S", "K230L", "K215F"]
COMMON = ["K230S/KCode230.v", "K230L/Codes230.v", "K215F/Codes222.v", "K215F/Thm222.v"]


def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--out", type=Path, default=HERE / "build")
    ap.add_argument("--candidate-only", action="store_true")
    args = ap.parse_args()
    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=True)
    provenance = json.loads((HERE / "provenance.json").read_text())
    for rel, record in provenance["upstream"].items():
        assert digest(HERE / rel) == record["sha256"], f"upstream source drift: {rel}"
    for name in ("Codes222.v", "Thm222.v", "ThmDom.v"):
        exact = (HERE / "upstream" / ("production_" + name)).read_text()
        assert (HERE / "src/K215F" / name).read_text() == exact.replace("From Stdlib Require", "From Coq Require")
    assert (HERE / "src/K230S/KCode230.v").read_bytes() == (HERE / "upstream/KCode230.v").read_bytes()
    assert (HERE / "src/K230L/Codes230.v").read_bytes() == (HERE / "upstream/Codes230.v").read_bytes()
    expected_core = (HERE / "src/K215F/DominatedImplication.v").read_bytes()
    subprocess.run(["python3", str(HERE / "render_core.py")], check=True)
    assert (HERE / "src/K215F/DominatedImplication.v").read_bytes() == expected_core, "regeneration drift"
    coqc = shutil.which("coqc")
    coqchk = shutil.which("coqchk")
    if not coqc or not coqchk:
        raise SystemExit("coqc and coqchk are required")
    receipt = {"toolchain": subprocess.check_output([coqc, "--version"], text=True).strip(),
               "scope": "generic core, exact Nat interface, unchanged ThmDom client; no full ZFC rebuild",
               "regeneration_exact": True, "runs": {}}
    for mode in (["candidate"] if args.candidate_only else ["baseline", "candidate"]):
        dst = out / mode
        src = dst / "src"
        logs = dst / "logs"
        logs.mkdir(parents=True, exist_ok=True)
        src.mkdir(parents=True, exist_ok=True)
        for rel in COMMON + ["K215F/DomRho8.v", "K215F/ThmDom.v", "K215F/Audit.v"]:
            dest = src / rel
            dest.parent.mkdir(parents=True, exist_ok=True)
            if mode == "baseline" and rel == "K215F/DomRho8.v":
                s = (HERE / "upstream/production_DomRho8.v").read_text().replace("From Stdlib Require", "From Coq Require")
                dest.write_text(s)
            else:
                shutil.copy2(HERE / "src" / rel, dest)
        order = COMMON + (["K215F/DominatedImplication.v"] if mode == "candidate" else []) + ["K215F/DomRho8.v", "K215F/ThmDom.v", "K215F/Audit.v"]
        if mode == "candidate":
            shutil.copy2(HERE / "src/K215F/DominatedImplication.v", src / "K215F/DominatedImplication.v")
        flags = [item for ns in PREFIXES for item in ("-Q", str(src / ns), ns)]
        results = []
        for rel in order:
            logfile = logs / (rel.replace("/", "_") + ".log")
            start = time.perf_counter()
            with logfile.open("w") as fp:
                p = subprocess.run([coqc, *flags, str(src / rel)], stdout=fp, stderr=subprocess.STDOUT)
            item = {"file": rel, "returncode": p.returncode, "seconds": round(time.perf_counter() - start, 4),
                    "source_sha256": digest(src / rel), "source_bytes": (src / rel).stat().st_size,
                    "source_lines": len((src / rel).read_text().splitlines()),
                    "assumptions_closed_count": logfile.read_text().count("Closed under the global context")}
            if p.returncode == 0:
                item["object_bytes"] = (src / rel).with_suffix(".vo").stat().st_size
                item["object_sha256"] = digest((src / rel).with_suffix(".vo"))
            results.append(item)
            if p.returncode:
                print(logfile.read_text())
                raise SystemExit(f"compile failed: {mode} {rel}")
            expected_assumptions = {"K215F/DomRho8.v": 2, "K215F/ThmDom.v": 1,
                                    "K215F/Audit.v": 2, "K215F/DominatedImplication.v": 6}.get(rel, 0)
            assert item["assumptions_closed_count"] == expected_assumptions, f"unexpected assumptions: {mode} {rel}"
        start = time.perf_counter()
        with (logs / "coqchk.log").open("w") as fp:
            p = subprocess.run([coqchk, "-silent", *flags, "K215F.Audit"], stdout=fp, stderr=subprocess.STDOUT)
        receipt["runs"][mode] = {"modules": results, "coqchk": {"returncode": p.returncode,
                                 "seconds": round(time.perf_counter()-start, 4)}}
        if p.returncode:
            raise SystemExit("coqchk failed")
    (out / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps(receipt, indent=2))


if __name__ == "__main__":
    main()
