#!/usr/bin/env python3
"""Focused baseline/candidate kernel checks, with exact facade and client audits.

Requires coqc/coqchk (tested with Coq 8.18.0). This does not rebuild the full
Rocq 9.1 ZFC endpoint. The only adaptation of inherited production source is
the standard-library prefix Stdlib -> Coq. Source/proof changes are explicit.
"""
from pathlib import Path
import argparse
import hashlib
import json
import shutil
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
COMMON = ["K230S/KCode230.v", "K230L/Codes230.v", "K215F/Codes222.v", "K215F/Thm222.v"]
TAIL = ["K215F/DomRho8.v", "K215F/ThmDom.v", "K215F/CD222.v",
        "K215F/BasisClients.v", "K215F/Audit.v"]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--out", type=Path, default=HERE / "build")
    args = ap.parse_args()
    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=True)
    provenance = json.loads((HERE / "provenance.json").read_text())
    for rel, record in provenance["upstream"].items():
        assert sha(HERE / rel) == record["delivered_sha256"], f"input drift: {rel}"
    expected = (HERE / "src/K215F/DominatedImplication.v").read_bytes()
    subprocess.run([sys.executable, str(HERE / "render_core.py")], check=True)
    assert (HERE / "src/K215F/DominatedImplication.v").read_bytes() == expected
    coqc, coqchk = shutil.which("coqc"), shutil.which("coqchk")
    if not coqc or not coqchk:
        raise SystemExit("coqc and coqchk must be on PATH")
    receipt = {
        "toolchain": subprocess.check_output([coqc, "--version"], text=True).strip(),
        "repository_commit": "57541fe0cfe3af62b4cb58747d8d1d7c16b338d5",
        "scope": "58-step shared core, DomRho8/CD222 facades, unchanged ThmDom, exact Prop222 client segment; no full ZFC endpoint rebuild",
        "regeneration_exact": True,
        "runs": {},
    }
    for mode in ("baseline", "candidate"):
        dst = out / mode
        src, logs = dst / "src", dst / "logs"
        logs.mkdir(parents=True, exist_ok=True)
        order = COMMON + (["K215F/DominatedImplication.v"] if mode == "candidate" else []) + TAIL
        for rel in order:
            target = src / rel
            target.parent.mkdir(parents=True, exist_ok=True)
            if mode == "baseline" and Path(rel).name in ("DomRho8.v", "CD222.v"):
                original = HERE / "upstream" / ("production_" + Path(rel).name)
                target.write_text(original.read_text().replace("From Stdlib Require", "From Coq Require"))
            else:
                shutil.copy2(HERE / "src" / rel, target)
        flags = [x for ns in ("K230S", "K230L", "K215F") for x in ("-Q", str(src / ns), ns)]
        results = []
        for rel in order:
            log = logs / (rel.replace("/", "_") + ".log")
            start = time.perf_counter()
            with log.open("w") as stream:
                proc = subprocess.run([coqc, *flags, str(src / rel)], stdout=stream, stderr=subprocess.STDOUT)
            text = log.read_text()
            item = {"source": rel, "returncode": proc.returncode,
                    "seconds": round(time.perf_counter()-start, 4),
                    "source_sha256": sha(src / rel),
                    "source_bytes": (src / rel).stat().st_size,
                    "source_lines": len((src / rel).read_text().splitlines()),
                    "closed_reports": text.count("Closed under the global context")}
            results.append(item)
            if proc.returncode or "Axioms:" in text:
                print(text)
                raise SystemExit(f"Failed check: {mode}: {rel}")
            expected_count = {"DomRho8.v": 2, "ThmDom.v": 1, "BasisClients.v": 4,
                              "Audit.v": 6, "DominatedImplication.v": 7,
                              "CD222.v": 4 if mode == "candidate" else 0}.get(Path(rel).name, 0)
            assert item["closed_reports"] == expected_count, item
            item["object_sha256"] = sha((src / rel).with_suffix(".vo"))
            item["object_bytes"] = (src / rel).with_suffix(".vo").stat().st_size
            print(f"{mode}: {rel}: PASS", flush=True)
        log = logs / "coqchk.log"
        start = time.perf_counter()
        with log.open("w") as stream:
            proc = subprocess.run([coqchk, "-silent", *flags, "K215F.Audit", "K215F.BasisClients"],
                                  stdout=stream, stderr=subprocess.STDOUT)
        check = {"returncode": proc.returncode, "seconds": round(time.perf_counter()-start, 4)}
        receipt["runs"][mode] = {"modules": results, "recursive_kernel_check": check}
        if proc.returncode:
            print(log.read_text())
            raise SystemExit(f"coqchk failed: {mode}")
        print(f"{mode}: recursive coqchk: PASS", flush=True)
    receipt["status"] = "PASS_FOCUSED_CLOSED_KERNEL"
    (out / "receipt.json").write_text(json.dumps(receipt, indent=2)+"\n")
    print(json.dumps({"status": receipt["status"], "receipt": str(out/"receipt.json")}))


if __name__ == "__main__":
    main()
