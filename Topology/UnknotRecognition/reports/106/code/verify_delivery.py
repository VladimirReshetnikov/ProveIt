#!/usr/bin/env python3
"""Check a research delivery without changing the supplied repository.

Always runs the standalone finite tests. With --repo, additionally reconstructs
the exact pinned touched files, checks and applies all patches in a temporary
directory, compares every patched byte hash, and independently replays the
five saved native source-bound packets using the supplied patched runtime.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path)
    parser.add_argument("--output", type=Path,
                        default=ROOT / "results/validation/delivery_validation.json")
    args = parser.parse_args()
    provenance = json.loads((ROOT / "PROVENANCE.json").read_text())
    integration = json.loads((ROOT / "integration/INTEGRATION.json").read_text())
    report = {"source_pin": provenance["source_pin"], "checks": {}}
    env = dict(os.environ, PYTHONPATH=str(ROOT / "code"))
    command = [sys.executable, "-m", "unittest", "discover", "-s", str(ROOT / "code/tests"),
               "-p", "test_triple_forest_research.py", "-v"]
    result = subprocess.run(command, env=env, cwd=ROOT, capture_output=True, text=True)
    if result.returncode:
        raise RuntimeError(result.stdout + result.stderr)
    log = ROOT / "results/validation/finite_solver_tests.txt"
    log.parent.mkdir(parents=True, exist_ok=True)
    log.write_text(result.stdout + result.stderr)
    report["checks"]["finite_solver_tests"] = dict(status="PASS", tests=15,
                                                  log=str(log.relative_to(ROOT)))

    if args.repo:
        repo = args.repo.resolve()
        patches = [ROOT / "integration" / name for name in integration["patch_order"]]
        for patch in patches:
            assert hashlib.sha256(patch.read_bytes()).hexdigest() == integration["patch_sha256"][patch.name]
        originals = sorted({line[6:] for patch in patches for line in patch.read_text().splitlines()
                            if line.startswith("--- a/")})
        with tempfile.TemporaryDirectory(prefix="proveit-delivery-check-") as temporary:
            check_root = Path(temporary)
            for rel in originals:
                raw = subprocess.check_output(["git", "show", provenance["source_pin"] + ":" + rel],
                                               cwd=repo)
                target = check_root / rel
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(raw)
            subprocess.run(["git", "apply", "--check", *map(str, patches)], cwd=check_root, check=True)
            subprocess.run(["git", "apply", *map(str, patches)], cwd=check_root, check=True)
            for rel, expected in integration["delivery_source_sha256"].items():
                assert hashlib.sha256((check_root / rel).read_bytes()).hexdigest() == expected, rel
                assert hashlib.sha256((repo / rel).read_bytes()).hexdigest() == expected, ("runtime", rel)
        report["checks"]["pinned_patch_application"] = dict(
            status="PASS", original_files=len(originals), patched_files=len(integration["delivery_source_sha256"]),
            exact_delivery_byte_hashes=True, repository_modified=False)
        sys.path.insert(0, str(repo / "Topology/UnknotRecognition/fast"))
        from fastunknot.normal_cut_handlebodies_verify import verify_normal_cut_handlebodies
        audit_path = ROOT / "results/native_packets/bounded_lower_forest_audit.json"
        audit = json.loads(audit_path.read_text())
        expected_packets = {item["packet"]: item for item in audit["cases"]
                            if item["status"] == "COMPLETE"}
        packets = []
        for path in sorted((ROOT / "results/native_packets").glob("*.json")):
            if path == audit_path:
                continue
            packet = json.loads(path.read_text())
            expected = expected_packets[path.name]
            assert packet["id"] == expected["id"]
            assert hashlib.sha256(path.read_bytes()).hexdigest() == expected["packet_sha256"]
            assert verify_normal_cut_handlebodies(packet["triangulation"], packet["coordinates"],
                                                  packet["certificate"]), path.name
            packets.append(dict(file=path.name, id=packet["id"],
                                sha256=hashlib.sha256(path.read_bytes()).hexdigest(), status="PASS"))
        assert len(packets) == len(expected_packets) == 5
        report["checks"]["native_source_packet_replay"] = packets
    else:
        report["checks"]["native_checks"] = "NOT_RUN; supply --repo with the patched pinned runtime"
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
