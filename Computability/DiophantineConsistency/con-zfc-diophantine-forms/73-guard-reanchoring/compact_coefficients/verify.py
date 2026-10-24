#!/usr/bin/env python3
"""Offline reconstruction of the complete compact coefficient tuple.

Requires Python 3.10+ and the standard library only. Upstream files are
authenticated and never modified. The upstream builder and an independent
tile-based auditor execute in a temporary copy.
"""
from pathlib import Path
from hashlib import sha1, sha256
import argparse
import gzip
import json
import platform
import shutil
import subprocess
import sys
import tempfile
import zlib

ROOT = Path(__file__).resolve().parent
COMMIT = "9cca523d9f27ad39d52993f4065cbd7e58f8bdd4"
INSTANCE = "wang943-complement67-shared-anchor-length8807-prime581197"
BINDING_HASH = "0599543212b8d2bbed2db018a29d6826702e1877faa5c8a1861d041998cb1783"
RAW_HASHES = {
    "beta": "0664a868cbfef9869ea05c40a1c445563f685ff857092594c1c1223bc4b21f9d",
    "K": "c6d523bd32af8dd0345db843cdadf6932bfcad186912a6d112314b60657c554e",
    "MC": "6007cabd5f5228618e8fb613f386d8fc3692a24520d6e4cd72af0262aae1ade4",
    "MF_source": "48333b0d30a4edeb8579f44286cb59806c5622cb42b367f5b5f9ee827711c737",
}
ALIASES = {"beta": "beta", "K0": "K", "MC": "MC", "MF": "MF_source"}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(raw):
    return sha256(raw).hexdigest()


def read_json(path):
    return json.loads(path.read_text(encoding="utf-8"))


def authenticate_sources():
    manifest = read_json(ROOT / "UPSTREAM_FILES.json")
    require(manifest["repository"] == "VladimirReshetnikov/ProveIt", "repository")
    require(manifest["retrieval_commit"] == COMMIT, "retrieval commit")
    seen = set()
    for entry in manifest["files"]:
        relative = Path(entry["path"])
        require(not relative.is_absolute() and ".." not in relative.parts, "source path")
        require(entry["path"] not in seen, "duplicate source path")
        seen.add(entry["path"])
        raw = (ROOT / relative).read_bytes()
        require(len(raw) == entry["bytes"], "source size: " + entry["path"])
        require(digest(raw) == entry["sha256"], "source SHA256: " + entry["path"])
        blob = sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest()
        require(blob == entry["git_blob_sha1"], "Git blob: " + entry["path"])
        require(entry["retrieval_commit"] == COMMIT, "mixed retrieval commit")
    return len(seen)


def inspect_payloads(directory, binding):
    result = {}
    for entry in binding["materialization"]["files"]:
        port = entry["port"]
        require(port in RAW_HASHES and port not in result, "unexpected or duplicate port")
        packed = (directory / entry["file"]).read_bytes()
        raw = gzip.decompress(packed)
        value = int.from_bytes(raw, "little", signed=False)
        require(value > 0, "nonpositive coefficient")
        require(value.bit_length() == entry["bits"], "coefficient bit length")
        require(len(raw) == (value.bit_length() + 7) // 8, "nonminimal encoding")
        require(len(raw) == entry["raw_bytes"], "raw byte length")
        require(len(packed) == entry["gzip_bytes"], "gzip byte length")
        require(digest(raw) == entry["sha256"] == RAW_HASHES[port], "raw coefficient hash")
        require(digest(packed) == entry["gzip_sha256"], "gzip coefficient hash")
        result[port] = (raw, packed)
    require(set(result) == set(RAW_HASHES), "incomplete coefficient tuple")
    return result


def run_script(directory, filename):
    command = [sys.executable]
    if sys.flags.optimize:
        command.append("-" + "O" * min(sys.flags.optimize, 2))
    command.append(str(directory / filename))
    completed = subprocess.run(command, cwd=directory, text=True,
                               capture_output=True, check=False)
    require(completed.returncode == 0,
            filename + " failed:\n" + completed.stdout + completed.stderr)
    return json.loads(completed.stdout)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--receipt", type=Path, help="write the verification receipt")
    parser.add_argument("--regenerate", type=Path,
                        help="save regenerated coefficients and binding in a new directory")
    args = parser.parse_args()
    require(sys.version_info >= (3, 10), "Python 3.10 or newer is required")
    if args.regenerate is not None:
        require(not args.regenerate.exists(), "regeneration directory already exists")

    source_count = authenticate_sources()
    original = ROOT / "native"
    binding_path = original / "COEFFICIENT_BINDING.json"
    require(digest(binding_path.read_bytes()) == BINDING_HASH, "active tuple binding hash")
    binding = read_json(binding_path)
    require(binding["instance"] == INSTANCE, "active tuple name")
    require((binding["b"], binding["L"], binding["d"]) == (67, 8807, 590069),
            "active tuple dimensions")
    require(binding["ports"] == {"Bm1": "beta", "Kconstant": "K", "MC": "MC", "MF": "MF_source"},
            "upstream port convention")
    port_manifest = read_json(ROOT / "POSITIVE_PORTS.json")
    require(port_manifest["instance"] == INSTANCE
            and port_manifest["binding"] == "native/COEFFICIENT_BINDING.json"
            and port_manifest["binding_sha256"] == BINDING_HASH,
            "positive equation integration binding")
    expected_ports = {}
    for variable, port in ALIASES.items():
        entry = next(row for row in binding["materialization"]["files"] if row["port"] == port)
        expected_ports[variable] = dict(entry, file="native/" + entry["file"])
    require(port_manifest["ports"] == expected_ports, "positive equation port aliases")
    payloads = inspect_payloads(original, binding)
    beta = int.from_bytes(payloads["beta"][0], "little")
    require(beta == (1 << 590069) - 1, "literal beta")
    require(sum(len(raw) for raw, _ in payloads.values()) == 295388, "raw tuple size")

    with tempfile.TemporaryDirectory(prefix="proveit-compact-coefficients-") as temporary:
        working = Path(temporary) / "native"
        shutil.copytree(original, working)
        rebuilt_binding = run_script(working, "build_coefficients.py")
        require(rebuilt_binding == read_json(working / "COEFFICIENT_BINDING.json"),
                "builder stdout and saved binding disagree")
        require({k: v for k, v in rebuilt_binding.items() if k != "materialization"}
                == {k: v for k, v in binding.items() if k != "materialization"},
                "builder changed tuple geometry or proof contract")
        rebuilt_payloads = inspect_payloads(working, rebuilt_binding)
        port_receipts = []
        for entry in binding["materialization"]["files"]:
            port = entry["port"]
            old_raw, old_gzip = payloads[port]
            new_raw, new_gzip = rebuilt_payloads[port]
            require(old_raw == new_raw, "regenerated integer mismatch: " + port)
            port_receipts.append(dict(port=port, bits=entry["bits"], raw_bytes=len(old_raw),
                sha256=digest(old_raw), raw_reconstruction="byte-identical",
                original_gzip_sha256=digest(old_gzip),
                rebuilt_gzip_sha256=digest(new_gzip),
                gzip_byte_identical=(old_gzip == new_gzip)))
        independent = run_script(working, "audit_coefficients.py")
        require(independent["status"] == "PASS", "independent tile reconstruction failed")
        require(independent == read_json(original / "INDEPENDENT_AUDIT.json"),
                "independent audit differs from the preserved upstream receipt")
        if args.regenerate is not None:
            args.regenerate.mkdir(parents=True)
            shutil.copytree(working / "coefficients", args.regenerate / "coefficients")
            shutil.copyfile(working / "COEFFICIENT_BINDING.json",
                            args.regenerate / "COEFFICIENT_BINDING.json")
            shutil.copyfile(working / "INDEPENDENT_AUDIT.json",
                            args.regenerate / "INDEPENDENT_AUDIT.json")

    receipt = dict(status="PASS", instance=INSTANCE, retrieval_commit=COMMIT,
        authenticated_source_files=source_count, active_binding_sha256=BINDING_HASH,
        positive_ports_sha256=digest((ROOT / "POSITIVE_PORTS.json").read_bytes()),
        python=platform.python_version(), zlib=zlib.ZLIB_RUNTIME_VERSION,
        assertions_disabled=bool(sys.flags.optimize), standard_library_only=True,
        fixed_numeral_aliases=ALIASES, raw_total_bytes=295388,
        all_original_gzip_bytes_preserved=True, ports=port_receipts,
        independent_audit=independent,
        scope="Exact finite reconstruction and provenance audit; the unbounded equivalence uses the named ordinary mathematical proofs.")
    rendered = json.dumps(receipt, indent=2) + "\n"
    if args.receipt is not None:
        args.receipt.parent.mkdir(parents=True, exist_ok=True)
        args.receipt.write_text(rendered, encoding="utf-8")
    print(rendered, end="")


if __name__ == "__main__":
    main()
