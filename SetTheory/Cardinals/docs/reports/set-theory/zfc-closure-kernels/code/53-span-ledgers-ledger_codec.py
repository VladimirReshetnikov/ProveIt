#!/usr/bin/env python3
"""Losslessly pack, reconstruct, and verify the search's deterministic DFS ledgers.

Examples:
  python ledger_codec.py pack raw.ledger.tsv packed.ledger.gz --choices 251
  python ledger_codec.py verify packed.ledger.gz
  python ledger_codec.py unpack packed.ledger.gz restored.ledger.tsv

Pack always reconstructs the complete byte stream into SHA256 before publishing
the archive. The verification path does not write the reconstructed multi-GB TSV.
Only a C++17 compiler, zlib, OpenSSL, and the Python standard library are needed.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        while block := f.read(8 << 20):
            h.update(block)
    return h.hexdigest()


def helper() -> Path:
    source = Path(__file__).with_suffix(".cpp").resolve()
    compiler = os.environ.get("CXX", "c++")
    flags = ["-O3", "-std=c++17", "-lz", "-lcrypto"]
    key = hashlib.sha256(source.read_bytes() + json.dumps([compiler, flags]).encode()).hexdigest()[:24]
    target = Path(tempfile.gettempdir()) / ("proveit-ledger-codec-" + key)
    if not target.exists():
        fd, tmp = tempfile.mkstemp(prefix=target.name + "-", dir=target.parent)
        os.close(fd)
        try:
            subprocess.run([compiler, flags[0], flags[1], str(source), *flags[2:], "-o", tmp], check=True)
            os.chmod(tmp, 0o700)
            os.replace(tmp, target)
        finally:
            Path(tmp).unlink(missing_ok=True)
    return target


def run(executable: Path, *args: object) -> dict:
    p = subprocess.run([str(executable), *(str(a) for a in args)], check=True, text=True, stdout=subprocess.PIPE)
    return json.loads(p.stdout)


def temporary_output(output: Path, force: bool) -> Path:
    if output.exists() and not force:
        raise FileExistsError(f"Output exists (use --force): {output}")
    output.parent.mkdir(parents=True, exist_ok=True)
    fd, name = tempfile.mkstemp(prefix=output.name + ".", suffix=".tmp", dir=output.parent)
    os.close(fd)
    return Path(name)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    subs = parser.add_subparsers(dest="command", required=True)
    pack = subs.add_parser("pack", help="Pack and verify every original byte before publishing the archive")
    pack.add_argument("raw", type=Path)
    pack.add_argument("packed", type=Path)
    pack.add_argument("--choices", type=int, required=True)
    pack.add_argument("--force", action="store_true")
    unpack = subs.add_parser("unpack", help="Restore the exact original TSV and verify its stored SHA256")
    unpack.add_argument("packed", type=Path)
    unpack.add_argument("raw", type=Path)
    unpack.add_argument("--force", action="store_true")
    verify = subs.add_parser("verify", help="Reconstruct and hash all TSV bytes, without writing the TSV")
    verify.add_argument("packed", type=Path)
    verify.add_argument("--raw", type=Path, help="Also independently hash this original TSV and compare")
    args = parser.parse_args()
    executable = helper()
    started = time.monotonic()

    if args.command == "pack":
        raw, packed = args.raw.resolve(), args.packed.resolve()
        if raw == packed:
            raise ValueError("Raw and packed paths must differ")
        metadata_path = packed.with_name(packed.name + ".json")
        if metadata_path.exists() and not args.force:
            raise FileExistsError(f"Metadata output exists (use --force): {metadata_path}")
        original = raw.stat()
        tmp = temporary_output(packed, args.force)
        try:
            metadata = run(executable, "pack", raw, tmp, args.choices)
            verification = run(executable, "verify", tmp)
            current = raw.stat()
            if (current.st_size, current.st_mtime_ns) != (original.st_size, original.st_mtime_ns):
                raise ValueError("Raw ledger changed while packing")
            # This independent implementation also checks the helper's source digest.
            raw_digest = sha256(raw)
            if raw_digest != metadata["raw_sha256"] or verification["raw_sha256"] != raw_digest:
                raise ValueError("Independent original/reconstructed SHA256 comparison failed")
            metadata.update({
                "raw_name": raw.name,
                "packed_name": packed.name,
                "packed_bytes": tmp.stat().st_size,
                "packed_sha256": sha256(tmp),
                "codec_cpp_sha256": sha256(Path(__file__).with_suffix(".cpp")),
                "codec_python_sha256": sha256(Path(__file__)),
                "verification": verification,
                "independent_python_raw_sha256": raw_digest,
                "seconds": round(time.monotonic() - started, 6),
            })
            os.replace(tmp, packed)
            metadata_path.write_text(json.dumps(metadata, indent=2) + "\n")
        finally:
            tmp.unlink(missing_ok=True)
        print(json.dumps(metadata))
    elif args.command == "unpack":
        if args.packed.resolve() == args.raw.resolve():
            raise ValueError("Packed and raw paths must differ")
        tmp = temporary_output(args.raw, args.force)
        try:
            result = run(executable, "unpack", args.packed, tmp)
            os.replace(tmp, args.raw)
        finally:
            tmp.unlink(missing_ok=True)
        print(json.dumps(result))
    else:
        result = run(executable, "verify", args.packed)
        result["packed_bytes"] = args.packed.stat().st_size
        result["packed_sha256"] = sha256(args.packed)
        if args.raw:
            digest = sha256(args.raw)
            if digest != result["raw_sha256"] or args.raw.stat().st_size != result["raw_bytes"]:
                raise ValueError("Original TSV does not match reconstructed bytes")
            result["independent_python_raw_sha256"] = digest
        print(json.dumps(result))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, ValueError, subprocess.CalledProcessError) as exc:
        print(f"ledger_codec: {exc}", file=sys.stderr)
        raise SystemExit(1)
