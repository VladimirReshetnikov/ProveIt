#!/usr/bin/env python3
"""Optional pinned-corpus audit; no submitted Python source is executed.

Missing archives are downloaded to the explicitly selected cache directory.
Existing archives must already have the recorded identities. ZIP members are
read as bytes and measured in one temporary file; nothing is extracted.
"""
import argparse
import hashlib
import io
import json
from pathlib import Path, PurePosixPath
import platform
import re
import sys
import tempfile
from urllib.parse import quote
from urllib.request import Request, urlopen
import zipfile

import source_measure


ROOT = Path(__file__).resolve().parents[1]


def read_json(name):
    return json.loads((ROOT / "evidence" / name).read_text(encoding="utf-8"))


def immutable_urls(repository, commit, path):
    encoded = quote(path, safe="/")
    return {
        "immutable_download_url":
            f"https://raw.githubusercontent.com/{repository}/{commit}/{encoded}",
        "immutable_html_url":
            f"https://github.com/{repository}/blob/{commit}/{encoded}",
    }


def validate_manifest(manifest, checksums):
    repository = manifest["repository"]
    commit = manifest["commit"]
    if not re.fullmatch(r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+", repository):
        raise ValueError("Unsupported repository name in source manifest")
    if not re.fullmatch(r"[0-9a-f]{40}", commit):
        raise ValueError("Source manifest must pin a full 40-character commit")
    entries = manifest["entries"]
    names = [entry["name"] for entry in entries]
    if len(set(names)) != len(names):
        raise ValueError("Duplicate archive names in source manifest")
    by_name = {row["name"]: row for row in checksums}
    if len(by_name) != len(checksums) or set(by_name) != set(names):
        raise ValueError("Archive checksum inventory disagrees with manifest")
    for entry in entries:
        name, path = entry["name"], entry["path"]
        parsed = PurePosixPath(path)
        if (Path(name).name != name or "\\" in name or
                not name.endswith(".zip") or parsed.is_absolute() or
                ".." in parsed.parts or "\\" in path or parsed.name != name):
            raise ValueError(f"Noncanonical archive path: {name!r}")
        if type(entry["size"]) is not int or entry["size"] < 0:
            raise ValueError(f"Invalid recorded size: {name}")
        if not re.fullmatch(r"[0-9a-f]{40}", entry["sha"]):
            raise ValueError(f"Invalid Git blob identity: {name}")
        checksum = by_name[name]
        if (checksum["bytes"] != entry["size"] or
                not re.fullmatch(r"[0-9a-f]{64}", checksum["sha256"])):
            raise ValueError(f"Invalid archive checksum entry: {name}")
        urls = immutable_urls(repository, commit, path)
        for field, value in urls.items():
            if entry.get(field) != value:
                raise ValueError(f"Missing or inconsistent {field}: {name}")
    return by_name


def verify_archive_bytes(data, entry, checksum):
    length = len(data)
    blob_sha = hashlib.sha1(
        b"blob " + str(length).encode("ascii") + b"\0" + data
    ).hexdigest()
    sha256 = hashlib.sha256(data).hexdigest()
    if length != entry["size"] or length != checksum["bytes"]:
        raise ValueError(f"Archive byte length mismatch: {entry['name']}")
    if blob_sha != entry["sha"]:
        raise ValueError(f"Archive Git blob SHA-1 mismatch: {entry['name']}")
    if sha256 != checksum["sha256"]:
        raise ValueError(f"Archive SHA-256 mismatch: {entry['name']}")
    return {
        "name": entry["name"], "bytes": length,
        "git_blob_sha1": blob_sha, "sha256": sha256,
        "immutable_download_url": entry["immutable_download_url"],
    }


def obtain_archive(entry, checksum, archive_dir, offline):
    destination = archive_dir / entry["name"]
    if destination.exists():
        data = destination.read_bytes()
        return data, verify_archive_bytes(data, entry, checksum), "reused"
    if offline:
        raise FileNotFoundError(f"Missing cached archive in offline mode: {destination}")
    request = Request(
        entry["immutable_download_url"],
        headers={"User-Agent": "ProveIt-pinned-source-audit/1"},
    )
    with urlopen(request, timeout=45) as response:
        # The immutable record supplies the exact expected length.
        data = response.read(entry["size"] + 1)
    identity = verify_archive_bytes(data, entry, checksum)
    # Never replace an existing invalid cache item, including a concurrent one.
    if destination.exists():
        existing = destination.read_bytes()
        return existing, verify_archive_bytes(existing, entry, checksum), "reused"
    temporary = None
    try:
        with tempfile.NamedTemporaryFile(
                prefix=".audit-download-", dir=archive_dir, delete=False) as stream:
            temporary = Path(stream.name)
            stream.write(data)
        temporary.replace(destination)
    finally:
        if temporary is not None and temporary.exists():
            temporary.unlink()
    return data, identity, "downloaded"


def measure_members(archives):
    rows = []
    seen = set()
    with tempfile.TemporaryDirectory(prefix="ipra-source-measure-") as directory:
        payload_path = Path(directory) / "member.py"
        for entry, data in archives:
            archive_stem = entry["name"][:-4]
            with zipfile.ZipFile(io.BytesIO(data)) as archive:
                for member in archive.infolist():
                    if member.is_dir() or not member.filename.endswith(".py"):
                        continue
                    # Member names only label evidence. They never become paths
                    # on the local filesystem, so no ZIP extraction occurs.
                    label = archive_stem + "/" + member.filename
                    if label in seen:
                        raise ValueError(f"Duplicate Python-member label: {label}")
                    seen.add(label)
                    payload = archive.read(member)  # Also checks the ZIP CRC.
                    payload_path.write_bytes(payload)
                    rows.append({"path": label, **source_measure.metrics(payload_path)})
    return sorted(rows, key=lambda row: row["path"])


def compare_inventory(actual, expected):
    expected_map = {row["path"]: row for row in expected}
    actual_map = {row["path"]: row for row in actual}
    if len(expected_map) != len(expected):
        raise ValueError("Duplicate paths in recorded Python-member inventory")
    missing = sorted(expected_map.keys() - actual_map.keys())
    extra = sorted(actual_map.keys() - expected_map.keys())
    differences = []
    for path in sorted(expected_map.keys() & actual_map.keys()):
        old, new = expected_map[path], actual_map[path]
        if old != new:
            fields = {
                key: {"expected": old.get(key), "actual": new.get(key)}
                for key in sorted(old.keys() | new.keys())
                if old.get(key) != new.get(key)
            }
            differences.append({"path": path, "fields": fields})
    return {
        "expected_occurrences": len(expected),
        "actual_occurrences": len(actual),
        "expected_unique_sha256": len({row["sha256"] for row in expected}),
        "actual_unique_sha256": len({row["sha256"] for row in actual}),
        "missing_paths": missing,
        "extra_paths": extra,
        "metric_or_content_differences": differences,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--archives", required=True, type=Path,
        help="Explicit directory containing the eleven pinned ZIPs; missing ZIPs are fetched here",
    )
    parser.add_argument(
        "--offline", action="store_true",
        help="Require every archive to be cached; make no network request",
    )
    parser.add_argument(
        "--output", type=Path,
        help="Optional JSON receipt path; the recorded corpus evidence is not overwritten",
    )
    args = parser.parse_args()
    manifest = read_json("sources_manifest.json")
    checksums = validate_manifest(manifest, read_json("source_checksums.json"))
    expected = read_json("all_draft_python_metrics.json")
    archive_dir = args.archives.expanduser().resolve()
    archive_dir.mkdir(parents=True, exist_ok=True)
    archives, identities = [], []
    transfers = {"reused": 0, "downloaded": 0}
    for entry in manifest["entries"]:
        data, identity, mode = obtain_archive(
            entry, checksums[entry["name"]], archive_dir, args.offline
        )
        archives.append((entry, data))
        identities.append(identity)
        transfers[mode] += 1
    actual = measure_members(archives)
    comparison = compare_inventory(actual, expected)
    passed = not (
        comparison["missing_paths"] or comparison["extra_paths"] or
        comparison["metric_or_content_differences"]
    )
    report = {
        "status": "passed" if passed else "failed",
        "repository": manifest["repository"],
        "commit": manifest["commit"],
        "python": platform.python_version(),
        "implementation": platform.python_implementation(),
        "normalizer_sha256":
            hashlib.sha256(Path(source_measure.__file__).read_bytes()).hexdigest(),
        "archive_count": len(archives),
        "transfers": transfers,
        "archive_identities": identities,
        "comparison": comparison,
        "scope": (
            "Every direct Python ZIP member is measured; no archive member is "
            "extracted, imported, or executed. Content inventory reproduction "
            "does not itself classify every member as a complete proof checker."
        ),
    }
    if args.output is not None:
        output = args.output.expanduser().resolve()
        protected = {
            (ROOT / "evidence" / name).resolve()
            for name in (
                "sources_manifest.json", "source_checksums.json",
                "all_draft_python_metrics.json",
            )
        }
        if output in protected:
            raise ValueError("Refusing to overwrite recorded corpus evidence")
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    summary = {
        key: report[key] for key in (
            "status", "repository", "commit", "python", "implementation",
            "normalizer_sha256", "archive_count", "transfers",
        )
    }
    summary.update({
        key: comparison[key] for key in (
            "expected_occurrences", "actual_occurrences",
            "expected_unique_sha256", "actual_unique_sha256",
        )
    })
    summary["missing_paths"] = comparison["missing_paths"]
    summary["extra_paths"] = comparison["extra_paths"]
    summary["difference_count"] = len(comparison["metric_or_content_differences"])
    summary["first_differences"] = comparison["metric_or_content_differences"][:10]
    print(json.dumps(summary, indent=2))
    if not passed:
        print(
            "Source inventory differs. Exact normalized metrics were recorded "
            "with CPython 3.12.14; ast.unparse output can vary by Python version.",
            file=sys.stderr,
        )
    return 0 if passed else 1


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, ValueError, KeyError, zipfile.BadZipFile) as error:
        print(f"Source audit failed: {error}", file=sys.stderr)
        raise SystemExit(1)
