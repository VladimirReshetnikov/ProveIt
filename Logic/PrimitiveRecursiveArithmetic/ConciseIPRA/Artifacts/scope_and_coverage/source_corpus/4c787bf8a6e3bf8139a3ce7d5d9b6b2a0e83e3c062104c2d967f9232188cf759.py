"""Reproduce the pinned ZIP corpus audit without executing corpus Python code.

Usage:
    python3 audit_corpus.py /path/to/ProveIt/docs/drafts

Archive identities and per-content measurements are compared with the
included evidence. ZIP members are read as bytes; only the trusted bundled
source_measure.py is imported. Temporary files supply its path-based API.
No checkout, archive, or evidence file is changed.
"""
import argparse
from collections import Counter
import hashlib
import importlib.util
import json
from pathlib import Path, PurePosixPath
import platform
import sys
import tempfile
from zipfile import ZipFile


ROOT = Path(__file__).resolve().parent
METRICS = ("source_tokens", "normalized_tokens", "ast_nodes",
           "normalized_bytes", "raw_bytes", "sha256")


class AuditMismatch(Exception):
    pass


def require(condition, message):
    if not condition:
        raise AuditMismatch(message)


def compare_value(label, actual, expected):
    require(actual == expected,
            f"{label}: expected {expected!r}, observed {actual!r}")


def compare_members(label, actual, expected):
    missing = list((expected - actual).elements())
    extra = list((actual - expected).elements())
    require(not missing and not extra,
            f"{label}: missing {len(missing)} {missing[:5]!r}; "
            f"extra {len(extra)} {extra[:5]!r}")


def member_identity(recorded_path):
    """Map an old extraction path to an archive/member pair, relocatably."""
    parts = PurePosixPath(recorded_path).parts
    require("drafts_unpacked" in parts,
            f"Unrecognized recorded source path: {recorded_path!r}")
    index = parts.index("drafts_unpacked") + 1
    require(len(parts) > index + 1,
            f"Incomplete recorded source path: {recorded_path!r}")
    return parts[index] + ".zip", "/".join(parts[index + 1:])


def expected_error(row):
    """No current rows have errors; explicit future error rows are supported.

    A parse_error/error record may be a {type,message} object or the
    equivalent 'Type: message' string. No error is silently skipped.
    """
    value = row.get("parse_error", row.get("error"))
    if value is None:
        return None
    if isinstance(value, dict):
        require(set(value) == {"type", "message"},
                f"Unsupported parse-error record for {row.get('sha256')}: {value!r}")
        return f"{value['type']}: {value['message']}"
    require(isinstance(value, str),
            f"Unsupported parse-error record for {row.get('sha256')}: {value!r}")
    return value


def audit(directory):
    archives = json.loads((ROOT / "evidence/archive_verification.json").read_text())
    expected_rows = json.loads((ROOT / "evidence/all_python_metrics.json").read_text())
    require(isinstance(archives, list) and isinstance(expected_rows, list),
            "Expected archive and per-content evidence arrays")
    require(directory.is_dir(), f"Not a drafts directory: {directory}")

    archive_names = [row["archive"] for row in archives]
    require(len(archive_names) == len(set(archive_names)),
            "Duplicate archive names in pinned evidence")
    compare_members("Top-level ZIP archives",
                    Counter(p.name for p in directory.glob("*.zip") if p.is_file()),
                    Counter(archive_names))

    expected = {}
    all_expected_members = Counter()
    for row in expected_rows:
        digest = row["sha256"]
        require(digest not in expected, f"Duplicate content row in evidence: {digest}")
        members = Counter(member_identity(path) for path in row["paths"])
        require(all(archive in archive_names for archive, _ in members),
                f"Unknown archive referenced by content row {digest}")
        expected[digest] = row, members
        all_expected_members.update(members)

    actual = {}
    all_actual_members = Counter()
    for row in archives:
        name = row["archive"]
        require(PurePosixPath(name).name == name,
                f"Archive evidence must use a basename: {name!r}")
        path = directory / name
        raw = path.read_bytes()
        observed = {
            "bytes": len(raw),
            "git_blob_sha1": hashlib.sha1(
                b"blob " + str(len(raw)).encode("ascii") + b"\0" + raw).hexdigest(),
            "sha256": hashlib.sha256(raw).hexdigest(),
        }
        for field, value in observed.items():
            compare_value(f"Archive {name} {field}", value, row[field])
        with ZipFile(path) as archive:
            for item in archive.infolist():
                if item.is_dir() or not item.filename.endswith(".py"):
                    continue
                data = archive.read(item)
                digest = hashlib.sha256(data).hexdigest()
                member = name, item.filename
                all_actual_members[member] += 1
                if digest not in actual:
                    actual[digest] = data, Counter()
                else:
                    require(actual[digest][0] == data,
                            f"SHA-256 collision among Python members: {digest}")
                actual[digest][1][member] += 1

    compare_value("Python member occurrence count", sum(all_actual_members.values()),
                  sum(all_expected_members.values()))
    compare_members("Python member identities", all_actual_members, all_expected_members)
    compare_value("Distinct Python content count", len(actual), len(expected))
    compare_members("Distinct Python content hashes", Counter(actual.keys()),
                    Counter(expected.keys()))
    for digest, (_, members) in actual.items():
        compare_members(f"Occurrences of content {digest}", members, expected[digest][1])

    # This imports only the audited helper distributed with this report.
    # No source taken from a ZIP member is imported, evaluated, or executed.
    spec = importlib.util.spec_from_file_location(
        "bundled_source_measure", ROOT / "reference/source_measure.py")
    require(spec is not None and spec.loader is not None,
            "Cannot load bundled source measurement helper")
    measure = importlib.util.module_from_spec(spec)
    bytecode_setting = sys.dont_write_bytecode
    sys.dont_write_bytecode = True
    try:
        spec.loader.exec_module(measure)
    finally:
        sys.dont_write_bytecode = bytecode_setting

    parse_errors = 0
    with tempfile.TemporaryDirectory(prefix="ipra-corpus-audit-") as temporary:
        for digest, (data, _) in sorted(actual.items()):
            row, members = expected[digest]
            origin = next(iter(members))
            path = Path(temporary) / (digest + ".py")
            path.write_bytes(data)
            error = None
            measured = None
            try:
                measured = measure.metrics(path)
            except Exception as exc:
                error = f"{type(exc).__name__}: {exc}"
            saved_error = expected_error(row)
            if error is not None or saved_error is not None:
                compare_value(f"Parse error for {digest} ({origin!r})", error, saved_error)
                parse_errors += 1
                if "raw_bytes" in row:
                    compare_value(f"Raw bytes of parse-error content {digest}",
                                  len(data), row["raw_bytes"])
                continue
            for field in METRICS:
                require(field in row,
                        f"Missing expected metric {field} for content {digest}")
                compare_value(f"Content {digest} ({origin!r}) metric {field}",
                              measured[field], row[field])

    return {
        "status": "PASS",
        "archives": len(archives),
        "python_member_occurrences": sum(all_actual_members.values()),
        "distinct_python_sources": len(actual),
        "parse_error_records": parse_errors,
        "measurement_python": platform.python_version(),
        "archive_checks": ["bytes", "git_blob_sha1", "sha256"],
        "metric_fields": list(METRICS),
        "corpus_code_executed": False,
        "evidence_modified": False,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("drafts_directory", type=Path,
                        help="A checkout's docs/drafts directory at the pinned snapshot")
    args = parser.parse_args()
    try:
        result = audit(args.drafts_directory.resolve())
    except Exception as exc:
        print(f"FAIL: {type(exc).__name__}: {exc}", file=sys.stderr)
        return 1
    print(json.dumps(result, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
