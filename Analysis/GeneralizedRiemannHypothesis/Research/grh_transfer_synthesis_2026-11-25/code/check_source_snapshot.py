#!/usr/bin/env python3
"""Check the selected upstream evidence without building or importing Lean.

Default (offline, Python standard library only):
    python code/check_source_snapshot.py

Also compare the recorded blob IDs with an existing upstream Git checkout:
    python code/check_source_snapshot.py --upstream-repo /path/to/grh-lean

Optionally save the machine-readable result:
    python code/check_source_snapshot.py --output validation/source_snapshot_checks.json

This checks source-byte integrity, Git blob SHA1, declaration anchors, and
coverage of direct upstream source links in the report.  It is not a proof
kernel check, an import-closure check, or a rebuild of the upstream project.
The offline checks use the bundled manifest as their integrity reference;
they do not independently authenticate that manifest.
"""

import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys


PINNED_COMMIT = "72fead102f663d5c7a407964a13dc0cf9d977207"
SOURCE_REPOSITORY = "https://github.com/lsernau/grh-lean"


def git_blob_sha1(data):
    header = b"blob " + str(len(data)).encode("ascii") + b"\0"
    return hashlib.sha1(header + data).hexdigest()


def resolve_bundled_path(package, value):
    relative = PurePosixPath(value)
    if relative.is_absolute() or ".." in relative.parts:
        raise ValueError("Manifest path must remain inside the package: " + value)
    path = (package / Path(*relative.parts)).resolve()
    path.relative_to(package.resolve())
    return path


def direct_source_links(package):
    """Return repository-relative source paths directly linked by LaTeX."""
    found = set()
    documents = sorted((package / "sections").glob("*.tex"))
    if (package / "report.tex").is_file():
        documents.append(package / "report.tex")
    src_pattern = re.compile(r"\\src\{([^{}]+)\}\{([^{}]+)\}")
    url_pattern = re.compile(
        r"https://github\.com/lsernau/grh-lean/(?:blob|raw)/"
        r"[0-9a-f]{40}/([^\s{}#\\]+)"
    )
    for document in documents:
        contents = document.read_text(encoding="utf-8")
        for match in src_pattern.finditer(contents):
            found.add("grh/src/" + match.group(1) + ".lean")
        for match in url_pattern.finditer(contents):
            # The definition of the \src macro contains #1; it is excluded
            # by this expression, while its concrete uses are read above.
            path = match.group(1)
            if path.endswith((".lean", ".md", ".toml", ".json")):
                found.add(path)
    return found


def check(package, manifest_path, upstream_repo=None):
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    errors = []
    if manifest.get("pinned_commit") != PINNED_COMMIT:
        errors.append("Manifest commit differs from the checker pin.")
    if manifest.get("source_repository") != SOURCE_REPOSITORY:
        errors.append("Unexpected upstream repository in manifest.")
    files = manifest.get("files", [])
    if not files:
        errors.append("No files in source manifest.")

    bundled_names = set()
    snapshot_repository_paths = set()
    unique_git_blobs = {}
    anchors_checked = 0
    byte_count = 0

    for entry in files:
        name = entry["bundled_path"]
        if name in bundled_names:
            errors.append("Duplicate bundled path: " + name)
            continue
        bundled_names.add(name)
        try:
            path = resolve_bundled_path(package, name)
            data = path.read_bytes()
        except (OSError, ValueError) as exc:
            errors.append(f"Cannot read {name}: {exc}")
            continue
        byte_count += len(data)
        if len(data) != entry["bytes"]:
            errors.append("Byte length mismatch: " + name)
        if hashlib.sha256(data).hexdigest() != entry["sha256"]:
            errors.append("SHA256 mismatch: " + name)
        if git_blob_sha1(data) != entry["git_blob_sha1"]:
            errors.append("Git blob SHA1 mismatch: " + name)

        repository_path = entry["repository_path"]
        expected_url = f"{SOURCE_REPOSITORY}/blob/{PINNED_COMMIT}/{repository_path}"
        if entry.get("source_url") != expected_url:
            errors.append("Source URL does not match the pin: " + name)
        previous = unique_git_blobs.setdefault(repository_path, entry["git_blob_sha1"])
        if previous != entry["git_blob_sha1"]:
            errors.append("Conflicting copies of upstream path: " + repository_path)
        expected_snapshot_name = "evidence/upstream/" + repository_path
        if name == expected_snapshot_name:
            snapshot_repository_paths.add(repository_path)

        try:
            lines = data.decode("utf-8").splitlines(keepends=True)
        except UnicodeDecodeError:
            if entry.get("declaration_anchors"):
                errors.append("Non-UTF8 file has declaration anchors: " + name)
            continue
        for anchor in entry.get("declaration_anchors", []):
            start, end = anchor["line_start"], anchor["line_end"]
            if not (isinstance(start, int) and isinstance(end, int)
                    and 1 <= start <= end <= len(lines)):
                errors.append("Invalid declaration line range: " + name)
                continue
            text = "".join(lines[start-1:end])
            if text != anchor["utf8_text"]:
                errors.append(f"Declaration text mismatch: {name}: {anchor['label']}")
            if hashlib.sha256(text.encode("utf-8")).hexdigest() != anchor["sha256"]:
                errors.append(f"Declaration hash mismatch: {name}: {anchor['label']}")
            anchors_checked += 1

    actual_snapshot_files = {
        str(path.relative_to(package))
        for path in (package / "evidence" / "upstream").rglob("*")
        if path.is_file()
    }
    expected_snapshot_files = {
        name for name in bundled_names if name.startswith("evidence/upstream/")
    }
    for extra in sorted(actual_snapshot_files - expected_snapshot_files):
        errors.append("Unmanifested upstream snapshot file: " + extra)
    for missing in sorted(expected_snapshot_files - actual_snapshot_files):
        errors.append("Missing upstream snapshot file: " + missing)

    direct_links = direct_source_links(package)
    for missing in sorted(direct_links - snapshot_repository_paths):
        errors.append("Direct report source link has no bundled snapshot: " + missing)

    git_paths_checked = 0
    if upstream_repo is not None:
        try:
            commit = subprocess.check_output(
                ["git", "rev-parse", PINNED_COMMIT + "^{commit}"],
                cwd=upstream_repo, text=True, stderr=subprocess.STDOUT,
            ).strip()
            if commit != PINNED_COMMIT:
                errors.append("Git checkout resolved an unexpected pinned commit.")
            else:
                for repository_path, expected in sorted(unique_git_blobs.items()):
                    actual = subprocess.check_output(
                        ["git", "rev-parse", PINNED_COMMIT + ":" + repository_path],
                        cwd=upstream_repo, text=True, stderr=subprocess.STDOUT,
                    ).strip()
                    if actual != expected:
                        errors.append("Pinned Git blob mismatch: " + repository_path)
                    git_paths_checked += 1
        except (OSError, subprocess.CalledProcessError) as exc:
            errors.append("Could not compare with upstream Git objects: " + str(exc))

    result = {
        "all_checks_passed": not errors,
        "source_repository": SOURCE_REPOSITORY,
        "pinned_commit": PINNED_COMMIT,
        "unique_repository_files": len(snapshot_repository_paths),
        "bundled_files_checked": len(files),
        "bundled_bytes_checked": byte_count,
        "sha256_checks": len(files),
        "git_blob_sha1_checks": len(files),
        "declaration_anchors_checked": anchors_checked,
        "direct_report_source_links_covered": len(direct_links),
        "compared_to_upstream_git": upstream_repo is not None,
        "unique_paths_compared_to_pinned_git_objects": git_paths_checked,
        "lean_rebuild_performed": False,
        "verification_scope": "Selected source-byte integrity and report-link coverage; no Lean proof or import-closure verification.",
        "errors": errors,
    }
    return result


def main():
    package = Path(__file__).resolve().parents[1]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path,
                        default=package / "evidence" / "upstream_manifest.json")
    parser.add_argument("--upstream-repo", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = check(package, args.manifest, args.upstream_repo)
    text = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text, encoding="utf-8")
    print(text, end="")
    return 0 if result["all_checks_passed"] else 1


if __name__ == "__main__":
    sys.exit(main())
