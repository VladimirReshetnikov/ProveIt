#!/usr/bin/env python3
"""Recompute the pinned PA/incoming literal-table census from a Git checkout.

Scope: direct PA .tm files; .tm/.txt/.csv/.tsv members of every PA or incoming
ZIP, recursively, scanning each distinct archive body once. No JSON or code
embedded encodings are decoded. This is not a behavioral correctness checker.
The frozen full-corpus census was run before the environment reset; this
portable restoration requires a checkout containing the pinned Git objects.
"""
from pathlib import Path
import argparse
import hashlib
import io
import json
import subprocess
import zipfile
from machine_classes import classify, parse
from finalize_census import finalize

PIN = "5784600f8709872fa258af66a94df8deb7075c2f"
PA_ROOT = "Computability/BusyBeaver/Research/PA/"


def maximum_reachable(data, info):
    """Correctly handle dense comparison tables whose implicit start0 is wrong."""
    if info["start"] is None or info["reachable"] == info["states"]:
        return info["reachable"]
    rows, states, _ = parse(data)
    maximum = info["reachable"]
    for root in states:
        seen, order = {root}, [root]
        for q in order:
            for bit in (0, 1):
                target = rows[q, bit][2]
                if target in states and target not in seen:
                    seen.add(target)
                    order.append(target)
        maximum = max(maximum, len(seen))
        if maximum == len(states):
            break
    return maximum


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True,
                        help="Fresh directory for the complete recomputed census")
    args = parser.parse_args()
    repo, output = args.repo.resolve(), args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    paths = subprocess.check_output([
        "git", "ls-tree", "-rz", "--name-only", PIN, "--", PA_ROOT, "docs/incoming"
    ], cwd=repo).decode().split("\0")
    paths = [path for path in paths if path.endswith((".tm", ".zip"))]
    process = subprocess.Popen(["git", "cat-file", "--batch"], cwd=repo,
                               stdin=subprocess.PIPE, stdout=subprocess.PIPE)

    def git_bytes(path):
        process.stdin.write((PIN + ":" + path + "\n").encode())
        process.stdin.flush()
        header = process.stdout.readline().decode().strip().split()
        if len(header) != 3 or header[1] != "blob":
            raise ValueError("Cannot read pinned blob: " + path)
        size = int(header[2])
        data = process.stdout.read(size)
        if len(data) != size or process.stdout.read(1) != b"\n":
            raise ValueError("Incomplete git-cat-file response")
        return data

    occurrences, malformed, cache, archives, seen_archives = [], [], {}, [], {}

    def table(path, data, origin):
        digest = hashlib.sha256(data).hexdigest()
        if digest not in cache:
            try:
                info = classify(data)
                info["max_reachable"] = maximum_reachable(data, info)
                cache[digest] = info
            except (ValueError, UnicodeError, KeyError):
                cache[digest] = None
        info = cache[digest]
        if info is None:
            if path.endswith(".tm"):
                malformed.append(dict(path=path, origin=origin,
                                      reason="Not a complete numeric five-column binary table"))
            return
        record = dict(info)
        record["roots"] = sorted(record["roots"])
        record.update(path=path, origin=origin, sha256=digest)
        occurrences.append(record)

    def archive(path, data, origin, depth=0):
        digest = hashlib.sha256(data).hexdigest()
        if digest in seen_archives:
            archives.append(dict(path=path, origin=origin, sha256=digest,
                                 duplicate_of=seen_archives[digest]))
            return
        seen_archives[digest] = path
        with zipfile.ZipFile(io.BytesIO(data)) as handle:
            archives.append(dict(path=path, origin=origin, sha256=digest,
                                 members=len(handle.infolist()), depth=depth))
            for member in handle.infolist():
                if member.is_dir():
                    continue
                name = member.filename
                if name.lower().endswith(".zip"):
                    archive(path + "!" + name, handle.read(member), origin, depth + 1)
                elif name.lower().endswith((".tm", ".txt", ".csv", ".tsv")):
                    table(path + "!" + name, handle.read(member), origin)

    try:
        for path in paths:
            data = git_bytes(path)
            if path.endswith(".zip"):
                origin = "incoming" if path.startswith("docs/incoming") else "PA_nested_archive"
                archive(path, data, origin)
            else:
                table(path, data, "PA_direct")
    finally:
        process.stdin.close()
        process.wait()
    (output / "table_occurrences.json").write_text(json.dumps(occurrences, indent=2) + "\n")
    (output / "archive_manifest.json").write_text(json.dumps(archives, indent=2) + "\n")
    (output / "unparsed_tm.json").write_text(json.dumps(malformed, indent=2) + "\n")
    print(json.dumps(dict(table_occurrences=len(occurrences),
        parsed_table_byte_forms=len({record["sha256"] for record in occurrences}),
        candidate_payload_byte_forms=len(cache), unique_archive_bodies=len(seen_archives),
        unparsed_tm=len(malformed)), indent=2))
    summary = finalize(output)
    print(json.dumps({key: value for key, value in summary.items()
                      if key != "diagnostic_classes_excluded"}, indent=2))


if __name__ == "__main__":
    main()
