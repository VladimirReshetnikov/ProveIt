#!/usr/bin/env python3
"""Audit explicit binary, two-direction, five-column TM tables.

Reads the two requested repository trees, including recursively nested ZIPs.
Never executes repository code. For a table with a vertex reaching every
control, the unrooted hash is an exact invariant under control renaming.
The audit preserves start conventions separately: an unrooted match alone
is not a proof of equivalence from the blank initial configuration.
"""
from __future__ import annotations
import argparse, collections, csv, hashlib, io, json, pathlib, re, subprocess, zipfile

PA = "Computability/BusyBeaver/Research/PA"
ROOTS = [PA, "docs/incoming"]
DIRECT_SUFFIXES = {".tm", ".zip"}


def parse(data):
    rows = {}
    declared = None
    for line in data.decode("utf-8-sig").splitlines():
        line = line.strip()
        if not line:
            continue
        if line.startswith("#"):
            m = re.search(r"\bstart(?:\s+state)?\s*(?:[=:]\s*)?(\d+)\b", line, re.I)
            if m:
                value = int(m.group(1))
                if declared is not None and declared != value:
                    raise ValueError("conflicting declared starts")
                declared = value
            continue
        fields = line.split()
        if len(fields) != 5:
            raise ValueError("not a five-column row: " + line[:90])
        q, b, w, d, nxt = fields
        q, b, w, nxt = map(int, (q, b, w, nxt))
        if b not in (0, 1) or w not in (0, 1) or d not in ("L", "R"):
            raise ValueError("invalid symbol/direction")
        if (q, b) in rows:
            raise ValueError("duplicate transition")
        rows[q, b] = (w, d, nxt)
    controls = {q for q, b in rows}
    if not controls or len(rows) != len(controls) * 2:
        raise ValueError("missing transition(s)")
    if declared is not None and declared not in controls:
        raise ValueError("declared start not a working control")
    return rows, controls, declared


def rooted(rows, controls, start, mirror=False):
    index = {start: 0}
    queue = [start]
    serial = []
    for q in queue:
        for bit in (0, 1):
            w, d, nxt = rows[q, bit]
            if mirror:
                d = "L" if d == "R" else "R"
            if nxt in controls:
                if nxt not in index:
                    index[nxt] = len(queue)
                    queue.append(nxt)
                target = index[nxt]
            else:
                target = -1
            serial.append((w, d, target))
    digest = hashlib.sha256(json.dumps(serial, separators=(",", ":")).encode()).hexdigest()
    return digest, len(queue)


def classify(data):
    rows, controls, declared = parse(data)
    by_root = {q: rooted(rows, controls, q) for q in controls}
    maximum = max(n for h, n in by_root.values())
    unrooted = min(h for h, n in by_root.values() if n == maximum)
    full = maximum == len(controls)
    conventional = 0 if controls == set(range(len(controls))) else None
    start = declared if declared is not None else conventional
    out = {
        "states": len(controls),
        "transitions": len(rows),
        "halting_labels": sorted({n for w, d, n in rows.values()} - controls),
        "declared_start": declared,
        "conventional_dense_start": conventional,
        "rooted_hash": by_root[start][0] if start is not None else None,
        "reachable_from_start": by_root[start][1] if start is not None else None,
        "unrooted_hash": unrooted,
        "maximum_reachable": maximum,
        "unrooted_hash_is_complete_invariant": full,
        "possible_root_hashes": {str(q): h for q, (h, n) in by_root.items() if n == maximum},
    }
    return out


def scan(repo, out, git_commit=None):
    out.mkdir(parents=True, exist_ok=True)
    tables_dir = out / "representative_tables"
    tables_dir.mkdir(exist_ok=True)
    occurrences, archives, errors = [], [], []
    stats = collections.Counter()
    cache = {}
    candidate_suffixes = {".tm", ".txt", ".table", ".bb"}

    def item(name, data, depth=0):
        stats["files_or_archive_members_examined"] += 1
        lower = name.lower()
        if lower.endswith(".zip"):
            if depth > 12:
                errors.append({"path": name, "error": "archive nesting beyond 12"})
                return
            try:
                with zipfile.ZipFile(io.BytesIO(data)) as z:
                    members = [m for m in z.infolist() if not m.is_dir()]
                    archives.append({"path": name, "sha256": hashlib.sha256(data).hexdigest(), "members": len(members)})
                    for m in members:
                        if m.file_size > 200_000_000:
                            errors.append({"path": name + "!" + m.filename, "error": "member exceeds 200 MB; not read"})
                            continue
                        # Only table-like members and nested archives need bytes.
                        suffix = pathlib.PurePosixPath(m.filename).suffix.lower()
                        if suffix in candidate_suffixes or suffix == ".zip":
                            item(name + "!" + m.filename, z.read(m), depth + 1)
                        else:
                            stats["other_archive_members"] += 1
            except Exception as e:
                errors.append({"path": name, "error": "ZIP: " + str(e)})
            return
        suffix = pathlib.PurePosixPath(name).suffix.lower()
        if suffix not in candidate_suffixes:
            return
        stats["table_like_files"] += 1
        if suffix != ".tm":
            meaningful = [s for s in data.splitlines() if s.strip() and not s.lstrip().startswith(b"#")]
            if len(meaningful) < 20 or not all(re.fullmatch(rb"\s*\d+\s+[01]\s+[01]\s+[LR]\s+\d+\s*", line) for line in meaningful[:20]):
                return
        digest = hashlib.sha256(data).hexdigest()
        try:
            if digest not in cache:
                cache[digest] = classify(data)
                # A byte representative is needed for independently repeatable checks.
                (tables_dir / (digest + ".tm")).write_bytes(data)
            occurrences.append({"path": name, "sha256": digest})
        except Exception as e:
            errors.append({"path": name, "error": "table: " + str(e)})

    if git_commit:
        entries = subprocess.check_output(["git", "-C", str(repo), "ls-tree", "-r", "-z", git_commit, "--", *ROOTS]).split(b"\0")
        cat = subprocess.Popen(["git", "-C", str(repo), "cat-file", "--batch"], stdin=subprocess.PIPE, stdout=subprocess.PIPE)
        for entry in entries:
            if not entry:
                continue
            metadata, name = entry.split(b"\t", 1)
            mode, kind, oid = metadata.split()
            name = name.decode("utf-8")
            stats["filesystem_files"] += 1
            if pathlib.PurePosixPath(name).suffix.lower() not in DIRECT_SUFFIXES:
                continue
            cat.stdin.write(oid + b"\n")
            cat.stdin.flush()
            header = cat.stdout.readline().split()
            if len(header) != 3:
                raise RuntimeError("cat-file failed for " + name + ": " + repr(header))
            size = int(header[2])
            data = cat.stdout.read(size)
            assert cat.stdout.read(1) == b"\n"
            item(name, data)
        cat.stdin.close()
        cat.wait()
    else:
        for root in ROOTS:
            for path in sorted((repo / root).rglob("*")):
                if not path.is_file():
                    continue
                stats["filesystem_files"] += 1
                if path.suffix.lower() in DIRECT_SUFFIXES:
                    item(str(path.relative_to(repo)), path.read_bytes())

    classes = {}
    for occurrence in occurrences:
        info = cache[occurrence["sha256"]]
        # Full-state rooted graph hashes are exact. Exceptional disconnected
        # controls remain explicitly flagged rather than silently certified.
        key = str(info["states"]) + ":" + info["unrooted_hash"]
        if key not in classes:
            classes[key] = {
                "states": info["states"], "unrooted_hash": info["unrooted_hash"],
                "maximum_reachable": info["maximum_reachable"],
                "exact": info["unrooted_hash_is_complete_invariant"],
                "members": [], "content_hashes": [], "rooted_hashes": []}
        c = classes[key]
        c["members"].append(occurrence["path"])
        c["content_hashes"].append(occurrence["sha256"])
        if info["rooted_hash"]:
            c["rooted_hashes"].append(info["rooted_hash"])
    for c in classes.values():
        c["content_hashes"] = sorted(set(c["content_hashes"]))
        c["rooted_hashes"] = sorted(set(c["rooted_hashes"]))
        # Prefer a descriptive first proposal over copied census members.
        c["representative"] = min(c["members"], key=lambda p: (sum(t in p.lower() for t in ("reference", "census", "input", "archive", "comparison", "rejected", "search/")), "!" in p, len(p), p))
    class_list = sorted(classes.values(), key=lambda x: (x["states"], x["unrooted_hash"]))
    states_summary = dict(sorted(collections.Counter(x["states"] for x in class_list).items()))
    summary = {
        "scope": ROOTS, "git_commit": git_commit, "stats": dict(stats),
        "table_occurrences": len(occurrences), "distinct_table_bytes": len(cache),
        "unrooted_classes": len(class_list), "classes_by_state_count": states_summary,
        "archives": len(archives), "parse_errors": len(errors),
        "incomplete_unrooted_invariants": sum(not c["exact"] for c in class_list),
        "qualification": "Counts classify explicit five-column TM tables. They include rejected experiments and parent machines; a class count is not a count of valid consistency machines. Dense 0 starts are recorded as a convention, not inferred fact."
    }
    for filename, obj in (("summary.json", summary), ("table_occurrences.json", occurrences), ("table_contents.json", cache), ("classes.json", class_list), ("archives.json", archives), ("parse_errors.json", errors)):
        (out / filename).write_text(json.dumps(obj, indent=2) + "\n")
    with (out / "classes.tsv").open("w") as f:
        writer = csv.writer(f, delimiter="\t")
        writer.writerow(["states", "unrooted_hash", "maximum_reachable", "exact", "files", "distinct_bytes", "representative"])
        for c in class_list:
            writer.writerow([c["states"], c["unrooted_hash"], c["maximum_reachable"], c["exact"], len(c["members"]), len(c["content_hashes"]), c["representative"]])
    print(json.dumps(summary, indent=2), flush=True)


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", type=pathlib.Path, required=True)
    ap.add_argument("--out", type=pathlib.Path, required=True)
    ap.add_argument("--git-commit")
    args = ap.parse_args()
    scan(args.repo, args.out, args.git_commit)
