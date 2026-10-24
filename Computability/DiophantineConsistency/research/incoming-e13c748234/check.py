#!/usr/bin/env python3
"""Replay the intake from inert ZIP/JSON/gzip bytes; execute no incoming code.

Default use checks the closed packet seal and both retained deterministic
receipts. --output writes the current receipt outside this packet. The explicit
--write-reports-and-seal maintenance command invokes only this checker in normal
and optimized Python, writes their receipts, and seals the six-file packet.

The inventory's historical comparison is preserved. Every *claimed* historical
byte match is reauthenticated; newly added repository files cannot change that
historical census. This does not prove historical absence of other copies.
"""

import argparse
from collections import Counter, defaultdict
from contextlib import ExitStack
import gzip
import hashlib
import io
import json
from pathlib import Path
import posixpath
import subprocess
import sys
import zipfile


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
PAYLOAD_FILES = {"README.md", "INVENTORY.json", "check.py", "NORMAL.json", "OPTIMIZED.json"}
OPS = {"add", "sub", "mul"}


def need(condition, message):
    if not condition:
        raise ValueError(message)


def sha256(raw):
    return hashlib.sha256(raw).hexdigest()


def encoded(value):
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()


def repository_path(relative):
    path = ROOT / relative
    need(path.resolve().is_relative_to(ROOT), "repository path escapes root")
    return path


def repository_bytes(relative, historical_commit):
    """Use current bytes if present; otherwise read the pinned Git object.

    Relocation must not require restoring historical files or extracting ZIPs.
    A present but changed file still fails its normal hash comparison.
    """
    path = repository_path(relative)
    if path.is_file():
        return path.read_bytes()
    need(not path.exists(), "expected historical file is now a directory")
    return subprocess.check_output(["git", "show", historical_commit + ":" + relative], cwd=ROOT)


def quartic_check(z, member, obj, names):
    if not member.endswith("/equation.json"):
        return None
    if not isinstance(obj.get("residuals"), list) or not isinstance(obj.get("variables"), list):
        return None
    parent = posixpath.dirname(member)
    expanded = next((parent + "/" + f for f in ["expanded_polynomial.json", "polynomial.json"]
                     if parent + "/" + f in names), None)
    if expanded is None:
        return None
    actual_packet = json.loads(z.read(expanded))
    calculated = defaultdict(int)
    for row in obj["residuals"]:
        terms = row["terms"] if isinstance(row, dict) else row
        for coefficient, variables in terms:
            need(type(coefficient) is int and len(variables) <= 2, "invalid quadratic term")
            need(all(type(v) is int and 0 <= v < len(obj["variables"]) for v in variables),
                 "quadratic variable index outside equation")
            for other_coefficient, other_variables in terms:
                calculated[tuple(sorted(variables + other_variables))] += coefficient * other_coefficient
    calculated = {key: value for key, value in calculated.items() if value}
    actual = defaultdict(int)
    for coefficient, variables in actual_packet["terms"]:
        need(type(coefficient) is int, "noninteger expanded coefficient")
        actual[tuple(sorted(variables))] += coefficient
    actual = {key: value for key, value in actual.items() if value}
    need(calculated == actual, "entire SOS coefficient mismatch: " + member)
    need(len(actual_packet["terms"]) == len(actual), "expanded polynomial is not collected")
    return {
        "equation": member, "expanded": expanded, "variables": len(obj["variables"]),
        "residuals": len(obj["residuals"]), "degree": max(map(len, calculated)),
        "monomials": len(calculated), "height": max(map(abs, calculated.values())),
        "result": "exact complete coefficient match",
    }


def dag_check(member, obj):
    nodes = obj.get("nodes")
    if not (isinstance(nodes, list) and nodes and isinstance(nodes[0], list)
            and len(nodes[0]) == 2 and nodes[0][0] in {"variable", "coefficient", "integer"}
            and "output" in obj):
        return None
    if not all(isinstance(row, list) and row and row[0] in OPS | {"variable", "coefficient", "integer"}
               for row in nodes):
        return None
    counts = Counter()
    for i, row in enumerate(nodes):
        if row[0] in OPS:
            need(len(row) == 3 and all(type(k) is int and 0 <= k < i for k in row[1:]),
                 "DAG not topologically ordered: " + member)
            counts[row[0]] += 1
    need(type(obj["output"]) is int and 0 <= obj["output"] < len(nodes), "invalid DAG output")
    live = set()
    pending = [obj["output"]]
    while pending:
        i = pending.pop()
        if i in live:
            continue
        live.add(i)
        if nodes[i][0] in OPS:
            pending.extend(nodes[i][1:])
    need(len(live) == len(nodes), "dead nodes in DAG: " + member)
    if "operations" in obj:
        need(sum(counts.values()) == obj["operations"], "DAG operation census mismatch")
    return {
        "member": member, "variables": len(obj.get("variables", [])),
        "operations": sum(counts.values()), "operation_counts": dict(counts),
        "nodes": len(nodes), "all_nodes_live": True, "topologically_ordered": True,
        "claimed_exact_degree": obj.get("exact_degree"), "degree_verified_here": False,
    }


def payload_checks(z, member, obj, names, checks):
    payloads = obj.get("payloads", obj.get("ports"))
    if not isinstance(payloads, dict):
        return
    for port, binding in payloads.items():
        if not isinstance(binding, dict):
            continue
        file_name = binding.get("file", binding.get("gzip_payload"))
        expected = binding.get("raw_sha256", binding.get("sha256"))
        if not isinstance(file_name, str) or not expected:
            continue
        path = posixpath.normpath(posixpath.join(posixpath.dirname(member), file_name))
        if path not in names:
            checks["unresolved_historical_payload_paths"].append({"binding": member, "port": port, "path": path})
            continue
        compressed = z.read(path)
        try:
            raw = gzip.decompress(compressed)
        except (ValueError, gzip.BadGzipFile):
            continue
        need(sha256(raw) == expected, "decoded payload hash mismatch: " + path)
        bits = int.from_bytes(raw, "little").bit_length()
        if "raw_bytes" in binding:
            need(len(raw) == binding["raw_bytes"], "decoded payload length mismatch")
        if "bits" in binding:
            need(bits == binding["bits"], "decoded payload bit count mismatch")
        if "gzip_sha256" in binding:
            need(sha256(compressed) == binding["gzip_sha256"], "compressed payload hash mismatch")
        checks["coefficient_payloads"].append({
            "binding": member, "port": port, "member": path, "raw_sha256": sha256(raw),
            "compressed_sha256": sha256(compressed), "raw_bytes": len(raw), "bits": bits,
        })


def archive_checks(z, members):
    checks = {key: [] for key in ["quartic_sum_of_squares", "literal_dag_census", "coefficient_payloads",
                                  "unresolved_historical_payload_paths"]}
    names = set(z.namelist())
    for member in members:
        name = member["member"]
        if not name.endswith(".json"):
            continue
        try:
            obj = json.loads(z.read(name))
        except (ValueError, UnicodeDecodeError):
            continue
        if not isinstance(obj, dict):
            continue
        quartic = quartic_check(z, name, obj, names)
        if quartic is not None:
            checks["quartic_sum_of_squares"].append(quartic)
        dag = dag_check(name, obj)
        if dag is not None:
            checks["literal_dag_census"].append(dag)
        payload_checks(z, name, obj, names, checks)
    return checks


def collect_evidence():
    inventory_bytes = (HERE / "INVENTORY.json").read_bytes()
    inventory = json.loads(inventory_bytes)
    need(inventory["hash_algorithm"] == "SHA-256", "unsupported inventory hash algorithm")
    need(len(inventory["archives"]) == 6, "expected six arrivals")
    archive_reports = []
    totals = Counter()
    all_member_hashes = set()
    for archive in inventory["archives"]:
        raw = repository_bytes(archive["archive"], inventory["review_commit"])
        need(sha256(raw) == archive["sha256"] and len(raw) == archive["size"], "complete arrival mismatch")
        blob = hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest()
        need(blob == archive["git_blob_at_review_commit"], "working bytes differ from pinned Git blob")
        commit_blob = subprocess.check_output(
            ["git", "rev-parse", inventory["review_commit"] + ":" + archive["archive"]],
            cwd=ROOT, text=True).strip()
        need(commit_blob == blob and archive["working_archive_equals_review_commit"] is True,
             "arrival differs from named commit")
        with zipfile.ZipFile(io.BytesIO(raw)) as z:
            records = []
            need(len(z.namelist()) == len(set(z.namelist())), "duplicate ZIP member paths")
            for info in z.infolist():
                if info.is_dir():
                    continue
                data = z.read(info)
                records.append({"member": info.filename, "size": len(data), "compressed_size": info.compress_size,
                                "crc32": f"{info.CRC:08x}", "sha256": sha256(data)})
                all_member_hashes.add(sha256(data))
            need(records == archive["members"], "full ordered member inventory mismatch")
            need(len(records) == archive["file_count"] and sum(m["size"] for m in records) == archive["uncompressed_size"],
                 "archive totals mismatch")
            calculated = archive_checks(z, records)
            need(calculated == archive["static_checks"], "static evidence differs from historical record")
            for key, results in calculated.items():
                totals[key] += len(results)
            archive_reports.append({"archive": archive["archive"], "sha256": archive["sha256"],
                                    "git_blob": blob, "members": len(records),
                                    "static_check_counts": {k: len(v) for k, v in calculated.items()}})
    need(dict(totals) == inventory["static_check_totals"], "combined static totals mismatch")
    need(sum(a["members"] for a in archive_reports) == 2145, "member census differs from intake")

    # Recheck every positive byte-match claim, retaining the historical universe.
    match_counts = Counter()
    file_cache = {}
    with ExitStack() as stack:
        zip_cache = {}
        member_cache = {}
        for digest, matches in inventory["content_matches_by_sha256"].items():
            need(digest in all_member_hashes, "match index contains no arrival member")
            for relative in matches.get("existing_file_matches", []):
                if relative not in file_cache:
                    file_cache[relative] = sha256(repository_bytes(relative, inventory["recorded_existing_git_head"]))
                need(file_cache[relative] == digest, "historical existing-file match changed: " + relative)
                match_counts["existing_file_matches"] += 1
            for reference in matches.get("prior_incoming_member_matches", []):
                key = (reference["archive"], reference["member"])
                if key not in member_cache:
                    if key[0] not in zip_cache:
                        prior_raw = repository_bytes(key[0], inventory["recorded_existing_git_head"])
                        zip_cache[key[0]] = stack.enter_context(zipfile.ZipFile(io.BytesIO(prior_raw)))
                    member_cache[key] = sha256(zip_cache[key[0]].read(key[1]))
                need(member_cache[key] == digest, "historical prior-member match changed")
                match_counts["prior_incoming_member_matches"] += 1
            for relative in matches.get("complete_incoming_archive_matches", []):
                if relative not in file_cache:
                    file_cache[relative] = sha256(repository_bytes(relative, inventory["recorded_existing_git_head"]))
                need(file_cache[relative] == digest, "embedded complete archive mismatch")
                match_counts["complete_incoming_archive_matches"] += 1
    for archive in inventory["archives"]:
        index = inventory["content_matches_by_sha256"]
        for key, label in [("existing_file_matches", "members_matching_existing_files"),
                           ("prior_incoming_member_matches", "members_matching_prior_incoming")]:
            need(sum(key in index.get(m["sha256"], {}) for m in archive["members"]) == archive[label],
                 "historical matched-member census mismatch")
    return {
        "status": "PASS", "schema": "incoming_e13_inert_replay_v1",
        "python_optimized": bool(sys.flags.optimize), "review_commit": inventory["review_commit"],
        "historical_comparison_head": inventory["recorded_existing_git_head"],
        "inventory_sha256": sha256(inventory_bytes), "checker_sha256": sha256(Path(__file__).read_bytes()),
        "archives": archive_reports, "member_count": 2145, "static_check_totals": dict(totals),
        "claimed_historical_match_counts": dict(match_counts), "unique_authenticated_file_locations": len(file_cache),
        "unique_prior_member_locations": len(member_cache),
        "incoming_code_executed": False, "lean_executed": False,
        "scope": "Exact inert data/hash replay and positive historical match authentication; no new universal/calibration proof.",
    }


def verify_seal():
    manifest = json.loads((HERE / "MANIFEST.json").read_bytes())
    need(manifest["schema"] == "closed_sha256_packet_v1", "unknown packet seal")
    expected_names = PAYLOAD_FILES | {"MANIFEST.json"}
    need({p.name for p in HERE.iterdir()} == expected_names, "unsealed extra or missing packet file")
    need(set(manifest["files"]) == PAYLOAD_FILES, "manifest inventory is not closed")
    need(manifest["self_exclusion"] == "MANIFEST.json", "incorrect self-exclusion")
    for name, pin in manifest["files"].items():
        raw = (HERE / name).read_bytes()
        need(pin == {"sha256": sha256(raw), "size": len(raw)}, "packet seal mismatch: " + name)


def write_reports_and_seal():
    need({p.name for p in HERE.iterdir()} <= PAYLOAD_FILES | {"MANIFEST.json"}, "unexpected packet output")
    for optimized, name in [(False, "NORMAL.json"), (True, "OPTIMIZED.json")]:
        command = [sys.executable, "-B"] + (["-O"] if optimized else [])
        command += [str(Path(__file__).resolve()), "--inert-evidence-json"]
        report = json.loads(subprocess.check_output(command, cwd=ROOT))
        need(report["status"] == "PASS" and report["python_optimized"] is optimized, "self-replay mode mismatch")
        (HERE / name).write_bytes(encoded(report))
    files = {name: {"sha256": sha256((HERE / name).read_bytes()), "size": (HERE / name).stat().st_size}
             for name in sorted(PAYLOAD_FILES)}
    (HERE / "MANIFEST.json").write_bytes(encoded({"schema": "closed_sha256_packet_v1",
                                                  "self_exclusion": "MANIFEST.json", "files": files}))
    verify_seal()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="write deterministic current-mode receipt outside this packet")
    parser.add_argument("--write-reports-and-seal", action="store_true", help="regenerate this packet's two receipts and closed seal")
    parser.add_argument("--inert-evidence-json", action="store_true", help=argparse.SUPPRESS)
    args = parser.parse_args()
    need(not (args.write_reports_and_seal and (args.output or args.inert_evidence_json)), "incompatible modes")
    if args.write_reports_and_seal:
        write_reports_and_seal()
        print("PASS: regenerated deterministic normal/-O receipts and closed packet seal")
        return
    if not args.inert_evidence_json:
        verify_seal()
    report = collect_evidence()
    result = encoded(report)
    if args.inert_evidence_json:
        sys.stdout.buffer.write(result)
        return
    for optimized, name in [(False, "NORMAL.json"), (True, "OPTIMIZED.json")]:
        expected = dict(report, python_optimized=optimized)
        need((HERE / name).read_bytes() == encoded(expected), "deterministic retained receipt differs: " + name)
    if args.output:
        need(not args.output.resolve().is_relative_to(HERE), "receipt output must be outside sealed packet")
        if args.output.exists():
            need(args.output.is_file() and args.output.read_bytes() == result,
                 "receipt destination already contains different data")
        else:
            with args.output.open("xb") as stream:
                stream.write(result)
    print("PASS: closed seal; six commit-pinned ZIPs; 2145 members; 33 quartics; 39 DAGs; 54 bindings; historical matches")


if __name__ == "__main__":
    try:
        main()
    except (ValueError, KeyError, OSError, zipfile.BadZipFile, subprocess.CalledProcessError) as error:
        print("FAIL: " + str(error), file=sys.stderr)
        sys.exit(1)
