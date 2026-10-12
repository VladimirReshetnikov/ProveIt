"""Classify saved annular refusals by base type; no absorption is performed."""
import argparse
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path
import sys
from time import perf_counter


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--unknot-root", type=Path, required=True)
    parser.add_argument("--census-audit", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    sys.path.insert(0, str(args.unknot_root / "fast"))
    from fastunknot.parallelity_boundary_words import normal_parallelity_boundary_words
    from fastunknot.parallelity_boundary_words_verify import verify_parallelity_boundary_words

    bank_path = args.unknot_root / "synthesis/data/parallelity-audit.json"
    bank = {r["id"]: r for r in json.loads(bank_path.read_text())["source_proofs"]}
    census = json.loads(args.census_audit.read_text())
    selected = [r for r in census["cases"]
                if r.get("native_reason") == "annular_core_attachment"]
    records = []
    started = perf_counter()
    for original in selected:
        source = bank[original["id"]]
        profiles = source["certificate"]["summary"]["base_profiles"]
        ported = [(i, p) for i, p in enumerate(profiles) if p["core_ports"]]
        is_disk = lambda p: (p["orientable"] and p["euler_characteristic"] == 1
                             and p["boundary_components"] == 1)
        nondisks = [(i, p) for i, p in ported if not is_disk(p)]
        if all(p["boundary_components"] == 1 and p["original_boundary_edges"] > 0
               for _, p in nondisks):
            eligible, method = True, "saved_base_profiles"
            detail = None
        elif any(p["original_boundary_edges"] == 0 for _, p in nondisks):
            eligible, method = False, "saved_base_profiles"
            detail = None
        else:
            result = normal_parallelity_boundary_words(
                source["triangulation"], source["coordinates"], record_certificate=True)
            assert result["status"] == "COMPLETE"
            assert verify_parallelity_boundary_words(
                source["triangulation"], source["coordinates"], result["certificate"])
            port_base = {p: i for i, profile in enumerate(profiles)
                         for p in profile["core_ports"]}
            circles = [a for a in result["skeleton"]["attachment_components"]
                       if a["kind"] == "circle"]
            assert circles
            detail = []
            for circle in circles:
                owners = {port_base[abs(p) - 1] for p in circle["word"]}
                assert len(owners) == 1
                index = owners.pop()
                profile = profiles[index]
                detail.append(dict(base_profile=index, disk_base=is_disk(profile),
                                   word=circle["word"],
                                   orientable=profile["orientable"],
                                   euler_characteristic=profile["euler_characteristic"],
                                   boundary_components=profile["boundary_components"]))
            eligible = all(r["disk_base"] for r in detail)
            method = "new_independently_replayed_boundary_words"
        record = dict(id=source["id"], every_full_circle_has_disk_base=eligible,
                      method=method, full_circle_details=detail,
                      ported_base_profiles=[dict(base_profile=i, **p) for i, p in ported])
        records.append(record)
        print(source["id"], eligible, method, flush=True)
    counts = Counter("only_disk_base_circles" if r["every_full_circle_has_disk_base"]
                     else "at_least_one_nondisk_base_circle" for r in records)
    report = dict(
        scope="Geometric absorption eligibility only; no augmented cancellation or census acceptance tested.",
        source_revision=census["source_revision"],
        saved_parallelity_audit_sha256=sha256(bank_path.read_bytes()).hexdigest(),
        census_audit_sha256=sha256(args.census_audit.read_bytes()).hexdigest(),
        total=len(records), counts=dict(counts),
        independently_replayed_new_boundary_queries=sum(
            r["method"] == "new_independently_replayed_boundary_words" for r in records),
        seconds=perf_counter() - started, cases=records)
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: v for k, v in report.items() if k != "cases"}), flush=True)


if __name__ == "__main__":
    main()
