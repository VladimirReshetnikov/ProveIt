#!/usr/bin/env python3
"""Audit producer sector rays against complete Regina enumeration results.

The producer is imported only for the call under test. Expected vectors,
Euler signs, support admissibility, and nullities originate in the separate
Regina corpus and exact reference selector. Capped cases are recorded as
incomplete and never counted as passes.
"""

from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import importlib
import json
from pathlib import Path
import platform
import sys
import time
import traceback


def flat(rows):
    return tuple(x for row in rows for x in row)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--fast",type=Path,required=True)
    ap.add_argument("--corpus",type=Path,default=Path(__file__).with_name("discovery_corpus.json"))
    ap.add_argument("--cases",type=Path,default=Path(__file__).with_name("sector_cases.json"))
    ap.add_argument("--output",type=Path,default=Path(__file__).with_name("sector_audit.json"))
    ap.add_argument("--max-bases",type=int,default=100000)
    ap.add_argument("--max-seconds-per-phase",type=float,default=20)
    ap.add_argument("--only",nargs="*")
    args = ap.parse_args()
    sys.path.insert(0,str(args.fast.resolve()))
    producer = importlib.import_module("fastunknot.normal_sector")
    corpus = json.loads(args.corpus.read_text())
    references = json.loads(args.cases.read_text())
    assert hashlib.sha256(args.corpus.read_bytes()).hexdigest() == references["corpus_sha256"]
    fixtures = {r["id"]:r for r in corpus["records"]}
    results = {
        "schema":"normal-sector-independent-audit-v1",
        "producer_source_sha256":hashlib.sha256(Path(producer.__file__).read_bytes()).hexdigest(),
        "corpus_sha256":references["corpus_sha256"],
        "cases_sha256":hashlib.sha256(args.cases.read_bytes()).hexdigest(),
        "audit_source_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "python":platform.python_version(),"platform":platform.platform(),
        "regina_version":corpus["regina_version"],
        "max_bases":args.max_bases,"max_seconds_per_phase":args.max_seconds_per_phase,
        "records":[],"summary":{},
    }
    totals = Counter()
    started = time.perf_counter()
    for index,case in enumerate(references["cases"]):
        if args.only and case["fixture_id"] not in args.only:
            continue
        fixture = fixtures[case["fixture_id"]]
        allowed = [(i,q) for i,q in enumerate(case["types"]) if q>=0]
        record = {"case_index":index,"fixture_id":case["fixture_id"],
                  "types":case["types"],"selection":case["selection"],"phases":{}}
        for phase,collection,indices in [
            ("quadrilateral","quad_vertices",case["quad_indices"]),
            ("standard","standard_vertices",case["standard_indices"])]:
            expected = {flat(fixture[collection][i]["coordinates"]) for i in indices}
            begin = time.perf_counter()

            def check():
                if time.perf_counter()-begin>args.max_seconds_per_phase:
                    raise TimeoutError("configured audit phase time cap")

            try:
                vectors,stats = producer.enumerate_sector(
                    fixture["triangulation"],allowed,phase=phase,
                    max_bases=args.max_bases,check=check)
                actual = {flat(v) for v in vectors}
                assert len(actual) == len(vectors), "duplicate emitted vectors"
                assert stats["matching_nullity"] == case["kernel_dimension"], (
                    "nullity",stats["matching_nullity"],case["kernel_dimension"])
                if actual != expected:
                    raise AssertionError({"missing":sorted(expected-actual),
                                          "extra":sorted(actual-expected)})
                entry = {"status":"PASS","seconds":time.perf_counter()-begin,
                         "expected_rays":len(expected),"stats":stats}
                totals[f"{phase}_passed"] += 1
                totals[f"{phase}_rays_compared"] += len(expected)
            except (producer.SearchLimit,TimeoutError) as exc:
                entry = {"status":"CAPPED","reason":str(exc),
                         "seconds":time.perf_counter()-begin,
                         "expected_rays":len(expected)}
                totals[f"{phase}_capped"] += 1
            except Exception as exc:
                entry = {"status":"FAIL","error":repr(exc),
                         "traceback":traceback.format_exc(),
                         "seconds":time.perf_counter()-begin}
                totals[f"{phase}_failed"] += 1
            record["phases"][phase] = entry
        results["records"].append(record)
        totals["cases_processed"] += 1
        results["summary"] = dict(totals,wall_seconds=time.perf_counter()-started)
        if index%50==0 or any(p["status"]!="PASS" for p in record["phases"].values()):
            args.output.write_text(json.dumps(results,indent=2)+"\n")
            print(index,case["fixture_id"],{p:x["status"] for p,x in record["phases"].items()},
                  "elapsed",round(time.perf_counter()-started,2),flush=True)
        if any(p["status"]=="FAIL" for p in record["phases"].values()):
            args.output.write_text(json.dumps(results,indent=2)+"\n")
            raise RuntimeError(f"independent audit failed at case {index}")
    args.output.write_text(json.dumps(results,indent=2)+"\n")
    print(json.dumps(results["summary"],indent=2))


if __name__ == "__main__":
    main()
