#!/usr/bin/env python3
"""Force the small-cone support enumerator on every reference sector k<=2."""

import argparse
import hashlib
import importlib
import json
from pathlib import Path
import sys
import time


def flatten(rows):
    return tuple(x for row in rows for x in row)


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--fast",type=Path,required=True)
    ap.add_argument("--corpus",type=Path,default=Path(__file__).with_name("discovery_corpus.json"))
    ap.add_argument("--cases",type=Path,default=Path(__file__).with_name("sector_cases.json"))
    ap.add_argument("--output",type=Path,default=Path(__file__).with_name("support_method_audit.json"))
    args=ap.parse_args()
    sys.path.insert(0,str(args.fast.resolve()))
    producer=importlib.import_module("fastunknot.normal_sector")
    corpus=json.loads(args.corpus.read_text())
    cases=json.loads(args.cases.read_text())
    assert hashlib.sha256(args.corpus.read_bytes()).hexdigest()==cases["corpus_sha256"]
    fixtures={r["id"]:r for r in corpus["records"]}
    result={"schema":"normal-sector-forced-support-audit-v1",
        "producer_sha256":hashlib.sha256(Path(producer.__file__).read_bytes()).hexdigest(),
        "source_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "corpus_sha256":cases["corpus_sha256"],"records":[]}
    start=time.perf_counter()
    for i,case in enumerate(cases["cases"]):
        allowed=[(t,q) for t,q in enumerate(case["types"]) if q>=0]
        if len(allowed)>2:
            continue
        fixture=fixtures[case["fixture_id"]]
        expected={flatten(fixture["standard_vertices"][j]["coordinates"])
                  for j in case["standard_indices"]}
        rows,stats=producer.enumerate_sector(fixture["triangulation"],allowed,
                                             phase="standard",method="supports")
        actual={flatten(row) for row in rows}
        assert len(actual)==len(rows) and actual==expected,(i,case["fixture_id"])
        result["records"].append({"case_index":i,"fixture_id":case["fixture_id"],
            "allowed_types":len(allowed),"rays":len(expected),"stats":stats,"passed":True})
    result["summary"]={"cases_passed":len(result["records"]),
        "rays_compared":sum(r["rays"] for r in result["records"]),
        "wall_seconds":time.perf_counter()-start}
    args.output.write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps(result["summary"],indent=2))


if __name__=="__main__":
    main()
