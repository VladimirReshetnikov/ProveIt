"""Fetch hash-pinned public sources and reproduce the bounded machine checks.

Run with Python 3.10+ from any directory. The 12-source manifest pins a
historical ProveIt commit. Downloads are verified before any source is run.
Use --offline after fetching once; --search-orders repeats 288 old choices;
--search-conjunctions repeats the 9,216 new compiler choices (about 3 minutes).
All output stays next to this script. No repository is modified or published.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import urllib.request

ROOT=Path(__file__).resolve().parent


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--offline",action="store_true")
    parser.add_argument("--fetch-only",action="store_true")
    parser.add_argument("--search-orders",action="store_true")
    parser.add_argument("--search-conjunctions",action="store_true")
    args=parser.parse_args()
    manifest=json.loads((ROOT/"source-manifest.json").read_text())
    for item in manifest["files"]:
        path=ROOT/"repo"/item["path"]
        if not path.exists():
            if args.offline:
                raise FileNotFoundError(path)
            url=(f"https://raw.githubusercontent.com/{manifest['repository']}/"
                 f"{manifest['commit']}/{item['path']}")
            request=urllib.request.Request(url,headers={"User-Agent":"ConZFC-reproduction/1"})
            with urllib.request.urlopen(request,timeout=60) as response:
                data=response.read()
            if hashlib.sha256(data).hexdigest()!=item["sha256"]:
                raise ValueError("download hash mismatch: "+item["path"])
            path.parent.mkdir(parents=True,exist_ok=True)
            path.write_bytes(data)
        data=path.read_bytes()
        if len(data)!=item["bytes"] or hashlib.sha256(data).hexdigest()!=item["sha256"]:
            raise ValueError("source hash mismatch: "+item["path"])
    print(f"Verified {len(manifest['files'])} pinned source files.",flush=True)
    if args.fetch_only:
        return
    research=ROOT/"repo/Computability/BusyBeaver/Research/ZFC"
    def run(script,*arguments):
        subprocess.run([sys.executable,str(script),*map(str,arguments)],check=True,cwd=ROOT)
    run(research/"audit_tm.py",research/"raw-candidate-252.tm",
        "--expected-sha256","58f8aab7fcc21a7e3a88e6250bf05b7a97eaafd340f75ea8117b6d8f989f3142",
        "--expected-states",252,"--expected-halt",252,
        "--window-radius",4,"--macro-steps",64,"--self-test","--trace-steps",1000000,
        "--output",ROOT/"independent_252_audit.json")
    extra=["--search-orders"] if args.search_orders else []
    run(research/"theory_backend_experiment.py","--scratch",ROOT/"backend_output",
        "--output-evidence",ROOT/"independent_backend.json",*extra)
    run(ROOT/"generate_candidate250.py")
    run(research/"audit_tm.py",ROOT/"conjunction-candidate-250.tm",
        "--expected-sha256","d7af3920268db1c95bf71dc06b77e53c8266086a13043b2fc91f9319c520aff1",
        "--expected-states",250,"--expected-halt",250,
        "--window-radius",4,"--macro-steps",64,"--self-test","--trace-steps",1000000,
        "--output",ROOT/"candidate250-audit.json")
    run(ROOT/"base3_codec.py")
    if args.search_conjunctions:
        run(ROOT/"search_conjunctions.py")


if __name__=="__main__":
    main()
