#!/usr/bin/env python3
"""Paired complete-kernel measurements. These are not knot-recognition timings."""
from __future__ import annotations
import csv, gc, json, platform, statistics, time, hashlib
from pathlib import Path
from sparse_cuts import solve, circular_ladder, thue_morse
from checker import verify_certificate
from reference import expand, expanded_small_cut_signature
from audit import star_pair

ROOT=Path(__file__).resolve().parents[1]


def source_hashes():
    paths=sorted((ROOT/"src").glob("*.py"))+sorted((ROOT/"experiments").glob("*.py"))+sorted((ROOT/"tests").glob("*.py"))
    return {str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}

def encoded_response(response):
    return json.dumps([[*key,c] for key,c in sorted(response.items())],separators=(",",":"))

def paired(a,b,reps=7):
    assert a()==b()
    a();b()  # identical warm-up count
    raw=[]
    for i in range(reps):
        order=[("a",a),("b",b)] if i%2==0 else [("b",b),("a",a)]
        row={"repeat":i}
        for name,fn in order:
            gc.collect(); start=time.perf_counter_ns(); value=fn()
            row[name+"_ns"]=time.perf_counter_ns()-start
        raw.append(row)
    ma=statistics.median(x["a_ns"] for x in raw)/1e6
    mb=statistics.median(x["b_ns"] for x in raw)/1e6
    return {"a_median_ms":ma,"b_median_ms":mb,"b_over_a":mb/ma,"raw":raw}

def main():
    rows=[]; ladders=[]
    for n in [1,2,4,8,16,32]:
        def compressed(n=n): return encoded_response(solve(circular_ladder(n)).response())
        def literal(n=n): return encoded_response(expanded_small_cut_signature(expand(circular_ladder(n)),3))
        r=solve(circular_ladder(n)); p=paired(compressed,literal)
        p.update(copies=n,expanded_vertices=2*n,rules=len(r.grammar["nodes"]),
                 peak_states=max(map(len,r.tables)))
        ladders.append(p)
        print("ladder",n,p["a_median_ms"],p["b_median_ms"],flush=True)
    stars=[]
    for arms in [4,8,12,16]:
        g=star_pair(arms)
        fast,slow=solve(g),solve(g,cost_indexed=False)
        def indexed(g=g): return encoded_response(solve(g).response())
        def unindexed(g=g): return encoded_response(solve(g,cost_indexed=False).response())
        p=paired(indexed,unindexed,5)
        p.update(arms_per_child=arms,root_states=len(fast.response()),indexed_operations=fast.operations,
                 unindexed_operations=slow.operations)
        stars.append(p)
        print("stars",arms,p["a_median_ms"],p["b_median_ms"],flush=True)
    huge=[]
    for bits in [8,32,128,256,512,1024]:
        g=circular_ladder(1<<bits)
        times=[]
        for _ in range(5):
            start=time.perf_counter_ns(); r=solve(g); out=encoded_response(r.response())
            times.append(time.perf_counter_ns()-start)
        cert=r.certificate()
        start=time.perf_counter_ns(); assert verify_certificate(g,cert)["verified"]
        replay=(time.perf_counter_ns()-start)/1e6
        huge.append({"exponent_bits_minus_one":bits,"rules":len(g["nodes"]),
                     "peak_states":max(map(len,r.tables)),"total_states":sum(map(len,r.tables)),
                     "solve_median_ms":statistics.median(times)/1e6,"raw_ns":times,
                     "complete_replay_ms":replay,"grammar_bytes":len(json.dumps(g,separators=(",",":"))),
                     "certificate_bytes":len(json.dumps(cert,separators=(",",":")))})
        print("binary",bits,huge[-1]["solve_median_ms"],replay,flush=True)
    controls=[]
    for label,fn in [("ladder_8_compressed",lambda:encoded_response(solve(circular_ladder(8)).response())),
                     ("star_12_indexed",lambda:encoded_response(solve(star_pair(12)).response()))]:
        p=paired(fn,fn);p["name"]=label;controls.append(p)
    result={"source_sha256":source_hashes(),"python":platform.python_version(),"platform":platform.platform(),
            "method":"Alternating A/B order, gc.collect before each call, equal warm-up counts; complete query output serialization included. Local standard-library kernels only; no native recognizer.",
            "ladder_a":"build grammar + sparse solve + response serialization",
            "ladder_b":"build grammar + literal expansion + explicit tree-cut enumeration + response serialization",
            "star_a":"cost-indexed solve + response serialization",
            "star_b":"same producer without cost buckets + response serialization",
            "ladders":ladders,"stars":stars,"binary_stress":huge,"aa_controls":controls}
    (ROOT/"data/benchmark.json").write_text(json.dumps(result,indent=2)+"\n")
    with (ROOT/"data/benchmark.csv").open("w",newline="") as f:
        w=csv.writer(f);w.writerow(["family","parameter","a_ms","b_ms","b_over_a"])
        for family,data,param in [("ladder",ladders,"copies"),("star",stars,"arms_per_child")]:
            for row in data:w.writerow([family,row[param],row["a_median_ms"],row["b_median_ms"],row["b_over_a"]])

if __name__=="__main__":main()
