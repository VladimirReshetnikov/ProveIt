#!/usr/bin/env python3
"""Recheck the complete finite novelty claim without a repository checkout."""
import argparse, hashlib, json, pathlib, time
from inventory_tables import parse, rooted
from exact_graphs import isomorphism

HERE = pathlib.Path(__file__).resolve().parent


def transform(rows, states, reflection=False, exchange=False):
    out={}
    for (q,b),(w,d,n) in rows.items():
        if reflection:d="L" if d=="R" else "R"
        if exchange:b,w=1-b,1-w
        if n not in states:w,d=0,"R"
        out[q,b]=w,d,n
    return out


def canonical(rows, states):
    full=[h for q in states for h,n in [rooted(rows,states,q)] if n==len(states)]
    return min(full) if full else None


def require(condition, message):
    if not condition:raise ValueError(message)


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("candidates",nargs="*",type=pathlib.Path)
    ap.add_argument("--output",type=pathlib.Path)
    args=ap.parse_args()
    if not args.candidates:
        args.candidates=[HERE/"new_machines/PA194OM.tm",HERE/"new_machines/PA194OMF.tm"]
    require(len(args.candidates)>=1,"At least one candidate is required")
    begin=time.monotonic()
    prior=json.loads((HERE/"frontier194_index.json").read_text())
    require(len(prior)==550,"Expected the pinned 550-class corpus")
    lookup={}; nonspanning=[]; stored_classes=set()
    for item in prior:
        raw=(HERE/item["file"]).read_bytes()
        require(hashlib.sha256(raw).hexdigest()==item["sha256"],"Corrupt representative: "+item["file"])
        rows,states,start=parse(raw)
        require(len(states)==194 and len(rows)==388,"Incorrect representative size")
        require(item["class_id"] not in stored_classes,"Duplicate indexed class ID")
        stored_classes.add(item["class_id"])
        signature=canonical(transform(rows,states),states)
        require((signature is not None)==item["spanning"],"Spanning metadata mismatch")
        if signature is None:
            nonspanning.append(rows)
        else:
            lookup.setdefault(signature,[]).append(item["class_id"])
    require(len(nonspanning)==2,"Expected two disconnected diagnostics")
    require(isomorphism(nonspanning[0],nonspanning[1]) is None,"Diagnostics were improperly conflated")
    new_meta=json.loads((HERE/"new_designs.json").read_text())
    expected={r["sha256"]:r["name"] for r in new_meta}
    results=[]; raw_candidates=[]
    for path in args.candidates:
        raw=path.read_bytes(); digest=hashlib.sha256(raw).hexdigest()
        rows,states,declared=parse(raw)
        require(len(states)==194 and len(rows)==388,"Candidate is not a 194-control total binary table")
        checks=[]
        for reflection in (False,True):
            for exchange in (False,True):
                signature=canonical(transform(rows,states,reflection,exchange),states)
                require(signature is not None,"Candidate must have a spanning control")
                matches=lookup.get(signature,[])
                checks.append({"reflection":reflection,"symbol_exchange":exchange,
                               "ignored_terminal_actions":True,"unrooted_hash":signature,"prior_matches":matches})
        results.append({"name":expected.get(digest,path.stem),"file":str(path),"sha256":digest,
                        "states":194,"transitions":388,"symmetry_checks":checks,
                        "distinct_from_every_prior_class":all(not r["prior_matches"] for r in checks)})
        raw_candidates.append((rows,states))
    pair_checks=[]
    for i in range(len(results)):
        for j in range(i):
            target=results[j]["symmetry_checks"][0]["unrooted_hash"]
            equal=any(c["unrooted_hash"]==target for c in results[i]["symmetry_checks"])
            pair_checks.append({"left":results[j]["name"],"right":results[i]["name"],"equivalent":equal})
    # Exact renamed positive control. This is stronger than trusting filenames.
    rows,states=raw_candidates[0]
    rename={q:17+3*q for q in states}
    renamed={(rename[q],b):(w,d,rename.get(n,-999)) for (q,b),(w,d,n) in rows.items()}
    require(isomorphism(rows,renamed) is not None,"Renaming positive control failed")
    renamed_signature=canonical(transform(renamed,set(rename.values())),set(rename.values()))
    require(renamed_signature==results[0]["symmetry_checks"][0]["unrooted_hash"],"Canonical positive control failed")
    report={"commit":"883da8d55452ea097910ed2509a1eefc833ce292",
        "prior_whole_194_graph_classes":550,"prior_spanning_classes":548,"prior_nonspanning_classes":2,
        "comparison_relation":"Arbitrary control renaming/root, optional L/R reflection and global read/write bit exchange, terminal-entry write/move actions ignored",
        "candidate_results":results,"new_pair_checks":pair_checks,
        "renamed_positive_control_passed":True,"nonspanning_diagnostics_distinguished":True,
        "seconds":round(time.monotonic()-begin,3),
        "scope":"Finite table-graph novelty only; no halting-equivalence or arithmetic calibration theorem is inferred."}
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps(report,indent=2))
    require(all(r["distinct_from_every_prior_class"] for r in results),"A candidate matches a prior table")
    require(all(not p["equivalent"] for p in pair_checks),"The new pair is not structurally distinct")


if __name__=="__main__":main()
