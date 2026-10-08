"""Run the bounded RIII unlocking query (not unknot recognition).

Input is {"pd": [...]} or {"braid": {"strands": s, "word": [...]}}.
An uncapped completed negative answer is NO_BOUNDED_UNLOCK, never KNOTTED.
"""
from __future__ import annotations
import argparse, json, time
from pathlib import Path
from dart_kernel import from_pd, from_braid
from layered_search import Stats, SearchExhausted
from connected_kernel import kernel_unlock
from verify_certificate import serialize, verify

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input",type=Path)
    parser.add_argument("--depth",type=int,required=True)
    parser.add_argument("--max-trials",type=int)
    parser.add_argument("--max-regions",type=int)
    parser.add_argument("--certificate",type=Path)
    args=parser.parse_args()
    if args.depth<0 or any(x is not None and x<0 for x in (args.max_trials,args.max_regions)):
        parser.error("depth and resource caps must be nonnegative")
    try:
        data=json.loads(args.input.read_text())
        if "pd" in data: initial=from_pd(data["pd"])
        else: initial=from_braid(data["braid"]["strands"],data["braid"]["word"])
    except (OSError,ValueError,KeyError,TypeError) as exc: parser.error(str(exc))
    stats=Stats();start=time.perf_counter()
    try:
        witness,regions=kernel_unlock(initial,args.depth,max_trials=args.max_trials,
                                      max_regions=args.max_regions,stats=stats)
        result={"status":"FOUND_UNLOCK" if witness is not None else "NO_BOUNDED_UNLOCK",
                "crossings":initial.n,"depth":args.depth,"regions":regions}
        if witness is not None:
            certificate=serialize(initial,witness,args.depth)
            result["verification"]=verify(certificate)
            if args.certificate:
                args.certificate.parent.mkdir(parents=True,exist_ok=True)
                args.certificate.write_text(json.dumps(certificate,indent=2)+"\n")
                result["certificate"]=str(args.certificate)
    except SearchExhausted as exc:
        result={"status":"UNKNOWN","reason":str(exc),"crossings":initial.n,"depth":args.depth}
    result["statistics"]=vars(stats)
    result["seconds"]=time.perf_counter()-start
    print(json.dumps(result,indent=2))

if __name__=="__main__": main()
