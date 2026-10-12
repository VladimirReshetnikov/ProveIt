"""CLI: python src/query.py examples/prism.json --check --certificate out.json"""
from __future__ import annotations
import argparse, json, sys
from pathlib import Path
from gauge_cuts import compile_grammar, BudgetExceeded, extract_cut_addresses
from checker import verify_packet

def main() -> int:
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("grammar",type=Path); p.add_argument("--check",action="store_true")
    p.add_argument("--certificate",type=Path); p.add_argument("--work-limit",type=int)
    args=p.parse_args()
    try:
        source=json.loads(args.grammar.read_text(encoding="utf-8"))
        packet=compile_grammar(source,work_limit=args.work_limit)
        result={"query":packet["query"],"rules":len(packet["atlases"]),
                "peak_rows":max(x["states"] for x in packet["statistics"]),"candidate_work":packet["candidate_work"]}
        if args.check: result["replay"]=verify_packet(packet,source)
        if packet["query"]["status"]=="MARKED_CUT":
            ri=next(i for i,r in enumerate(packet["atlases"][-1]["rows"]) if r[3]==3)
            result["cut_addresses"]=extract_cut_addresses(packet,ri)
            result["address_scope"]="grammar edge occurrences, not geometric disc or full shore coloring"
        if args.certificate: args.certificate.write_text(json.dumps(packet,sort_keys=True,indent=2)+"\n",encoding="utf-8")
        print(json.dumps(result,indent=2)); return 0
    except BudgetExceeded as e:
        print(json.dumps({"query":{"status":"INCONCLUSIVE"},"reason":str(e)})); return 2
    except (ValueError,OSError,KeyError,TypeError) as e:
        print(json.dumps({"status":"ERROR","reason":str(e)}),file=sys.stderr); return 1
if __name__=="__main__": raise SystemExit(main())
