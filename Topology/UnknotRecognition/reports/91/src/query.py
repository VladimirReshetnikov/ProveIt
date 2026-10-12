"""Command line query and certificate emission; no topological verdict."""
import argparse
import json
from pathlib import Path
from sparse_cuts import solve, witness_dag, cut_addresses, mark_address, BudgetExceeded, InputError
from checker import verify_certificate


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("grammar", type=Path)
    p.add_argument("--threshold", type=int, default=3)
    p.add_argument("--certificate", type=Path)
    p.add_argument("--witness", type=Path)
    p.add_argument("--check", action="store_true")
    p.add_argument("--operation-limit", type=int)
    p.add_argument("--state-limit", type=int)
    args = p.parse_args()
    try:
        g = json.loads(args.grammar.read_text())
        result = solve(g, args.threshold, operation_limit=args.operation_limit, state_limit=args.state_limit)
        report = {"status": "complete", "root_metadata": result.metadata[result.root].record(),
                  "response": [[*key, cost] for key, cost in sorted(result.response().items())],
                  "peak_entries": max(map(len, result.tables)), "total_entries": sum(map(len, result.tables)),
                  "operations": result.operations}
        cert = result.certificate()
        if args.check:
            report["independent_replay"] = verify_certificate(g, cert)
        if args.certificate:
            args.certificate.write_text(json.dumps(cert, indent=2)+"\n")
        if not g["nodes"][result.root]["terminals"]:
            report["marked_cut_exists"] = result.has_marked_cut()
            if report["marked_cut_exists"]:
                report["cut_addresses"] = cut_addresses(result)
                report["mark_addresses"] = [mark_address(result, c) for c in (0, 1)]
                if args.witness:
                    args.witness.write_text(json.dumps(witness_dag(result), indent=2)+"\n")
        print(json.dumps(report, indent=2))
    except (BudgetExceeded, InputError, ValueError, OSError) as e:
        print(json.dumps({"status": "inconclusive", "reason": str(e)}))
        raise SystemExit(2)

if __name__ == "__main__":
    main()
