#!/usr/bin/env python3
"""Unbounded finite-ground refutation recognizer for the closure kernels.

The theorem concerns the ideal algorithm with unbounded integers and memory.
Host errors, resource exhaustion, and --max-stage exits are not refutations.
The default fc15 mode is the recommended nine-function FC15* theory.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import ground_kernel as K


def templates(theory="fc15"):
    extensional = theory == "fc17"
    if theory == "fc16":
        from coded_extensional import full_clauses
        clauses = full_clauses()
    else:
        fs = K.signature(extensional, member_witness=True)
        clauses = K.source_clauses(extensional, member_witness=True)
        clauses += K.equality_clauses(extensional, functions=fs)
    return clauses, extensional


def stages(theory="fc15"):
    """Yield each finite decision. Stop only after an UNSAT stage.

    With no resource bounds, this generator produces indefinitely many
    SAT stages exactly when the corresponding finite theory is consistent.
    """
    clauses, extensional = templates(theory)
    stage = 0
    while True:
        cnf = list(K.instances(clauses, stage, extensional, member_witness=True))
        valuation = K.solve(cnf)
        if valuation is not None and not K.valuation_satisfies(cnf, valuation):
            raise RuntimeError("invalid SAT assignment")
        result = {
            "theory": theory,
            "stage": stage,
            "ground_instances": len(cnf),
            "distinct_atoms": len({abs(l) for c in cnf for l in c}),
            "satisfiable": valuation is not None,
        }
        yield result
        if valuation is None:
            return
        stage += 1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--theory", choices=("fc15", "fc16", "fc17"), default="fc15")
    parser.add_argument("--max-stage", type=int,
                        help="finite demo limit; stopping here is not a refutation")
    parser.add_argument("--output", type=Path, help="write a finite demo transcript")
    args = parser.parse_args()
    if args.max_stage is not None and args.max_stage < 0:
        parser.error("--max-stage must be nonnegative")
    if args.output and args.max_stage is None:
        parser.error("--output requires --max-stage; unbounded logs are not retained")
    results = []
    for result in stages(args.theory):
        print(json.dumps(result), flush=True)
        if args.output:
            results.append(result)
        if not result["satisfiable"]:
            status = "finite_refutation_found"
            break
        if args.max_stage is not None and result["stage"] >= args.max_stage:
            status = "demo_limit_reached_not_a_refutation"
            break
    final = {"status": status, "theory": args.theory}
    print(json.dumps(final), flush=True)
    if args.output:
        args.output.write_text(json.dumps({"stages": results, **final}, indent=2) + "\n")


if __name__ == "__main__":
    main()
