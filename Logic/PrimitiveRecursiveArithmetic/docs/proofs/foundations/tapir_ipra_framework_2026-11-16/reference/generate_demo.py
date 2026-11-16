from __future__ import annotations

import json
from pathlib import Path

from tapir_reference import CertificateUse, Node, compile_graph


def main() -> None:
    nodes = [
        Node("dead_experiment", "UnusedLemma", residuals=("UnusedOracle",)),
        Node("arithmetic", "ArithmeticInfrastructure"),
        Node(
            "local_chart",
            "ExistsValidChart",
            deps=("arithmetic",),
            certificate=CertificateUse(),
        ),
        Node(
            "stable_observer",
            "ChartIndependentObservation",
            deps=("local_chart",),
            certificate=CertificateUse(
                appears_in_public=True,
                observer_proved=True,
            ),
        ),
        Node(
            "bounded_scan",
            "CompleteBoundedSolutionScan",
            deps=("arithmetic",),
            residuals=("HeightBound(q,H)", "CodeCoverage(q,H)"),
        ),
        Node(
            "least_solution",
            "LeastNamedSolution",
            deps=("bounded_scan",),
            certificate=CertificateUse(explicitly_named=True),
        ),
        Node(
            "root",
            "PublicTheorem",
            deps=("stable_observer", "least_solution"),
        ),
    ]
    compiled = compile_graph(nodes, "root")
    payload = {
        "schema_version": 1,
        "description": "TAPIR demonstration contract; not an iPRA proof object.",
        "nodes": [
            {
                "id": n.ident,
                "conclusion": n.conclusion,
                "deps": list(n.deps),
                "residuals": list(n.residuals),
                "kind": n.kind,
                **(
                    {
                        "certificate": {
                            "appears_in_public": n.certificate.appears_in_public,
                            "observer_proved": n.certificate.observer_proved,
                            "explicitly_named": n.certificate.explicitly_named,
                        }
                    }
                    if n.certificate is not None
                    else {}
                ),
            }
            for n in nodes
        ],
        "compiled": compiled.to_json_obj(),
    }
    out = Path(__file__).resolve().parents[1] / "examples" / "demo_contract.json"
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(out)


if __name__ == "__main__":
    main()
