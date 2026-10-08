"""Regenerate example q=6 replay certificates and the exact q=5 collision."""
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "fast"))
sys.path.insert(0, str(ROOT / "research"))
from fastunknot.diagram import Diagram
from fastunknot.potts_exact import potts_exact
from fastunknot.potts_factorized_exact import factorized_potts_exact
from verify_potts_certificate import make_certificate, verify_certificate


def main():
    cases = json.loads((ROOT / "benchmarks/potts_benchmark.json").read_text())["cases"]
    by_name = {item["name"]: item for item in cases}
    output = ROOT / "certificates"
    output.mkdir(exist_ok=True)
    summaries = []
    specs = [("conway", "conway_q6", False),
             ("kinoshita_terasaka", "kinoshita_terasaka_q6", False),
             ("random_order_05", "random_order_05_q6_factorized", True),
             ("weaving_W3_5", "weaving_5_q6", False)]
    for name, filename, factored in specs:
        case = by_name[name]
        diagram = Diagram.from_json(case["input"])
        evaluator = factorized_potts_exact if factored else potts_exact
        raw = evaluator(diagram, colors=6, order=case["order"],
                        max_states=None, max_transitions=None)
        certificate = make_certificate(diagram.pd, case["order"], raw["shade"],
                                       raw, fast_dir=ROOT / "fast")
        result = verify_certificate(certificate, fast_dir=ROOT / "fast")
        path = output / (filename + "_certificate.json")
        path.write_text(json.dumps(certificate, indent=2) + "\n")
        summaries.append({"file": path.name, "result": result})

    # A real long, bounded-frontier example exercises hexadecimal serialization.
    diagram = Diagram.from_braid(3, [1, -2] * 6001)
    order = list(range(diagram.crossings))
    raw = factorized_potts_exact(diagram, colors=6, order=order, shade=0,
                                 max_states=None, max_transitions=None)
    certificate = make_certificate(diagram.pd, order, 0, raw, fast_dir=ROOT / "fast")
    path = output / "weaving_6001_q6_factorized_certificate.json"
    path.write_text(json.dumps(certificate, separators=(",", ":")) + "\n")
    result = verify_certificate(json.loads(path.read_text()), fast_dir=ROOT / "fast")
    summaries.append({"file": path.name, "result": result})

    diagram = Diagram.from_braid(3, [1, -2] * 5)
    order = list(range(diagram.crossings))
    five = potts_exact(diagram, colors=5, order=order, shade=0)
    six = potts_exact(diagram, colors=6, order=order, shade=0)
    assert five["partition_function"] == five["unknot_partition"]
    assert six["partition_function"] == [-119 * x for x in six["unknot_partition"]]
    record = {"family": "closure((sigma1 sigma2^-1)^m)", "m": 5,
              "pd": diagram.pd, "order": order, "determinant": 121,
              "q5_normalized_jones": 1, "q6_normalized_jones": -119,
              "q5": five, "q6": six,
              "scope": "Exact q5 equality is INCONCLUSIVE for this nontrivial knot."}
    (output / "weaving_5_collision.json").write_text(json.dumps(record, indent=2) + "\n")
    (output / "replay_results.json").write_text(json.dumps(summaries, indent=2) + "\n")
    print(json.dumps({"status": "PASS", "verified_certificates": len(summaries),
                      "collision_record": "weaving_5_collision.json"}, indent=2))


if __name__ == "__main__":
    main()
