#!/usr/bin/env python3
"""Emit four complete circuits by explicit, locally auditable edits."""
from pathlib import Path
import copy, hashlib, json

ROOT = Path(__file__).resolve().parent

def main():
    out = []
    for parent_no, weight in ((78, "V2"), (79, "bV")):
        parent_path = ROOT / "proof_sources" / f"denominator_parent_{parent_no}.json"
        parent = json.loads(parent_path.read_text())
        for den in ("XY", "q4"):
            graph = copy.deepcopy(parent)
            rows = []
            for name, op, a, b in parent["source"]:
                if name in ("Y2", "Tp", "V0"):
                    continue
                if name == "Xp1":
                    row = ["XY", "*", "X", "Y"]
                elif name == "Am1":
                    row = [name, "+", "XY", "Y"]
                elif name == "V0k":
                    row = [name, "*", "XY", "kY"]
                elif name == "cT":
                    row = [name, "*", "c", "T"]
                else:
                    row = [name, op, den if a == "Y2" else a, den if b == "Y2" else b]
                rows.append(row)
                if den == "q4" and name == "q2":
                    rows.append(["q4", "*", "q2", "q2"])
            ops = {op: sum(row[1] == op for row in rows) for op in ("+", "-", "*")}
            degree = {("XY", "V2"): 626, ("XY", "bV"): 464,
                      ("q4", "V2"): 622, ("q4", "bV"): 460}[den, weight]
            graph.update(
                name=f"staged_unshifted_{den}_{weight}", source=rows,
                operations=len(rows), operation_breakdown=ops, exact_degree=degree,
                denominator=den, transport_weight=weight, proof="PROOF.md",
                parent={"path": str(parent_path.relative_to(ROOT)),
                        "sha256": hashlib.sha256(parent_path.read_bytes()).hexdigest()},
                status="explicit polynomial; ordinary arithmetic proof, inherited native calibration",
                generation="Private T shift deleted; XY and kY shared in both Pell bases; carrier denominator replaced."
            )
            filename = f"equation_{den}_{weight}.json"
            (ROOT / filename).write_text(json.dumps(graph, indent=2) + "\n")
            out.append({"file":filename, "operations":len(rows), "degree":degree,
                        "breakdown":ops})
    (ROOT / "build_metrics.json").write_text(json.dumps(out, indent=2) + "\n")
    print(json.dumps(out, indent=2))

if __name__ == "__main__":
    main()
