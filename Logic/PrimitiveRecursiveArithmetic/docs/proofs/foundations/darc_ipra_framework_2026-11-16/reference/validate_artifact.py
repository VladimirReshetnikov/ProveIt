"""Static validation for the DARC research package.

This script checks artifact consistency only.  It does not elaborate Lean and
is not an iPRA proof checker.
"""
from __future__ import annotations

import json
import py_compile
import re
from pathlib import Path

import jsonschema


ROOT = Path(__file__).resolve().parents[1]


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(message)


def main() -> None:
    # Python sources must parse.
    for path in sorted((ROOT / "reference").glob("*.py")):
        py_compile.compile(str(path), doraise=True)

    schema = json.loads((ROOT / "schema" / "darc_plan.schema.json").read_text())
    plan = json.loads((ROOT / "examples" / "sample_plan.json").read_text())
    jsonschema.Draft202012Validator.check_schema(schema)
    jsonschema.validate(plan, schema)

    names = [row["name"] for row in plan["resources"]]
    require(len(names) == len(set(names)), "sample plan has duplicate resource names")
    caps = {row["name"]: row["capacity"] for row in plan["resources"]}
    for rule in plan["rules"]:
        for side in ("triggers", "requirements"):
            for name, level in rule[side].items():
                require(name in caps, f"rule uses unknown resource {name}")
                require(0 <= level <= caps[name], f"rule level outside capacity: {name}={level}")

    structural = (ROOT / "lean" / "DARC" / "StructuralKernel.lean").read_text()
    require(re.search(r"\bsorry\b", structural) is None, "StructuralKernel contains sorry")
    require(re.search(r"\badmit\b", structural) is None, "StructuralKernel contains admit")
    require(re.search(r"^\s*axiom\b", structural, re.MULTILINE) is None,
            "StructuralKernel declares a new axiom")

    claims = json.loads((ROOT / "metadata" / "CLAIMS.json").read_text())
    require(claims["lean_status"]["new_kernel_checked_theorems"] == 0,
            "claims file overstates kernel-checked results")

    demo = json.loads((ROOT / "examples" / "demo.json").read_text())
    fixed = demo["demand_analysis"]["fixed_point"]
    require(fixed["cert:branch"] == 0 and fixed["cert:trace"] == 0,
            "value-only demo unexpectedly exports certificates")
    require(fixed["residual:tail_modulus"] == 1,
            "value-only demo failed to expose the tail residual")
    require(demo["bounded_strategy"]["accepted"], "strategy fixture was rejected")
    require(demo["normalized_trace"]["accepted"], "trace fixture was rejected")

    tex = (ROOT / "paper" / "darc_ipra_framework.tex").read_text()
    for section in re.findall(r"\\input\{([^}]+)\}", tex):
        require((ROOT / "paper" / f"{section}.tex").exists(),
                f"missing LaTeX input: {section}.tex")

    print("Python parse: OK")
    print("JSON Schema and sample plan: OK")
    print("Structural Lean source scan: OK (no sorry/admit/new axiom)")
    print("Claims and generated fixture consistency: OK")
    print("LaTeX input closure: OK")


if __name__ == "__main__":
    main()
