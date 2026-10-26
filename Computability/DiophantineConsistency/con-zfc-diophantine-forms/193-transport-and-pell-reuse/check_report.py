#!/usr/bin/env python3
"""Bind the printed finite definitions to the independently checked artifacts."""
import importlib.util
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise ValueError(message)


def main():
    report = ROOT / "report"
    spec = importlib.util.spec_from_file_location(
        "report_assembler", report / "build_report.py")
    builder = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(builder)
    standalone = (report / "report.tex").read_text()
    require(builder.assemble(report / "main.tex") == standalone,
            "Standalone LaTeX is stale")
    require(not re.search(r"\\input\{", standalone),
            "Standalone LaTeX has an unresolved input")
    for printed, source in [
        ("P83_definition.tex", "direct/P83_definition.tex"),
        ("coefficient_recipe.tex", "positive/coefficient_recipe.tex"),
    ]:
        require((report / printed).read_bytes() == (ROOT / source).read_bytes(),
                "Printed appendix differs from checked source: " + printed)
    graph = json.loads((ROOT / "positive/whole190.json").read_text())
    table = (report / "circuit.tex").read_text()
    lines = [s for s in table.splitlines() if re.match(r"\d+ & ", s)]
    require(len(lines) == len(graph["source"]) == 118,
            "Printed circuit row count differs")
    symbols = {"+": "+", "-": "-", "*": r"\mathbin{\cdot}"}
    for number, (line, row) in enumerate(zip(lines, graph["source"]), 1):
        name, op, left, right = row
        clean = line.replace(r"\_", "_")
        match = re.fullmatch(
            r"(\d+) & \\texttt\{([^}]*)\} & "
            r"\$\\mathtt\{([^}]*)\} (.*?) \\mathtt\{([^}]*)\}\$ \\\\",
            clean)
        require(match is not None, "Unrecognized printed circuit row")
        actual = match.groups()
        require(actual == (str(number), name, str(left), symbols[op], str(right)),
                "Printed circuit coefficient or operation differs")
    metrics = json.loads((ROOT / "direct/P83/METRICS.json").read_text())
    macros = (report / "direct_metrics.tex").read_text()
    require(r"\newcommand{\DirectVariables}{" + str(metrics["variables"]) + "}"
            in macros, "Printed direct dimension differs")
    require(r"\newcommand{\DirectDegree}{" + str(metrics["exact_degree"]) + "}"
            in macros, "Printed direct degree differs")
    tight = json.loads((ROOT / "direct/P83/TIGHT_HEIGHT.json").read_text())
    exponent = tight["strict_power_of_two_exponent"]
    require(f"2^{{{exponent}}}" in (report / "direct_results.tex").read_text(),
            "Printed direct height bound differs")
    factored = json.loads((ROOT / "direct/factored83/METRICS.json").read_text())
    original_factor_tex = (ROOT / "direct/factored83/factored_evaluator.tex").read_text()
    adjusted_factor_tex = original_factor_tex.replace(
        r"\subsection{An exact factored evaluator for $D_{83}$}",
        r"\subsection{A factored evaluator for the same polynomial}")
    require((report / "factored_evaluator.tex").read_text() == adjusted_factor_tex,
            "Printed factorization subsection differs")
    direct_text = (report / "direct_results.tex").read_text()
    require(f"{factored['live_binary_gates']:,}".replace(",", "{,}") in direct_text,
            "Printed preferred operation count differs")
    require(r"\(64\)" in direct_text and factored["largest_absolute_literal"] == 64,
            "Printed preferred literal bound differs")
    require((report / "report.pdf").read_bytes().startswith(b"%PDF"),
            "Compiled PDF is missing or invalid")
    print(json.dumps({
        "status": "PASS",
        "standalone_tex": "exact recursive assembly",
        "positive_literal_rows_parsed": 118,
        "direct_appendix": "byte identical to coefficient-checked definition",
        "coefficient_recipe": "byte identical to reconstructed tuple specification",
        "printed_direct_variables": metrics["variables"],
        "printed_direct_degree": metrics["exact_degree"],
        "printed_height_bound_exponent": exponent,
        "preferred_factored_operations": factored["live_binary_gates"],
    }, indent=2))


if __name__ == "__main__":
    main()
