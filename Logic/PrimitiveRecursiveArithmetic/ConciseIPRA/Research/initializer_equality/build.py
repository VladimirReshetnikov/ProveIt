"""Assemble a standalone TeX source and compile the report."""
from pathlib import Path
import argparse
import json
import os
import re
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent


def evidence():
    seed = json.loads((ROOT / "code/results.json").read_text())
    shared = json.loads((ROOT / "shared_traversal/verification.json").read_text())
    metrics = seed["metrics"]
    old, new = metrics["general_context"], metrics["seed_only"]
    canonical = shared["modes"]["canonical"]
    rows = [
        ("One-template control", old),
        ("Initializer rule (selected)", new),
        ("Initializer rule (explicit guards)", metrics["seed_checked"]),
        ("Canonical R, inherited", canonical["old"]),
        ("Canonical R, shared traversal", canonical["new"]),
    ]
    tex = [r"\begin{center}", r"\small",
           r"\begin{tabular}{@{}lrrrr@{}}", r"\toprule",
           r"Complete module & Tokens & AST nodes & Bytes & Gzip 9\\",
           r"\midrule"]
    for label, m in rows:
        tex.append(f"{label} & {m['tokens']} & {m['ast_nodes']} & "
                   f"{m['normalized_bytes']} & {m['gzip9']}" + r"\\")
    tex += [r"\bottomrule", r"\end{tabular}", r"\end{center}"]
    reduction = old["normalized_bytes"] - new["normalized_bytes"]
    percent = 100 * reduction / old["normalized_bytes"]
    tex.append(f"The matched initializer change saves {reduction} normalized "
               f"bytes ({percent:.4f}\\%), "
               f"{old['tokens']-new['tokens']} significant tokens, and "
               f"{old['ast_nodes']-new['ast_nodes']} AST nodes. "
               f"Gzip-9 grows by {new['gzip9']-old['gzip9']} bytes.")
    (ROOT / "evidence/metrics_table.tex").write_text("\n".join(tex) + "\n")
    (ROOT / "evidence/macros.tex").write_text(
        f"\\newcommand{{\\SeedBytes}}{{{new['normalized_bytes']}}}\n")
    processes = seed["process_checks"]
    assert all(p["expected"] == p["accepted"] for p in processes)
    shared_count = sum(v["process_checks"] for v in shared["modes"].values())
    traversals = sum(v["additional_exact_traversal_comparisons"]
                     for v in shared["modes"].values())
    semantic = sum(v["inherited_semantic"]["independent_evaluation_comparisons"]
                   for v in shared["modes"].values())
    summary = r"""\begin{itemize}
\item The new calculus and matched controls passed %d command-line
checks across readable and normalized sources, under ordinary and
optimized Python, with no mismatch.
\item Thirty closed proof-translation round trips preserved their
conclusions. An additional open-context round trip kept the counter
and body parameters fixed when replacing the initializer.
\item The new syntax passed 180 independent numerical
substitution/evaluation comparisons and explicit nested-counter,
state-capture, and nested-formula capture controls.
\item The separate shared traversal refactoring passed %d process
checks on 86 inherited named cases, %d independent numerical
comparisons, and %d exact old/new traversal comparisons.
\end{itemize}
""" % (len(processes), shared_count, semantic, traversals)
    (ROOT / "evidence/validation_summary.tex").write_text(summary)
    concise = {
        "python": seed["python"],
        "matched_metrics": metrics,
        "matched_byte_saving": reduction,
        "matched_byte_saving_percent": percent,
        "closed_round_trips": len(seed["closed_translation_checks"]),
        "open_parameter_round_trip": seed["open_parameter_translation"],
        "new_cli_checks": len(processes),
        "new_cli_mismatches": 0,
        "new_substitution": seed["substitution"],
        "shared_cli_checks": shared_count,
        "shared_numerical_comparisons": semantic,
        "shared_exact_traversal_comparisons": traversals,
    }
    (ROOT / "evidence/summary.json").write_text(json.dumps(concise, indent=2) + "\n")


def expand(path):
    source = path.read_text()
    source = re.sub(r"\\input\{([^}]+)\}",
                    lambda m: expand(ROOT / m.group(1)), source)
    source = re.sub(r"\\lstinputlisting\{([^}]+)\}",
                    lambda m: "\\begin{lstlisting}\n"
                    + (ROOT / m.group(1)).read_text().rstrip()
                    + "\n\\end{lstlisting}", source)
    return source


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--tex-only", action="store_true")
    args = parser.parse_args()
    evidence()
    (ROOT / "report.tex").write_text(expand(ROOT / "main.tex"))
    if args.tex_only:
        print("Assembled standalone report.tex")
        return
    env = os.environ.copy()
    env["SOURCE_DATE_EPOCH"] = "1794449134"
    env["FORCE_SOURCE_DATE"] = "1"
    with tempfile.TemporaryDirectory(prefix="ipra_tex_") as directory:
        for _ in range(3):
            proc = subprocess.run(
                ["pdflatex", "-interaction=nonstopmode", "-halt-on-error",
                 "-output-directory", directory, "report.tex"],
                cwd=ROOT, env=env, text=True, capture_output=True)
            if proc.returncode:
                print(proc.stdout[-9000:])
                raise SystemExit(proc.returncode)
        log = (Path(directory) / "report.log").read_text()
        warnings = [line for line in log.splitlines()
                    if "Warning" in line or "Overfull" in line or "Underfull" in line]
        (ROOT / "evidence/tex_warnings.txt").write_text("\n".join(warnings) + "\n")
        shutil.copyfile(Path(directory) / "report.pdf", ROOT / "report.pdf")
        if "undefined references" in log or "Citation" in "\n".join(warnings):
            raise RuntimeError("Unresolved TeX reference")
    print("Compiled report.pdf; warnings recorded for visual review.")


if __name__ == "__main__":
    main()
