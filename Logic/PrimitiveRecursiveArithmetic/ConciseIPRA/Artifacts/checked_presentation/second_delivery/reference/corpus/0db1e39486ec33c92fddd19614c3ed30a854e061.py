"""Assemble the standalone LaTeX paper and optionally compile it."""
import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent


def read(path):
    return (ROOT / path).read_text()


def tex_environment():
    """Use an ordinary TeX installation, or bootstrap missing local caches."""
    env = os.environ.copy()
    probe = subprocess.run(["kpsewhich", "pdflatex.fmt"], capture_output=True, text=True)
    if probe.returncode == 0 and probe.stdout.strip():
        return env
    roots = [Path("/usr/share/texlive/texmf-dist"), Path("/usr/share/texmf")]
    if not all(p.is_dir() for p in roots):
        raise RuntimeError("A configured TeX Live installation is required")
    local = ROOT / "tmp/tex"
    local.mkdir(parents=True, exist_ok=True)
    env["TEXMF"] = "{" + ",".join(str(p) for p in roots) + "}"
    env["TEXFORMATS"] = str(local) + os.pathsep
    env["TEXFONTMAPS"] = str(local) + os.pathsep
    if not (local / "pdflatex.fmt").exists():
        result = subprocess.run(
            ["pdftex", "-ini", "-etex", "-jobname=pdflatex", "-progname=pdflatex",
             "-interaction=nonstopmode", "-halt-on-error",
             "-output-directory", str(local), "pdflatex.ini"],
            cwd=ROOT, env=env, capture_output=True, text=True)
        (local / "initialization.log").write_text(result.stdout + result.stderr)
        if result.returncode:
            raise RuntimeError("Local pdfLaTeX format generation failed")
    maps = [roots[1] / "fonts/map/dvips/lm/lm.map"]
    maps += [roots[0] / ("fonts/map/dvips/amsfonts/" + name)
             for name in ["cm.map", "cmextra.map", "symbols.map", "latxfont.map"]]
    (local / "pdftex.map").write_text("\n".join(p.read_text() for p in maps))
    return env


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--pdf", action="store_true")
    args = parser.parse_args()
    m = json.loads(read("evidence/metrics.json"))["programs"]
    step, control = m["code/checker.py"], m["code/control_zero.py"]
    macros = "\n".join(
        "\\newcommand{\\" + name + "}{" + str(value) + "}"
        for name, value in [
            ("StepBytes", step["normalized_bytes"]), ("StepTokens", step["tokens"]),
            ("StepAST", step["ast_nodes"]), ("ControlBytes", control["normalized_bytes"]),
            ("ControlTokens", control["tokens"]), ("ControlAST", control["ast_nodes"]),
            ("StepSourceBytes", step["source_bytes"]),
            ("StepSourceGzip", step["source_gzip9_bytes"]),
        ])
    rows = [
        ("Matched zero-normal Comp/Tr", "code/control_zero.py"),
        ("Matched raw three-case Eval", "code/control_raw.py"),
        ("Incoming canonical clausal", "code/reference/incoming_clausal.py"),
        ("New uniform Step", "code/checker.py"),
    ]
    table = [r"\begin{center}", r"\small",
             r"\begin{tabular}{lrrrr}", r"\toprule",
             r"Complete checker & Bytes & Tokens & AST & Gzip 9\\", r"\midrule"]
    for label, key in rows:
        d = m[key]
        table.append(label + " & " + " & ".join(str(d[x]) for x in
                     ["normalized_bytes", "tokens", "ast_nodes", "gzip9_bytes"]) + r"\\")
    table.extend([r"\bottomrule", r"\end{tabular}", r"\end{center}"])
    v = json.loads(read("evidence/clausal_verification.json"))
    n = json.loads(read("evidence/native_verification.json"))
    r = json.loads(read("evidence/clausal_review.json"))
    summary = (
        r"\begin{itemize}" + "\n"
        + r"\item Primary clausal suite: " + str(v["checks"])
        + r" standalone-process checks in ordinary and optimized Python; no failures." + "\n"
        + r"\item Explicit-sequent suite: " + str(n["positive_certificates"])
        + r" positive certificates, " + str(n["negative_certificates"])
        + r" negative controls, and " + str(n["translation_roundtrips"])
        + r" complete proof-translation round trips; "
        + str(n["command_line_checks"]) + r" command-line checks." + "\n"
        + r"\item Independent opening audit: " + str(r["semantic_opening_checks"])
        + r" semantic comparisons, " + str(r["targeted_negative_certificates"])
        + r" targeted malformed/capture controls, and one positive smoke check."
        + "\n" + r"\end{itemize}")
    text = (read("source/front.tex").replace("@@METRIC_MACROS@@", macros)
            + read("source/theory.tex")
            + read("source/implementation.tex")
              .replace("@@METRICS_TABLE@@", "\n".join(table))
              .replace("@@TEST_SUMMARY@@", summary))
    for index, path in enumerate(["inherited_choice_basis.tex", "inherited_ordinary_bridge.tex",
                                 "scalar_predecessor.tex", "equality_reflection.tex",
                                 "primitive_recursion.tex"]):
        text += ("\n" if index == 0 else "\n\\clearpage\n") + read("reference/" + path)
    text += read("source/back.tex").replace("@@CHECKER@@", read("code/checker.py").rstrip())
    if "@@" in text:
        raise RuntimeError("Unfilled paper placeholder")
    (ROOT / "report.tex").write_text(text)
    print(f"Assembled report.tex: {len(text.encode())} bytes")
    if args.pdf:
        build = ROOT / "tmp/build"
        build.mkdir(parents=True, exist_ok=True)
        env = tex_environment()
        for pass_number in range(1, 4):
            result = subprocess.run(
                ["pdflatex", "-interaction=nonstopmode", "-halt-on-error",
                 "-output-directory", str(build), "report.tex"],
                cwd=ROOT, env=env, capture_output=True, text=True)
            (build / f"pass{pass_number}.log").write_text(result.stdout + result.stderr)
            if result.returncode:
                raise RuntimeError(f"LaTeX failed; see {build}/pass{pass_number}.log")
        shutil.copy2(build / "report.pdf", ROOT / "report.pdf")
        print("Compiled report.pdf")


if __name__ == "__main__":
    main()
