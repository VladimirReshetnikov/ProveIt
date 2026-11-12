#!/usr/bin/env python3
"""Flatten the report and build its PDF using pdflatex; no network access."""
from pathlib import Path
import argparse
import os
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent
APPENDICES = [
    "inherited_choice_basis.tex",
    "inherited_ordinary_bridge.tex",
    "scalar_predecessor.tex",
    "equality_reflection.tex",
    "primitive_recursion.tex",
]


def flatten(text, base):
    def include(match):
        path = (ROOT / match.group(1)).resolve()
        return "\n% BEGIN " + str(path.relative_to(ROOT)) + "\n" + flatten(
            path.read_text(encoding="utf-8"), path.parent
        ) + "\n% END " + str(path.relative_to(ROOT)) + "\n"
    return re.sub(r"\\input\{([^}]+)\}", include, text)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tex-only", action="store_true")
    args = parser.parse_args()
    source = (ROOT / "main.tex").read_text(encoding="utf-8")
    inherited = "\n\n".join(
        "\\input{reference/" + filename + "}" for filename in APPENDICES
    )
    source = source.replace("% INHERITED_APPENDICES", inherited)
    source = flatten(source, ROOT)
    target = ROOT / "ipra_template_free.tex"
    target.write_text(source, encoding="utf-8")
    if args.tex_only:
        print(target.name + " regenerated")
        return
    executable = shutil.which("pdflatex")
    if not executable:
        raise SystemExit("pdflatex is required. Install TeX Live, or use --tex-only.")
    build = ROOT / "build"
    build.mkdir(exist_ok=True)
    env = os.environ.copy()
    env.setdefault("SOURCE_DATE_EPOCH", "1794448719")
    env.setdefault("FORCE_SOURCE_DATE", "1")
    command = [
        executable, "-interaction=nonstopmode", "-halt-on-error", "-no-shell-escape",
        "-output-directory=" + str(build), target.name
    ]
    for pass_number in range(1, 4):
        result = subprocess.run(
            command, cwd=ROOT, env=env, text=True,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT
        )
        (build / ("pass_" + str(pass_number) + ".txt")).write_text(
            result.stdout, encoding="utf-8"
        )
        if result.returncode:
            print(result.stdout[-12000:])
            raise SystemExit(result.returncode)
    shutil.copy2(build / "ipra_template_free.pdf", ROOT / "ipra_template_free.pdf")
    log = (build / "ipra_template_free.log").read_text(encoding="utf-8", errors="replace")
    diagnostics = [
        line for line in log.splitlines()
        if "Warning" in line or "Overfull" in line or "Output written" in line
    ]
    print("\n".join(diagnostics) or "PDF built successfully")


if __name__ == "__main__":
    main()
