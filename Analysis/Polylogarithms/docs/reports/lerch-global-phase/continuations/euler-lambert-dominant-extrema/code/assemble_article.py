#!/usr/bin/env python3
"""Assemble a consolidated TeX source from the reviewed modular sections.

Run from any directory. The generated article.tex is the canonical build
input; figures are relative to the package root. No network access is used.
"""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PARTS = [
    "preamble.tex",
    "sections/01_introduction.tex",
    "sections/02_setup.tex",
    "sections/03_global_euler.tex",
    "sections/04_euler_refinement.tex",
    "sections/03_kernel_extrema.tex",
    "sections/04_exact_M2.tex",
    "sections/05_harmonic.tex",
    "sections/06_zero_distribution.tex",
    "sections/07_cohen_extremes.tex",
    "sections/08_bessel_edge.tex",
    "sections/08_computation.tex",
    "sections/09_audit.tex",
    "sections/10_research_agenda.tex",
    "bibliography.tex",
]

def main():
    chunks = ["% Consolidated research article. Regenerate with code/assemble_article.py.\n"]
    for name in PARTS:
        path = ROOT / name
        if not path.is_file():
            raise SystemExit(f"Missing article component: {name}")
        chunks.append(f"\n% ===== {name} =====\n")
        chunks.append(path.read_text(encoding="utf-8"))
    (ROOT / "article.tex").write_text("".join(chunks), encoding="utf-8")
    (ROOT / "main.tex").write_text(
        "% Modular build entry; article.tex is the consolidated equivalent.\n"
        + "".join("\\input{" + name + "}\n" for name in PARTS),
        encoding="utf-8",
    )
    print("Assembled article.tex and main.tex from all required components.")

if __name__ == "__main__":
    main()
