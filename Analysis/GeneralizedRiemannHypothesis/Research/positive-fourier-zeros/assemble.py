#!/usr/bin/env python3
"""Assemble the collected papers. Pass --compile to rebuild each PDF first."""
import argparse
from pathlib import Path
import subprocess
import pymupdf as pdf

ROOT = Path(__file__).resolve().parent
PARTS = [
    ("overview/guide", "Reading guide", "Guide", None),
    ("steinerberger/support", "The sharp Fourier support radius", "I", "Support radius"),
    ("square_gaps/squares", "Zero-free intervals for square frequencies", "II", "Square frequencies"),
    ("global_endpoint/endpoint", "Sharp localization at Dirichlet zeros", "III", "All Dirichlet zeros"),
    ("kozma/gaps", "The three-frequency gap problem", "IV", "Three frequencies"),
    ("ring_density/frobenius", "Frobenius rank and progression-free density", "V", "Finite rings"),
    ("graph_onset/onset", "The onset of the spanning-tree law", "VI", "Graph towers"),
]

def assemble(recompile):
    volume = pdf.open()
    outline, labels, starts = [], [], []
    for basename, title, part, guide_label in PARTS:
        stem = ROOT / basename
        if recompile:
            for _ in range(2):
                subprocess.run(["pdflatex", "-interaction=nonstopmode", "-halt-on-error",
                                stem.with_suffix(".tex").name], cwd=stem.parent, check=True)
        with pdf.open(stem.with_suffix(".pdf")) as source:
            offset = len(volume)
            volume.insert_pdf(source, links=False)
            outline.append([1, title, offset + 1])
            outline.extend([level + 1, label, offset + page] for level, label, page in source.get_toc())
            labels.append(dict(startpage=offset, prefix=part + "–", style="D", firstpagenum=1))
            if guide_label:
                starts.append((guide_label, offset))
            # Resolve each paper's local named destinations before merging. LaTeX
            # reuses names such as section.1 across independent documents.
            for i, page in enumerate(source):
                for link in page.get_links():
                    rect = link["from"]
                    if link["kind"] == pdf.LINK_URI:
                        volume[offset + i].insert_link({"kind": pdf.LINK_URI, "from": rect, "uri": link["uri"]})
                    elif link["kind"] in (pdf.LINK_GOTO, pdf.LINK_NAMED) and link.get("page", -1) >= 0:
                        local = link["page"]
                        position = link.get("to", pdf.Point(0, 0))
                        if link["kind"] == pdf.LINK_NAMED:
                            position = position * source[local].transformation_matrix
                        volume[offset+i].insert_link({"kind": pdf.LINK_GOTO, "from": rect,
                            "page": offset+local, "to": position, "zoom": 0})
    cover = volume[0]
    for label, dest in starts:
        rectangles = cover.search_for(label)
        if not rectangles:
            raise ValueError(f"Missing contents entry {label}")
        cover.insert_link({"kind": pdf.LINK_GOTO, "from": rectangles[-1], "page": dest,
                           "to": pdf.Point(0, 0)})
    volume.set_toc(outline, collapse=1)
    volume.set_page_labels(labels)
    volume.set_metadata({"title": "Positive averages and prescribed Fourier zeros",
                         "subject": "Six mathematical research notes extending ProveIt"})
    output = ROOT / "positive-fourier-zeros.pdf"
    volume.save(output, garbage=4, deflate=True)
    print(f"Wrote {output.name} ({len(volume)} pages).")

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--compile", action="store_true", help="recompile all papers with pdfLaTeX")
    assemble(parser.parse_args().compile)
