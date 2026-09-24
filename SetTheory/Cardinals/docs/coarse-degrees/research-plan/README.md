# Turing Degrees: A Unified Research Report

Second edition: 18 September 2026, revised after research round 1.

This package integrates the three reports supplied in Turing.zip. It includes
43 consolidated research topics, three separately marked bounded programmes,
the complete proposed tower-padding arguments, diagnostic lemmas, a shared
formalization audit, one bibliography, and an input-to-output crosswalk.

## Changes in the second edition

Round 1 (nine reports, `../research-reports/01`-`09`, merged in
`../research-synthesis/Turing_Degrees_Synthesis.pdf`) settled the first
edition's target C1 negatively; the bare answer already followed from
Hirschfeldt-Jockusch-Kuyper-Schupp (2016). Accordingly:

- C1 is retired as a target. Its results are kept only as a list of established
  tools (K1-K7) at the head of the coarse section, with pointers to the
  synthesis. The identifier C1 is not reused.
- C2 (effective-dense least representatives) is re-triaged from E to B, with
  the obstruction found in round 1 and a line of attack whose one gap is
  stated explicitly.
- Five follow-on topics are added: C4 (every countable Turing ideal as a core;
  proof sketch, tier V), C5 (minimal elements and the shape of coarse spectra),
  C6 (arithmetical bounds for exact partners; a 0'' bound is sketched),
  C7 (sparse-disagreement minimal pairs below 0'), C8 (uniform coarse classes).
- The protocol gains a "status audit by derived consequence" step, and the
  B ratings of M1 and M3 are made conditional on it.
- A new context section, "Turing degrees, large countable ordinals, and large
  cardinals" (Section 12), covers the hyperarithmetic hierarchy, the invariant
  omega_1^X, higher-type functionals and master codes, well-ordering principles
  and the Veblen functions, determinacy and the Martin measure, and Martin's
  conjecture as the junction of the two hierarchies. It adds no catalogue
  entries; its directions (O1)-(O5) are unaudited. It was written largely from
  memory, and its verification box says which statements were checked.
- New evidence code S26: a topic arising from the round-1 synthesis, not a
  literature-listed open problem.

The proposals under C2, C4 and C6 are unreviewed.

## Files

- turing_degrees_unified.tex: self-contained editable LaTeX source.
- turing_degrees_unified.pdf: compiled report.
- source_crosswalk.csv: all 60 original numbered entries plus three programmes,
  and five rows (source S) for the topics added from the round-1 synthesis.
  The row C,P05,C1 is kept as the historical mapping of the retired entry.
- build.sh: reproducible PDF build command.
- checks/: the two inherited Python check programs and freshly generated results.
- validation.txt: document checks and the scope of verification.

## Build

Use a standard TeX Live installation with pdfLaTeX, latexmk, Latin Modern,
AMS packages, geometry, booktabs, longtable, tabularx, microtype, enumitem,
xcolor, fancyhdr, listings, xurl, titlesec, hyperref and bookmark.

Run `./build.sh`, or run:

    latexmk -pdf -interaction=nonstopmode -halt-on-error turing_degrees_unified.tex

No external bibliography processor or image assets are required.
No font binaries are distributed.

## Run the finite checks

Requires Python 3.10 or later, standard library only:

    python3 checks/check_padding.py
    python3 checks/finite_checks.py

The tests check only finite combinatorial identities and examples. They do
not prove the infinite tower claims, settle published questions, certify
novelty, or constitute Lean verification. The report is explicit about the
weak-tower convention issue and the absence of an independently reviewed
or Lean-checked proof. Original software audits are inherited source
inspections; no Lean build was performed for this synthesis.

The three original PDFs and unrelated source-package metadata are not
duplicated here. Their provenance and entry mappings are in the report.
