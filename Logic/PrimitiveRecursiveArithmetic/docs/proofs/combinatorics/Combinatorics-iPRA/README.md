# Finite combinatorics in intuitionistic primitive recursive arithmetic

Open **combinatorics.pdf** for the manuscript. The editable entry point is **combinatorics.tex**. Keep its chapter files in the same directory. The table of contents, the two-page index of proved results, and internal theorem references are clickable.

## Contents and scope

The 77 numbered result groups include direct answers to questions in the starting article, statements located on its immediate linked pages, and further theorems proved from the same finite constructions. Many groups include several identities or corollaries. The source map identifies which relationship applies and explains grouped results. Scope includes finite and coded rational structures, primitive recursive numerical word sequences, and specific analytic estimates with explicit rational precision data.

- `sources/direct-links.tsv` records 276 distinct section/anchor/URL triples (229 distinct targets) from the introduction, article body, captions and See also of English Wikipedia’s *Combinatorics*, revision 1384635198. Article links are drawn from `/wiki/` targets with readable anchor text. Bibliographic lists and navigation templates are outside the inventory.
- `sources/theorem-map.tsv` connects each numbered group to the root or an immediate outgoing target. The “topic extension” designation indicates that the link anchors the mathematics and the paper develops a related result. It does not assert that the destination states that result. Rows follow the numbered statements in the PDF and include page numbers.
- `lean/` contains five standalone kernel-checked files and one optional upstream integration file. `validation.txt` records the runs. No standalone file uses `sorry` or `native_decide`.
- `checks/` contains independent bounded experiments. They exercise the constructions on small inputs and cross-check representative numerical results. The quantified proofs are in the paper and, for the identified endpoints, the Lean files.

## Rebuild

Use pdfLaTeX with a standard recent TeX Live installation, including Latin Modern, AMS packages, TikZ, titlesec, and hyperref. Run in this directory:

```sh
pdflatex -halt-on-error combinatorics.tex
pdflatex -halt-on-error combinatorics.tex
```

## Verify

Use Lean 4.32.0 and Python 3.10 or later. No external Python package or Mathlib checkout is required for the standalone checks.

```sh
python3 verify.py
python3 verify.py --python-only
```

`--lean /absolute/path/to/lean` selects a specific Lean executable. The five checked files concern bounded search, a word-counting derivation in a small equational fragment, handshaking, Kirkman’s schedule, and the Thue–Morse word. The optional `lean/ProveItEndpoints.lean` is a list of actual source names for integration with the pinned ProveIt checkout and is excluded from `verify.py`. Its build command is in the file. A full ordinary `Prf PRAAx` derivation for every chapter remains future work. Section 15 gives the object-logic targets and proof strategy.
