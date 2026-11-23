# Finite graph theory in intuitionistic primitive recursive arithmetic

Open **graph-ipra.pdf** for the manuscript. **theorem-index.tsv** lists the 69 numbered results and the worked six-vertex example, with a PDF page, TeX file and label for each. The manuscript includes a source guide, the finite graph conventions and the object-language formalization plan.

## Contents

- Sections 1–4 give the arithmetic interpretation, degree and walk identities, graph search, spanning forests, cycle spaces and cut spaces.
- Sections 5–9 treat Euler and postman tours, Prüfer coding, matrix–tree formulas, graph operations, reconstruction, automorphism groups and exact spectral results.
- Sections 10–13 cover spherical embeddings, five colours, flows, matching, vertex and edge colouring and the chromatic polynomial.
- Sections 14–17 give effective extremal bounds, Hamiltonian theorems, Tutte and flow polynomials, and the boundary between finite and unrestricted reachability.
- Sections 18–19 give the source guide, reusable ProveIt interfaces, precise proof obligations, and verification results.

## Rebuild the manuscript

Run the following in this directory with pdfLaTeX and the standard AMS, TikZ, geometry, hyperref, enumitem, booktabs and related LaTeX packages installed.

    pdflatex -halt-on-error graph-ipra.tex
    pdflatex -halt-on-error graph-ipra.tex

The entry file includes the source chapters from `tex/`. The theorem index applies to the compiled PDF in this archive. Pagination may differ with another TeX distribution.

## Replay the Lean checks

Use Lean 4.32.0. Run `sh lean/check.sh` from this directory. The script uses a fresh directory for build products and prints the axioms of seven representative theorems. The three standalone modules import only the standard distribution and each other. The exact output is in `validation/lean.txt`.

| File | Checked mathematical content |
| --- | --- |
| `lean/GraphCore.lean` | Totals of endpoint counts, the handshaking identity, bounded scan reflection, adjacency-power positivity and bounded reachability |
| `lean/CutParity.lean` | Parity of degrees and cuts, parity along a walk, and the necessary Euler-trail boundary condition, counting edge occurrences with multiplicity |
| `lean/ColorCert.lean` | Reflection of clique and colouring certificates, distinct colours on a clique, and impossibility of an odd closed walk under a proper binary colouring |

The file `lean/proveit/Incidence.lean` belongs to the ProveIt environment. It includes an object-language digit reader, the row- and column-degree sums, and `LeanProofs.IPRA.GraphIncidence.incidence_closed`, the universally closed internal formula for equality of the totals. Its source interfaces were reviewed at ProveIt commit `bbb85238dac533fc4b7b84a750cca864fe35fed5`. It was not compiled with the full ProveIt dependency tree in this run. To replay it, in a checkout of that commit with its normal Lake dependencies, run these commands.

    lake build IPRADerivations.Core.Fubini IPRADerivations.Core.Division IPRADerivations.Core.Powers
    lake env lean /absolute/path/to/lean/proveit/Incidence.lean

The full paper supplies human iPRA derivations and an implementation plan. The machine-checked standalone modules concern standard finite data in Lean. The separate adapter illustrates the proposed repository-level proof target.

## Replay the independent finite checks

Run these commands with Python 3.10 or newer and assertions enabled. They use the standard library. `validation/` records the outputs from this package.

    python3 code/check_examples.py
    python3 code/check_flows.py
    python3 code/check_rotations.py
    python3 code/check_tree_identities.py
    python3 code/vizing.py

The finite tests cross-check witness constructors and numerical identities. Section 19 gives their scope. The unbounded mathematical claims are proved in the manuscript.

## Repository and source articles

[ProveIt, pinned iPRA directory](https://github.com/VladimirReshetnikov/ProveIt/tree/bbb85238dac533fc4b7b84a750cca864fe35fed5/Logic/PrimitiveRecursiveArithmetic) · [Graph (discrete mathematics)](https://en.wikipedia.org/wiki/Graph_%28discrete_mathematics%29) · [Graph theory](https://en.wikipedia.org/wiki/Graph_theory)
