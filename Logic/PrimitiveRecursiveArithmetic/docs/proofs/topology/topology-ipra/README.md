# Topology in intuitionistic primitive recursive arithmetic

Open **topology.pdf** for the 54-page manuscript. The contents page links to the proof families. The index on the final two pages links to all 64 numbered theorems, lemmas, propositions, and corollaries. The text also derives unnumbered consequences, including the calculation of the fundamental group of a product of circles.

The numerical theory is first-order intuitionistic logic with defining equations for primitive recursive functions, successor axioms, and quantifier-free induction. The finite results are uniform in the sizes of the input tables. Statements involving infinite spaces specify fixed algorithms for names and any required moduli or open-cover data. Section 13 maps the proved formulations to Wikipedia's *Topology* article and its linked topics.

## Contents

- **topology.tex** and **src/** are the complete editable source of the main manuscript. Its two illustrations are generated directly by LaTeX.
- **lean/GridWinding.lean** contains candidate Lean 4 proofs of integer telescoping on a strip and a cylinder.
- **lean/ObjectGrid.lean** expresses the same computation as a candidate family of derivations in ProveIt's object language, with a separate proof term obtained for each external rectangle size. Section 12 explains how to make the dimensions internal numerical variables.
- **code/** contains seven independent finite and rational regression programs. They exercise finite topology, grid separation and winding, cone-direction search, metric and Cantor calculations, surface and persistence computations, knot diagrams, and subgroup folding.
- **check.py** replays the tests and verifies the Git blob hashes of the credited materials.
- **validation/** contains results from this build. The counts refer to test inputs and computations, not to the number of mathematical theorems.

## Three credited mathematical companions

These are previously written ProveIt reports at commit **6d03f3643ebb91a6243eb1e35e7599b388197786**. Each directory below contains the repository PDF, its complete LaTeX manuscript and supporting Lean and Python files. Section 11 of the main manuscript explains the results and hypotheses.

| Directory under companions/ | Paper | Length |
| --- | --- | --- |
| dimension_invariance_ipra/ | dimension_invariance.pdf | 18 pages |
| approximate_brouwer_ipra/ | brouwer.pdf | 9 pages |
| hairy_ball_ipra/ | hairy_ball.pdf | 14 pages |

The general_topology_ipra_2026_11_19/ directory contains four selected Lean modules from the earlier general-topology packet. The original README files in the three mathematical companions describe their upstream packets. The exact subset reproduced here is listed in **upstream.json**, including each original path and its Git object ID. All 42 copied files were verified against their pinned Git blobs. The main manuscript and its two Lean source files are separate work.

## Reproduction

With a standard TeX Live installation, run the following in this directory.

    latexmk -pdf -interaction=nonstopmode -halt-on-error topology.tex

Run the numerical tests with Python 3.10 or later, using its standard library.

    python3 check.py

For only the seven main test programs, use the following.

    python3 check.py --main-only

## Lean verification status

The two new Lean sources were **not compiled in this environment**. The embedded iPRA derivation of the entire manuscript remains a formalization plan. Its arithmetic representations, quantifier-free invariants, and remaining proof obligations are given alongside the human proofs and assembled in Section 12.

To check the new sources, use Lean 4.32.0 and the ProveIt checkout pinned above. GridWinding.lean needs only the Lean distribution. For ObjectGrid.lean, run the second command from a prepared ProveIt workspace with IPRADerivations built, replacing the sample path.

    lean lean/GridWinding.lean
    lake env lean /absolute/path/to/topology-ipra/lean/ObjectGrid.lean

The upstream general-topology packet reports checking the four selected semantic Lean modules with 4.32.0. The Brouwer and hairy-ball packets report checks of their stated partial results with 4.19.0. The dimension companion identifies its Blueprint.lean as a documentation-only outline. These historical checks were not rerun here. The numerical test suites for all three mathematical companions were rerun.

## Sources

- https://en.wikipedia.org/wiki/Topology
- https://github.com/VladimirReshetnikov/ProveIt/tree/6d03f3643ebb91a6243eb1e35e7599b388197786/Logic/PrimitiveRecursiveArithmetic
