# Finite presentations and categorical methods in iPRA

This archive accompanies a mathematical research report responding to the
PrimitiveRecursiveArithmetic collection in Vladimir Reshetnikov's ProveIt
repository. The inspected snapshot is
`bb86091690bc4f920f046a37cfc87719299b4019`.

## Start here

- `paper/ipra_categorical_methods.pdf` is the complete human-readable paper.
- `paper/ipra_categorical_methods.tex`, `paper/sections/`, and
  `paper/references.tex` are its editable LaTeX sources.
- `lean/FORMALIZATION.md` describes the precise endpoint in the repository's
  embedded `Prf PRAAx` calculus and the ordered route to a complete Lean proof.
- `PROOF_STATUS.json` distinguishes mathematical proofs, specifications,
  executable finite checks, and unfinished machine formalization.

## Main mathematical content

1. A compositional framework for finite-demand proof contracts, with explicit
   backward query substitution and quantifier-free induction obligations.
2. Three controlled settings for category theory: fixed primitive recursive
   presentations, uniformly coded finite categories, and external families of
   specified programs and their arithmetic proofs. The paper develops functor
   categories, Yoneda, finite limits and colimits, finite function objects,
   adjunction calculations, and finite Kan extensions.
3. Finite sheaf gluing, a constructive Chinese remainder pullback, and a
   bounded-surjective-lifting theorem for coherent towers.
4. A capped Macaulay-matrix procedure that produces finite multiplication
   certificates and a complete rational-zero list whenever its closure test
   succeeds. It permits redundant generators and noncommuting action matrices.
5. Two explicit computability obstructions: a two-class count does not uniformly
   produce a finite representative cover, and PR-selectable nodes at every
   level of a binary tree do not produce a computable coherent branch.
6. A targeted comparison with the Mordell–Weil, Siegel, Faltings, and Puiseux
   reports, keeping their remaining hypotheses explicit.

## Proof and validation status

The paper supplies human arguments designed for iPRA and states their numerical
encodings, guards, finite bounds, and induction invariants. A human proof is not
a completed Lean derivation. The three `.lean` files are **uncompiled**: a Lean
executable was unavailable in the preparation environment. `ObjectCategory.lean`
contains proposed source expressions whose conclusions are in the actual
embedded arithmetic proof judgement; the larger files are definitions and
targets, not completed proofs of their main theorems.

The four executable Python suites pass using exact integer and rational
arithmetic. These checks cover selected finite instances and catch coding
errors. They do not establish arbitrary-instance correctness, arithmetic
formalizability, or kernel verification. Full results are in `validation/`.

No general iPRA proof of Mordell–Weil, Siegel, or Faltings is claimed. No
algorithm is claimed to extract exact Puiseux branch coefficients from arbitrary
computable Cauchy names. A rejected Macaulay degree cap does not prove the
polynomial system has no rational solutions.

## Reproduce the executable examples

Use Python 3.12 or a compatible Python 3 version; the code uses only the standard
library. From the directory containing this README:

```sh
python3 verify.py
```

This runs `code/check_categories.py`, `code/challenge_contracts.py`,
`code/finite_descent.py`, and `code/macaulay.py`, and writes per-suite JSON and
the combined `validation/reproduction.json`. Tests are deterministic; execution
time and Python version may differ between machines.

## Rebuild the PDF

With a normal TeX Live installation including the standard mathematics packages,
Latin Modern, `microtype`, `tikz-cd`, `booktabs`, and `hyperref`:

```sh
./build_pdf.sh
```

The script makes three LaTeX passes, stops on errors or unresolved references,
and writes logs in `validation/`. It also requires `rg` and Poppler's `pdfinfo`.
It includes a local fallback for a Linux TeX installation whose format files and
font map have not been initialized. That fallback generates `.tex-runtime/`,
which is a reproducible cache and is excluded from the delivered archive.
On another TeX installation one may instead run `pdflatex` three times from
`paper/`; no shell escape, bibliography download, or network access is needed.

## Lean integration

The target repository uses Lean `4.32.0` and Mathlib `v4.32.0`, with the manifest
pin recorded in `provenance/`. Follow `lean/FORMALIZATION.md` in a checkout of the
pinned upstream commit. Preserve its package layout and dependencies. The archive
does not vendor ProveIt or its dependencies, and does not supply a misleading
standalone Lake project that would omit the actual arithmetic calculus.

## Source coverage and reproducibility

`provenance/source_inventory.json` records inspected repository paths, immutable
URLs, Git blob identifiers, and hashes where available. The bibliographic links
in the paper point to primary mathematical sources and the pinned repository.
All twelve foundation READMEs were reviewed, with targeted underlying proof
sections and application reports. This is not a review of all 63 packets.

`provenance/proof_trust_audit.md` and `provenance/category_scope.md` record the
scope of the proof audit. `validation/pdf_quality.json` records the PDF check.
`MANIFEST.sha256` lists the delivered files except itself. The upstream MIT No
Attribution license is preserved in `provenance/ProveIt_LICENSE.txt` for adapted upstream
build conventions and proof-interface examples.
