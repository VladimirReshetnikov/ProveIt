# Sparse Disagreement and Turing Minimal Pairs

Research manuscript prepared for Vladimir Reshetnikov, 18 September 2026.

Start with `coarse_minimal_pair.pdf`; its complete source is
`coarse_minimal_pair.tex`.

## Mathematical result

For any oracle Z and any computable, nondecreasing, unbounded integer budget b,
the manuscript gives a finite-extension construction of sets A,B <=_T Z'' such
that both are individually 1-generic relative to Z, their disagreement count
below every n is at most b(n), and every total function computable from both
Z join A and Z join B is computable from Z.

Taking Z empty and b(n) = floor(log2(n+1)) gives two coarsely equal sets forming
a nonzero Turing minimal pair. Their common uniform and nonuniform coarse
classes have no least Turing degree, even when natural-valued representatives
are allowed. The construction does not make the two sets mutually generic.

Further results proved in the manuscript:

- Uniform and nonuniform coarse classes at the same function have exactly the
  same Turing representative spectrum, already realized by actual coarse
  descriptions. This spectrum is upward closed.
- Every Turing degree occurs as the unattained infimum of such a spectrum,
  with two representatives below the corresponding double jump witnessing
  that exact infimum.
- A coarse class has a least Turing degree exactly when it lies in the image
  of the manuscript's nonuniform robust block-code embedding.
- The sparse disagreement set has no computable density-zero cover (relative
  to the chosen base oracle), despite its explicit computable counting bound.

## Status and limitations

The target is C1 of the supplied `turing_degrees_unified.tex`, corresponding to
the coarse instance of Gerdes's Question 7. A literature check shows that the
negative answer to the literal least-degree question already follows from
Hirschfeldt--Jockusch--Kuyper--Schupp, *Coarse Reducibility and Algorithmic
Randomness* (2016), Theorem 4.2. No priority claim is made for that negative
answer. The present main construction is independent of that theorem.

The precise quantitative minimal-pair construction was developed for this
manuscript; the searches performed did not establish whether it is new.
Complete conventional proofs are supplied, but they have not been independently
refereed or checked by a proof assistant. No Lean formalization is claimed.

The oracle pseudocode requires Z'' decisions. The Python program checks finite
lemmas, not the actual infinite sets or the arithmetical decisions. It is not
a computable generator of generic sets or a finite simulation that certifies
minimal-pair existence. Effective-dense questions C2 and C3 are not solved.
The absence of a least representative is not a claim that there are no minimal
representatives.

## Files

- `coarse_minimal_pair.tex` and `coarse_minimal_pair.pdf`: manuscript.
- `checks/check_finite_lemmas.py`: standard-library Python finite checker.
- `checks/results.json`: the actual successful check output.
- `checks/document_validation.json`: PDF page count and document-validation scope.
- `build.sh`: rerun checks and compile the manuscript.
- `proof_audit.md`: claim-by-claim proof dependencies and critical boundaries.
- `source_ledger.md`: source provenance and novelty-search limitations.
- `source_material/turing_degrees_unified.tex`: unchanged supplied input.

## Reproduce

Requirements: Python 3.10 or later; a TeX installation providing pdflatex and
the standard packages used by the source. `latexmk` is preferred but optional.
No third-party Python dependencies are needed.

```sh
bash build.sh
```

The command runs the checks, writes `checks/results.json`, builds the PDF,
and places TeX intermediate files in `.build/`. To use another build directory:

```sh
BUILD_DIR=/tmp/coarse-pair-build bash build.sh
```

For the finite checks alone:

```sh
python3 checks/check_finite_lemmas.py
```

The final distributed PDF was compiled and rendered for visual inspection.
No font binaries, TeX intermediates, or uncompiled placeholder Lean files are
included. Embedded PDF fonts are part of the PDF, not separate font files.
