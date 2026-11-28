# Three local simplifications of the theta-lift proof of Dirichlet GRH

Open **theta-lift-simplifications.pdf** for the complete mathematical report. Section 2 gives the row construction for local denominators and its second application to the compressed determinant. Section 3 gives the denser family of finite-field labels. Section 4 constructs the sparse infinite places explicitly. Section 5 compares all five existing proposal packages at the pinned revision and explains the verification scope.

## Rebuild

Keep all four TeX files together. With standard TeX Live and Latin Modern installed, run

    latexmk -pdf -halt-on-error theta-lift-simplifications.tex

## Reproduce the checks

The independent Lean modules use Lean 4.32.0 and its standard library. Run from the extracted top-level directory

    lean formal/IntegralPivots.lean
    lean formal/FlagRows.lean
    lean formal/LabelArithmetic.lean
    lean formal/DigitRigidity.lean

The integral-pivot module works with finite evaluation coordinates over a field with a valuation-ring predicate. The row module proves its determinant formula by Laplace expansion. The label module proves arithmetic facts about exponents. The digit module proves injectivity, bounds and modular rigidity for all the finite parameters in the manuscript.

The exact regression examples use Python 3.10 or newer, standard library only. Run with assertions enabled

    python3 checks/check_flag.py
    python3 checks/check_labels.py
    python3 checks/check_places.py

The Lean and Python outputs are in checks/results.txt. The enlarged projector and the application of the local lemmas inside the full GRH project have yet to be compiled. The paper gives the integration arguments and identifies the callers.

## Source correspondence

The source snapshot is VladimirReshetnikov/ProveIt at commit 89d12dd40424f1217fd818d84877b3da52396a3b. Its Analysis/GeneralizedRiemannHypothesis/Lean/grh tree has Git ID 2e133df63d7f4da6b3059c4195324f8e9187ba73, equal to the readable grh tree of lsernau/grh-lean at 72fead102f663d5c7a407964a13dc0cf9d977207. The baseline uses Lean 4.35.0 and Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.

The table in checks/sources.tsv records the exact file hash, line number, line hash and immutable link for 90 anchors in 34 files, including the guide and the TeX sources from all five proposal packages. To verify it against a ProveIt checkout at the revision given above, run

    python3 checks/check_sources.py /path/to/ProveIt

[Base proof verification record](https://math.mit.edu/~drew/shortgrh/)
