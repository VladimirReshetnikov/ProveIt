# Proposed ProveIt integration

Suggested **new research-only** directory:

```text
Combinatorics/Ramsey/Research/GowersSzemeredi/
  local-quantitative-refinements/exact-odd-order-cube-stability/
```

Copy the package into that directory. The article has no relative dependency on the predecessor's source and uses an inline bibliography, so it can compile independently.

Add a research-index entry such as:

> Exact Odd-Order Cube Stability — exact parity-corrected complement identity; proof of the small-distance odd-order cubic-profile conjecture; weighted extension, equality classification, and quantitative rigidity. Human-readable research draft with exact finite verification scripts; not kernel-checked.

After reconciling the predecessor's actual repository location, add a note near `conj:oddexact` pointing to Theorem 1.1 of the new manuscript. Preserve the historical statement of the conjecture rather than silently replacing it. The source-provenance mismatch recorded in `SOURCE_AUDIT.md` should be resolved before assigning the predecessor a commit-pinned citation.

Do **not** change formalization status to “proved in Lean/Rocq” based on this package. The verification scripts are exact finite tests, not proof-assistant proofs. No `.lean` or `.v` stubs are included.

## Formalization roadmap

1. Encode the finite cube incidence data and prove the 256-pattern nonnegative certificate.
2. Prove affine reindexing for unimodular matrices and the determinant-two parity count.
3. Prove the weighted multilinear extension with positional variables.
4. Derive the exact defect identity and the polynomial small-distance estimate.
5. Port the weighted boundary argument, energy rounding, and uniqueness lemma.

A clean formalization can import finite-sum infrastructure without importing any unproved global progression theorem. The article's proof-dependency appendix identifies this separation.

No repository write, branch creation, pull request, or status change was performed during the preparation of these files.
