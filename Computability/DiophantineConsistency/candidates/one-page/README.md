# A complete equation on one page

[equation.pdf](equation.pdf) contains the complete fifteen-positive-variable
P69 equation, all polynomial abbreviations, all four fixed coefficient
definitions and the full 1,294-digit seed needed by those definitions.
Nothing in its mathematical specification refers to an external table,
program, hash or coefficient blob. It fits on one ordinary letter-size page.
The two source files are [equation.tex](equation.tex) and
[seed-display.tex](seed-display.tex); both are committed.

The constant definitions use fixed finite sums, powers, arithmetic and
integer quotient/remainder, as permitted by the owner. These operations
occur only in fixed constants. After evaluating those constants and
substituting the displayed polynomial abbreviations, the equation is an
ordinary integer polynomial in exactly the fifteen listed unknowns.
Every unknown is strictly positive. Power towers are unnecessary here.

The seed decodes the 430 transition actions; source state and read symbol
are implicit in their index. Twenty-five explicit templates complete the
457 local modes. A quotient formula computes their lexicographic ranks,
so even the ordering is specified by finite arithmetic. The resulting
`beta`, `K`, `MC` and already shifted `MF_source` are byte for byte the
existing whole compact54-sharp tuple. See
[COMPACT54_ARITHMETIC.md](COMPACT54_ARITHMETIC.md) for the derivation and
[COMPACT54_ARITHMETIC.json](COMPACT54_ARITHMETIC.json) for the complete-byte
audit. This changes no coefficient or source convention.

The polynomial formula is the [69-operation P69](../../SHORT_EQUATION.md).
`ShortCircuit.value_zero_iff_baselineValue_zero` proves its full positive
zero-set equality with P67 for arbitrary coefficients with `beta>0`.
The inherited ordinary consistency argument composes the
[P67 proof](../../con-zfc-diophantine-forms/36-small-tuple/proofs/INHERITED_P67_PROOF.md),
the normalized-witness
[Pell audit](../../con-zfc-diophantine-forms/36-small-tuple/proofs/INHERITED_PELL_AUDIT.md),
and the whole compact54-sharp
[native interface](../split116-compact/compact54-sharp/provenance/interface_proof.md).
Thus its no-solution claim has the same ordinary mathematical calibration
as that candidate. The complete native Lean proof and the internal ZFC
consistency biconditional remain open. The page specifies the equation;
it does not contain that proof.

The transport variable is the old positive `z`: its factor is
`(K+w)*C+(q-F)-z*(q-1)`. `MF_source` is shifted by `B-1` exactly once.
All intermediate display symbols are abbreviations, not extra unknowns.

Reproduce from the repository root:

```sh
python3 Computability/DiophantineConsistency/tools/verify_one_page_tuple54.py
python3 -O Computability/DiophantineConsistency/tools/verify_one_page_tuple54.py
python3 Computability/DiophantineConsistency/tools/build_one_page_equation.py --check
```

The first two commands reconstruct and compare every byte of all four
ports. The last builds the committed TeX in a temporary directory, checks
one letter-size page and no overflowing boxes, extracts the complete seed
from the rendered PDF, and compares the generated PDF byte for byte.
It requires `pdflatex`, `pdfinfo` and `pdftotext`. Omit `--check` to regenerate
the PDF, seed display and rendering receipt. Ordinary Mathlib polynomial
semantics and the report's arithmetic-gate accounting remain separate from
the work needed to evaluate the fixed constants.
