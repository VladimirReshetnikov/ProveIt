# Offline proof dependencies

These are exact, unmodified source files from
`VladimirReshetnikov/ProveIt` at commit
`22e75dd6b87b1b199bb08c778d7cf075ae5aae08`.
`DEPENDENCIES_MANIFEST.json` records each original repository path, Git blob
SHA-1, SHA-256, byte count, and mathematical role. The source documents retain
their own historical pins and relative references. The map below resolves the
references needed for the new secondary construction without reproducing old
coefficient archives or generated circuits.

## Reading the twelve-positive-variable proof offline

1. Read `../../positive/POSITIVE_PROOF.md` for the new degree-nine majorant,
   carrier, soundness, completeness, and exact degree. The independent audit is
   `../../proofs/POSITIVE_AUDIT.md`.
2. The authentic complete coefficient interface is
   `../source31/coefficients/COEFFICIENT_PROOF.md`. Its literal tuple, bindings,
   and payloads are under `../source31/signed10/data/`; the precise provenance
   is in `../SOURCE31_MANIFEST.json`. Use all four ports of this one tuple.
3. `34-synthesis_report.tex`, section "A lower degree twelve variable norm",
   gives the uniform inherited positive reduction. The detailed precursor is
   `34-INHERITED_POSITIVE12_PROOF.md`; `34-SHIFTED12_PROOF.md` records the
   source34 change of positive carrier.
4. `24-POSITIVE_AND_PELL_SATURATION.tex` is source24's section as preserved in
   source34. It contains the rational Pell saturation lemma and the sharper
   auxiliary-root bound used by the new proof.
5. `37-positive_section.tex` and `37-POSITIVE_PROOF.md` prove the complete
   change of coordinates `w_old=w+q`. The new proof retains this shift.
6. For the inherited signed-quotient statement, read
   `ORDINARY_BLANK_PROOF.md`, especially sections 2--7. It permits signed
   auxiliary coordinates and proves the needed rank and main-root recovery.
   A normalized strong witness is converted there by
   `i_ordinary=Delta*i_normalized`; this is a proof-only substitution.
7. `FIXED_BLANK_67_PROOF.md` and `PELL_LEMMA_AUDIT.md` supply the normalized
   blank-input interface and exact Pell hypotheses. The half-binomial kernel
   and its positive converse are in `pell_kernel_half_binomial42.md`.
8. The compiler chain is supported by
   `WANG943_LANGUAGE_AND_COMPILER.md`, `WANG943_COMPACT_LAYOUT.md`,
   `BLANK_HELICAL_PROOF.md`, `25-COEFFICIENT_PROOF.md`, and
   `27-COEFFICIENT_PROOF.md`, together with the source31 coefficient proof.
   The old name `WANG943_COEFFICIENTS.md` in the compact-layout note refers to
   the shared language/interface proof archived here as
   `WANG943_LANGUAGE_AND_COMPILER.md`.
9. `KEndpoint215.lean` states the calibrated equivalence between blank
   halting of the literal 215-state machine and ZFC refutation. Its imports
   remain part of the pinned ProveIt development.

`QUARTIC31_PROOF.md` is the separate quartic source used by the new
ten-integer-variable construction. It is included here for provenance, while
the signed source and coefficient data remain under `../source31/`.

This collection makes the direct proof references and principal inherited
interfaces readable offline. It is not a standalone Lean project or a copy of
every historical paper mentioned by those sources. The new results are
ordinary mathematical reductions; the finite arithmetic checks do not replace
the compiler semantics, Pell proofs, or calibrated machine theorem.
