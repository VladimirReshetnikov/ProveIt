# Separate review of the relative iPRA argument

This memo records a separate assistant review pass within this research. It is not external human peer review.

Reviewed 2026-11-14 against the final `report/relative_preservation.tex`,
`report/ipra_transfer.tex`, the PA194AX11QH command and literal-runtime
checkers, and the pinned primary source at commit
`1c9524d8bf2e0a27b9a16ff622359927f536e663`.

## Conclusion

After the repairs described below, I find the **ordinary written proof of the
relative result** mathematically supported:

\[
\mathrm{iPRA}\vdash\operatorname{Halt}(M_0)
\leftrightarrow\operatorname{Halt}(M_1),\qquad
\mathrm{iPRA}\vdash\operatorname{NH}(M_0)
\leftrightarrow\operatorname{NH}(M_1).
\]

Here `M0` is the primary PA194 table with dense SHA-256
`4bfea62b17aad7d8c8c5e682fe8942e0a86b93e4351f8e675e32705bdaae007f`,
and `M1` is PA194AX11QH with dense SHA-256
`19e215df20429fa6a35f0a99ba0dcfcb40893a6e4b9a4ae6e450b0225f110e50`.

This is a review of a written mathematical argument with finite executable
certificates. It is **not a new kernel-checked derivation in iPRA**, and it does
not establish either machine's absolute equivalence to `Con(PA)`. The latter
still needs the internal PA-to-numerical-calculus calibration identified in
the paper. No relative equivalence can supply that missing premise.

## Material issues found and repaired

1. **A source HALT leaf is still a live physical frame.** The earlier frame
   description incorrectly risked treating it as a physical halted state.
   The final construction distinguishes an unexecuted HALT instruction from
   an absorbing executed-halt tag. The tag preserves the prehalt configuration;
   its frame is the actual endpoint of the certified positive halt segment.
   This makes the halt correspondence, including its final tape, exact.

2. **A frame needs more than the nine registers and source PC.** Header padding,
   signed header location and a nonempty tagged spare list are now explicit
   ghost fields, with deterministic updates and a quantified initial invariant.
   The command-to-source proof uses the unaugmented source; the separate
   lift/forget proof connects it to the augmented source. No history-dependent
   ghost state is silently reconstructed from the scheduler store.

3. **Uniform proof compilation needs a permitted induction predicate.** The
   final proof sets leaf height to one, uses the capped height parameter
   `min(k,D)`, and bounds the proof code and all recursive-call stores. Its
   finite-word evaluator is primitive recursive. The induction predicate is
   therefore a primitive-recursive characteristic-function equation, rather
   than an unbounded assertion about every stack. The shrinking store budget
   is sufficient because completed recursive calls restore their protected
   stack. It does not purport to bound all internal AX constructor values.

4. **Generic list and arithmetic inductions needed their weak-base form.**
   The final text fixes the coded input list or initial registers and inducts
   on a prefix length or drained-unit count. This avoids silently importing
   the stronger quantifier structure of reference Lean proofs that were
   written with generalized parameters.

5. **Abstract macro names were insufficient to identify source semantics.**
   The final proof supplies clean-workspace contracts and exact cutpoints.
   Its 190-token AX plan checks all actual resolved rows and successors,
   including every structured break/continue exit. The 133 named occurrences
   match nine primary helper prototypes; 57 are literal increments. The
   contracts correctly distinguish push-and-copy composites from plain
   addition, and include the gate's deliberately nonclean intermediate state.

6. **The remaining source also needed an exact binding check.** I added and
   ran `check_outside_ax_rows.py`, with result `proof/OUTSIDE_AX_BINDING.json`.
   It checks all 140 retained non-AX rows and every target, the exact deleted
   MP dummy-push interval `[3634,3653)`, the retained success copy at new site
   3652, dispatcher targets, and the nine new Shift-prefix rows. Together
   with the AX intervals, these cover all 3,671 candidate source sites.

7. **Two different destructive comparisons have different clocks.** The
   final text gives both gate clock `K` and MP clock `J`; the latter has
   `J(0,0)=2` because equality exits directly. The new H-only Shift is a
   clear-T loop followed by copy-H, then the inherited comparison. Its
   halting cost is `2t+7h+11` when `h=1`; its normal prefix costs
   `2t+9h+10`. The exact extra AX field is consumed by the full MP reader,
   and both zero and positive values are accounted for.

## Positive findings and verification scope

The numerical command algebra was checked separately, including the Cantor
zero alias, trailing zero proofs, arbitrary carried stores for the refutation
word, the protected stack used by MP compilation, and early halting when a
premise or conclusion is one. The primary Discard word is correctly restricted
to the zero-offset/zero-cache inputs actually used by its compiler.

The scheduler argument supplies a concrete code for a halting command word
and the primitive-recursive command bound `(n+2)^2`. The positive-segment
transfer proposition supplies both halting-witness directions by
quantifier-free induction and bounded search. It requires no Markov principle
or semantic soundness assertion for the numerical calculus.

I inspected and independently reran the AX transplantation generator and
the added non-AX row checker. I inspected the literal symbolic engine's
three operational rules and the recorded runtime evidence; the full literal
replays are documented by the separately produced receipts. The physical
argument relies on the mathematical soundness of those explicit rules and
finite row calculations, not on a claimed proof-assistant certificate for
the Python checker.

The restricted-implication exchange certificate, numerical proof translation,
command compilers, source contracts and physical simulation now form a
coherent relative proof. My review found no remaining mathematical
counterexample or unacknowledged calibration premise in that relative chain.
The remaining limitations are the absence of a newly compiled internal
kernel proof and, decisively for the original task, the unresolved absolute
`Con(PA)` calibration.
