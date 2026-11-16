/-!
# Open bridge completion: exact proof plan

This file is documentation-oriented until placed in the repository, where it
should import `IPRABridge.FoundationToConcise`,
`IPRABridge.ConciseToFoundation`, and the Foundation finite-context
deduction/closure files.

No axiom or opaque bridge theorem is declared here.

Milestones:

1. `codeNormalization`: every Foundation PR construction code is provably
   extensionally equal to `toFoundationCode (toConciseCode c)`.
   Structural recursion handles zero/succ/proj/comp; QF induction handles
   primitive recursion.

2. Lift normalization to terms and equality-only formulas.

3. Compose with `nativeOrderRoundtrip` for the standard language with `<`.

4. Internalize an open finite-context proof as a universally closed implication
   chain, use the existing closed Foundation-to-Concise transport, open the
   variables with `Prf.allOpen`, and apply translated assumptions.

5. Re-export the existing `toFoundation_provable_of_axioms` as the reverse
   open-context theorem specialized to `PRAAx` and `standardTheory`.

Desired public endpoints:

theorem standardToConciseCtx ...
theorem conciseToStandardCtx ...
theorem standard_concise_ctx_iff ...
-/
