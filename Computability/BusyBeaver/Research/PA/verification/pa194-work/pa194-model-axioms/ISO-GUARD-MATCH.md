# Contextual matching from the Q guard

`PA194IsoGuardMatch.lean` connects the guarded ordinal property Q with the three-variable predecessor-matching template. `isoGuard_match_components` proves the exact typed substitution identity: the guard `domain(b) ∧ orderIso(a,b)` equals the conjunction of the domain and isomorphism components of the fixed predecessor-matching theorem at `(a,b,p)`. Indices are arbitrary model values and are not identified with one another.

`isoGuardMatchProof` takes proofs in a common source context of this guard, `successor(p,a)`, and the closed predecessor-matching theorem; it derives a target predecessor y in the domain, with `successor(y,b)` and `orderIso(p,y)`. `isoGuardMatchProof_val` and `isoGuardMatchGraph_defined` establish the exact code and a single fixed Σ₁ proof-code graph in every candidate-PRA model with IΣ₁ reduct.

The source theory, context, and premise proof codes remain explicit. This can be applied inside the guarded identity-packet invariant; it does not establish the Q successor induction premise, the PA translation/substitution correspondence, closed-formula environment independence, native iPRA internalization, or machine correctness.

Run `bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-axioms/check-iso-guard-match.sh REPO NEW_OUTPUT`. The new source is rebuilt in a fresh output against pinned prebuilt dependencies, including the independently replayed model-indexed predecessor-match application and repository unified syntax. This is not a full transitive source rebuild. A successful run reports four axiom audits with no `sorryAx`.
