# Late novelty correction: H1 and H2 excluded

This note overrides their positive historical decisions in baseline_audit/ and
validation/INDEPENDENT_REVIEW.md. The earlier source checks remain source checks.

The Library packet “Four Further Lean Proof Refinements”, received during the
review, was materialized at version0. Its archive SHA-256 is
bab188a31d586762212096523ab818c9135824b6d443b2a577827bf8759583c4.
All82listed artifact hashes agree. This is an integrity check, not independent
replay of that packet's reported Lean compilation.

Its closing corpus pin is f42d3f94f78eb63639316a33e25f2f69d12c651e and it treats
rounds a–v as prior work. The exact evidence excerpts are retained under
refinements_evidence/. They are another packet's work, not ours.

## H1

Our product-action periodicity argument replaces row_zero_of_helix's signed
induction. The other packet C replaces the identical induction by exhibiting
period1 for s ↦ T(x+w*s)(t-s) and applying Function.Periodic.int_mul_eq. Although
the proof terms differ, both discharge the same global helix orbit transport
by the same existing periodicity machinery. Under the user's semantic exclusion
rule, H1 is not a new proposal. Its9line delta is not credited here.

## H2

The other packet D introduces the same band_quotient_properties theorem retaining
MarkedWord and exact band binding for the literal quotientWord, and reuses it in
marked_word_of_halt and canonicalWord_properties. This is the same mechanism
and helper interface as H2. Its4line delta is not credited here.

## Scope

Keep these two candidate families only as comparison evidence, not as recommended
patches or an alternative route around the prior-applied assumption. Their own
uncompiled status is unchanged. Other-packet compilation evidence does not
validate the differing H1 proof or our local H2 proof bytes.
