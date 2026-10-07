# Source audit and claim boundaries

## Pinned source

Repository: VladimirReshetnikov/ProveIt.
Commit: `588552b79497c93d0e2f3a3f9224fd7681e8d396`.

Files read:

1. `Combinatorics/Ramsey/Lean/GowersSzemeredi/Section16.lean`, blob `c5c7d2bee91bc589de1d3082429f7ee3597e99f9`. Relevant ranges include the controls and multiple-linearity definition; cube-domain and good-domain definitions; the two line-cover count bounds; the width formula; and the complete two-premise `lemma_16_10`. A subsequent default-branch read returned the same blob.
2. `Definitions.lean` in the same directory, blob `97113b7afa6925a2dd4b76641eeaeff09597ab6a`. Full definitions checked: `ModAP`, properness, `IsMultilinear`, `Box`, carrier, width, partition. Properness means cardinality equals formal length; modular wrapping without repetition is allowed by that predicate.
3. `Sections14_15.lean`, blob `5d91dce37bbca59fc76dfd30ec3a485d72ba583c`. Checked `HasProductProperty` and `AxisCube`. Axis cubes are arbitrary pairs of base and side vectors: zero sidelengths are permitted, so the all-cubes witness genuinely yields a full good domain.
4. `Proofs16LocalAffineLift.lean`, blob `03f86c7c8145fe3a1faa13953abb9f0c0bf6cb9e`. Read the complete theorem and its proof. The explicit output index count is r*p0 + r^2*p0^2; it is not identified with the unsupported target bound.
5. `Proofs16ClosingComparison.lean` scope note and the status/search results describing it. These explicitly concern a numerical comparison and do not assert a counterexample to the full implication.
6. The README for the existing merged local quantitative refinements, to distinguish the contribution from existing shared-anchor, phase, energy, cube-count, and restriction work. This was not a line-by-line audit of every earlier research article.

The bibliography contains live links to the pinned files. Source line ranges refer to the pinned source, not to future moving branches.

## Published paper

W. T. Gowers, *A new proof of Szemerédi's theorem*, Geometric and Functional Analysis 11 (2001), 465–588; DOI 10.1007/s00039-001-0332-9. The published pages 574–575 (PDF indices 109–110 in the public UMD copy) were visually inspected, including the closing comparison.

The article deliberately applies its negative theorem to the exact repository abstraction. It does not infer a counterexample to the entire contextual assertion in the original paper merely from a failure of the bundled formulation.

## Central distinctions

- The source catalogue entry is a `Prop`-valued definition, not a Lean theorem proved by the repository. The new manuscript does not allege a Lean kernel inconsistency.
- The old numerical-gap result and the new counterexample are different claims. Failure of a calculation alone would not prove falsity; the new argument verifies both antecedents and bounds every allowed target cover.
- The full good domain is realized by actual all-cube selections and a zero anchor. It is not substituted for the named domain without proof.
- The gamma-side and delta-side graph counts are different. The witness uses qGamma = R and qDelta = 1.
- The example persists at theta = gamma = 1 and at all primes above an explicit threshold. Small outer parameters and finite-modulus defects are not the cause.
- The stronger full-domain product property at gamma = 1 is characterized exactly in the article. It excludes the example, so that upstream property has not been silently assumed.
- The new results do not claim priority for concentration, root bounds, conditional expectation, interpolation, or the endpoint separate-affinity argument. The asserted contribution is their exact cover-profile formulation and source-specific consequence; broader priority has not been exhaustively checked.

## What was executed

The LaTeX was compiled. Exact standard-library Python checks were run for finite cover inequalities, a finite separate-affinity characterization, the F_257 AP-frequency certificate, and a deterministic F_31 construction. The output JSON files are included. The large counterexample is an existence theorem with a deterministic specification, not a computed table of field values.

No Lean build, no independent review, and no repository write was performed.
