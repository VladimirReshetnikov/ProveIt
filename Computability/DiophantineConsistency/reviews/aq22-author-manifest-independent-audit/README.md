# Independent static review of the AQ22 author plan

The static audit passed for the author plan SHA-256
`3c5df040f94803b19ccbed14ec93be2e3de2e16ed9c31efd9bcfb531373200df`.
`audit.py` and `receipt.json` record the checks. The script requires the historical
parent manifest at `/tmp/ipra-aq29-fresh-source-closure-v2/manifest.json` with
SHA-256 `63b846158674d41beeaa99843d92008465f8e0fe5c45bb9e1fed4b78e1a2ab48`.
That local file is an input, not part of this receipt. The audit rejects optimized
Python (`python3 -O` exited 1 before checking any inputs).

The 37 modules are the exact ordered 30-module prior AQ26 and standard-theory
plan followed by seven AQ22 modules. Every row is a tracked regular Git blob at
`bd19027b6835198b97bd58b5d8cb58c1849fcd99`, with the planned SHA-256 and
identical working-tree bytes. The first 30 rows and their diagnostic policies
are equal to the earlier pinned plan. All actual direct source imports are
accounted for and appear earlier in the addition order, in the 1,210-module
parent, or in its declared external modules. No addition shadows a parent
module. The source lists contain 94 `#print axioms` declarations, and all 94
appear in the corresponding planned policy in order. Four simple manifest
mutations were rejected, as shown in the receipt. In a separate check,
`research/adaptive-aq22-proof/check_literal.py` reported that 22 variables,
four ports, and all 114 gates match the pinned AQ22 graph.

The exact final source theorem,
`IPRAStandardAQ22.literal_iff_translated_consistency`, states that
`standardTheory` proves the biconditional between native no-zero for the
positive-shifted AQ22 literal with `CurrentWindowCarry2011.ports` and the
Gödel–Gentzen translation of Foundation's chosen consistency sentence after its
language map. It composes the native equivalence with the selected Foundation
consistency bridge. The model-level `AdaptiveAQ22.shifted_no_zero_iff` gives
both directions for arbitrary natural ports, with the fixed-port corollary
`current_no_zero_iff`. These are statements in the inspected source; this static
review does not itself establish that Lean accepted them.

The author runner separately checks tracked identities, parent guards,
direct imports and their observed hashes, topological order, errors,
`sorry`/`sorryAx`, exact diagnostic names, and the allowlist `propext`,
`Classical.choice`, `Quot.sound` for each reported axiom list. This review
checked those guard provisions in source; it did **not** execute the runner,
produce any diagnostic result, or validate the inherited parent artifacts.
The exploratory AQ22 compile is not a guarded run or an independent peer.
The plan's historical parent/provider and package-transitive/dynamic provenance
limits remain in force. No current-source, untranslated consistency, literal
PDF identity, degree, or global-minimality claim follows from this review.
