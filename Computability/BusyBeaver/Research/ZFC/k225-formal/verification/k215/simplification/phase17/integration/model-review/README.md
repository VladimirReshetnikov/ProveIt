# Phase17 model and logic source review

Reviewed frozen main `140d832128fd43873f16e385766cd3cee08df8a9` against the
checked phase16 branch checkpoint `d3ff74a6fadba99e05576fe844f1f5ace9eab648`.
The complete 4,682-line model diff covers 48 paths: 46 extant modules and two
retirements. These paths contain 659 fewer Lean lines in total. The full
[scope and hashes](scope.json), [diff](model.diff), and detailed
[review](review.json) bind the review to exact Git source bytes.

No mathematical blocker was found. This is a source review; it does not claim
Lean compilation, endpoint acceptance, or a smaller Turing machine.

## The direct seed argument

Commit `ff928ef0ec` replaces the equality-free semantic encode/decode route and
indiscernibility quotient with a named bundle on the original model. For any
named matrix `ψ`, including literal equality, it uses `m = ¬¬ψ` and chooses
`k = enc(th m)`. The proof of `1 < k` avoids the input/output labels 0 and 1.
The implications `Free i m → Free i (th m)` and `Free i f → i < enc f`
show that `k` is fresh in `m`.

The equality interpretation commutes through the named bundle only to establish
code derivability. The hypothesis that the original model satisfies every
`DerivableNF` supplies satisfaction of that named bundle itself, preserving
literal equality in its matrix. The named semantic normalization proves the
seed property from freshness and distinct role labels. It does not transport
literal equality from an indiscernibility quotient or require an extra semantic
schema. The endpoint retains irreflexivity as a separate `FullSeed` field and
passes the original inhabitant `e 0` to the subsequent lower chain.

Seven complete declarations move unchanged to `KSeedInterface222`:
`negNF`, `reqNF`, `closNF`, `bundleNF`, `enc_bundleNF`, `DerivableNF`, and
`FullSeed`. The [complete-body comparison](moved-constants.json) removes comments
and whitespace before comparing. The `KIndisc222.FullSeed` name remains available
to the lower chain. The two old modules are absent, and their maintained imports
have migrated. The [caller census](seed-callers.txt) spans all four maintained
Lean roots.

## Other reviewed changes

The constructibility, finite-set, inductive-attempt, ordinal/rank/order,
positive-closure, profile/composition, named semantics, and well-founded model
changes shorten proof terms. They preserve their explicit source statements,
definitions, formula-indexed resources, and premise restrictions. The
[header comparison](declaration-header-delta.json) finds no changes to the
explicit headers of declarations present on both sides. It supplements the
hunk review and does not establish elaborated implicit parameter identity.

Commit `a7b8f1ae67` shortens the strong trace, literal subset representative, and
quotient container proofs. The raw membership guards and explicit inhabitant
remain. No raw irreflexivity is transported across bisimilarity. These changes
combine with phase16's twelve unused strong wrapper retirements and the inline
weak trace instance. Retaining that inline requires the explicit `PowerSyntax`
import in `QuotientModel`.

The [static scan](source-scan.json) finds no `sorry`, `admit`, custom `axiom`,
`unsafe`, `native_decide`, `implemented_by`, `extern`, or `skipKernelTC` tokens
outside comments in these 46 extant reviewed modules. This is a narrow source
scan, not an axiom audit of their transitive dependencies.

## Additional prepared simplification

The root agent requested exact candidate copies after the review identified two
small removable helpers. The [candidate diff](candidate.diff) and
[before/after map](candidate-map.json) bind four complete source copies under
`candidate/` to frozen main.

* Inline `fullSeed_direct_of_derivable` at its only semantic caller,
  `KEndpoint.c222_of_zf_refutation`, as
  `have hfull : FullSeed mem := ⟨hirr, seed_direct mem hT⟩`.
* Remove the one-use duplicate `KLower.seedProp_congr` and use the existing
  equivalence `(KSeed222.seedProp_congr mem A key).mp hs`.
* Update the endpoint's documentation reference and remove stale interface prose
  about optional quotient routes.

These four candidate files remove 18 further lines and 690 bytes. They have been
read in full but remain uncompiled. The recursive freshness facts, named closure
normalization, and small reusable semantic freshness lemma are retained because
they explain the direct argument and avoid duplicating inductions or binder
calculations.

The combined source needs a fresh closure build, typed clients for generic
`seed_direct`/`FullSeed` and native equality, and endpoint/API axiom audits.
Phase16 evidence must not be reused as acceptance of changed source modules.
No compilers, generators, supplied scripts, canonical files, Claude's worktree,
Git references, or external messaging were touched by this review. One inert
metadata script failed in its final summary print after writing its outputs;
separate readback verified the files. It was not a Lean or candidate failure.

The root-authored `DirectSeed17Api` client was also read in full. Its original-domain
constructor, native equality `x = y` orientation, absence of `hirr`/`EqFree` in the
equality seed instance, and existing `FormSeed` composition pass source review.
The [client review and exact hash](typed-client-review.json) await the same root
compilation; the client bytes are retained under `clients/`.
