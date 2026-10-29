# Candidate-PRA comparison for bounded induction

`ParsonsISigmaZeroComparison.comparison` proves in Lean that every actual
Foundation IΣ₀ theorem maps, through the ordered-ring language embedding, to
an actual theorem of the candidate PRA theory. `ParsonsBoundedComparison`
also translates every proof in a newly defined Parsons-style calculus whose
induction rule is restricted to Σ₀ predicates, producing a candidate-PRA
theorem of the universally closed mapped conclusion, with arbitrary free
parameters. `ParsonsBoundedProof.toRule` embeds this smaller calculus into
the existing intermediate rule calculus.

The proof preserves every arithmetic hierarchy level under the language map,
including positivity of bounded terms, and checks that successor-induction
commutes with the map. Candidate-PRA proofs of all PA-minus axioms and
parameterized bounded induction give model validity; soundness and equality
model completeness yield the actual candidate-PRA theorems. The existence
proof is noncomputable in the Lean metatheory.

This is a **bounded-induction** comparison. It does not translate arbitrary
`ParsonsRule.Proof` values, which may use Σ₁ induction, and therefore cannot be
composed with the strict Π₂ endpoint without an additional comparison.
Neither full Σ₁ conservation nor a primitive-recursive witnessing result for
that endpoint is claimed. The completed HA result for the 14-variable PDF
equation is separate.

Two fresh Lean 4.32 builds of all five modules and checks passed without
warnings under `-M6000 -j1 -DElab.async=false`; every object and full log
matches. The six axiom reports list only `propext`, `Classical.choice`, and
`Quot.sound`; no `sorryAx` is reported. The [42-file replay manifest](parsons-bounded-bridge-replay/FILES.json)
has SHA-256 `cc47d8f84eb9dbcbcc378084d9a25d00118efab8b38836eda9ec4bec1a8428c9`.

Each run authenticates 95 candidate-provider parent source/object pairs and
both bounded-induction module pairs against the copied provider manifest
SHA-256 `90d753ea0b20e407c4595abe24d92f1739483b90851d6fea1d2402c9c93f898c`,
before and after compilation. The direct ParsonsRule source and object hashes
are respectively `7fe1dd093fa3ff9585fa37968e0bf75d483b743c9b18fa33c4587a677bb15325`
and `eb5c49e2362e7d7f05b6e7dea5d0f671134657c57f0f09a9ec959f7c01a57ec3`.
Earlier Parsons providers and Foundation/Mathlib are inherited, not a fresh
transitive audit. The parent candidate provider is the independently replayed
`/tmp/pra-bounded-induction-independent-rm8rcvo8/lib`.

An independent replay at `/tmp/parsons-bounded-bridge-build-tyibxsz4` passed
with matching sources, objects and complete logs. Its bounded-induction
provider and the eighty-two-module candidate chain have also since been
independently replayed. The inherited Foundation/Mathlib boundary remains.
