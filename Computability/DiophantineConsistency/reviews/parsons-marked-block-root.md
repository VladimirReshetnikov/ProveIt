# Principal induction-block cases in the marked invariant

`ParsonsMarkedBlock.parameter_root` identifies the principal LK existential
conclusion with the marked parameter block. `parameter_case` opens one
parameter witness, updates the exact `ParsonsBlock.State`, retains the same
marked side projection, and invokes its explicit local recursive hypothesis
on the actual cut-free premise at strictly smaller height.

`counter_case` handles the final counter-witness when the remaining marked
side disjunction is already Σ₁. It recovers the term-rewritten induction
formula from the finished block state, invokes the existing cut-free matrix
inversion and guarded induction-rule construction, and marks the base, step,
and negated-witness premises as Π₂ side entries. The three recursive
hypotheses are explicit and require cut-free proofs strictly below the
principal existential inference. The result is a rule proof of the marked
output, including the special block's false contribution.

Two fresh Lean 4.32 builds of source and checks passed without warnings under
`-M6000 -j1 -DElab.async=false`. Both objects and complete logs match. Six
axiom reports use only `propext`, `Classical.choice`, and `Quot.sound`. The
[16-file replay manifest](parsons-marked-block-replay/FILES.json) has SHA-256
`848431d4cecf54f9e58f4d559cc10274c5626b18f5af298b8a23fa8270fff302`.
Direct `ParsonsInvariant` source/object hashes are
`39afa448679b7bc1b8f4d42b7d5a8611e9a9469172adaa3ca48eb3ce6d96f0be` /
`8686a84574be389aa2dc1a5ab2303812e27e967be61cf1cd9f8b9ed7a32a0fc4`;
`ParsonsSide` hashes are
`194177f493841a8c493907737cf4599a33ff8f8baa7cd6c8851039474722e450` /
`ed00fefeb57cd59214e6e1cb34ce1d350d23c0b0ad2a1dd99abb343cf00d4e50`.
Their earlier provider chain and inherited Foundation/Mathlib/completeness
boundary are described in prior receipts; this is not a fresh transitive
audit. Scratch attempts around the witness cast and height transport failed
before being fixed; their console logs were not retained.

The explicit Σ₁ side-guard hypothesis is a material restriction: a general
marked context supplies only a non-prenex Π₂ certificate. Its universal
opening and normalization to such a guard, marked nonprincipal logical cases,
and the single global strong induction are still missing. No complete
conservation or PRA witnessing theorem is asserted.

## Independent root replay

A third build at `/tmp/parsons-marked-block-build-worae8fw` passed; source,
object and complete-log hashes match both author builds. The invariant
provider matches the independently rebuilt object. The [independent artifacts](parsons-marked-block-replay/root-build/)
are preserved; Foundation/Mathlib remains an inherited boundary.
