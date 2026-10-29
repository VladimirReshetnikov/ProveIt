# Integrated marked cut-free context

`ParsonsUnified.Mark` puts the three occurrence types in one context: a Π₂
side formula, the negation of a shaped positive base theorem with its actual
rule proofs under arbitrary rewrites, or a certified partially opened Σ₁
induction block. `initial` converts the actual normalized IΣ₁ proof and a Π₂
conclusion certificate into this context; `initial_derivation` retains the
exact cut-free sequent and `initial_result` recovers the original conclusion
from a proof of its marked output.

The file integrates the no-block branch, duplicate-safe contraction,
eigenvariable shifts of all three entry kinds, ordinary principal side rules
for ∀, ∃, ∨ and ∧, the parameter-witness and counter-witness induction-block
cases, and the negative-base universal and terminal cases. Each premise
inference uses explicit strictly-smaller cut-free recursive hypotheses where
appropriate. A terminal base reclassification preserves the sequent and
height but `terminal_measure` proves that it strictly reduces the number of
base entries; this supplies the intended secondary measure. The no-block
branch discharges arbitrary stored positive base theorems, not just unmodified
closed axioms.

Two fresh Lean 4.32 builds of source and checks passed without warnings under
`-M6000 -j1 -DElab.async=false`. Both objects and complete logs match.
Fourteen axiom reports use only `propext`, `Classical.choice`, and
`Quot.sound`. The [16-file replay manifest](parsons-unified-replay/FILES.json)
has SHA-256 `6e8dc1f5204e9ca63c4799b1f652eabffb818cc4e070b1a83c425179ea2271dd`.
The current sources of the five immediate providers matched their respective
frozen snapshots:

| Provider | Source SHA-256 | Object SHA-256 |
| --- | --- | --- |
| ParsonsBaseShape | `b6ae9e2163bfec9c891a6a042596b35036e69b64ea7fecc318add0291139f6f2` | `724f705c7b609f7622978a3e627152c6fca781c7a9242073f58800b30d15b99c` |
| ParsonsShift | `cae209be8847f09d58ee5b142114a6fecf3d42f2230879f8ecb779c7f1a537f0` | `cb5b43c8187cc894279de8f2a18c174e75e82c8db7407c77b6b22b709368f437` |
| ParsonsFold | `c176115407aabd79ea2e39ade1a3818f5d0233a7dba15253eb4b66b16a61d402` | `9396383c58f41461c56e470afdbf159ed30c31ac389b8a538d193a7ec32f4411` |
| ParsonsMarkedLogical | `13d52850378acfb270efbb2bfdabc2fc596523dc4ab6a3356490990210476c32` | `f775468d0890e00151f50b8a99edfc8972fe5e7f6cb3e9acd3a7bb5530ee6ee2` |
| ParsonsMarkedBlock | `689a419acb80f4eeeb27038695aff2633d5c55bf6c31ed7aeeaa489b22769a4c` | `b1ab5749afcb4f20192e6ea2ec9f0732cd72f37cedc8f44a4ea480ea9243a380` |

Earlier provider chains, Foundation/Mathlib, and completeness objects remain
an inherited boundary, not a fresh transitive source audit.

This is a collection of integrated cases, **not a complete strong induction**.
In particular, the final induction counter-witness case explicitly requires
its remaining marked side disjunction to be Σ₁; the unified context currently
certifies only non-prenex Π₂. A general Π₂-side opening/normalization adapter,
remaining leaf/case analysis, and the global well-founded recursion are not
proved. The logical/collection constructions use completeness and choice and
are noncomputable. No overall conservation theorem, PRA-internal proof, or
PRA witnessing conclusion is asserted.

## Independent root replay

A third build at `/tmp/parsons-unified-build-_3rl07ko` passed; source, object
and complete-log hashes match both author runs. All five direct providers
match independently rebuilt objects. The [independent artifacts](parsons-unified-replay/root-build/)
are preserved; Foundation/Mathlib remains an inherited boundary.
