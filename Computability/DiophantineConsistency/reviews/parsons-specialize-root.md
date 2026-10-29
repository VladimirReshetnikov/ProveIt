# Arbitrary-parameter Σ₁ collection rule

`ParsonsSpecialize.specialize_closure` constructs an actual rule-calculus
proof of `A ⇜ v` from a proof of `∀⁰* A` for an arbitrary finite term vector
v. The recursion peels the outermost universal and uses a proved substitution
composition identity under the remaining binders. `specialize_univCl`
instantiates a universally closed open formula at its original free variables.

`collect` combines that specialization with the universally closed
finite-extension theorem, the PA-minus base, and the Σ₁ induction rule. For
any Σ₁ formula D(i,y) with arbitrary additional free parameters, it takes an
actual rule proof over PA-minus of `∀i ∃y D(i,y)` and returns an actual rule
proof of `∀k ∃B ∀i<k ∃y<B D(i,y)`. It assumes no finite-extension proof and
no collection axiom. This is a proof-transforming **rule**, not a proof of
the conditional collection formula `H → C` under an arbitrary assumption.
The construction is noncomputable: the finite-extension and zero-minimum
proofs use Foundation's model-theoretic completeness and classical choice.
It establishes proof existence and does not claim a primitive-recursive
transformation or a proof formalized inside PRA.

Two fresh Lean 4.32 builds of source and checks passed without warnings under
`-M6000 -j1 -DElab.async=false`. Both objects and complete logs match. Four
axiom reports use only `propext`, `Classical.choice`, and `Quot.sound`. The
[16-file replay manifest](parsons-specialize-replay/FILES.json) has SHA-256
`9bc2b608d46c94153749c970bac307c4d8d849f76838bc0550c2b9443182775a`.
Scratch failures around finite indices and dependent casts were fixed; their
console logs were not retained.

The following previously built provider objects were used. Their current
source hashes were checked equal to the source snapshots in the named prior
replay; this checks these direct providers but is not a fresh transitive audit
of the inherited Foundation/Mathlib/completeness object boundary.

| Provider | Source SHA-256 | Object SHA-256 |
| --- | --- | --- |
| ParsonsCollectionSemantic | `afb46628b179088dc386e035b434be079ce9f46ded009f47bc10d42ae129503d` | `ffa190ad0101e50dbd2ca5f24b7e8d8c95e7649ae54c73c00ea5611fe5ce2e16` |
| ParsonsCollectionRule | `2a00fe7e6368cd05cf57477021fe4f311228727896892f8f287aed06d12787df` | `6753554df276ab0e47cfc61481355338f468d647ba760c96ed43354a4fff3cca` |
| ParsonsCollection | `e4d1811c4b6644006f14ea321fc2c236c3824d2bf89068b83c7748794a4a3a6b` | `02adc359d3997eeff4b5f21ae44dd117372c51631134695e3f9e47dc98987822` |
| ParsonsPrenex | `2c8a2b3682493560b0681df701fd6744374e7113241b84f3dbb94bfc6b035bb6` | `b1f8b7257a48a3d54177b38b6300d460dc17770a36bcd50dce585b53258f733c` |
| ParsonsRuleEmbedding | `076a1d32a29e9bf4e257bb3f2d6e9965677e786dfca0c12720cc58afc26847a1` | `b85ce569b406c04a2fd74e85a036b49a657b9fbaaa9808e87fadabd7aa8565df` |
| ParsonsCutFree | `45c6c35b16faa01ffe9e6e021844a41d1df740677d7c4be2e523d61891a2e087` | `93461a90f9f33d21e8a07a87fe0971f31108e51454800b746c4684ed2bb1f436` |
| ParsonsRule | `7fe1dd093fa3ff9585fa37968e0bf75d483b743c9b18fa33c4587a677bb15325` | `eb5c49e2362e7d7f05b6e7dea5d0f671134657c57f0f09a9ec959f7c01a57ec3` |
| ParsonsGuard | `ba4d334d660d7438a1cfda46fb1b654fc870e0d16965c6d18e677ed11ff6497d` | `6ed2a4c0e10113e0c82c64ca7a4e05c0ff965a51f1ed3e3ad16400d3d7a728d1` |

The positive-guarded-context adapter and its interaction with the remaining
cut-free cases have not been established. The complete strict Π₂ adapter,
global cut-free translation, and PRA witnessing remain open.

## Independent root replay

A third build at `/tmp/parsons-specialize-build-eikanqys` passed; its
sources, objects and complete logs match both author runs. Its two immediate
collection providers match the independently rebuilt objects accepted in the
prior reviews. The [independent artifacts](parsons-specialize-replay/root-build/)
are preserved; the Foundation/Mathlib boundary remains inherited.
