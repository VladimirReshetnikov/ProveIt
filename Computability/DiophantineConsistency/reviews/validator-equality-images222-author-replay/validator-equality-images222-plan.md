# Actual C222 equality axiom images: read-only implementation plan

26 October 2026. Author: circuit_reduction. This is a source and dependency
plan, not a new Lean proof or compiler result. No proof source, accepted
object, shared documentation or Git state was changed by this audit.

The recommended next leaf is `ZFCinPA.ValidatorEqualityImages222`, with one
focused Checks file. It can discharge the actual `AxOK` boundary for the
finite equality subtheory of the set language and prove a literal
irreflexivity image using the current `Eind` encoder. It need not import the
old R2 interpreter, the ZF schemata, or the native semantic interpretation.

## 1. Actual theory and recognizer

`Foundation/FirstOrder/Basic/Eq.lean:29–60` defines the equality theory by
five constructors: reflexivity, symmetry, transitivity, function congruence
and relation congruence. In the actual set language there are no function
symbols and exactly two binary relation symbols, equality and membership.
Consequently its instances reduce to five closed sentences:

- `Theory.Eq.refl ℒₛₑₜ`;
- `Theory.Eq.symm ℒₛₑₜ`;
- `Theory.Eq.trans ℒₛₑₜ`;
- `Theory.Eq.relExt (Language.Eq.eq : (ℒₛₑₜ).Rel 2)`;
- `Theory.Eq.relExt (Language.Mem.mem : (ℒₛₑₜ).Rel 2)`.

These are the actual fully quantified source sentences. The relation
congruence bodies retain `Matrix.conj`'s terminal truth, which becomes a
terminal falsum in the NNF negative antecedent. The four quantifiers and
the exact bound-variable order must remain literal checked identities.
This is not merely a list of convenient unquantified examples.

`ZFCinPA/ZFDelta1.lean:63` defines the actual equality recognizer by

```lean
noncomputable instance eqAxiom_delta1 : (𝗘𝗤 ℒₛₑₜ : SetTheory).Δ₁ :=
  Theory.Δ₁.ofFinite _ Theory.EqAxiom.finite
```

The narrow leaf should use a local explicit abbreviation with precisely
this body, rather than import all of `ZFDelta1` or install a competing
global instance. The intended endpoint is schematically:

```lean
noncomputable abbrev equalityDelta : (𝗘𝗤 ℒₛₑₜ : SetTheory).Δ₁ :=
  Theory.Δ₁.ofFinite _ Theory.EqAxiom.finite

theorem axOK_equality :
    letI := equalityDelta
    ValidatorSourceDerivation222.AxOK (𝗘𝗤 ℒₛₑₜ) V
```

Here `V` has the existing `ORingStructure` and `V ⊧* IΣ1` assumptions. This
must not be generalized to an arbitrary `Theory.Δ₁` instance: its internal
recognizer, not only its standard extension, matters. The displayed body
is definitionally the existing instance's body; a later client importing
that named instance can check the binding by reduction.

`Foundation/FirstOrder/Bootstrapping/Syntax/Theory.lean:90–121` supplies the
actual singleton/list/finite recognizers. The needed finite extraction is:

```lean
mem_ch_ofList (l : List SetTheorySentence) {p : V}
    (h : V ⊧/![p] (Theory.Δ₁.ofList l).ch.val) :
    ∃ σ ∈ l, p = ⌜σ⌝

mem_ch_ofFinite (T : SetTheory) (hT : Set.Finite T) {p : V}
    (h : V ⊧/![p] (Theory.Δ₁.ofFinite T hT).ch.val) :
    ∃ σ ∈ T, p = ⌜σ⌝
```

These follow directly by recursion on the finite *defining list*: empty
is false, cons is the actual disjunction, and singleton evaluates to
`p = numeral (Encodable.encode σ)`. The quote/cast identity then gives the
conclusion. `ofFinite` is `ofList hT.toFinset.toList` followed by `ofEq`.
`ConstructibleInterpretation.lean:564–585` already contains this exact
short proof pattern; it is a source guide only, not an imported result.
This handles an arbitrary internally coded `p`. It neither assumes that
all internal numbers are standard nor uses the standard-quotation-only
`Δ₁Class.mem_iff` in the wrong direction.

## 2. Finite actual encoder and proof interfaces

The proposed sole import is `ZFCinPA.ValidatorSourceDerivation222`. Its
transitive current closure already supplies the actual encoder,
`ValidatorAtomicTransport222`, `ValidatorEind222`, the relational and
quantifier rules, typed quotations and finite-theory syntax.

The five source endpoints should have the stronger uniform form

```lean
CProv (encode F 0 s (⌜actualEqualitySentence⌝ : V))
```

for arbitrary internal `F` and `s`, without stream freshness, parity or
label-distinctness premises. `AxOK` then accepts and does not need its
extra `StreamFree s F` premise in these finite cases. Its source typing
premise remains in the statement of `AxOK`.

The small typed encoder helpers must prove that bound equality atoms
encode to `Eind B.[i] B.[j]` and membership atoms to `wel B.[i] B.[j]`.
The total vector access allows arbitrary `B`; no unstated `len B` premise
is needed for these fixed quoted variables. Typed negative atoms encode
to numeric negation, and the actual `encode_all`, `encode_or` and falsum
rules expose the source closure. No equality atom is changed to `weq`.

The already proved, actual C222 contracts are:

- `ValidatorAtomicTransport222.eind_refl`;
- `eind_symm`, `eind_trans`, `eind_congr`;
- `ValidatorAtomicTransport222.rel_congr`;
- `ValidatorRelationalCore222.double_neg_elim`, conjunction projections,
  finite implication composition and actual `cProv_gen`.

Finite `Kalmar.Der wim CProv` deductions suffice for the NNF glue:
symmetry uses `DN E → R`, transitivity uses `DN E₁ → DN E₂ → E₃`, and
relation congruence uses `conj (DN E₀) (DN E₁) → DN R → R'`. These follow
from the cited current transport implications and their numeric
conjunction/negation encodings. The actual C222 calculus is classical;
using its checked double-negation rule here does not introduce any new HA
rule or assert an HA derivation of an arithmetic target.

The exact quoted bodies to bind by definitional equalities are:

```text
refl:      ∀ eq(0,0)
symm:      ∀∀ (neq(1,0) ∨ eq(0,1))
trans:     ∀∀∀ (neq(2,1) ∨ (neq(1,0) ∨ eq(2,0)))
relExt R:  ∀∀∀∀ ((neq(0,2) ∨ (neq(1,3) ∨ ⊥))
                 ∨ (nR(0,1) ∨ R(2,3)))
```

The one/two/three/four actual numeric generalizations then close the
sentences at labels `s`, `s+2`, and so on. Source membership extraction
followed by the actual `Theory.eqAxiom` cases discharges `AxOK`: the
function case is impossible in this language, and the two relation cases
are the two literal proofs. No internal induction over arbitrary binder
counts is needed for this finite subtheory. Applying the existing generic
source derivation theorem later still requires its explicit IΣ2 hypothesis.

## 3. Irreflexivity through Eind, including label zero

The current `ValidatorSeedWitness222` does not itself export an
irreflexivity theorem. The needed statement is a small consequence of
already accepted current resources:

```lean
wel_zero_zero : wel (0 : V) 0 = 1
not_mem_self (s : V) : CProv (wim (wel s s) 1)
irreflexivity_image (F s : V) :
  CProv (encode F 0 s (⌜(“∀ x, x ∈ x → ⊥” : SetTheorySentence)⌝ : V))
```

The first is the literal Cantor/tagged-code calculation. For `s=0`, the
second is self-implication of falsum. For `s≠0`, current `eind_symm` and
`rel_congr s 0 s 0` give
`L : CProv (Eind 0 s → (wel s s → 1))`.
`ValidatorEind222.Eind_ex 0 s` and `ex_mono 0 L` give
`CProv (ex 0 (wel s s → 1))`. Relational vacuity at binder zero, using
`0≠s`, and `vac_neg` permit `ex_elim_of_vac`. This is a genuine current
history proof; it uses neither an `Eind → weq` converse nor a semantic
interpretation of equality. Finally the quoted source body is exactly
`∀ (nmem(0,0) ∨ ⊥)`, so numeric NNF glue and one generalization prove the
literal source image.

`NativeTheory.lean:38–46` defines `NativeSet.irForm` as
`.fAll (.fImp (.fMem 0 0) .fBot)` and `irAx` as its `toSet 0` universal
closure. Reading the exact `Translation.toSet` clauses shows the same
literal source sentence. A theorem naming `NativeSet.irAx` nevertheless
requires that declaration in the environment. The recommended first
leaf proves the actual literal sentence above; it does not claim a checked
FQName binding without importing its owner. A later narrow/approved-wide
binding can establish the definitional identity. No edits or moves of
existing declarations are proposed here.

## 4. Focused checks and scope

Aim for approximately 220–280 main lines and 60–85 Checks lines; this is
an estimate, not a source budget claim. Checks should bind all five named
source quotations, the full congruence antecedent and quantifier order,
the current `Eind` atom equation, the local exact recognizer and the full
`AxOK` type. Include arbitrary internal environments, label zero, repeated
labels, and the separate nonzero-label irreflexivity argument. Report the
axioms of public endpoints and the optional direct equality-subtheory
refutation witness composed from the accepted source interpreter.

No equality-image premise is imported. This closes only the finite
actual equality subtheory and the stated literal irreflexivity image.
Container/collection instances, arbitrary internally sized universal
closures of those schemata, tagged-seed padding and the full native/source
ZFC `AxOK` obligation remain separate. Root owns the new seed-padding
work. This packet does not prove source ZFC equivalence, runtime215
simulation, an HA equation equivalence or a new consistency calibration.

## 5. Authenticated narrow cache and alternative costs

The read-only inventory is
[`validator-equality-images222-plan.json`](validator-equality-images222-plan.json),
SHA256 `62f27ed2d44e5ebaa5b74a3b3eec11726e2571ee7394319f6a018fd2b39287bd`.
It rehashed **165 current source/object pairs, 117 Foundation modules,
516 selected object artifacts and 40 explicit boundaries including Init
and meta Aesop**. It made 843 authentication observations and created no
overlay or Lean process. The import parser preserves public/meta imports.
The exact toolchain, manifest, companion/trace evidence and boundary paths
are recorded. The inherited provenance qualification for two Foundation
SetTheory companion groups is unchanged: their companion hashes are
current observations, not retroactive historical captures.

Selected new provider is the independently replayed
`/tmp/validator-source-derivation222-peer-zt8k99i_/lib`:

- main source `a0f2e51b1c27fc5725e3cd4f4762770d3564607113e7587c417cc1e6e8605831`;
- main object `919ef6ae97757dafc46708e6112749f95335f0a659ec625824ce5213dbaf8ddc`;
- author packet `d688e71398add24dc4e54cdb2ba002d45524c3fbe2af324bc2d95f411f4e195c`;
- peer packet `c375939e62d66e03f0730d270b83917c0dd063f66842e8d5dbfd75c2e9166f3e`.

Root accepted this provider after the inventory was written, in commit
`85cbb6bd42`. The frozen inventory honestly retains its earlier
acceptance-pending wording; the separate acceptance pins are:

- `reviews/validator-source-derivation222-root.md`,
  SHA256 `05449dfb6101031d03c4f7a27e5bfe3c854bddd5a096235c4cdb88d6cff2ee9d`;
- its `root-authentication/FILES.json`,
  SHA256 `1c08846e3ba48817a8d75193899a7f51853a087a755e1dbb97106caa355fcf82`.

The same inventory records current-source-only alternative import cones:
adding `ZFDelta1` would make 188 modules/136 Foundation/45 boundaries;
adding `NativeTheory` would make 224/139/45. Those alternative object
closures were **not** authenticated or selected by this audit. Avoiding
them is why the first leaf uses the exact local finite recognizer and a
literal irreflexivity sentence, with named native binding deferred.

Only two future new leaf objects are proposed. Before any approved
execution, retain the full final source/Checks and driver reads, new
regular private outputs, Lean4.32 `-M6000 -j1 -DElab.async=false`, one
thread, the 512MiB reserve, pre/post source/object/boundary pins and every
failed attempt. No dependency or Foundation build is proposed.
