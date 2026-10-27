# Fixed Foundation consistency: proposed HA normalization

This is a read-only proposal, not a new theorem or compiler result. It follows
the accepted `FoundationHASigmaOneGG` packet (commit `39242517d6`). The proposed
new result is an HA proof comparing the existing fixed GG consistency sentence
with the HA negation of the **ordinary interpretation of its actual positive
Foundation provability predicate**. It does not compare that predicate in HA
with the independent PAHF `BProv` checker, C222, C254, or the current equation.

## Exact fixed source and hypotheses

Use the same imports and instances as the accepted
`Lean/DiophantineConsistency/FoundationZFCConsistencyNat.lean:31`:

```lean
noncomputable def rho : ArithmeticSentence :=
  LO.FirstOrder.Arithmetic.Bootstrapping.provabilityPred
    (LO.FirstOrder.SetTheory.ZermeloFraenkelChoice : LO.FirstOrder.SetTheory)
    (⊥ : LO.FirstOrder.SetTheorySentence)

theorem source_eq_neg_rho :
    FoundationZFCConsistencyNat.sourceSentence = ∼rho := rfl
```

These are proposed declarations; elaboration has not been run. The `rfl`
binding is a required check, not a fallback appeal to semantic equivalence.
It pins the actual `Theory.Δ₁` instance used by the accepted source sentence.
An arbitrary extensionally equal theory or different coding instance is not
silently substituted.

The relevant source definitions, relative to the Foundation package root
`/home/codex/src/Proofs/lib/FormalizedFormalLogic-Foundation`, are:

* `Foundation/FirstOrder/Incompleteness/Consistency.lean:38` defines
  `Theory.consistent := .mkPi (∼provabilityPred T ⊥)`.
* `Foundation/FirstOrder/Bootstrapping/Syntax/Proof/Basic.lean:469` defines
  `derivation` using the existing fixed-point blueprint. Its `proof` is a
  typed Δ₁ pair; `provable` is the Σ₁ formula `∃ d, (proof T).sigma d φ`.
  Lines 484–490 define `provabilityPred`, `provabilityPred'`, and the exact
  `provabilityPred'_val` equality.
* `Foundation/FirstOrder/Arithmetic/Definability/Hierarchy.lean:70,89`
  supplies the typed formula's `val` and actual syntactic `sigma_prop`.
* `Foundation/FirstOrder/Bootstrapping/Syntax/Theory.lean:13` defines
  `Theory.Δ₁`. Its fields include a particular Δ₁ formula, standard-Nat
  membership semantics, and an IΣ₁ `ProvablyProperOn` certificate. None is
  itself an HA proof that the represented checker is decidable.

The necessary non-model typeclasses are `L.Encodable`, `L.LORDefinable`, and
`T.Δ₁`, for `L = ℒₛₑₜ`, `T = ZermeloFraenkelChoice`. Their actual providers are
Foundation `SetTheory/Basic/Misc.lean:61`, repository
`Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/Instances.lean:52`, and
`ZFDelta1.lean:83`. The latter uses the genuine finite, separation,
replacement, choice-singleton, and union construction. No model `V`,
standardness assumption, or arbitrary-model axiom is needed merely to form
the source sentence and its syntactic hierarchy certificate.

The concrete hierarchy proof is short:

```lean
theorem rho_sigma_one : Arithmetic.Hierarchy 𝚺 1 rho := by
  simpa only [rho, provabilityPred'_val] using
    (provabilityPred'
      (ZermeloFraenkelChoice : LO.FirstOrder.SetTheory)
      (⊥ : SetTheorySentence)).sigma_prop
```

The existing actual Σ₁ certificate is sufficient. No prenex conversion,
bounded-checker identification, or Δ₁-to-HA-decision theorem is required for
this normalization. In particular the formula inside `proof.sigma` is not
asserted to be DeltaZero.

## Exact target syntax and the one missing syntax identity

Let `F` be PAHF `SetTheory.PA.Formula`. Use the existing eight-constructor
`FoundationHADeltaZero.ordinaryAux`, without changing it:

```lean
noncomputable def ordinaryRefutation : F :=
  ordinaryAux Fin.elim0 Empty.elim rho

noncomputable def ordinaryConsistency : F := HA.neg ordinaryRefutation
```

Here `rho : Semiformula ℒₒᵣ Empty 0`. Both original source variable
environments are empty. The explicit order atom remains the existing
capture-avoiding `ltFormula`, including its own existential witness.
Every binder recursively uses `liftBound` and `liftFree`.

The needed generic syntax lemma is:

```lean
theorem sentence_empty_env (φ : Sentenceᵢ ℒₒᵣ) :
    FoundationPAHFSyntax.sentence φ =
      FoundationPAHFSyntax.formulaAux Fin.elim0 Empty.elim φ
```

Proof route: unfold only `sentence` and `formula`, use the existing
`formulaAux_rew` at `Rew.emb`, then identify the two empty-domain functions
by function extensionality and empty elimination. The source definitions
are `FoundationPAHFSyntax.lean:118,175–180`, Foundation
`Syntax/Predicate/Rew.lean:103,847`. This is a syntax equality; it does not
follow from equality of standard-model evaluations. Applied to `rhoᴺ`, it
aligns the accepted Σ₁ theorem exactly with the already maintained
`sentence rhoᴺ` convention.

No new generic negation proof is needed. The accepted public theorem
`FoundationHASigmaOneGG.neg_of_doubleNeg_equiv` already packages the
contrapositive/triple-negation argument, with no decidability premise on
the matrix. The generic derivation is exactly

```lean
neg_of_doubleNeg_equiv
  (sigma_one_doubleNeg rho_sigma_one Fin.elim0 Empty.elim)
```

After `sentence_empty_env`, it gives an actual `HA.Proves` of
`¬sentence rhoᴺ ↔ ¬ordinaryRefutation`.

Reuse `FoundationHACurrentTransfer.translated_neg rho` unchanged. Its
two directions are `¬sentence rhoᴺ → sentence (∼rho)ᴺ` and the reverse.
It already maps Foundation's genuine intuitionistic
`Derivation.neg_doubleNegation` proof to the HA calculus. The exact
embedding identity `Semiformula.emb_doubleNegation` and the homomorphism's
`map_neg` have been checked in that accepted proof. There is no reason to
copy the GG recursion or its negation-duality proof.

Composing these two proof equivalences and the fixed `source_eq_neg_rho`
gives the proposed nonconditional endpoint:

```lean
HA.Proves (.and
  (.imp FoundationZFCConsistencyNat.ggConsistency ordinaryConsistency)
  (.imp ordinaryConsistency FoundationZFCConsistencyNat.ggConsistency))
```

Both ordinary implication projections and a `Relative Ax_s G` weakening
are cheap optional exports. No PA equivalence premise or target consistency
assumption appears in this endpoint. In contrast, the still-open actual
equation/source PA equivalence is not supplied by this proof.

Critically, `ordinaryAux ... (∼rho)` is **not** substituted for
`HA.neg (ordinaryAux ... rho)`. Source negation is NNF duality. The target
negation in the proposed result is explicitly outside the ordinary positive
predicate. No general positive Σ₁ double-negation elimination, Markov rule,
unbounded DNS, or blanket Π₁ stability is used.

## Closedness and standard-Nat conventions

The source is an actual `ArithmeticSentence`, not an open proposition with
an implicit valuation. The proposed empty-environment interpretation preserves
this construction. The existing syntax APIs do not yet expose a general
`Formula.Sentence (ordinaryAux Fin.elim0 Empty.elim φ)` lemma. In PAHF,
`Formula.Sentence` means `∀ k, ¬Formula.Free k φ`; `Formula.bound = 0` is
not an appropriate substitute (see `PAHF/PASyntax.lean:482–502`).

A finite additional support proof is feasible if a syntactic `Sentence`
certificate is wanted: prove that a free target index of `ordinaryAux bv fv p`
comes from a free index in some `bv i` or `fv x`. First prove the analogous
term lemma and the free-index identity for `ltFormula`; handle quantifiers
with `liftBound`/`liftFree` and the exact successor-index rule for `Free`.
Empty environments then finish by elimination. This is an estimated
50–80-line generic syntax subtask, not an existing checked theorem.

A smaller optional standard-Nat interpretation lemma is also concrete:

```lean
Formula.Sat FoundationPAHFNatSemantics.natStructure ee
    (ordinaryAux bv fv p) ↔
  p.Eval (fun i => Term.eval natStructure ee (bv i))
    (fun x => Term.eval natStructure ee (fv x))
```

Prove this by the actual eight-constructor NNF induction, reusing
`eval_termAux`, `sat_ltFormula`, `eval_liftBound`, and `eval_liftFree` from
`FoundationPAHFNatSemantics.lean`. Ordinary `and/or/all/ex` are interpreted
directly; this is not another negative-translation algorithm. Empty
environments give valuation independence for the positive predicate and
its outer HA negation. The existing
`FoundationZFCConsistencyNat.source_nat_iff_no_refutation`, together with
the literal source-negation identity, then gives

```lean
Formula.Sat natStructure ee ordinaryConsistency ↔
  ¬ _root_.SetTheory.BProv
    LeanProofs.BoundedZFCConsistency.ZFCax_s [] _root_.SetTheory.Form.fBot
```

That is only a standard-Nat semantic theorem. Its source convention uses
the accepted C254/refutation comparison and standard-model soundness;
neither C254 runtime facts nor this semantic equivalence enter the new HA
normalization proof. An HA comparison with that separate BProv checker
remains open. This semantic supplement is estimated at 40–60 lines and
can be deferred without weakening the proposed HA endpoint.

## Smallest implementation and authenticated cache boundary

Recommended first implementation: one new
`FoundationHAConsistencyNormalization.lean` plus focused checks, importing
only:

```lean
import DiophantineConsistency.FoundationHASigmaOneGG
import DiophantineConsistency.FoundationHACurrentTransfer
import DiophantineConsistency.FoundationZFCConsistencyNat
```

The core is estimated at 70–110 lines plus 40–60 checks. A separate generic
negation helper would duplicate an already public theorem. The short
`sentence_empty_env` identity can be private or public in this leaf. Keep
any optional free-support/semantic supplement separately scoped if it
would make the first packet substantially larger. Required checks should
pin the exact source by `rfl`, the actual Σ₁ certificate, both HA
implications, empty-environment binder identities on nested quantifiers,
and complete axiom reports. There should be no fabricated Δ₀-checker
certificate or undecidable positive-Σ₁ recovery check.

The accompanying JSON freezes the actual dependency union and observations:

* Start from the accepted 448-cache `FoundationHAZFCValidator` input closure.
* The accepted Σ₁ parent closure adds six modules: `FoundationHAOrderDecidable`,
  `HAStrictIntervals`, `HABoundedQuantifiers`, `FoundationHADeltaZero`,
  `FoundationHADeltaZeroGG`, and `HABoundedDoubleNegation`.
* Add the now accepted root-replayed `FoundationHASigmaOneGG` itself.
  The result is **455 cached current-source modules, 139 Foundation modules,
  872 cached object/companion artifacts, 57 explicit external boundaries**.
  An import-graph traversal from the three proposed imports reaches the
  entire union; there are no missing modules or unused cached modules.
* The narrower hypothetical generic bridge using only CurrentTransfer and
  Σ₁ has 141 cached modules / 85 Foundation / 49 boundaries. With Σ₁ alone,
  the already available generic negation theorem needs its existing 105
  module closure. A separate such leaf would not close the fixed binding.
* The selected Σ₁ primary is
  `/tmp/foundation-ha-sigma-one-gg-root-peer-f4n97u0a/lib`, object SHA256
  `63c087fe421399605afebff35e4347a296e957860e29a449880dafd553a8b2b0`.
  The original author provider and its complete provenance are retained.
  Root acceptance record SHA256 is
  `1b078703886c29a6932bc5645b3a477d5494ab5694c4da4464067da3316e239c`.

All selected source hashes and recorded artifacts are checked read-only.
Existing per-module source/import records, inherited authentication records,
compiler hash, explicit package boundaries, and same-source alternate
providers are retained. This audit performs no Lean build, object import,
dependency copy, vendor edit, or proof-source edit. A later authorized
implementation would compile only its two new leaves in a fresh private
overlay, with the established Lean 4.32.0 / 6000MiB / one-job / async-false
limits and 512MiB disk reserve, after another preflight and full source read.
