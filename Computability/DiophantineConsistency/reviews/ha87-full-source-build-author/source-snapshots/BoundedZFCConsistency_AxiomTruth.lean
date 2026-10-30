import BoundedZFCConsistency.LevelSoundnessProof

/-!
# Truth of the internal ZFC axiom codes at a fixed level

`BoundedZFCConsistency.LevelSoundness` names three obligations.  Two are
discharged — `LevelTwoValuedAt` by `BoundedZFCConsistency.LevelCollapse` and
`LevelSoundnessAt` by `BoundedZFCConsistency.LevelSoundnessProof`.  This module
addresses the third and last, `AxiomCodesTrueAt`: every internal ZFC axiom code
whose complexity is bounded by the numeral of `n` is true at level `n+1`.

## The statement is relative to a richer semantic bundle

`ZFAxioms` is Extensionality, Separation, Pairing, Union, Infinity and
Replacement.  `IsZFCAxiomCode` recognizes Powerset, Regularity and Choice as
well, and nothing in the weaker bundle makes those three true — indeed they are
false in models of it.  Axiom truth is therefore stated relative to `ZFCAxioms`,
which adjoins exactly the three missing principles in the form the extraction
bridges of `ZF.Zf` and `BoundedZFCConsistency.Choice` deliver them.

The strengthening costs nothing at the endpoint.  What
`zfcprov_conZFCForm_of_valid` consumes is truth of `Con_n(ZFC)` in every model of
the *sentence theory* `ZFCax_s`, and a model of `ZFCax_s` satisfies all nine
axioms; `zfcAxioms_of_zfcModel` extracts the richer bundle from it, exactly as
`zfAxioms_of_zfcModel` extracts the weaker one.  Every module below this one
continues to be stated over `ZFAxioms`.

## The two halves of the axiom-code predicate

**The seven fixed axioms** are quotations of specific external formulas, so their
truth reduces to metatheoretic satisfaction.  `levelTruth_formCode` is that
reduction, and it is proved for an arbitrary external formula: at every level
bounding the relevant rank, the fixed-level predicates of
`BoundedZFCConsistency.UniverseTruthLevel` read a quotation exactly as `Sat`
reads the formula, under the environment `univEnvOf` that a universe environment
induces.  The induction is the one the hierarchy is built for — external on the
level, structural on the formula, with the two quantifier heads consuming the
*previous* level on the opposite polarity through the polarity switches.

**The two schemas** are the mathematically substantial half, because the
existential in `IsZFCAxiomCode` ranges over an *internal* code.  In a nonstandard
model that code quotes no external formula, so no external induction reaches
inside it and `levelTruth_formCode` does not apply.  What replaces it is the
observation the whole hierarchy exists to license: at a fixed level the truth
predicate is itself a `Form`, so `ZFAxioms.sep` and `ZFAxioms.repl` may be
instantiated *at it*.  The subset a nonstandard Separation instance describes is
carved out by `sepD` applied to `fSigmaTrueF`, and the image a nonstandard
Replacement instance describes is collected by `H.repl` applied to the same
formula.

Two smaller points make those two arguments cheaper than they look.  The
separating condition never mentions the set being separated: the schema renaming
`rsep` sends the instance's free variables past the two bound slots, so the
substitution lemma rewrites the instance's truth at the three-fold extended
environment to its truth at `econs x E`, which depends on the separated element
alone.  And the two directions of the carved biconditional need different
polarities, one of which is free: membership in the carved set gives Sigma-truth
of the instance, and the other direction needs Pi-truth of it, which exclusivity
supplies with no bound at all.

## Conventions

De Bruijn slots named `_i` are ABSOLUTE positions in the environment at the use
site, matching `ZF.Zf`, `BoundedZFCConsistency.InternalSat` and
`BoundedZFCConsistency.UniverseTruthLevel`.
-/

namespace LeanProofs
namespace BoundedZFCConsistency

open SetTheory
open SetTheory.Form

/- `conZFCForm n` and the sealed ZFC axioms are large terms, and the elaborator
recurses through them when it checks a definitional unfolding. -/
set_option maxRecDepth 8000

/- `sealF g` is `closeN (bound g) g`, so reducing it evaluates `bound` over the
whole of the formula being closed.  Nothing here needs to see through the
closure operator. -/
attribute [local irreducible] SetTheory.sealF

universe u

/-! ## The richer semantic bundle

`ZFAxioms` carries the six axioms every internal result of this project is
relative to.  The axiom-code predicate recognizes three more, so axiom truth
needs them; they are adjoined here in the shape their extraction bridges
produce. -/

/-- **The semantic axioms of ZFC.**  The six of `ZFAxioms` together with
Powerset, Regularity and Zermelo's choice principle.

Each added field is the right-hand side of the corresponding bridge —
`bridge_Pow` and `bridge_Reg` of `ZF.Zf`, `bridge_Choice` of
`BoundedZFCConsistency.Choice` — so a model of the sealed sentence theory yields
the bundle by the same extraction pattern `zfAxioms_of_zfcModel` uses. -/
structure ZFCAxioms {V : Type u} (mem : V → V → Prop) : Prop extends
    ZFAxioms mem where
  pow : ∀ a, ∃ p, ∀ x, mem x p ↔ SetTheory.Sub mem x a
  reg : ∀ a, (∃ x, mem x a) → ∃ m, mem m a ∧ ¬ ∃ z, mem z m ∧ mem z a
  choice : ChoiceSem mem

section AxiomTruth

variable {V : Type u} {mem : V → V → Prop}

/-! ### The nine axioms, as satisfaction statements

Each is one bridge applied to one field.  All nine formulas are closed, so the
environment is immaterial and is left universally quantified. -/

theorem sat_Ext_form (K : ZFCAxioms mem) (e : Nat → V) :
    Sat mem e Ext_form :=
  (bridge_Ext (mem := mem)).mpr K.ext e

theorem sat_Pair_form (K : ZFCAxioms mem) (e : Nat → V) :
    Sat mem e Pair_form :=
  (bridge_Pair (mem := mem)).mpr K.pair e

theorem sat_Union_form (K : ZFCAxioms mem) (e : Nat → V) :
    Sat mem e Union_form :=
  (bridge_Union (mem := mem)).mpr K.union e

theorem sat_Inf_form (K : ZFCAxioms mem) (e : Nat → V) :
    Sat mem e Inf_form :=
  (bridge_Inf (mem := mem) e).mpr K.inf

theorem sat_Pow_form (K : ZFCAxioms mem) (e : Nat → V) :
    Sat mem e Pow_form :=
  (bridge_Pow (mem := mem)).mpr K.pow e

theorem sat_Reg_form (K : ZFCAxioms mem) (e : Nat → V) :
    Sat mem e Reg_form :=
  (bridge_Reg (mem := mem)).mpr K.reg e

theorem sat_Choice_form (K : ZFCAxioms mem) (e : Nat → V) :
    Sat mem e Choice_form :=
  (bridge_Choice (mem := mem)).mpr K.choice e

/-! ## The metatheoretic environment induced by a universe environment

A universe environment is an internal function on the internal omega.  Reading
it at the numerals gives an ordinary Lean environment, and that is the only
bridge between internal and external satisfaction this module needs. -/

/-- The metatheoretic environment read off a universe environment at the
numerals. -/
noncomputable def univEnvOf (H : ZFAxioms mem) (E : V) : Nat → V :=
  fun k => applyV H E (natV H k)

/-- **The shift is read correctly.**  Extending a universe environment
internally is extending the induced environment externally. -/
theorem univEnvOf_econs (H : ZFAxioms mem) {E : V} (hE : IsUnivEnv H E) (d : V) :
    univEnvOf H (econs H d E) = scons d (univEnvOf H E) := by
  funext k
  match k with
  | 0 => exact econs_apply_zero H hE d
  | m+1 => exact econs_apply_succ H hE d (natV_mem_omega H m)

/-! ## Fixed-level truth of a quotation

The externally indexed predicates read a quotation exactly as `Sat` reads the
formula, at every level bounding the polarity rank in question.  Both polarities
travel together, since the Sigma clause of an implication asks for Pi-falsity of
its antecedent, and each quantifier head consumes the previous level on the
opposite polarity. -/

/-- **Quotations are read correctly at every level bounding their rank.**

The outer induction is on the metatheoretic level; its base case is the
quotation bridge of `BoundedZFCConsistency.UniverseTruthZero`, available because
a formula of rank zero on either polarity is quantifier-free.  The inner
induction is structural on the formula, with the environment generalized because
the two binder cases apply it at a shifted environment.

The atomic and Boolean cases read the biconditional Tarski clauses at the same
level.  The universal head on the Sigma side and the existential head on the Pi
side read the polarity switches of `BoundedZFCConsistency.LevelCollapse`, whose
oriented bounds are supplied by the rank identities on quotations, and consume
the outer induction hypothesis at the *previous* level on the opposite
polarity. -/
theorem levelTruth_formCode (H : ZFAxioms mem) :
    ∀ (n : Nat) (phi : Form) (E : V), IsUnivEnv H E →
      (sigmaRank phi ≤ n →
          (SigmaTrue H n (formCode H phi) E ↔ Sat mem (univEnvOf H E) phi)) ∧
        (piRank phi ≤ n →
          (PiFalse H n (formCode H phi) E ↔ ¬ Sat mem (univEnvOf H E) phi)) := by
  intro n
  induction n with
  | zero =>
      intro phi E hE
      have hs : sigmaRank phi ≤ 0 → IsQuantFree phi := fun h =>
        (isQuantFree_iff_quantifierBounded_zero phi).mpr
          (Nat.le_trans (Nat.min_le_left _ _) h)
      have hp : piRank phi ≤ 0 → IsQuantFree phi := fun h =>
        (isQuantFree_iff_quantifierBounded_zero phi).mpr
          (Nat.le_trans (Nat.min_le_right _ _) h)
      exact ⟨fun h => (levelSat_formCode_zero H hE phi (hs h)).1,
        fun h => (levelSat_formCode_zero H hE phi (hp h)).2⟩
  | succ n ih =>
      intro phi
      induction phi with
      | fMem i j =>
          intro E hE
          exact ⟨fun _ => sigmaTrue_memAtom H (n+1) (natV_mem_omega H i)
              (natV_mem_omega H j) hE,
            fun _ => piFalse_memAtom H (n+1) (natV_mem_omega H i)
              (natV_mem_omega H j) hE⟩
      | fEq i j =>
          intro E hE
          exact ⟨fun _ => sigmaTrue_eqAtom H (n+1) (natV_mem_omega H i)
              (natV_mem_omega H j) hE,
            fun _ => piFalse_eqAtom H (n+1) (natV_mem_omega H i)
              (natV_mem_omega H j) hE⟩
      | fBot =>
          intro E hE
          refine ⟨fun _ => ?_, fun _ => ?_⟩
          · exact ⟨fun h => absurd h (sigmaTrue_bot H (n+1)), fun h => h.elim⟩
          · exact ⟨fun _ h => h.elim, fun _ => piFalse_bot H (n+1) hE⟩
      | fImp a b iha ihb =>
          intro E hE
          have hca := formCode_isFormCodeSem H a
          have hcb := formCode_isFormCodeSem H b
          refine ⟨fun h => ?_, fun h => ?_⟩
          · simp only [sigmaRank] at h
            obtain ⟨h1, h2⟩ := Nat.max_le.mp h
            have hstep : SigmaTrue H (n+1) (formCode H (fImp a b)) E ↔
                (PiFalse H (n+1) (formCode H a) E ∨
                  SigmaTrue H (n+1) (formCode H b) E) :=
              sigmaTrue_imp H n hca hcb hE
            rw [hstep, (iha E hE).2 h1, (ihb E hE).1 h2]
            constructor
            · rintro (hna | hb) hsa
              · exact absurd hsa hna
              · exact hb
            · intro k
              rcases Classical.em (Sat mem (univEnvOf H E) a) with hsa | hsa
              · exact Or.inr (k hsa)
              · exact Or.inl hsa
          · simp only [piRank] at h
            obtain ⟨h1, h2⟩ := Nat.max_le.mp h
            have hstep : PiFalse H (n+1) (formCode H (fImp a b)) E ↔
                (SigmaTrue H (n+1) (formCode H a) E ∧
                  PiFalse H (n+1) (formCode H b) E) :=
              piFalse_imp H n hca hcb hE
            rw [hstep, (iha E hE).1 h1, (ihb E hE).2 h2]
            constructor
            · rintro ⟨hsa, hnb⟩ k
              exact hnb (k hsa)
            · intro k
              rcases Classical.em (Sat mem (univEnvOf H E) a) with hsa | hsa
              · exact ⟨hsa, fun hb => k (fun _ => hb)⟩
              · exact absurd (fun hsa' => absurd hsa' hsa) k
      | fAnd a b iha ihb =>
          intro E hE
          have hca := formCode_isFormCodeSem H a
          have hcb := formCode_isFormCodeSem H b
          refine ⟨fun h => ?_, fun h => ?_⟩
          · simp only [sigmaRank] at h
            obtain ⟨h1, h2⟩ := Nat.max_le.mp h
            have hstep : SigmaTrue H (n+1) (formCode H (fAnd a b)) E ↔
                (SigmaTrue H (n+1) (formCode H a) E ∧
                  SigmaTrue H (n+1) (formCode H b) E) :=
              sigmaTrue_and H n hca hcb hE
            rw [hstep, (iha E hE).1 h1, (ihb E hE).1 h2]
            exact Iff.rfl
          · simp only [piRank] at h
            obtain ⟨h1, h2⟩ := Nat.max_le.mp h
            have hstep : PiFalse H (n+1) (formCode H (fAnd a b)) E ↔
                (PiFalse H (n+1) (formCode H a) E ∨
                  PiFalse H (n+1) (formCode H b) E) :=
              piFalse_and H n hca hcb hE
            rw [hstep, (iha E hE).2 h1, (ihb E hE).2 h2]
            constructor
            · rintro (hna | hnb) ⟨ha, hb⟩
              · exact hna ha
              · exact hnb hb
            · intro k
              rcases Classical.em (Sat mem (univEnvOf H E) a) with hsa | hsa
              · exact Or.inr (fun hb => k ⟨hsa, hb⟩)
              · exact Or.inl hsa
      | fOr a b iha ihb =>
          intro E hE
          have hca := formCode_isFormCodeSem H a
          have hcb := formCode_isFormCodeSem H b
          refine ⟨fun h => ?_, fun h => ?_⟩
          · simp only [sigmaRank] at h
            obtain ⟨h1, h2⟩ := Nat.max_le.mp h
            have hstep : SigmaTrue H (n+1) (formCode H (fOr a b)) E ↔
                (SigmaTrue H (n+1) (formCode H a) E ∨
                  SigmaTrue H (n+1) (formCode H b) E) :=
              sigmaTrue_or H n hca hcb hE
            rw [hstep, (iha E hE).1 h1, (ihb E hE).1 h2]
            exact Iff.rfl
          · simp only [piRank] at h
            obtain ⟨h1, h2⟩ := Nat.max_le.mp h
            have hstep : PiFalse H (n+1) (formCode H (fOr a b)) E ↔
                (PiFalse H (n+1) (formCode H a) E ∧
                  PiFalse H (n+1) (formCode H b) E) :=
              piFalse_or H n hca hcb hE
            rw [hstep, (iha E hE).2 h1, (ihb E hE).2 h2]
            constructor
            · rintro ⟨hna, hnb⟩ (ha | hb)
              · exact hna ha
              · exact hnb hb
            · intro k
              exact ⟨fun ha => k (Or.inl ha), fun hb => k (Or.inr hb)⟩
      | fAll a iha =>
          intro E hE
          have hca := formCode_isFormCodeSem H (fAll a)
          refine ⟨fun h => ?_, fun h => ?_⟩
          · have hpi : piRank (fAll a) ≤ n := by
              simp only [sigmaRank] at h
              exact Nat.le_of_succ_le_succ h
            have hb : PiBounded H (natV H n) (formCode H (fAll a)) :=
              (piBounded_formCode_iff H n (fAll a)).mpr hpi
            have hsw : SigmaTrue H (n+1) (formCode H (fAll a)) E ↔
                PiTrue H n (formCode H (fAll a)) E :=
              sigmaTrue_all H n hca hE hb
            have hprev := (ih (fAll a) E hE).2 hpi
            rw [hsw]
            constructor
            · intro hp
              exact Classical.byContradiction (fun hns => hp (hprev.mpr hns))
            · intro hsat hf
              exact (hprev.mp hf) hsat
          · have hpa : piRank a ≤ n+1 := by
              simp only [piRank] at h
              exact Nat.le_trans (Nat.le_max_right 1 (piRank a)) h
            constructor
            · intro hf hsat
              obtain ⟨d, hd⟩ := piFalse_all_elim H (n+1) hE hf
              have hstep := (iha (econs H d E) (econs_isUnivEnv H hE d)).2 hpa
              rw [univEnvOf_econs H hE d] at hstep
              exact (hstep.mp hd) (hsat d)
            · intro hns
              have hex : ∃ d, ¬ Sat mem (scons d (univEnvOf H E)) a :=
                Classical.byContradiction (fun hall =>
                  hns (fun d =>
                    Classical.byContradiction (fun hnd => hall ⟨d, hnd⟩)))
              obtain ⟨d, hd⟩ := hex
              refine piFalse_all_intro H n hE (d := d) ?_
              have hstep := (iha (econs H d E) (econs_isUnivEnv H hE d)).2 hpa
              rw [univEnvOf_econs H hE d] at hstep
              exact hstep.mpr hd
      | fEx a iha =>
          intro E hE
          have hca := formCode_isFormCodeSem H (fEx a)
          refine ⟨fun h => ?_, fun h => ?_⟩
          · have hsa : sigmaRank a ≤ n+1 := by
              simp only [sigmaRank] at h
              exact Nat.le_trans (Nat.le_max_right 1 (sigmaRank a)) h
            have hstep : SigmaTrue H (n+1) (formCode H (fEx a)) E ↔
                ∃ d, SigmaTrue H (n+1) (formCode H a) (econs H d E) :=
              sigmaTrue_ex H n hE
            rw [hstep]
            constructor
            · rintro ⟨d, hd⟩
              refine ⟨d, ?_⟩
              have hb := (iha (econs H d E) (econs_isUnivEnv H hE d)).1 hsa
              rw [univEnvOf_econs H hE d] at hb
              exact hb.mp hd
            · rintro ⟨d, hd⟩
              refine ⟨d, ?_⟩
              have hb := (iha (econs H d E) (econs_isUnivEnv H hE d)).1 hsa
              rw [univEnvOf_econs H hE d] at hb
              exact hb.mpr hd
          · have hsi : sigmaRank (fEx a) ≤ n := by
              simp only [piRank] at h
              exact Nat.le_of_succ_le_succ h
            have hb : SigmaBounded H (natV H n) (formCode H (fEx a)) :=
              (sigmaBounded_formCode_iff H n (fEx a)).mpr hsi
            have hsw : PiFalse H (n+1) (formCode H (fEx a)) E ↔
                ¬ SigmaTrue H n (formCode H (fEx a)) E :=
              piFalse_ex H n hca hE hb
            rw [hsw, (ih (fEx a) E hE).1 hsi]

/-- **The Sigma side, in the form the fixed axioms consume.**  A closed external
formula true in the structure and quoted by a code of bounded complexity is
Sigma-true at the level above the bound.

The unoriented bound orients itself in at least one way.  On the Sigma side the
rank identity gives the conclusion directly; on the Pi side it gives Pi-truth at
the bound, which the collapse carries up one level and two-valuedness converts. -/
theorem sigmaTrue_formCode_of_valid (H : ZFAxioms mem) (n : Nat) {E : V}
    (hE : IsUnivEnv H E) (phi : Form)
    (hq : QuantBounded H (natV H n) (formCode H phi))
    (hsat : ∀ e : Nat → V, Sat mem e phi) :
    SigmaTrue H (n+1) (formCode H phi) E := by
  have hc := formCode_isFormCodeSem H phi
  rcases sigmaBounded_or_piBounded H hq with hb | hb
  · have hr : sigmaRank phi ≤ n := (sigmaBounded_formCode_iff H n phi).mp hb
    exact ((levelTruth_formCode H (n+1) phi E hE).1
      (Nat.le_trans hr (Nat.le_succ n))).mpr (hsat _)
  · have hr : piRank phi ≤ n := (piBounded_formCode_iff H n phi).mp hb
    have hpt : PiTrue H n (formCode H phi) E := fun hf =>
      ((levelTruth_formCode H n phi E hE).2 hr).mp hf (hsat _)
    exact (sigmaTrue_iff_piTrue H n hc hq hE).mpr
      (piTrue_mono H (Nat.le_succ n) hc hE hb hpt)

/-- Level truth of the quotation of a valid closed formula, which is what each
of the seven fixed axiom codes is.  The Pi half is exclusivity and needs no
further bound. -/
theorem levelTrue_formCode_of_valid (H : ZFAxioms mem) (n : Nat) {E : V}
    (hE : IsUnivEnv H E) (phi : Form)
    (hq : QuantBounded H (natV H n) (formCode H phi))
    (hsat : ∀ e : Nat → V, Sat mem e phi) :
    LevelTrue H n (formCode H phi) E :=
  levelTrue_of_sigmaTrue H n (formCode_isFormCodeSem H phi) hE
    (sigmaTrue_formCode_of_valid H n hE phi hq hsat)

/-! ## Descent of the bound through a universal head

The every-occurrence restriction supplies the *unoriented* bound, and the
polarity switch at a universal head consumes the Pi-oriented one.  The two are
interchangeable there: a universal code Sigma-bounded at a successor is
Pi-bounded at its predecessor, and no universal code is Sigma-bounded by
zero. -/

/-- **A bounded universal code is Pi-bounded at the same numeral.** -/
theorem piBounded_of_quantBounded_all (H : ZFAxioms mem) {a : V} {n : Nat}
    (hq : QuantBounded H (natV H n) (kpair H (natV H 6) a)) :
    PiBounded H (natV H n) (kpair H (natV H 6) a) := by
  rcases sigmaBounded_or_piBounded H hq with hb | hb
  · cases n with
    | zero => exact absurd hb (not_sigmaBounded_zero_all H)
    | succ m =>
        exact piBounded_natV_le H (Nat.le_succ m)
          (piBounded_of_sigmaBounded_all H hb)
  · exact hb

/-! ## The Separation schema

`sepCodeV H p` is the code of

```text
forall a, exists s, forall x, x in s <-> x in a and p[x]
```

with `p` an *internal* code, so in a nonstandard model it quotes no external
formula.  The witness `s` is nevertheless available, because at a fixed level the
truth predicate of the hierarchy is a `Form`: `sepSet` is `sepD` applied to it.

Two facts make the argument work at the level the bound leaves.  The schema
renaming sends the instance's free variables past the two slots the schema binds,
so the separating condition depends on the separated element alone —
`compV_rsepV_econs`.  And the carved biconditional needs Sigma-truth of the
instance in one direction and Pi-truth of it in the other, the second of which
exclusivity supplies with no bound at all. -/

/-- **Composition with a two-value shift map, by its three defining equations.**
Every schema renaming of `ZF.Zf` is such a map, so each composition identity
below is this lemma at three application equations, and no internal induction is
repeated. -/
theorem compV_twoMapV (H : ZFAxioms mem) {A B : V} (hA : IsUnivEnv H A)
    (hB : IsUnivEnv H B) (a0 a1 k : Nat)
    (h0 : applyV H A (natV H a0) = applyV H B (natV H 0))
    (h1 : applyV H A (natV H a1) = applyV H B (natV H 1))
    (hs : ∀ m, mem m (omegaV H) →
      applyV H A (vsuccIter H k m) = applyV H B (vsucc H (vsucc H m))) :
    compV H A (twoMapV H a0 a1 k) = B := by
  refine funOn_ext H (compV_isUnivEnv H hA (twoMapV_isVarMap H a0 a1 k)) hB
    (fun n hn => ?_)
  rw [compV_applyU H hA (twoMapV_isVarMap H a0 a1 k) hn]
  rcases nat_zero_or_succ H n hn with rfl | ⟨m, hm, rfl⟩
  · rw [twoMapV_zero]
    exact h0
  · rcases nat_zero_or_succ H m hm with rfl | ⟨m', hm', rfl⟩
    · rw [twoMapV_one]
      exact h1
    · rw [twoMapV_succ_succ H a0 a1 k hm']
      exact hs m' hm'

/-- **The Separation renaming, computed at a three-fold extended environment.**
Composing with `rsepV` deletes the two bound slots and shifts the rest back, so
neither the carved set nor the set being separated survives. -/
theorem compV_rsepV_econs (H : ZFAxioms mem) {E : V} (hE : IsUnivEnv H E)
    (x s d : V) :
    compV H (econs H x (econs H s (econs H d E))) (rsepV H) = econs H x E := by
  have hEd : IsUnivEnv H (econs H d E) := econs_isUnivEnv H hE d
  have hEs : IsUnivEnv H (econs H s (econs H d E)) := econs_isUnivEnv H hEd s
  have hEx : IsUnivEnv H (econs H x (econs H s (econs H d E))) :=
    econs_isUnivEnv H hEs x
  have h0 : mem (vempty H) (omegaV H) := vempty_in_omega H
  refine compV_twoMapV H hEx (econs_isUnivEnv H hE x) 0 3 4 ?_ ?_ ?_
  · exact (econs_apply_zero H hEs x).trans (econs_apply_zero H hE x).symm
  · have h1 : mem (vsucc H (vempty H)) (omegaV H) := omega_succ H _ h0
    have h2 : mem (vsucc H (vsucc H (vempty H))) (omegaV H) := omega_succ H _ h1
    exact ((econs_apply_succ H hEs x h2).trans
      ((econs_apply_succ H hEd s h1).trans (econs_apply_succ H hE d h0))).trans
      (econs_apply_succ H hE x h0).symm
  · intro m hm
    have h1 : mem (vsucc H m) (omegaV H) := omega_succ H m hm
    have h2 : mem (vsucc H (vsucc H m)) (omegaV H) := omega_succ H _ h1
    have h3 : mem (vsucc H (vsucc H (vsucc H m))) (omegaV H) :=
      omega_succ H _ h2
    exact ((econs_apply_succ H hEs x h3).trans
      ((econs_apply_succ H hEd s h2).trans (econs_apply_succ H hE d h1))).trans
      (econs_apply_succ H hE x h1).symm

/-- The separating condition of a Separation instance, as a `Form`: "the code in
slot `1` is Sigma-true at level `n` under the environment in slot `2` extended by
slot `0`".

| de Bruijn slot | contents                 |
| -------------- | ------------------------ |
| `0`            | the extended environment |
| `1`            | the separated element    |
| `2`            | the instance code        |
| `3`            | the ambient environment  |
-/
def fSepCondF (n : Nat) : Form :=
  fEx (fAnd (fEconsF 0 1 3) (fSigmaTrueF n 2 0))

/-- The parameter block of `fSepCondF`: the instance code and the ambient
environment. -/
noncomputable def envInstance (H : ZFAxioms mem) (p E : V) : Nat → V :=
  scons p (scons E (fun _ => vempty H))

theorem fSepCondF_spec (H : ZFAxioms mem) (n : Nat) {E : V} (hE : IsUnivEnv H E)
    (p x : V) :
    Sat mem (scons x (envInstance H p E)) (fSepCondF n) ↔
      SigmaTrue H n p (econs H x E) := by
  constructor
  · rintro ⟨w, hw, hs⟩
    have hw' : w = econs H x E :=
      (fEconsF_spec H (scons w (scons x (envInstance H p E))) 0 1 3 hE.1).mp hw
    have hs' := (fSigmaTrueF_spec H n
      (scons w (scons x (envInstance H p E))) 2 0).mp hs
    rw [hw'] at hs'
    exact hs'
  · intro h
    refine ⟨econs H x E, ?_, ?_⟩
    · exact (fEconsF_spec H (scons (econs H x E)
        (scons x (envInstance H p E))) 0 1 3 hE.1).mpr rfl
    · exact (fSigmaTrueF_spec H n (scons (econs H x E)
        (scons x (envInstance H p E))) 2 0).mpr h

/-- **The subset a Separation instance describes**, carved out of `d` by
Sigma-truth of the instance code at level `n`. -/
noncomputable def sepSet (H : ZFAxioms mem) (n : Nat) (p E d : V) : V :=
  sepD H (fSepCondF n) (envInstance H p E) d

theorem sepSet_spec (H : ZFAxioms mem) (n : Nat) {E : V} (hE : IsUnivEnv H E)
    (p d x : V) :
    mem x (sepSet H n p E d) ↔
      (mem x d ∧ SigmaTrue H n p (econs H x E)) :=
  (sepD_spec H (fSepCondF n) (envInstance H p E) d x).trans
    (and_congr_right fun _ => fSepCondF_spec H n hE p x)

/-- **Sigma-truth of a Separation instance code**, given that the carved subset
exists at every level.

The bound descends through the three binders, alternating polarity at each: the
outer universal is Pi-bounded at the numeral, the existential Sigma-bounded one
below it, the inner universal Pi-bounded one below that.  Since no universal code
is Pi-bounded by zero the numeral is at least three, and the level at which the
instance's truth is read is exactly two below it. -/
theorem sigmaTrue_sepCodeVOf (H : ZFAxioms mem) (n : Nat) {q E : V}
    (hq : IsFormCodeSem H q) (hE : IsUnivEnv H E)
    (hbd : QuantBounded H (natV H n) (sepCodeVOf H q))
    (hcarve : ∀ (j : Nat) (d : V), ∃ s, ∀ x, mem x s ↔
        (mem x d ∧ SigmaTrue H j q (econs H x (econs H s (econs H d E))))) :
    SigmaTrue H (n+1) (sepCodeVOf H q) E := by
  have hcA : IsFormCodeSem H (formCode H (fMem 0 1)) :=
    formCode_isFormCodeSem H (fMem 0 1)
  have hcM : IsFormCodeSem H (formCode H (fMem 0 2)) :=
    formCode_isFormCodeSem H (fMem 0 2)
  have hcB : IsFormCodeSem H (andCodeV H (formCode H (fMem 0 2)) q) :=
    andCodeV_isFormCodeSem H hcM hq
  have hcI : IsFormCodeSem H (iffCodeV H (formCode H (fMem 0 1))
      (andCodeV H (formCode H (fMem 0 2)) q)) :=
    iffCodeV_isFormCodeSem H hcA hcB
  have hcAll : IsFormCodeSem H (allCodeV H (iffCodeV H (formCode H (fMem 0 1))
      (andCodeV H (formCode H (fMem 0 2)) q))) := allCodeV_isFormCodeSem H hcI
  have hcEx : IsFormCodeSem H (exCodeV H (allCodeV H
      (iffCodeV H (formCode H (fMem 0 1))
        (andCodeV H (formCode H (fMem 0 2)) q)))) :=
    exCodeV_isFormCodeSem H hcAll
  rw [sepCodeVOf_eq H q] at hbd ⊢
  have hb0 : PiBounded H (natV H n) (allCodeV H (exCodeV H (allCodeV H
      (iffCodeV H (formCode H (fMem 0 1))
        (andCodeV H (formCode H (fMem 0 2)) q))))) :=
    piBounded_of_quantBounded_all H hbd
  have hb1 : PiBounded H (natV H n) (exCodeV H (allCodeV H
      (iffCodeV H (formCode H (fMem 0 1))
        (andCodeV H (formCode H (fMem 0 2)) q)))) :=
    piBounded_all H (natV_mem_omega H n) hb0
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := by
    cases n with
    | zero => exact absurd hb1 (not_piBounded_zero_ex H)
    | succ m => exact ⟨m, rfl⟩
  have hb3 : SigmaBounded H (natV H m) (allCodeV H
      (iffCodeV H (formCode H (fMem 0 1))
        (andCodeV H (formCode H (fMem 0 2)) q))) :=
    sigmaBounded_ex H (natV_mem_omega H m)
      (sigmaBounded_of_piBounded_ex H hb1)
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := by
    cases m with
    | zero => exact absurd hb3 (not_sigmaBounded_zero_all H)
    | succ k => exact ⟨k, rfl⟩
  have hb4 : PiBounded H (natV H k) (allCodeV H
      (iffCodeV H (formCode H (fMem 0 1))
        (andCodeV H (formCode H (fMem 0 2)) q))) :=
    piBounded_of_sigmaBounded_all H hb3
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := by
    cases k with
    | zero => exact absurd hb4 (not_piBounded_zero_all H)
    | succ j => exact ⟨j, rfl⟩
  refine sigmaTrue_all_of_piTrue H (j+1+1+1) hE hb0 ?_
  intro hf
  obtain ⟨d, hd⟩ := piFalse_all_elim H (j+1+1+1) hE hf
  have hEd : IsUnivEnv H (econs H d E) := econs_isUnivEnv H hE d
  refine piFalse_ex_elim H (j+1+1) hcEx hEd hd ?_
  obtain ⟨s, hs⟩ := hcarve (j+1) d
  have hEs : IsUnivEnv H (econs H s (econs H d E)) := econs_isUnivEnv H hEd s
  refine sigmaTrue_ex_intro H (j+1) hEd (d := s) ?_
  refine sigmaTrue_all_of_piTrue H (j+1) hEs hb4 ?_
  rw [piTrue_all H j hEs]
  intro x
  have hEx : IsUnivEnv H (econs H x (econs H s (econs H d E))) :=
    econs_isUnivEnv H hEs x
  have hx0 : applyV H (econs H x (econs H s (econs H d E))) (natV H 0) = x :=
    econs_apply_zero H hEs x
  have hx1 : applyV H (econs H x (econs H s (econs H d E))) (natV H 1) = s := by
    rw [show natV H 1 = vsucc H (natV H 0) from rfl,
      econs_apply_succ H hEs x (natV_mem_omega H 0)]
    exact econs_apply_zero H hEd s
  have hx2 : applyV H (econs H x (econs H s (econs H d E))) (natV H 2) = d := by
    rw [show natV H 2 = vsucc H (natV H 1) from rfl,
      econs_apply_succ H hEs x (natV_mem_omega H 1),
      show natV H 1 = vsucc H (natV H 0) from rfl,
      econs_apply_succ H hEd s (natV_mem_omega H 0)]
    exact econs_apply_zero H hE d
  have hAs : SigmaTrue H (j+1) (formCode H (fMem 0 1))
      (econs H x (econs H s (econs H d E))) ↔ mem x s := by
    have h := sigmaTrue_memAtom H (j+1) (natV_mem_omega H 0)
      (natV_mem_omega H 1) hEx
    rw [hx0, hx1] at h
    exact h
  have hAp : PiFalse H (j+1) (formCode H (fMem 0 1))
      (econs H x (econs H s (econs H d E))) ↔ ¬ mem x s := by
    have h := piFalse_memAtom H (j+1) (natV_mem_omega H 0)
      (natV_mem_omega H 1) hEx
    rw [hx0, hx1] at h
    exact h
  have hMs : SigmaTrue H (j+1) (formCode H (fMem 0 2))
      (econs H x (econs H s (econs H d E))) ↔ mem x d := by
    have h := sigmaTrue_memAtom H (j+1) (natV_mem_omega H 0)
      (natV_mem_omega H 2) hEx
    rw [hx0, hx2] at h
    exact h
  have hMp : PiFalse H (j+1) (formCode H (fMem 0 2))
      (econs H x (econs H s (econs H d E))) ↔ ¬ mem x d := by
    have h := piFalse_memAtom H (j+1) (natV_mem_omega H 0)
      (natV_mem_omega H 2) hEx
    rw [hx0, hx2] at h
    exact h
  intro hIf
  rcases (piFalse_and H j (impCodeV_isFormCodeSem H hcA hcB)
      (impCodeV_isFormCodeSem H hcB hcA) hEx).mp hIf with h1 | h2
  · obtain ⟨hsA, hpB⟩ := (piFalse_imp H j hcA hcB hEx).mp h1
    obtain ⟨hxd, hqt⟩ := (hs x).mp (hAs.mp hsA)
    rcases (piFalse_and H j hcM hq hEx).mp hpB with hpm | hpq
    · exact (hMp.mp hpm) hxd
    · exact sigmaTrue_not_piFalse H (j+1) q _ hq hEx hqt hpq
  · obtain ⟨hsB, hpA⟩ := (piFalse_imp H j hcB hcA hEx).mp h2
    obtain ⟨hsm, hsq⟩ := (sigmaTrue_and H j hcM hq hEx).mp hsB
    exact (hAp.mp hpA) ((hs x).mpr ⟨hMs.mp hsm, hsq⟩)

/-- **Sigma-truth of every internal Separation instance code**, including the
nonstandard ones.  The witness is `sepSet`, and the substitution lemma at a fixed
level identifies the separating condition with truth of the instance at the
environment extended by the separated element alone. -/
theorem sigmaTrue_sepCodeV (H : ZFAxioms mem) (n : Nat) {p E : V}
    (hp : IsFormCodeSem H p) (hE : IsUnivEnv H E)
    (hbd : QuantBounded H (natV H n) (sepCodeV H p)) :
    SigmaTrue H (n+1) (sepCodeV H p) E := by
  have hbd' : QuantBounded H (natV H n)
      (sepCodeVOf H (renameV H (rsepV H) p)) := hbd
  show SigmaTrue H (n+1) (sepCodeVOf H (renameV H (rsepV H) p)) E
  refine sigmaTrue_sepCodeVOf H n
    (renameV_isFormCodeSem H hp (rsepV_isVarMap H)) hE hbd'
    (fun j d => ⟨sepSet H j p E d, fun x => ?_⟩)
  rw [sepSet_spec H j hE p d x]
  refine and_congr_right (fun _ => ?_)
  rw [sigmaTrue_renameV H j hp (rsepV_isVarMap H)
      (econs_isUnivEnv H (econs_isUnivEnv H (econs_isUnivEnv H hE d)
        (sepSet H j p E d)) x),
    compV_rsepV_econs H hE x (sepSet H j p E d) d]

/-! ## The Replacement schema

`replCodeV H p` is the code of

```text
(forall x y1 y2, p[y1,x] and p[y2,x] -> y1 = y2) ->
  forall a, exists r, forall y, y in r <-> exists x in a, p[y,x]
```

again with `p` internal.  The Sigma clause of an implication offers Pi-falsity of
the antecedent *or* Sigma-truth of the succedent, so the proof splits on whether
the relation the instance defines is functional — and that is a genuine
disjunction of the metatheory, decided by excluded middle, not something the
code has to decide.

If functionality fails, the three universal quantifiers of the functionality
clause are refuted by recording the counterexample, and nothing but the recorded
witnesses is needed: `piFalse_all_intro` carries no bound.  If it holds, the
image set is `H.repl` applied to the truth predicate at the level the bound
leaves, and the image clause is verified exactly as the Separation clause is,
with exclusivity again supplying the polarity the carved biconditional does not
record.

The two branches read the instance at different levels — the counterexample at
the level of the whole implication, the image two levels below it — but only
upward monotonicity is needed to reconcile them, because the case split is made
at the lower level. -/

/-- The graph of a Replacement instance, as a `Form`: "the code in slot `4` is
Sigma-true at level `n` under the environment in slot `5` extended by the
argument in slot `3` and then by the value in slot `2`".

| de Bruijn slot | contents                        |
| -------------- | ------------------------------- |
| `0`            | the doubly extended environment |
| `1`            | the singly extended environment |
| `2`            | the value                       |
| `3`            | the argument                    |
| `4`            | the instance code               |
| `5`            | the ambient environment         |
-/
def fReplRelF (n : Nat) : Form :=
  fEx (fEx (fAnd (fEconsF 1 3 5) (fAnd (fEconsF 0 2 1) (fSigmaTrueF n 4 0))))

theorem fReplRelF_spec (H : ZFAxioms mem) (n : Nat) {E : V} (hE : IsUnivEnv H E)
    (p y x : V) :
    relOf mem (fReplRelF n) (envInstance H p E) y x ↔
      SigmaTrue H n p (econs H y (econs H x E)) := by
  have hEx : IsUnivEnv H (econs H x E) := econs_isUnivEnv H hE x
  constructor
  · rintro ⟨w1, w2, h1, h2, h3⟩
    have e1 : w1 = econs H x E :=
      (fEconsF_spec H (scons w2 (scons w1
        (scons y (scons x (envInstance H p E))))) 1 3 5 hE.1).mp h1
    have e2 : w2 = econs H y w1 :=
      (fEconsF_spec H (scons w2 (scons w1
        (scons y (scons x (envInstance H p E))))) 0 2 1 (by rw [e1]; exact hEx.1)).mp h2
    have e3 := (fSigmaTrueF_spec H n (scons w2 (scons w1
      (scons y (scons x (envInstance H p E))))) 4 0).mp h3
    rw [e2, e1] at e3
    exact e3
  · intro h
    refine ⟨econs H x E, econs H y (econs H x E), ?_, ?_, ?_⟩
    · exact (fEconsF_spec H (scons (econs H y (econs H x E))
        (scons (econs H x E) (scons y (scons x (envInstance H p E)))))
        1 3 5 hE.1).mpr rfl
    · exact (fEconsF_spec H (scons (econs H y (econs H x E))
        (scons (econs H x E) (scons y (scons x (envInstance H p E)))))
        0 2 1 hEx.1).mpr rfl
    · exact (fSigmaTrueF_spec H n (scons (econs H y (econs H x E))
        (scons (econs H x E) (scons y (scons x (envInstance H p E)))))
        4 0).mpr h

/-- **The first functionality renaming, computed at a three-fold extended
environment.** -/
theorem compV_rf1V_econs (H : ZFAxioms mem) {E : V} (hE : IsUnivEnv H E)
    (x y1 y2 : V) :
    compV H (econs H y2 (econs H y1 (econs H x E))) (rf1V H) =
      econs H y1 (econs H x E) := by
  have hEx : IsUnivEnv H (econs H x E) := econs_isUnivEnv H hE x
  have hE1 : IsUnivEnv H (econs H y1 (econs H x E)) := econs_isUnivEnv H hEx y1
  have hE2 : IsUnivEnv H (econs H y2 (econs H y1 (econs H x E))) :=
    econs_isUnivEnv H hE1 y2
  have h0 : mem (vempty H) (omegaV H) := vempty_in_omega H
  refine compV_twoMapV H hE2 hE1 1 2 3 ?_ ?_ ?_
  · exact econs_apply_succ H hE1 y2 h0
  · exact econs_apply_succ H hE1 y2 (omega_succ H _ h0)
  · intro m hm
    exact econs_apply_succ H hE1 y2 (omega_succ H _ (omega_succ H m hm))

/-- **The second functionality renaming, computed at a three-fold extended
environment.** -/
theorem compV_rf2V_econs (H : ZFAxioms mem) {E : V} (hE : IsUnivEnv H E)
    (x y1 y2 : V) :
    compV H (econs H y2 (econs H y1 (econs H x E))) (rf2V H) =
      econs H y2 (econs H x E) := by
  have hEx : IsUnivEnv H (econs H x E) := econs_isUnivEnv H hE x
  have hE1 : IsUnivEnv H (econs H y1 (econs H x E)) := econs_isUnivEnv H hEx y1
  have hE2 : IsUnivEnv H (econs H y2 (econs H y1 (econs H x E))) :=
    econs_isUnivEnv H hE1 y2
  have h0 : mem (vempty H) (omegaV H) := vempty_in_omega H
  refine compV_twoMapV H hE2 (econs_isUnivEnv H hEx y2) 0 2 3 ?_ ?_ ?_
  · exact (econs_apply_zero H hE1 y2).trans (econs_apply_zero H hEx y2).symm
  · exact ((econs_apply_succ H hE1 y2 (omega_succ H _ h0)).trans
      (econs_apply_succ H hEx y1 h0)).trans
      (econs_apply_succ H hEx y2 h0).symm
  · intro m hm
    have h1 : mem (vsucc H m) (omegaV H) := omega_succ H m hm
    exact ((econs_apply_succ H hE1 y2 (omega_succ H _ h1)).trans
      (econs_apply_succ H hEx y1 h1)).trans
      (econs_apply_succ H hEx y2 h1).symm

/-- **The image renaming, computed at a four-fold extended environment.**  The
two distinguished arguments are exchanged, which is what `ri` does. -/
theorem compV_riV_econs (H : ZFAxioms mem) {E : V} (hE : IsUnivEnv H E)
    (a r y x : V) :
    compV H (econs H x (econs H y (econs H r (econs H a E)))) (riV H) =
      econs H y (econs H x E) := by
  have hEa : IsUnivEnv H (econs H a E) := econs_isUnivEnv H hE a
  have hEr : IsUnivEnv H (econs H r (econs H a E)) := econs_isUnivEnv H hEa r
  have hEy : IsUnivEnv H (econs H y (econs H r (econs H a E))) :=
    econs_isUnivEnv H hEr y
  have hEx4 : IsUnivEnv H (econs H x (econs H y (econs H r (econs H a E)))) :=
    econs_isUnivEnv H hEy x
  have hEx : IsUnivEnv H (econs H x E) := econs_isUnivEnv H hE x
  have h0 : mem (vempty H) (omegaV H) := vempty_in_omega H
  refine compV_twoMapV H hEx4 (econs_isUnivEnv H hEx y) 1 0 4 ?_ ?_ ?_
  · exact (econs_apply_succ H hEy x h0).trans
      ((econs_apply_zero H hEr y).trans (econs_apply_zero H hEx y).symm)
  · exact (econs_apply_zero H hEy x).trans
      (((econs_apply_succ H hEx y h0).trans
        (econs_apply_zero H hE x)).symm)
  · intro m hm
    have h1 : mem (vsucc H m) (omegaV H) := omega_succ H m hm
    have h2 : mem (vsucc H (vsucc H m)) (omegaV H) := omega_succ H _ h1
    have h3 : mem (vsucc H (vsucc H (vsucc H m))) (omegaV H) :=
      omega_succ H _ h2
    exact ((econs_apply_succ H hEy x h3).trans
      ((econs_apply_succ H hEr y h2).trans
        ((econs_apply_succ H hEa r h1).trans
          (econs_apply_succ H hE a hm)))).trans
      ((econs_apply_succ H hEx y h1).trans
        (econs_apply_succ H hE x hm)).symm

/-- **Sigma-truth of a Replacement instance code**, given the graph the instance
denotes abstractly.

`P l` is the relation the instance defines when read at level `l`; the three
`e`-hypotheses say that the three renamed copies of the instance are read as that
relation at the environments the schema's binders produce, `hmono` that the
reading is monotone in the level, and `himg` that a functional reading has
images.  All four are supplied by the substitution lemma and by `H.repl` in
`sigmaTrue_replCodeV`. -/
theorem sigmaTrue_replCodeVOf (H : ZFAxioms mem) (n : Nat) {q1 q2 q3 E : V}
    (hq1 : IsFormCodeSem H q1) (hq2 : IsFormCodeSem H q2)
    (hq3 : IsFormCodeSem H q3) (hE : IsUnivEnv H E)
    (hbd : QuantBounded H (natV H n) (replCodeVOf H q1 q2 q3))
    (P : Nat → V → V → Prop)
    (e1 : ∀ (l : Nat) (x y1 y2 : V),
      SigmaTrue H l q1 (econs H y2 (econs H y1 (econs H x E))) ↔ P l y1 x)
    (e2 : ∀ (l : Nat) (x y1 y2 : V),
      SigmaTrue H l q2 (econs H y2 (econs H y1 (econs H x E))) ↔ P l y2 x)
    (e3 : ∀ (l : Nat) (a r y x : V),
      SigmaTrue H l q3 (econs H x (econs H y (econs H r (econs H a E)))) ↔
        P l y x)
    (hmono : ∀ (l l' : Nat), l ≤ l' → ∀ y x, P l y x → P l' y x)
    (himg : ∀ (l : Nat) (a : V), (∀ x y1 y2, P l y1 x → P l y2 x → y1 = y2) →
      ∃ r, ∀ y, mem y r ↔ ∃ x, mem x a ∧ P l y x) :
    SigmaTrue H (n+1) (replCodeVOf H q1 q2 q3) E := by
  have hcEq : IsFormCodeSem H (formCode H (fEq 1 0)) :=
    formCode_isFormCodeSem H (fEq 1 0)
  have hcA : IsFormCodeSem H (formCode H (fMem 0 1)) :=
    formCode_isFormCodeSem H (fMem 0 1)
  have hcM3 : IsFormCodeSem H (formCode H (fMem 0 3)) :=
    formCode_isFormCodeSem H (fMem 0 3)
  have hcF : IsFormCodeSem H (allCodeV H (allCodeV H (allCodeV H
      (impCodeV H (andCodeV H q1 q2) (formCode H (fEq 1 0)))))) :=
    allCodeV_isFormCodeSem H (allCodeV_isFormCodeSem H
      (allCodeV_isFormCodeSem H (impCodeV_isFormCodeSem H
        (andCodeV_isFormCodeSem H hq1 hq2) hcEq)))
  have hcC : IsFormCodeSem H
      (exCodeV H (andCodeV H (formCode H (fMem 0 3)) q3)) :=
    exCodeV_isFormCodeSem H (andCodeV_isFormCodeSem H hcM3 hq3)
  have hcIall : IsFormCodeSem H (allCodeV H (iffCodeV H (formCode H (fMem 0 1))
      (exCodeV H (andCodeV H (formCode H (fMem 0 3)) q3)))) :=
    allCodeV_isFormCodeSem H (iffCodeV_isFormCodeSem H hcA hcC)
  have hcIex : IsFormCodeSem H (exCodeV H (allCodeV H
      (iffCodeV H (formCode H (fMem 0 1))
        (exCodeV H (andCodeV H (formCode H (fMem 0 3)) q3))))) :=
    exCodeV_isFormCodeSem H hcIall
  have hcI : IsFormCodeSem H (allCodeV H (exCodeV H (allCodeV H
      (iffCodeV H (formCode H (fMem 0 1))
        (exCodeV H (andCodeV H (formCode H (fMem 0 3)) q3)))))) :=
    allCodeV_isFormCodeSem H hcIex
  rw [replCodeVOf_eq H q1 q2 q3] at hbd ⊢
  have hqI : QuantBounded H (natV H n) (allCodeV H (exCodeV H (allCodeV H
      (iffCodeV H (formCode H (fMem 0 1))
        (exCodeV H (andCodeV H (formCode H (fMem 0 3)) q3)))))) := by
    rcases sigmaBounded_or_piBounded H hbd with hb | hb
    · exact quantBounded_of_sigmaBounded H (natV_mem_omega H n)
        (sigmaBounded_imp H (natV_mem_omega H n) hb).2
    · exact quantBounded_of_piBounded H (natV_mem_omega H n)
        (piBounded_imp H (natV_mem_omega H n) hb).2
  have hbI : PiBounded H (natV H n) (allCodeV H (exCodeV H (allCodeV H
      (iffCodeV H (formCode H (fMem 0 1))
        (exCodeV H (andCodeV H (formCode H (fMem 0 3)) q3)))))) :=
    piBounded_of_quantBounded_all H hqI
  have hb1 : PiBounded H (natV H n) (exCodeV H (allCodeV H
      (iffCodeV H (formCode H (fMem 0 1))
        (exCodeV H (andCodeV H (formCode H (fMem 0 3)) q3))))) :=
    piBounded_all H (natV_mem_omega H n) hbI
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := by
    cases n with
    | zero => exact absurd hb1 (not_piBounded_zero_ex H)
    | succ m => exact ⟨m, rfl⟩
  have hb3 : SigmaBounded H (natV H m) (allCodeV H
      (iffCodeV H (formCode H (fMem 0 1))
        (exCodeV H (andCodeV H (formCode H (fMem 0 3)) q3)))) :=
    sigmaBounded_ex H (natV_mem_omega H m)
      (sigmaBounded_of_piBounded_ex H hb1)
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := by
    cases m with
    | zero => exact absurd hb3 (not_sigmaBounded_zero_all H)
    | succ k => exact ⟨k, rfl⟩
  have hb4 : PiBounded H (natV H k) (allCodeV H
      (iffCodeV H (formCode H (fMem 0 1))
        (exCodeV H (andCodeV H (formCode H (fMem 0 3)) q3)))) :=
    piBounded_of_sigmaBounded_all H hb3
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := by
    cases k with
    | zero => exact absurd hb4 (not_piBounded_zero_all H)
    | succ j => exact ⟨j, rfl⟩
  refine (sigmaTrue_imp H (j+1+1+1) hcF hcI hE).mpr ?_
  rcases Classical.em (∀ x y1 y2, P (j+1) y1 x → P (j+1) y2 x → y1 = y2)
    with hfun | hnf
  · refine Or.inr ?_
    refine sigmaTrue_all_of_piTrue H (j+1+1+1) hE hbI ?_
    intro hf
    obtain ⟨a, ha⟩ := piFalse_all_elim H (j+1+1+1) hE hf
    have hEa : IsUnivEnv H (econs H a E) := econs_isUnivEnv H hE a
    refine piFalse_ex_elim H (j+1+1) hcIex hEa ha ?_
    obtain ⟨r, hr⟩ := himg (j+1) a hfun
    have hEr : IsUnivEnv H (econs H r (econs H a E)) := econs_isUnivEnv H hEa r
    refine sigmaTrue_ex_intro H (j+1) hEa (d := r) ?_
    refine sigmaTrue_all_of_piTrue H (j+1) hEr hb4 ?_
    rw [piTrue_all H j hEr]
    intro y
    have hEy : IsUnivEnv H (econs H y (econs H r (econs H a E))) :=
      econs_isUnivEnv H hEr y
    have h0 : mem (vempty H) (omegaV H) := vempty_in_omega H
    have hy0 : applyV H (econs H y (econs H r (econs H a E))) (natV H 0) = y :=
      econs_apply_zero H hEr y
    have hy1 : applyV H (econs H y (econs H r (econs H a E))) (natV H 1) = r :=
      (econs_apply_succ H hEr y h0).trans (econs_apply_zero H hEa r)
    have hAs : SigmaTrue H (j+1) (formCode H (fMem 0 1))
        (econs H y (econs H r (econs H a E))) ↔ mem y r := by
      have h := sigmaTrue_memAtom H (j+1) (natV_mem_omega H 0)
        (natV_mem_omega H 1) hEy
      rw [hy0, hy1] at h
      exact h
    have hAp : PiFalse H (j+1) (formCode H (fMem 0 1))
        (econs H y (econs H r (econs H a E))) ↔ ¬ mem y r := by
      have h := piFalse_memAtom H (j+1) (natV_mem_omega H 0)
        (natV_mem_omega H 1) hEy
      rw [hy0, hy1] at h
      exact h
    have hM3s : ∀ x : V, SigmaTrue H (j+1) (formCode H (fMem 0 3))
        (econs H x (econs H y (econs H r (econs H a E)))) ↔ mem x a := by
      intro x
      have hx0 : applyV H (econs H x (econs H y (econs H r (econs H a E))))
          (natV H 0) = x := econs_apply_zero H hEy x
      have hx3 : applyV H (econs H x (econs H y (econs H r (econs H a E))))
          (natV H 3) = a :=
        (econs_apply_succ H hEy x (natV_mem_omega H 2)).trans
          ((econs_apply_succ H hEr y (natV_mem_omega H 1)).trans
            ((econs_apply_succ H hEa r (natV_mem_omega H 0)).trans
              (econs_apply_zero H hE a)))
      have h := sigmaTrue_memAtom H (j+1) (natV_mem_omega H 0)
        (natV_mem_omega H 3) (econs_isUnivEnv H hEy x)
      rw [hx0, hx3] at h
      exact h
    intro hIf
    rcases (piFalse_and H j (impCodeV_isFormCodeSem H hcA hcC)
        (impCodeV_isFormCodeSem H hcC hcA) hEy).mp hIf with hL | hR
    · obtain ⟨hsA, hpC⟩ := (piFalse_imp H j hcA hcC hEy).mp hL
      obtain ⟨x, hxa, hPyx⟩ := (hr y).mp (hAs.mp hsA)
      refine sigmaTrue_not_piFalse H (j+1) _ _ hcC hEy ?_ hpC
      exact sigmaTrue_ex_intro H j hEy (d := x)
        (sigmaTrue_and_intro H j (econs_isUnivEnv H hEy x)
          ((hM3s x).mpr hxa) ((e3 (j+1) a r y x).mpr hPyx))
    · obtain ⟨hsC, hpA⟩ := (piFalse_imp H j hcC hcA hEy).mp hR
      obtain ⟨x, hx⟩ := (sigmaTrue_ex H j hEy).mp hsC
      obtain ⟨hm3, hq3t⟩ :=
        (sigmaTrue_and H j hcM3 hq3 (econs_isUnivEnv H hEy x)).mp hx
      exact (hAp.mp hpA)
        ((hr y).mpr ⟨x, (hM3s x).mp hm3, (e3 (j+1) a r y x).mp hq3t⟩)
  · refine Or.inl ?_
    have hex : ∃ x y1 y2, P (j+1) y1 x ∧ P (j+1) y2 x ∧ y1 ≠ y2 :=
      Classical.byContradiction (fun hno => hnf (fun x y1 y2 hR1 hR2 =>
        Classical.byContradiction (fun hne => hno ⟨x, y1, y2, hR1, hR2, hne⟩)))
    obtain ⟨x, y1, y2, hR1, hR2, hne⟩ := hex
    have hEx : IsUnivEnv H (econs H x E) := econs_isUnivEnv H hE x
    have hE1 : IsUnivEnv H (econs H y1 (econs H x E)) := econs_isUnivEnv H hEx y1
    have hE2 : IsUnivEnv H (econs H y2 (econs H y1 (econs H x E))) :=
      econs_isUnivEnv H hE1 y2
    have h0 : mem (vempty H) (omegaV H) := vempty_in_omega H
    refine piFalse_all_intro H (j+1+1+1) hE (d := x) ?_
    refine piFalse_all_intro H (j+1+1+1) hEx (d := y1) ?_
    refine piFalse_all_intro H (j+1+1+1) hE1 (d := y2) ?_
    refine (piFalse_imp H (j+1+1+1) (andCodeV_isFormCodeSem H hq1 hq2) hcEq
      hE2).mpr ⟨?_, ?_⟩
    · refine sigmaTrue_and_intro H (j+1+1+1) hE2 ?_ ?_
      · exact (e1 (j+1+1+1+1) x y1 y2).mpr
          (hmono (j+1) (j+1+1+1+1) (by omega) y1 x hR1)
      · exact (e2 (j+1+1+1+1) x y1 y2).mpr
          (hmono (j+1) (j+1+1+1+1) (by omega) y2 x hR2)
    · have hz0 : applyV H (econs H y2 (econs H y1 (econs H x E)))
          (natV H 0) = y2 := econs_apply_zero H hE1 y2
      have hz1 : applyV H (econs H y2 (econs H y1 (econs H x E)))
          (natV H 1) = y1 :=
        (econs_apply_succ H hE1 y2 h0).trans (econs_apply_zero H hEx y1)
      have h := piFalse_eqAtom H (j+1+1+1+1) (natV_mem_omega H 1)
        (natV_mem_omega H 0) hE2
      rw [hz0, hz1] at h
      exact h.mpr hne

/-- **Sigma-truth of every internal Replacement instance code**, including the
nonstandard ones.  The relation is the instance read at the level the bound
leaves, the image set is `H.repl` applied to `fReplRelF`, and the three renamed
copies are identified with it by the substitution lemma. -/
theorem sigmaTrue_replCodeV (H : ZFAxioms mem) (n : Nat) {p E : V}
    (hp : IsFormCodeSem H p) (hE : IsUnivEnv H E)
    (hbd : QuantBounded H (natV H n) (replCodeV H p)) :
    SigmaTrue H (n+1) (replCodeV H p) E := by
  have hbd' : QuantBounded H (natV H n)
      (replCodeVOf H (renameV H (rf1V H) p) (renameV H (rf2V H) p)
        (renameV H (riV H) p)) := hbd
  show SigmaTrue H (n+1) (replCodeVOf H (renameV H (rf1V H) p)
    (renameV H (rf2V H) p) (renameV H (riV H) p)) E
  refine sigmaTrue_replCodeVOf H n
    (renameV_isFormCodeSem H hp (rf1V_isVarMap H))
    (renameV_isFormCodeSem H hp (rf2V_isVarMap H))
    (renameV_isFormCodeSem H hp (riV_isVarMap H)) hE hbd'
    (fun l y x => SigmaTrue H l p (econs H y (econs H x E)))
    (fun l x y1 y2 => ?_) (fun l x y1 y2 => ?_) (fun l a r y x => ?_)
    (fun l l' hle y x h => ?_) (fun l a hfun => ?_)
  · have hE2 : IsUnivEnv H (econs H y2 (econs H y1 (econs H x E))) :=
      econs_isUnivEnv H (econs_isUnivEnv H (econs_isUnivEnv H hE x) y1) y2
    rw [sigmaTrue_renameV H l hp (rf1V_isVarMap H) hE2,
      compV_rf1V_econs H hE x y1 y2]
  · have hE2 : IsUnivEnv H (econs H y2 (econs H y1 (econs H x E))) :=
      econs_isUnivEnv H (econs_isUnivEnv H (econs_isUnivEnv H hE x) y1) y2
    rw [sigmaTrue_renameV H l hp (rf2V_isVarMap H) hE2,
      compV_rf2V_econs H hE x y1 y2]
  · have hE4 : IsUnivEnv H (econs H x (econs H y (econs H r (econs H a E)))) :=
      econs_isUnivEnv H (econs_isUnivEnv H (econs_isUnivEnv H
        (econs_isUnivEnv H hE a) r) y) x
    rw [sigmaTrue_renameV H l hp (riV_isVarMap H) hE4,
      compV_riV_econs H hE a r y x]
  · exact sigmaTrue_mono H hle
      (econs_isUnivEnv H (econs_isUnivEnv H hE x) y) h
  · have hspec : ∀ y x : V,
        relOf mem (fReplRelF l) (envInstance H p E) y x ↔
          SigmaTrue H l p (econs H y (econs H x E)) :=
      fun y x => fReplRelF_spec H l hE p y x
    obtain ⟨r, hrr⟩ := H.repl (fReplRelF l) (envInstance H p E)
      (fun x y1 y2 k1 k2 =>
        hfun x y1 y2 ((hspec y1 x).mp k1) ((hspec y2 x).mp k2)) a
    exact ⟨r, fun y => (hrr y).trans
      (exists_congr (fun x => and_congr_right (fun _ => hspec y x)))⟩

/-! ## The obligation, discharged

The nine clauses of `IsZFCAxiomCode` split into the seven quotations, each of
which is `levelTrue_formCode_of_valid` at one bridge, and the two schemas, each
of which is one of the two theorems above followed by exclusivity. -/

/-- **Every internal ZFC axiom code of bounded complexity is true at the
level**, the last of the three obligations named in
`BoundedZFCConsistency.LevelSoundness`.

The quantification over codes is internal, so the two schema clauses cover the
nonstandard instances the internal axiom set contains and which no external
formula quotes. -/
theorem axiomCodesTrueAt (K : ZFCAxioms mem) (n : Nat) :
    AxiomCodesTrueAt K.toZFAxioms n := by
  intro c E hc hbd hE
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | ⟨p, hp, rfl⟩ |
    ⟨p, hp, rfl⟩
  · exact levelTrue_formCode_of_valid K.toZFAxioms n hE Ext_form hbd
      (sat_Ext_form K)
  · exact levelTrue_formCode_of_valid K.toZFAxioms n hE Pair_form hbd
      (sat_Pair_form K)
  · exact levelTrue_formCode_of_valid K.toZFAxioms n hE Union_form hbd
      (sat_Union_form K)
  · exact levelTrue_formCode_of_valid K.toZFAxioms n hE Pow_form hbd
      (sat_Pow_form K)
  · exact levelTrue_formCode_of_valid K.toZFAxioms n hE Inf_form hbd
      (sat_Inf_form K)
  · exact levelTrue_formCode_of_valid K.toZFAxioms n hE Reg_form hbd
      (sat_Reg_form K)
  · exact levelTrue_formCode_of_valid K.toZFAxioms n hE Choice_form hbd
      (sat_Choice_form K)
  · exact levelTrue_of_sigmaTrue K.toZFAxioms n
      (sepCodeV_isFormCodeSem K.toZFAxioms hp) hE
      (sigmaTrue_sepCodeV K.toZFAxioms n hp hE hbd)
  · exact levelTrue_of_sigmaTrue K.toZFAxioms n
      (replCodeV_isFormCodeSem K.toZFAxioms hp) hE
      (sigmaTrue_replCodeV K.toZFAxioms n hp hE hbd)

/-- **No bounded coded refutation from the internal ZFC axioms**, in any
structure carrying the richer bundle.  This is `noBoundedRefutationAtLevel` with
its axiom-truth premise discharged. -/
theorem noBoundedRefutationAtLevel_zfc (K : ZFCAxioms mem) (n : Nat) :
    NoBoundedRefutationAtLevel K.toZFAxioms n :=
  noBoundedRefutationAtLevel K.toZFAxioms n (axiomCodesTrueAt K n)

end AxiomTruth

/-! ## From models of ZFC to the object-level derivation

`zfAxioms_of_zfcModel` extracts the six-axiom bundle from a model of the sealed
sentence theory.  The three further principles are extracted from the same model
by the same pattern, so the richer bundle is available wherever the weaker one
is, and the endpoint bridge of `BoundedZFCConsistency.AxiomCode` applies with no
residual hypothesis. -/

section Endpoint

open SetTheory.FirstOrderClassicalCompleteness

/-- **A model of ZFC carries the richer semantic bundle.**  The three added
fields are `bridge_Pow`, `bridge_Reg` and `bridge_Choice` at the corresponding
sealed axioms. -/
theorem zfcAxioms_of_zfcModel {Dom : Type} {m : Dom → Dom → Prop} (v : Nat → Dom)
    (hmodel : ∀ g, ZFCax_s g → Sat m v g) : ZFCAxioms m :=
  { toZFAxioms := zfAxioms_of_zfcModel v hmodel
    pow := bridge_Pow_fwd
      (extract ZFCax_s v Pow_form hmodel
        (Or.inl (Or.inr (Or.inr (Or.inl rfl)))))
    reg := bridge_Reg_fwd
      (extract ZFCax_s v Reg_form hmodel (Or.inl (Or.inr (Or.inl rfl))))
    choice := bridge_Choice_fwd
      (extract ZFCax_s v Choice_form hmodel (Or.inr rfl)) }

/-- `Con_n(ZFC)` is a semantic consequence of ZFC, with no hypothesis: every
model of the sealed axioms carries the bundle, and no such structure admits a
bounded coded refutation from a context of axiom codes. -/
theorem conZFCForm_semanticConsequence_zfc (n : Nat) :
    TheorySemanticConsequence ZFCax_s (conZFCForm n) := by
  intro Dom m v hmodel
  exact (sat_conZFCForm_iff (zfcAxioms_of_zfcModel v hmodel).toZFAxioms n).mpr
    (noBoundedRefutationAtLevel_zfc (zfcAxioms_of_zfcModel v hmodel) n) v

/-- **`ZFC |- Con_n(ZFC)`, for every metatheoretic `n`.**

The parameter is specialized outside the object theory: each `n` yields a
separate derivation, and no single derivation proves the universal closure over
`n`.  That is the whole content of the Gödel-II boundary, and it is visible in
the type — the `Nat` is an argument of the theorem, not a de Bruijn slot of the
sentence. -/
theorem zfcprov_conZFCForm (n : Nat) :
    TheorySyntacticConsequence ZFCax_s (conZFCForm n) :=
  zfcprov_conZFCForm_of_valid n (conZFCForm_semanticConsequence_zfc n)

end Endpoint

end BoundedZFCConsistency
end LeanProofs
