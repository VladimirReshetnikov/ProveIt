import ZFCinPA.LGlue3

set_option autoImplicit false
noncomputable section

/-!
# The glue, internally: the formula induction

For every formula code `q` (level `0`) whose free variables lie below `j`,
`𝗭𝗙 ⊢ ∀t (¬M_j t ∨ (relativize L q ↔ envForm 0 q (t)))` (`glue`).

The induction is `IsFormula.sigma1_structural_induction`, whose quantifier
case passes through `free`, as the Tait rule does. The number of matched
variables grows by one per `free`, so the induction carries the budget
`j + complexity q ≤ C`. Each case compiles one step template of `LGlueT2`:
atoms by `LGlue3.glue_atom`, connectives literally, and quantifiers by
generalizing the freed premise (`LGlue2.QX_free`).
-/

namespace LeanProofs.ZFCinPA.LGlue4

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LO.FirstOrder.SetTheory Entailment
open LeanProofs.ZFCinPA LeanProofs.ZFCinPA.SetPlaceholders LeanProofs.ZFCinPA.LTemplate
open LeanProofs.ZFCinPA.LInvariant LeanProofs.ZFCinPA.EnvTransform LeanProofs.ZFCinPA.LDriverBase
open LeanProofs.ZFCinPA.LGlueT LeanProofs.ZFCinPA.LGlueT2 LeanProofs.ZFCinPA.LMatch
open LeanProofs.ZFCinPA.LGlue1 LeanProofs.ZFCinPA.LGlue2 LeanProofs.ZFCinPA.LGlue3
open LeanProofs.ZFCinPA.LGlueCodes LeanProofs.BoundedPAConsistency.InternalRelativization
open LeanProofs.ZFCinPA.NumeralOmega (numChainQ)
open LeanProofs.ZFCinPA.ConstructibleInterpretation (domL)
open scoped LO.FirstOrder.Arithmetic

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The domain of `L`, as a code. -/
abbrev dL : V := (⌜domL⌝ : V)

lemma hdL : IsSemiformula ℒₛₑₜ 1 (dL (V := V)) := ConstructibleInterpretation.isSemiformula_quote_domL
lemma hdLs : shift ℒₛₑₜ (dL (V := V)) = dL := ConstructibleInterpretation.shift_quote_domL

/-- The relativization to `L`. -/
abbrev rel (q : V) : V := relativize ℒₛₑₜ dL q

/-- The glue statement, on codes. -/
def gVal (j q : V) : V :=
  ^∀ (neg ℒₛₑₜ (mVal j) ^⋎
    ((neg ℒₛₑₜ (rel q) ^⋎ envForm 0 q) ^⋏ (neg ℒₛₑₜ (envForm 0 q) ^⋎ rel q)))

instance gVal_definable : 𝚺₁-Function₂ (gVal : V → V → V) := by
  unfold gVal rel
  definability

theorem GF_val (M R E : SF V 1) :
    (GF M R E).val = ^∀ (neg ℒₛₑₜ M.val ^⋎ ((neg ℒₛₑₜ R.val ^⋎ E.val) ^⋏ (neg ℒₛₑₜ E.val ^⋎ R.val))) := by
  simp [GF, LogicalConnective.iff, Bootstrapping.Semiformula.imp_def]

theorem gVal_of_GF {j q : V} (R E : SF V 1) (hR : R.val = rel q) (hE : E.val = envForm 0 q)
    (h : (𝗭𝗙 : SetTheory).internalize V ⊢ GF (MT j) R E) :
    Bootstrapping.Provable (𝗭𝗙 : SetTheory) (gVal j q) := by
  have := Bootstrapping.tprovable_iff_provable.mp h
  rwa [GF_val, hR, hE] at this

theorem GF_of_gVal {j q : V} (R E : SF V 1) (hR : R.val = rel q) (hE : E.val = envForm 0 q)
    (h : Bootstrapping.Provable (𝗭𝗙 : SetTheory) (gVal j q)) :
    (𝗭𝗙 : SetTheory).internalize V ⊢ GF (MT j) R E :=
  Bootstrapping.tprovable_iff_provable.mpr (by rw [GF_val, hR, hE]; exact h)

/-! ## Typed sides -/

/-- The relativized side, read at level one. -/
def RF {n p : V} (hp : IsSemiformula ℒₛₑₜ n p) (hn : n ≤ 1) : SF V 1 :=
  ⟨rel p, by simpa using isSemiformula_of_le (isSemiformula_relativize hdL hp) hn⟩

/-- `relativize`'s existential clause. -/
def RExT (R : SF V 1) : SF V 1 :=
  ∃⁰ ((⌜domL⌝ : SF V 1).subst (fun _ ↦ Bootstrapping.Semiterm.bvar 0) ⋏
    R.subst (fun _ ↦ Bootstrapping.Semiterm.bvar 0))

/-- `envForm`'s existential clause. -/
def EExT (E : SF V 1) : SF V 1 :=
  ∃⁰ ∃⁰ ((⌜econsS⌝ : SF V 3) ⋏ ((⌜domYS⌝ : SF V 3) ⋏ E.subst (fun _ ↦ Bootstrapping.Semiterm.bvar 0)))

section Concl

variable (Ks : (i : Fin 8) → SF V (arG i))

theorem tr_concl2 (A B : Semisentence GL 1) :
    translateFormula Ks (Rewriting.emb (∀⁰ (∼G 0 ⋎ (A 🡘 B)) : Sentence GL)) =
      GF (Ks 0) (translateFormula Ks (Rewriting.emb A)) (translateFormula Ks (Rewriting.emb B)) := by
  simp [GF, G, translateFormula, LogicalConnective.iff, Bootstrapping.Semiformula.imp_def]

theorem tr_relEx : translateFormula Ks (Rewriting.emb relEx) = RExT (Ks 1) := by
  simp [relEx, G, translateFormula, RExT]

theorem tr_envEx : translateFormula Ks (Rewriting.emb envEx) = EExT (Ks 2) := by
  simp [envEx, G, translateFormula, EExT]

end Concl

/-- Substituting `#0` for `#0` fixes a level-one code. -/
theorem sv0 (P : SF V 1) : subst ℒₛₑₜ (^#0 ∷ 0) P.val = P.val := by
  have h := congrArg Bootstrapping.Semiformula.val (Bootstrapping.Semiformula.subst_eq_self₁ P)
  rw [Bootstrapping.Semiformula.val_substs] at h
  have hv : Bootstrapping.SemitermVec.val
      (![Bootstrapping.Semiterm.bvar 0] : Bootstrapping.SemitermVec V ℒₛₑₜ 1 1) = ^#0 ∷ 0 := by
    simp [Bootstrapping.SemitermVec.val, Matrix.vecHead, Matrix.vecTail]
  rwa [hv] at h

theorem rAllT_val {p : V} (R : SF V 1) (hR : R.val = rel p) (hp : IsUFormula ℒₛₑₜ p) :
    (RAllT R).val = rel (^∀ p) := by
  have h1 := sv0 R
  rw [hR] at h1
  rw [rel, relativize_all hp]
  simp [RAllT, hR, h1, sv0 (⌜domL⌝ : SF V 1)]
  rfl

theorem rExT_val {p : V} (R : SF V 1) (hR : R.val = rel p) (hp : IsUFormula ℒₛₑₜ p) :
    (RExT R).val = rel (^∃ p) := by
  have h1 := sv0 R
  rw [hR] at h1
  rw [rel, relativize_exs hp]
  simp [RExT, hR, h1, sv0 (⌜domL⌝ : SF V 1)]
  rfl

theorem eAllT_val {p : V} (hp : IsSemiformula ℒₛₑₜ 1 p) :
    (EAllT (LDriver.envFormT 1 hp)).val = envForm 0 (^∀ p) := by
  have h1 := sv0 (LDriver.envFormT 1 hp)
  rw [envForm_all hp.isUFormula, LDriver.quote_neg_val, LDriver.quote_neg_val]
  simp [EAllT, LDriver.envFormT] at h1 ⊢
  and_intros <;> first | rfl | exact h1

theorem eExT_val {p : V} (hp : IsSemiformula ℒₛₑₜ 1 p) :
    (EExT (LDriver.envFormT 1 hp)).val = envForm 0 (^∃ p) := by
  have h1 := sv0 (LDriver.envFormT 1 hp)
  rw [envForm_exs hp.isUFormula]
  simp [EExT, LDriver.envFormT] at h1 ⊢
  and_intros <;> first | rfl | exact h1

/-! ## The cases -/

section Cases

variable (Ks : (i : Fin 8) → SF V (arG i))

theorem tr_andC : translateFormula Ks (Rewriting.emb (∀⁰ (∼G 0 ⋎ (G 1 ⋏ G 3 🡘 G 2 ⋏ G 4)) : Sentence GL)) =
    GF (Ks 0) (Ks 1 ⋏ Ks 3) (Ks 2 ⋏ Ks 4) := by
  simp [GF, G, translateFormula, LogicalConnective.iff, Bootstrapping.Semiformula.imp_def]

theorem tr_orC : translateFormula Ks (Rewriting.emb (∀⁰ (∼G 0 ⋎ (G 1 ⋎ G 3 🡘 G 2 ⋎ G 4)) : Sentence GL)) =
    GF (Ks 0) (Ks 1 ⋎ Ks 3) (Ks 2 ⋎ Ks 4) := by
  simp [GF, G, translateFormula, LogicalConnective.iff, Bootstrapping.Semiformula.imp_def]

theorem tr_negC : translateFormula Ks (Rewriting.emb (∀⁰ (∼G 0 ⋎ (∼G 1 🡘 ∼G 2)) : Sentence GL)) =
    GF (Ks 0) (∼Ks 1) (∼Ks 2) := by
  simp [GF, G, translateFormula, LogicalConnective.iff, Bootstrapping.Semiformula.imp_def]

end Cases

theorem case_top (j : V) : Bootstrapping.Provable (𝗭𝗙 : SetTheory) (gVal j ^⊤) := by
  have hc := compiledG topG_provable (K8 (MT j) ⊤ ⊤ ⊤ ⊤ ⊤ ⊤ ⊤ : (i : Fin 8) → SF V (arG i))
  have h : (𝗭𝗙 : SetTheory).internalize V ⊢ GF (MT j) ⊤ ⊤ := by
    simpa [topG, G, GF, translateFormula, K8, LogicalConnective.iff,
      Bootstrapping.Semiformula.imp_def] using hc
  exact gVal_of_GF ⊤ ⊤ (by simp [rel]) (by simp) h

theorem case_bot (j : V) : Bootstrapping.Provable (𝗭𝗙 : SetTheory) (gVal j ^⊥) := by
  have hc := compiledG botG_provable (K8 (MT j) ⊤ ⊤ ⊤ ⊤ ⊤ ⊤ ⊤ : (i : Fin 8) → SF V (arG i))
  have h : (𝗭𝗙 : SetTheory).internalize V ⊢ GF (MT j) ⊥ ⊥ := by
    simpa [botG, G, GF, translateFormula, K8, LogicalConnective.iff,
      Bootstrapping.Semiformula.imp_def] using hc
  exact gVal_of_GF ⊥ ⊥ (by simp [rel]) (by simp) h

theorem case_and {j p q : V} (hp : IsFormula ℒₛₑₜ p) (hq : IsFormula ℒₛₑₜ q)
    (h₁ : Bootstrapping.Provable (𝗭𝗙 : SetTheory) (gVal j p))
    (h₂ : Bootstrapping.Provable (𝗭𝗙 : SetTheory) (gVal j q)) :
    Bootstrapping.Provable (𝗭𝗙 : SetTheory) (gVal j (p ^⋏ q)) := by
  let R₁ := RF hp (by simp)
  let E₁ := LDriver.envFormT 0 hp
  let R₂ := RF hq (by simp)
  let E₂ := LDriver.envFormT 0 hq
  have t₁ := GF_of_gVal R₁ E₁ rfl rfl h₁
  have t₂ := GF_of_gVal R₂ E₂ rfl rfl h₂
  have hc := compiledG andG_provable (K8 (MT j) R₁ E₁ R₂ E₂ ⊤ ⊤ ⊤)
  rw [andG, LogicalConnective.HomClass.map_imply, translateFormula_imp, tr_andC] at hc
  simp only [LogicalConnective.HomClass.map_and, tr_andG, tr_gS] at hc
  refine gVal_of_GF (R₁ ⋏ R₂) (E₁ ⋏ E₂) ?_ ?_ (hc ⨀ K!_intro t₁ t₂)
  · simp [R₁, R₂, RF, rel, relativize_and hp.isUFormula hq.isUFormula]
  · simp [E₁, E₂, LDriver.envFormT, envForm_and hp.isUFormula hq.isUFormula]

theorem case_or {j p q : V} (hp : IsFormula ℒₛₑₜ p) (hq : IsFormula ℒₛₑₜ q)
    (h₁ : Bootstrapping.Provable (𝗭𝗙 : SetTheory) (gVal j p))
    (h₂ : Bootstrapping.Provable (𝗭𝗙 : SetTheory) (gVal j q)) :
    Bootstrapping.Provable (𝗭𝗙 : SetTheory) (gVal j (p ^⋎ q)) := by
  let R₁ := RF hp (by simp)
  let E₁ := LDriver.envFormT 0 hp
  let R₂ := RF hq (by simp)
  let E₂ := LDriver.envFormT 0 hq
  have t₁ := GF_of_gVal R₁ E₁ rfl rfl h₁
  have t₂ := GF_of_gVal R₂ E₂ rfl rfl h₂
  have hc := compiledG orG_provable (K8 (MT j) R₁ E₁ R₂ E₂ ⊤ ⊤ ⊤)
  rw [orG, LogicalConnective.HomClass.map_imply, translateFormula_imp, tr_orC] at hc
  simp only [LogicalConnective.HomClass.map_and, tr_andG, tr_gS] at hc
  refine gVal_of_GF (R₁ ⋎ R₂) (E₁ ⋎ E₂) ?_ ?_ (hc ⨀ K!_intro t₁ t₂)
  · simp [R₁, R₂, RF, rel, relativize_or hp.isUFormula hq.isUFormula]
  · simp [E₁, E₂, LDriver.envFormT, envForm_or hp.isUFormula hq.isUFormula]

/-- The freed premise of a quantifier step, generalized. -/
theorem qPremise {j p : V} (hp : IsSemiformula ℒₛₑₜ 1 p)
    (ih : Bootstrapping.Provable (𝗭𝗙 : SetTheory) (gVal (j + 1) (free ℒₛₑₜ p))) :
    (𝗭𝗙 : SetTheory).internalize V ⊢
      ∀⁰ QX (MT j) (RF hp le_rfl) (LDriver.envFormT 1 hp) := by
  have hE : (LDriver.envFormT 1 hp).shift = LDriver.envFormT 1 hp :=
    Bootstrapping.Semiformula.ext (shift_envForm hp)
  have t := GF_of_gVal (j := j + 1) (q := free ℒₛₑₜ p) (lift1 (RF hp le_rfl).free)
    (LDriver.envFormT 1 hp)
    (by simp [lift1, RF, rel, relativize_free hdL hdLs hp])
    (by simp [LDriver.envFormT, envForm_free hp]) ih
  rw [MT_succ, ← QX_free _ _ _ hE] at t
  exact Bootstrapping.TProof.all! t

theorem case_all {j p : V} (hp : IsSemiformula ℒₛₑₜ 1 p)
    (ih : Bootstrapping.Provable (𝗭𝗙 : SetTheory) (gVal (j + 1) (free ℒₛₑₜ p))) :
    Bootstrapping.Provable (𝗭𝗙 : SetTheory) (gVal j (^∀ p)) := by
  have hc := compiledG allG_provable
    (K8 (MT j) (RF hp le_rfl) (LDriver.envFormT 1 hp) ⊤ ⊤ ⊤ ⊤ ⊤)
  rw [allG, LogicalConnective.HomClass.map_imply, translateFormula_imp, tr_concl2, tr_relAll,
    tr_envAll] at hc
  simp only [LogicalConnective.HomClass.map_and, tr_andG, tr_funM, tr_qHyp] at hc
  exact gVal_of_GF _ _ (rAllT_val _ rfl hp.isUFormula) (eAllT_val hp)
    (hc ⨀ K!_intro (fun_MT j) (qPremise hp ih))

theorem case_ex {j p : V} (hp : IsSemiformula ℒₛₑₜ 1 p)
    (ih : Bootstrapping.Provable (𝗭𝗙 : SetTheory) (gVal (j + 1) (free ℒₛₑₜ p))) :
    Bootstrapping.Provable (𝗭𝗙 : SetTheory) (gVal j (^∃ p)) := by
  have hc := compiledG exG_provable
    (K8 (MT j) (RF hp le_rfl) (LDriver.envFormT 1 hp) ⊤ ⊤ ⊤ ⊤ ⊤)
  rw [exG, LogicalConnective.HomClass.map_imply, translateFormula_imp, tr_concl2, tr_relEx,
    tr_envEx] at hc
  simp only [LogicalConnective.HomClass.map_and, tr_andG, tr_funM, tr_qHyp] at hc
  exact gVal_of_GF _ _ (rExT_val _ rfl hp.isUFormula) (eExT_val hp)
    (hc ⨀ K!_intro (fun_MT j) (qPremise hp ih))

theorem atomR_val (isEq : Bool) (a b : V) :
    (atomR isEq a b).val = ^rel 2 (if isEq then 0 else 1) (^&a ∷ ^&b ∷ 0) := by
  cases isEq
  · simp [atomR, Bootstrapping.SemitermVec.val, Matrix.vecHead, Matrix.vecTail]
    change ((1 : Nat) : V) = 1
    simp
  · simp [atomR, Bootstrapping.SemitermVec.val, Matrix.vecHead, Matrix.vecTail]
    change ((0 : Nat) : V) = 0
    simp

/-- The arguments of an atom whose free variables lie below `j`. -/
theorem atom_args {j R v : V} (hR : (ℒₛₑₜ).IsRel 2 R) (hv : IsSemitermVec ℒₛₑₜ 2 0 v)
    (hfv : FvLt j (^rel 2 R v)) : ∃ a < j, ∃ b < j, v = ^&a ∷ ^&b ∷ 0 := by
  obtain ⟨a, ha, hva⟩ := fvLt_atom hR hv hfv (i := 0) (by simp)
  obtain ⟨b, hb, hvb⟩ := fvLt_atom hR hv hfv (i := 1) (by simp)
  obtain ⟨t₁, t₂, rfl⟩ := eq_doubleton_of_len_eq_two.mp hv.lh
  simp at hva hvb
  exact ⟨a, ha, b, hb, by rw [hva, hvb]⟩

theorem fvLt_nrel {j R v : V} (hR : (ℒₛₑₜ).IsRel 2 R) (hv : IsSemitermVec ℒₛₑₜ 2 0 v)
    (hfv : FvLt j (^nrel 2 R v)) : FvLt j (^rel 2 R v) := by
  unfold FvLt at hfv ⊢
  rw [ModelCodedBindFree.bindFreeAt_nrel _ hR hv.isUTerm] at hfv
  rw [ModelCodedBindFree.bindFreeAt_rel _ hR hv.isUTerm]
  simpa using hfv

theorem case_rel {j R v : V} (hR : (ℒₛₑₜ).IsRel 2 R) (hv : IsSemitermVec ℒₛₑₜ 2 0 v)
    (hfv : FvLt j (^rel 2 R v)) : Bootstrapping.Provable (𝗭𝗙 : SetTheory) (gVal j (^rel 2 R v)) := by
  obtain ⟨-, hR01⟩ := LDriver.isRel_set hR
  obtain ⟨a, ha, b, hb, rfl⟩ := atom_args hR hv hfv
  rcases hR01 with rfl | rfl
  · refine gVal_of_GF _ _ ?_ ?_ (glue_atom true j a b ha hb)
    · rw [atomR_val, rel, relativize_rel hR hv.isUTerm]
      rfl
    · rw [eAtomT_val true a b 0 (by simp), envForm_rel hR hv.isUTerm, atomOf]
      simp
  · refine gVal_of_GF _ _ ?_ ?_ (glue_atom false j a b ha hb)
    · rw [atomR_val, rel, relativize_rel hR hv.isUTerm]
      rfl
    · rw [eAtomT_val false a b 1 (by simp), envForm_rel hR hv.isUTerm, atomOf]
      simp

theorem case_nrel {j R v : V} (hR : (ℒₛₑₜ).IsRel 2 R) (hv : IsSemitermVec ℒₛₑₜ 2 0 v)
    (hfv : FvLt j (^nrel 2 R v)) : Bootstrapping.Provable (𝗭𝗙 : SetTheory) (gVal j (^nrel 2 R v)) := by
  obtain ⟨-, hR01⟩ := LDriver.isRel_set hR
  obtain ⟨a, ha, b, hb, rfl⟩ := atom_args hR hv (fvLt_nrel hR hv hfv)
  have key : ∀ isEq : Bool, R = (if isEq then 0 else 1) →
      Bootstrapping.Provable (𝗭𝗙 : SetTheory) (gVal j (^nrel 2 R (^&a ∷ ^&b ∷ 0))) := by
    intro isEq hRe
    have t := glue_atom isEq j a b ha hb
    have hc := compiledG negG_provable
      (K8 (MT j) (atomR isEq a b) (EAtomT isEq (numChainQ a) (numChainQ b)) ⊤ ⊤ ⊤ ⊤ ⊤)
    rw [negG, LogicalConnective.HomClass.map_imply, translateFormula_imp, tr_negC, tr_gS] at hc
    refine gVal_of_GF _ _ ?_ ?_ (hc ⨀ t)
    · change (∼atomR isEq a b).val = _
      rw [Bootstrapping.Semiformula.val_neg, atomR_val, rel, relativize_nrel hR hv.isUTerm, ← hRe,
        neg_rel hR hv.isUTerm]
    · change (∼EAtomT isEq (numChainQ a) (numChainQ b)).val = _
      rw [Bootstrapping.Semiformula.val_neg, eAtomT_val isEq a b R hRe, envForm_nrel hR hv.isUTerm,
        atomOf]
      simp
  rcases hR01 with rfl | rfl
  · exact key true (by simp)
  · exact key false (by simp)

theorem complexity_free {p : V} (hp : IsSemiformula ℒₛₑₜ 1 p) :
    formulaComplexity ℒₛₑₜ (free ℒₛₑₜ p) = formulaComplexity ℒₛₑₜ p := by
  rw [free, substs1, fomulaComplexity_substs (m := 0) hp.shift (by simp), formulaComplexity_shift hp.isUFormula]

/-- **The glue**: for every formula code `q` whose free variables lie below `j`,
`𝗭𝗙 ⊢ ∀t (¬M_j t ∨ (q^L ↔ envForm 0 q (t)))`, within the budget `C`. -/
theorem glue (C : V) {q : V} (hq : IsFormula ℒₛₑₜ q) :
    ∀ j ≤ C, j + formulaComplexity ℒₛₑₜ q ≤ C → FvLt j q →
      Bootstrapping.Provable (𝗭𝗙 : SetTheory) (gVal j q) := by
  refine IsFormula.sigma1_structural_induction (L := ℒₛₑₜ)
    (P := fun q ↦ ∀ j ≤ C, j + formulaComplexity ℒₛₑₜ q ≤ C → FvLt j q →
      Bootstrapping.Provable (𝗭𝗙 : SetTheory) (gVal j q))
    (by unfold FvLt; definability) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hq
  · intro k R v hR hv j _ _ hfv
    obtain ⟨rfl, -⟩ := LDriver.isRel_set hR
    exact case_rel hR hv hfv
  · intro k R v hR hv j _ _ hfv
    obtain ⟨rfl, -⟩ := LDriver.isRel_set hR
    exact case_nrel hR hv hfv
  · intro j _ _ _
    exact case_top j
  · intro j _ _ _
    exact case_bot j
  · intro p q hp hq ihp ihq j hj hc hfv
    obtain ⟨fp, fq⟩ := fvLt_and hp.isUFormula hq.isUFormula hfv
    rw [formulaComplexity_and hp.isUFormula hq.isUFormula] at hc
    have h1 : formulaComplexity ℒₛₑₜ p ≤
        max (formulaComplexity ℒₛₑₜ p) (formulaComplexity ℒₛₑₜ q) + 1 :=
      le_trans (le_max_left (formulaComplexity ℒₛₑₜ p) (formulaComplexity ℒₛₑₜ q)) (by simp)
    have h2 : formulaComplexity ℒₛₑₜ q ≤
        max (formulaComplexity ℒₛₑₜ p) (formulaComplexity ℒₛₑₜ q) + 1 :=
      le_trans (le_max_right (formulaComplexity ℒₛₑₜ p) (formulaComplexity ℒₛₑₜ q)) (by simp)
    exact case_and hp hq (ihp j hj (le_trans (add_le_add_right h1 j) hc) fp)
      (ihq j hj (le_trans (add_le_add_right h2 j) hc) fq)
  · intro p q hp hq ihp ihq j hj hc hfv
    obtain ⟨fp, fq⟩ := fvLt_or hp.isUFormula hq.isUFormula hfv
    rw [formulaComplexity_or hp.isUFormula hq.isUFormula] at hc
    have h1 : formulaComplexity ℒₛₑₜ p ≤
        max (formulaComplexity ℒₛₑₜ p) (formulaComplexity ℒₛₑₜ q) + 1 :=
      le_trans (le_max_left (formulaComplexity ℒₛₑₜ p) (formulaComplexity ℒₛₑₜ q)) (by simp)
    have h2 : formulaComplexity ℒₛₑₜ q ≤
        max (formulaComplexity ℒₛₑₜ p) (formulaComplexity ℒₛₑₜ q) + 1 :=
      le_trans (le_max_right (formulaComplexity ℒₛₑₜ p) (formulaComplexity ℒₛₑₜ q)) (by simp)
    exact case_or hp hq (ihp j hj (le_trans (add_le_add_right h1 j) hc) fp)
      (ihq j hj (le_trans (add_le_add_right h2 j) hc) fq)
  · intro p hp ih j hj hc hfv
    rw [formulaComplexity_all hp.isUFormula] at hc
    have hc' : j + 1 + formulaComplexity ℒₛₑₜ (free ℒₛₑₜ p) ≤ C := by
      rw [complexity_free hp, add_assoc, add_comm 1]
      exact hc
    have hj' : j + 1 ≤ C := le_trans (by simp) hc'
    exact case_all hp (ih (j + 1) hj' hc' (fvLt_free hp hfv))
  · intro p hp ih j hj hc hfv
    rw [formulaComplexity_ex hp.isUFormula] at hc
    have hc' : j + 1 + formulaComplexity ℒₛₑₜ (free ℒₛₑₜ p) ≤ C := by
      rw [complexity_free hp, add_assoc, add_comm 1]
      exact hc
    have hj' : j + 1 ≤ C := le_trans (by simp) hc'
    exact case_ex hp (ih (j + 1) hj' hc' (fvLt_free_ex hp hfv))

end LeanProofs.ZFCinPA.LGlue4
