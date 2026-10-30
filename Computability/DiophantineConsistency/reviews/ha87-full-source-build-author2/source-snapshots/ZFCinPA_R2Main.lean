import ZFCinPA.R2Quant

set_option autoImplicit false
noncomputable section

/-!
# R2: internal Foundation derivations become validator proofs

For a `Δ₁` theory `T` over `ℒₛₑₜ` whose every internal axiom code has a
validator proof of its encoding at every odd free environment and even binder
stream (`AxOK T`), every internal derivation translates (`translate`): for a
derivation of the sequent `Γ`, every listing `L` of `Γ`, odd environment `F` and
even stream `s`,

`CProv (¬enc A₁ → ¬enc A₂ → ⋯ → ¬enc Aₙ → ⊥)`   (`seqC F s L`).

The proof is order induction on the derivation code with a `Π₂` invariant
(`IΣ₂`), one case per Tait rule: the propositional rules by the context
calculus of `R2Ctx` and `R2Neg.encode_neg`; `∀` by `R2Quant.all_intro` at the
fresh label `lx F` (Codex's `encode_free`, `encode_shift`, `encode_vac`);
`∃` by `R2Quant.ex_intro` (`encode_substs1_fvar`); weakening and shift by
`der_sub`. Hence `Provable T ⊥ → CProv 1` (`cProv_falsum_of_provable`).
-/

namespace LeanProofs.ZFCinPA.R2Main

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open _root_.SetTheory.BusyBeaver.ZFC ArithmeticCode254
open LeanProofs.ZFCinPA.ValidatorProvability254 LeanProofs.ZFCinPA.ValidatorQuantifierCore254
open LeanProofs.ZFCinPA.ValidatorEnvironmentLabels254 LeanProofs.ZFCinPA.ValidatorEnvironmentVacuity254
open LeanProofs.ZFCinPA.ValidatorEnvironmentOpening254 LeanProofs.ZFCinPA.ValidatorEnvironmentInstantiation254
open LeanProofs.ZFCinPA.ValidatorEqualityContext254 LeanProofs.ZFCinPA.ValidatorNativeGicSlots254
open LeanProofs.ZFCinPA.R2Ctx LeanProofs.ZFCinPA.R2Neg LeanProofs.ZFCinPA.R2Quant
open scoped LO.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## Environments -/

lemma oddEnv_nil : OddEnv (0 : V) := fun i hi ↦ by simp at hi

lemma oddEnv_cons {x F : V} (hx : x % 2 = 1) (hF : OddEnv F) : OddEnv (x ∷ F) := by
  intro i hi
  rcases zero_or_succ i with (rfl | ⟨j, rfl⟩)
  · simpa using hx
  · simpa using hF j (by simpa using hi)

lemma oddEnv_tail {F : V} (hF : OddEnv F) : OddEnv (tail F) := by
  rcases nil_or_adjoin F with (rfl | ⟨x, F, rfl⟩)
  · simpa using oddEnv_nil
  · simp only [tail_cons]
    intro i hi
    simpa using hF (i + 1) (by simpa using hi)

instance oddEnv_definable : 𝚫₁-Predicate[V] OddEnv := by unfold OddEnv; definability

/-! ## Two propositional facts -/

lemma or_lemma (a b : V) :
    CProv (wim (wim (R2Neg.vneg b) (wim (R2Neg.vneg a) 1)) (wim (R2Neg.vneg a) b)) :=
  ded2 (.mp (.ax (double_neg_elim b))
    (Kalmar.deduction cProv_classical (.mp (.mp h2 h0) h1)))

/-! ## The translation -/

/-- Every internal axiom code is encoded to a validator theorem. -/
def AxOK (T : SetTheory) [T.Δ₁] (V : Type*) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] : Prop :=
  ∀ p : V, IsFormula ℒₛₑₜ p → p ∈ T.Δ₁Class →
    ∀ F s : V, OddEnv F → s % 2 = 0 → CProv (encode F 0 s p)

variable {T : SetTheory} [T.Δ₁]

/-- The translation invariant at a derivation code. -/
def Inv (T : SetTheory) [T.Δ₁] (d : V) : Prop :=
  Derivation T d → ∀ F s L : V, OddEnv F → s % 2 = 0 → Enum L (fstIdx d) → CProv (seqC F s L)

section Induction

variable [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 2]

private instance seqC_definable : 𝚺₁-Function₃[V] seqC := by
  unfold seqC; definability

private instance cProv_pi2 : 𝚷-[2]-Predicate[V] CProv := sigma1_to_pi2 cProv_definable
private instance seqC_sigma2 : 𝚺-[2]-Function₃[V] seqC := seqC_definable.of_sigmaOne

private lemma inv_pi2 : 𝚷-[2]-Predicate[V] (Inv T) := by
  unfold Inv
  apply HierarchySymbol.Definable.imp
  · definability
  apply HierarchySymbol.Definable.all
  apply HierarchySymbol.Definable.all
  apply HierarchySymbol.Definable.all
  apply HierarchySymbol.Definable.imp
  · definability
  apply HierarchySymbol.Definable.imp
  · definability
  apply HierarchySymbol.Definable.imp
  · definability
  · definability

lemma enum_cons {L s p : V} (hL : Enum L s) : Enum (p ∷ L) (insert p s) :=
  enum_of_mem fun y ↦ by simp [hL.mem]

lemma seqC_cons (F s p L : V) :
    seqC F s (p ∷ L) = imps (R2Neg.vneg (encode F 0 s p) ∷ negEnc F s L) 1 := by
  simp [seqC]

/-- **The translation of internal derivations.** -/
theorem translate (hAx : AxOK T V) : ∀ d : V, Inv T d := by
  apply InductionOnHierarchy.order_induction_sigma 𝚷 2 (P := Inv T) inv_pi2
  intro d ih hd F s0 L hF hs hL
  have hmem : ∀ A, A ∈ fstIdx d → R2Neg.vneg (encode F 0 s0 A) ∈ᵥ negEnc F s0 L :=
    fun A hA ↦ (mem_negEnc F s0 L _).2 ⟨A, hL.mem.2 hA, rfl⟩
  have hform : ∀ A, A ∈ᵥ L → IsFormula ℒₛₑₜ A :=
    fun A hA ↦ hd.isFormulaSet A (hL.mem.1 hA)
  have hvac : ∀ y, y ∈ᵥ negEnc F s0 L → Vac (lx F) y := by
    intro y hy
    obtain ⟨A, hA, rfl⟩ := (mem_negEnc F s0 L y).1 hy
    exact vac_neg (encode_formula_vac (hform A hA) F s0 (lx F)
      (freeAvoid_big (lx_gt F) (one_lt_lx F)) (streamAvoid_parity (lx_odd F) hs))
  have hsub : ∀ M, (∀ A, A ∈ᵥ M → A ∈ fstIdx d) →
      ∀ y, y ∈ᵥ negEnc F s0 M → y ∈ᵥ negEnc F s0 L := by
    intro M hM y hy
    obtain ⟨A, hA, rfl⟩ := (mem_negEnc F s0 M y).1 hy
    exact hmem A (hM A hA)
  unfold seqC
  change Der (negEnc F s0 L) 1
  rcases Derivation.case_iff.mp hd with ⟨hds,
      (⟨s, p, rfl, hps, hnps⟩ | ⟨s, rfl, hsv⟩ |
        ⟨s, p, q, dp, dq, rfl, hpq, h₁, h₂⟩ | ⟨s, p, q, d', rfl, hpq, h'⟩ |
        ⟨s, p, d', rfl, hp, h'⟩ | ⟨s, p, t, d', rfl, hp, ht, h'⟩ |
        ⟨s, d', rfl, hsub', hd'⟩ | ⟨s, d', rfl, hsh, hd'⟩ |
        ⟨s, p, d₁, d₂, rfl, h₁, h₂⟩ | ⟨s, p, rfl, hps, hT⟩)⟩
  -- axL
  · simp only [fstIdx_axL] at hmem hds
    have hp : IsFormula ℒₛₑₜ p := hds p hps
    have ne := encode_neg hp F 0 s0
    have d1 := der_mem (hmem _ hnps)
    have d2 := der_mp (der_of (contrapose_of ne.2)) d1
    exact der_mp d2 (der_mem (hmem p hps))
  -- verum
  · simp only [fstIdx_verumIntro] at hmem
    have h := hmem _ hsv
    rw [encode_verum] at h
    exact der_mp (der_mem h) (der_of cProv_truth)
  -- and
  · simp only [fstIdx_andIntro] at hmem hds hL
    have hf := hds _ hpq
    simp only [IsSemiformula.and] at hf
    have Hp : Der (negEnc F s0 L) (encode F 0 s0 p) := by
      have h := ih dp (by simp) h₁.2 F s0 (p ∷ L) hF hs (by rw [h₁.1]; exact enum_cons hL)
      rw [seqC_cons] at h
      exact der_byContra h
    have Hq : Der (negEnc F s0 L) (encode F 0 s0 q) := by
      have h := ih dq (by simp) h₂.2 F s0 (q ∷ L) hF hs (by rw [h₂.1]; exact enum_cons hL)
      rw [seqC_cons] at h
      exact der_byContra h
    have Hpq := der_mp (der_mp (der_of (conj_intro_imp _ _)) Hp) Hq
    have hm := hmem _ hpq
    rw [encode_and F 0 s0 hf.1.isUFormula hf.2.isUFormula] at hm
    exact der_absurd hm Hpq
  -- or
  · simp only [fstIdx_orIntro] at hmem hds hL
    have hf := hds _ hpq
    simp only [IsSemiformula.or] at hf
    have h := ih d' (by simp) h'.2 F s0 (p ∷ q ∷ L) hF hs
      (by rw [h'.1]; exact enum_cons (enum_cons hL))
    rw [seqC_cons, negEnc_cons] at h
    have H := der_mp (der_of (or_lemma (encode F 0 s0 p) (encode F 0 s0 q))) (der_ded (der_ded h))
    have hm := hmem _ hpq
    rw [encode_or F 0 s0 hf.1.isUFormula hf.2.isUFormula] at hm
    exact der_absurd hm H
  -- all
  · simp only [fstIdx_allIntro] at hmem hds hL
    have hp1 : IsSemiformula ℒₛₑₜ 1 p := by simpa using hds _ hp
    have hen : Enum (free ℒₛₑₜ p ∷ shiftList L) (insert (free ℒₛₑₜ p) (setShift ℒₛₑₜ s)) := by
      refine enum_of_mem fun y ↦ ?_
      simp only [memVec_adjoin_iff, mem_shiftList, mem_bitInsert_iff, mem_setShift_iff, hL.mem]
    have h := ih d' (by simp) h'.2 (lx F ∷ F) s0 _ (oddEnv_cons (lx_odd F) hF) hs (by rw [h'.1]; exact hen)
    rw [seqC_cons, encode_free hp1 F (lx F) s0,
      negEnc_shiftList (lx F ∷ F) s0 L (fun A hA ↦ (hform A hA).isUFormula), tail_cons] at h
    have H := all_intro hp1 hF hs (fun i hi ↦ hform _ (nth_mem_memVec hi)) (der_byContra h)
    exact der_absurd (hmem _ hp) H
  -- exs
  · simp only [fstIdx_exsIntro] at hmem hds hL
    have hp1 : IsSemiformula ℒₛₑₜ 1 p := by simpa using hds _ hp
    obtain ⟨j, rfl⟩ := term_is_fvar ht
    have h := ih d' (by simp) h'.2 F s0 _ hF hs (by rw [h'.1]; exact enum_cons hL)
    rw [seqC_cons, encode_substs1_fvar hp1 F j s0] at h
    have H := ex_intro hp1 hF hs (freeLabel_odd hF) freeLabel_lt (der_byContra h)
    exact der_absurd (hmem _ hp) H
  -- wk
  · simp only [fstIdx_wkRule] at hmem hsub
    obtain ⟨M, hM⟩ := exists_enum (fstIdx d')
    have h := ih d' (by simp) hd' F s0 M hF hs hM
    exact der_sub (hsub M fun A hA ↦ hsub' (hM.mem.1 hA)) h
  -- shift
  · simp only [fstIdx_shiftRule] at hmem hsub
    obtain ⟨M, hM⟩ := exists_enum (fstIdx d')
    have hMf : ∀ A, A ∈ᵥ M → IsUFormula ℒₛₑₜ A :=
      fun A hA ↦ (hd'.isFormulaSet A (hM.mem.1 hA)).isUFormula
    have h := ih d' (by simp) hd' (tail F) s0 M (oddEnv_tail hF) hs hM
    change Der (negEnc (tail F) s0 M) 1 at h
    rw [← negEnc_shiftList F s0 M hMf] at h
    refine der_sub (hsub (shiftList M) fun A hA ↦ ?_) h
    obtain ⟨B, hB, rfl⟩ := (mem_shiftList M A).1 hA
    rw [hsh]
    exact mem_setShift_iff.mpr ⟨B, hM.mem.1 hB, rfl⟩
  -- cut
  · simp only [fstIdx_cutRule] at hmem hL
    have hp : IsFormula ℒₛₑₜ p := (h₁.isFormulaSet.insert).1
    have H1 : Der (negEnc F s0 L) (encode F 0 s0 p) := by
      have h := ih d₁ (by simp) h₁.2 F s0 (p ∷ L) hF hs (by rw [h₁.1]; exact enum_cons hL)
      rw [seqC_cons] at h
      exact der_byContra h
    have H2 : Der (negEnc F s0 L) (encode F 0 s0 (neg ℒₛₑₜ p)) := by
      have h := ih d₂ (by simp) h₂.2 F s0 (neg ℒₛₑₜ p ∷ L) hF hs (by rw [h₂.1]; exact enum_cons hL)
      rw [seqC_cons] at h
      exact der_byContra h
    exact der_mp (der_mp (der_of (encode_neg hp F 0 s0).1) H2) H1
  -- axm
  · simp only [fstIdx_axm] at hmem hds
    exact der_absurd (hmem p hps) (der_of (hAx p (hds p hps) hT F s0 hF hs))

/-- **R2 for `T`**: in every `IΣ₂` model, an internal `T`-refutation yields
a validator proof of falsity, provided the axioms are encoded to theorems. -/
theorem cProv_falsum_of_provable (hAx : AxOK T V) (h : Provable T (^⊥ : V)) : CProv (1 : V) := by
  obtain ⟨d, hd⟩ := h
  have hen : Enum ((^⊥ : V) ∷ 0) (fstIdx d) := by
    rw [hd.1]
    exact enum_of_mem fun y ↦ by rw [singleton_eq_insert]; simp
  have h := translate hAx d hd.2 0 2 _ oddEnv_nil (by simp) hen
  simp only [seqC, negEnc_cons, negEnc_nil, imps_cons, imps_nil, encode_falsum] at h
  exact cProv_mp h (self_imp 1)

end Induction

end LeanProofs.ZFCinPA.R2Main
