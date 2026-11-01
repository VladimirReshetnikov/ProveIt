import DiophantineConsistency.PRAWitnessPR
import DiophantineConsistency.PRAWitnessSubsts
import ZFCinPA.ZFDelta1
/-! # Witness bounds for the ZFC axiom recognizer

`ZFCinPA.ZFC_delta1` recognizes ZFC as the union of the finite equality
axioms, seven fixed axioms, the separation and replacement schemata, and
choice, through Foundation's `Δ₁` combinators (`goodCh_singleton`,
`goodCh_add`, `goodCh_ofList`, ...). The schema recognizers `sepCh` and
`repCh` quantify over a core formula and its closure; their witnesses are the
values of `fvarVec`, `subst`, `qqAlls`, `shift`, `bv` and of the schema
bodies, the last bounded by towers of `tau` (`sepBodyVal_le`,
`repBodyVal_le`) through `PRAWitnessBoundTerms`. `goodCh_zfc` is the result:
both polarities of `𝗭𝗙𝗖.Δ₁ch` have bounded witnesses. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAWitnessZFCAxioms
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open StrictSigmaOneInduction PRAWitnessCalculus PRAWitnessArithmetic PRAWitnessVectors PRAWitnessSetTerms
  PRAWitnessTermRec PRAWitnessTermFunctions PRAWitnessFormulas PRAWitnessFormulaRec PRAWitnessRepeatVec
  PRAWitnessExpBounds PRAWitnessFormulaFunctions PRAWitnessCodeGrowth PRAWitnessSubsts PRAWitnessBoundTerms
  PRAWitnessBoundTerms.BoundTerm PRAWitnessPR LeanProofs.ZFCinPA

section sigma1
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem lt_iff_right (a x : V) : x < iff ℒₛₑₜ a x := by
  unfold iff imp
  exact lt_trans (lt_or_right _ _) (lt_K!_left _ _)

theorem lt_iff_left (a x : V) : a < iff ℒₛₑₜ a x := by
  unfold iff imp
  exact lt_trans (lt_or_right _ _) (lt_K!_right _ _)


/-- A common bound for the separation skeleton constants. -/
noncomputable def sepC : ℕ := sepSubstConst + sepAtomZYCode + sepAtomZXCode

theorem neg_le' (X T : V) (h : X ≤ T) : neg ℒₛₑₜ X ≤ tau (T + 8) (2 * T + 6) := by
  by_cases hX : IsUFormula ℒₛₑₜ X
  · exact le_trans (neg_le X hX) (tau_mono (add_le_add h le_rfl) (add_le_add (mul_le_mul' le_rfl h) le_rfl))
  · rw [neg_not_uformula hX]; simp

theorem subst_le' (w k : V) : subst ℒₛₑₜ w k ≤ tau (w + k + 8) (0 + 4 * k + 6) := by
  by_cases hk : IsUFormula ℒₛₑₜ k
  · exact subst_le k hk w w 0 (fun j _ => le_trans (nth_le w j) (le_tau w 0))
  · rw [substs_not_uformula hk]; simp

theorem imp_le {a b T : V} (ha : a ≤ T) (hb : b ≤ T) : imp ℒₛₑₜ a b ≤ tau (T + 8) (2 * T + 10) := by
  have hb' : b ≤ tau (T + 8) (2 * T + 6) := le_trans (le_trans hb le_self_add) (le_tau _ _)
  have h := code3_le_tau (small_le_tau (T + 8) (2 * T + 6) (n := 5) (by norm_num)) (neg_le' a T ha) hb'
  unfold imp
  exact le_trans (by simpa [qqOr] using h) (tau_mono le_rfl (le_of_eq (by ring)))

theorem iff_le {a b T : V} (ha : a ≤ T) (hb : b ≤ T) : iff ℒₛₑₜ a b ≤ tau (T + 8) (2 * T + 14) := by
  have h := code3_le_tau (small_le_tau (T + 8) (2 * T + 10) (n := 4) (by norm_num))
    (imp_le ha hb) (imp_le hb ha)
  unfold iff
  exact le_trans (by simpa [qqAnd] using h) (tau_mono le_rfl (le_of_eq (by ring)))

theorem all_le_tau {x X D : V} (h : x ≤ tau X D) : ^∀ x ≤ tau X (D + 2) := by
  simpa [qqAll] using code2_le_tau (small_le_tau X D (n := 6) (by norm_num)) h

theorem exs_le_tau {x X D : V} (h : x ≤ tau X D) : ^∃ x ≤ tau X (D + 2) := by
  simpa [qqExs] using code2_le_tau (small_le_tau X D (n := 7) (by norm_num)) h

theorem and_le_tau {x y X D : V} (hx : x ≤ tau X D) (hy : y ≤ tau X D) : x ^⋏ y ≤ tau X (D + 2 + 2) := by
  simpa [qqAnd] using code3_le_tau (small_le_tau X D (n := 4) (by norm_num)) hx hy

/-- **The separation body is a tower of two `tau`s in its core.** -/
theorem sepBodyVal_le (k : V) :
    sepBodyVal k ≤ tau (tau ((sepC : V) + k + 8) (4 * k + 10) + 8)
      (2 * tau ((sepC : V) + k + 8) (4 * k + 10) + 20) := by
  set T1 := tau ((sepC : V) + k + 8) (4 * k + 10) with hT1
  have hcs : ((sepSubstConst : ℕ) : V) ≤ sepC := by
    unfold sepC; push_cast; exact le_trans le_self_add le_self_add
  have hcy : ((sepAtomZYCode : ℕ) : V) ≤ sepC := by
    unfold sepC; push_cast; exact le_trans le_add_self le_self_add
  have hcx : ((sepAtomZXCode : ℕ) : V) ≤ sepC := by unfold sepC; push_cast; exact le_add_self
  have hbase {c : V} (hc : c ≤ sepC) (D : V) : c ≤ tau ((sepC : V) + k + 8) D :=
    le_trans (le_trans hc (le_trans le_self_add le_self_add)) (le_tau _ _)
  have hS : subst ℒₛₑₜ ((sepSubstConst : ℕ) : V) k ≤ tau ((sepC : V) + k + 8) (0 + 4 * k + 6) :=
    le_trans (subst_le' _ k) (tau_mono (add_le_add (add_le_add hcs le_rfl) le_rfl) le_rfl)
  have hX : ((sepAtomZXCode : ℕ) : V) ^⋏ subst ℒₛₑₜ ((sepSubstConst : ℕ) : V) k ≤ T1 := by
    have h := code3_le_tau (small_le_tau _ _ (n := 4) (by norm_num)) (hbase hcx _) hS
    exact le_trans (by simpa [qqAnd] using h) (tau_mono le_rfl (le_of_eq (by ring)))
  set X := ((sepAtomZXCode : ℕ) : V) ^⋏ subst ℒₛₑₜ ((sepSubstConst : ℕ) : V) k
  have hY : ((sepAtomZYCode : ℕ) : V) ≤ T1 := hbase hcy _
  have hiff := iff_le hY hX
  have ha1 := all_le_tau hiff
  have he1 := exs_le_tau ha1
  have ha2 := all_le_tau he1
  unfold sepBodyVal
  exact le_trans ha2 (tau_mono le_rfl (le_of_eq (by ring)))


/-- A common bound for the replacement skeleton constants. -/
noncomputable def repC : ℕ :=
  repSubst1Const + repSubst2Const + repSubst3Const + repAtomEqCode + repAtomYYCode + repAtomXXCode

/-- **The replacement body is a tower of three `tau`s in its core.** -/
theorem repBodyVal_le (k : V) :
    repBodyVal k ≤
      tau (tau (tau ((repC : V) + k + 8) (4 * k + 12) + 8) (2 * tau ((repC : V) + k + 8) (4 * k + 12) + 20) + 8)
        (2 * tau (tau ((repC : V) + k + 8) (4 * k + 12) + 8) (2 * tau ((repC : V) + k + 8) (4 * k + 12) + 20) + 10) := by
  set T0 := tau ((repC : V) + k + 8) (4 * k + 12)
  set T2 := tau (T0 + 8) (2 * T0 + 20)
  have hc {c : ℕ} (hc : c ≤ repC) (D : V) : (c : V) ≤ tau ((repC : V) + k + 8) D :=
    le_trans (le_trans (by exact_mod_cast hc) (le_trans le_self_add le_self_add)) (le_tau _ _)
  have hS {c : ℕ} (hcC : c ≤ repC) : subst ℒₛₑₜ (c : V) k ≤ T0 :=
    le_trans (subst_le' _ k) (tau_mono (add_le_add (add_le_add (by exact_mod_cast hcC) le_rfl) le_rfl)
      (by rw [zero_add]; exact add_le_add le_rfl (by norm_num)))
  have h1 : repSubst1Const ≤ repC := by unfold repC; omega
  have h2 : repSubst2Const ≤ repC := by unfold repC; omega
  have h3 : repSubst3Const ≤ repC := by unfold repC; omega
  have hq : repAtomEqCode ≤ repC := by unfold repC; omega
  have hy : repAtomYYCode ≤ repC := by unfold repC; omega
  have hx : repAtomXXCode ≤ repC := by unfold repC; omega
  have hT0 {t : V} (ht : t ≤ T0) (D : V) : t ≤ tau (T0 + 8) D := le_trans (le_trans ht le_self_add) (le_tau _ _)
  -- left: `^∀ ^∃ (s1 ^⋏ ^∀ imp s2 eq)`
  have hi2 := imp_le (hS h2) (hc hq (4 * k + 12))
  have ha2 := all_le_tau hi2
  have hc1 := and_le_tau (hT0 (hS h1) _) ha2
  have he1 := exs_le_tau hc1
  have ha1 := all_le_tau he1
  have hA1 : ^∀ ^∃ (subst ℒₛₑₜ (repSubst1Const : V) k ^⋏
      ^∀ imp ℒₛₑₜ (subst ℒₛₑₜ (repSubst2Const : V) k) (repAtomEqCode : V)) ≤ T2 :=
    le_trans ha1 (tau_mono le_rfl (le_of_eq (by ring)))
  -- right: `^∀ ^∃ ^∀ iff yy (^∃ (xx ^⋏ s3))`
  have hc3 := and_le_tau (hc hx (0 + 4 * k + 6)) (le_trans (subst_le' _ k)
    (tau_mono (add_le_add (add_le_add (show ((repSubst3Const : ℕ) : V) ≤ (repC : V) by exact_mod_cast h3)
      le_rfl) le_rfl) le_rfl))
  have he3 : ^∃ ((repAtomXXCode : V) ^⋏ subst ℒₛₑₜ (repSubst3Const : V) k) ≤ T0 :=
    le_trans (exs_le_tau hc3) (tau_mono le_rfl (le_of_eq (by ring)))
  have hf3 := iff_le (hc hy (4 * k + 12)) he3
  have ha3 := all_le_tau hf3
  have he4 := exs_le_tau ha3
  have ha4 := all_le_tau he4
  have hA2 : ^∀ ^∃ ^∀ iff ℒₛₑₜ (repAtomYYCode : V)
      (^∃ ((repAtomXXCode : V) ^⋏ subst ℒₛₑₜ (repSubst3Const : V) k)) ≤ T2 :=
    le_trans ha4 (tau_mono le_rfl (le_of_eq (by ring)))
  unfold repBodyVal
  exact imp_le hA1 hA2

end sigma1

section models
open PRAFiniteFunctionCodes PRALanguage PRATheory
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem wb_impGraph : WB M (impGraph ℒₛₑₜ).val := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := wb_negGraph (M := M); have := wb_qqOrDef (M := M)
  simp only [impGraph, HierarchySymbol.Semiformula.val_mkSigma]
  exact PRAWitnessTransfer.wb_exs_poly _ (by simp) ‘#0’
    (fun V _ _ e u h => ⟨u, by
      have h' := h; simp at h'
      simpa [h'.2] using le_of_lt (lt_or_left u (e 2)), h⟩) (by wb_auto)

theorem wb_iffGraph : WB M (iffGraph ℒₛₑₜ).val := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := wb_impGraph (M := M); have := wb_qqAndDef (M := M)
  simp only [iffGraph, HierarchySymbol.Semiformula.val_mkSigma]
  refine PRAWitnessTransfer.wb_exs_poly _ (by simp) ‘#0’
    (fun V _ _ e u h => ⟨u, by
      have h' := h; simp at h'
      simpa [h'.2] using le_of_lt (lt_K!_left u (imp ℒₛₑₜ (e 2) (e 1))), h⟩) ?_
  wb_auto
  exact PRAWitnessTransfer.wb_exs_poly _ (by simp) ‘#1’
    (fun V _ _ e u h => ⟨u, by
      have h' := h; simp at h'
      simpa [h'.2] using le_of_lt (lt_K!_right (e 0) u), h⟩) (by wb_auto)

theorem wb_sepBodyValGraph : WB M sepBodyValGraph.val := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := wb_substsGraph (M := M); have := wb_qqAndDef (M := M); have := wb_iffGraph (M := M)
  have := wb_qqAllDef (M := M); have := wb_qqExsDef (M := M)
  simp only [sepBodyValGraph, HierarchySymbol.Semiformula.val_mkSigma]
  refine PRAWitnessTransfer.wb_exs_poly _ (by simp) ‘#0’
    (fun V _ _ e u h => ⟨u, by
      have h' := h; simp at h'
      obtain ⟨-, hy⟩ := h'
      show u ≤ e 0; rw [hy]; exact le_of_lt (lt_trans (lt_K!_right _ _) (lt_trans (lt_iff_right _ _) (lt_trans (lt_forall _) (lt_trans (lt_exists _) (lt_forall _))))), h⟩) ?_
  wb_auto
  refine PRAWitnessTransfer.wb_exs_poly _ (by simp) ‘#1’
    (fun V _ _ e u h => ⟨u, by
      have h' := h; simp at h'
      obtain ⟨-, hy⟩ := h'
      show u ≤ e 1; rw [hy]; exact le_of_lt (lt_trans (lt_iff_right _ _) (lt_trans (lt_forall _) (lt_trans (lt_exists _) (lt_forall _)))), h⟩) ?_
  wb_auto
  refine PRAWitnessTransfer.wb_exs_poly _ (by simp) ‘#2’
    (fun V _ _ e u h => ⟨u, by
      have h' := h; simp at h'
      obtain ⟨-, hy⟩ := h'
      show u ≤ e 2; rw [hy]; exact le_of_lt (lt_trans (lt_forall _) (lt_trans (lt_exists _) (lt_forall _))), h⟩) ?_
  wb_auto
  refine PRAWitnessTransfer.wb_exs_poly _ (by simp) ‘#3’
    (fun V _ _ e u h => ⟨u, by
      have h' := h; simp at h'
      obtain ⟨-, hy⟩ := h'
      show u ≤ e 3; rw [hy]; exact le_of_lt (lt_trans (lt_exists _) (lt_forall _)), h⟩) ?_
  wb_auto
  exact PRAWitnessTransfer.wb_exs_poly _ (by simp) ‘#4’
    (fun V _ _ e u h => ⟨u, by
      have h' := h; simp at h'
      obtain ⟨-, hy⟩ := h'
      show u ≤ e 4; rw [hy]; exact le_of_lt (lt_forall _), h⟩) (by wb_auto)

/-- The inner tower of `sepBodyVal_le`, in the variable `#0`. -/
noncomputable def sepT {n : ℕ} : BoundTerm (n + 1) := tauT (poly ‘↑sepC + #0 + 8’) (poly ‘4 * #0 + 10’)

/-- The common positive recognizer for a schema with a bounded body graph. -/
private noncomputable def schemaSigma (arity : ℕ) (G : 𝚺₁.Semisentence 2) : ArithmeticSemisentence 1 :=
  “p. ∃ m < p + 1, ∃ b < p + 1,
    !qqAllsDef p b m ∧ !(Bootstrapping.isUFormula ℒₛₑₜ).sigma b
    ∧ !(Bootstrapping.shiftGraph ℒₛₑₜ) b b ∧ !(Bootstrapping.bvGraph ℒₛₑₜ) m b
    ∧ ∃ fv, !fvarVecDef fv m ∧ ∃ s, !(Bootstrapping.substsGraph ℒₛₑₜ) s fv b
      ∧ ∃ K < s + 1, !(Bootstrapping.isSemiformula ℒₛₑₜ).sigma ↑arity K ∧ !G s K”

private theorem wb_schemaSigma (arity : ℕ) (G : 𝚺₁.Semisentence 2) (hG : WB M G.val) :
    WB M (schemaSigma arity G) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := wb_qqAllsDef (M := M); have := wb_isUFormula_sigma (M := M); have := wb_shiftGraph (M := M)
  have := wb_bvGraph (M := M); have := wb_fvarVecDef (M := M); have := wb_substsGraph (M := M)
  have := wb_isSemiformula_sigma (M := M); have := hG
  unfold schemaSigma
  wb_auto
  refine wb_exs_bt' _ (by simp) (tauT (poly ‘(#1 + 2) * (#1 + 2) + 1’) (poly ‘2 * #1’))
    (fun V _ _ e x h => ⟨x, ?_, h⟩) ?_
  · have h' := h; simp at h'
    rw [h'.1]; simpa [vval_tauT, vval] using fvarVec_le (e 1) (e 1) le_rfl
  wb_auto
  refine wb_exs_bt' _ (by simp) (tauT (poly ‘#0 + #1 + 8’) (poly ‘0 + 4 * #1 + 6’))
    (fun V _ _ e x h => ⟨x, ?_, h⟩) ?_
  · have h' := h; simp at h'
    rw [h'.1]; simpa [vval_tauT, vval, numeral_eq_natCast] using subst_le' (e 0) (e 1)
  wb_auto

theorem wb_sepCh_sigma : WB M sepCh.sigma.val := by
  simpa only [sepCh, HierarchySymbol.Semiformula.sigma_mkDelta,
    HierarchySymbol.Semiformula.val_mkSigma, schemaSigma] using
    (wb_schemaSigma (M := M) 1 sepBodyValGraph wb_sepBodyValGraph)

theorem wb_sepCh_neg_pi : WB M (∼sepCh.pi.val) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := wb_qqAllsDef (M := M); have := wb_isUFormula_neg_pi (M := M); have := wb_shiftGraph (M := M)
  have := wb_bvGraph (M := M); have := wb_fvarVecDef (M := M); have := wb_substsGraph (M := M)
  have := wb_isSemiformula_neg_pi (M := M); have := wb_sepBodyValGraph (M := M)
  simp only [sepCh, HierarchySymbol.Semiformula.pi_mkDelta, HierarchySymbol.Semiformula.val_mkPi]
  wb_auto
  · exact wb_exs_bt _ (by simp) (tauT (poly ‘#0’) (poly ‘2 * #1’)) (fun V _ _ e x h => by
      have h' := h; simp at h'
      rw [h'.1]; simpa [vval_tauT, vval] using qqAlls_le (e 0) (e 1)) (by wb_auto)
  · exact wb_exs_bt _ (by simp) (tauT (poly ‘(#0 + 2) * (#0 + 2) + 1 + 8’) (poly ‘2 * #0 + 6’))
      (fun V _ _ e x h => by
        have h' := h; simp at h'
        rw [h'.1]
        by_cases hb : IsUFormula ℒₛₑₜ (e 0)
        · simpa [vval_tauT, vval, numeral_eq_natCast] using shift_le (e 0) hb
        · rw [shift_not_uformula hb]; simp) (by wb_auto)
  · exact PRAWitnessTransfer.wb_exs_poly _ (by simp) ‘#0’ (fun V _ _ e x h => ⟨x, by
      have h' := h; simp at h'
      rw [h'.1]; simpa using bv_le_self (e 0), h⟩) (by wb_auto)
  refine wb_exs_bt' _ (by simp) (tauT (poly ‘(#1 + 2) * (#1 + 2) + 1’) (poly ‘2 * #1’))
    (fun V _ _ e x h => ⟨x, ?_, h⟩) ?_
  · have h' := h; simp at h'
    rw [h'.1]; simpa [vval_tauT, vval] using fvarVec_le (e 1) (e 1) le_rfl
  wb_auto
  refine wb_exs_bt' _ (by simp) (tauT (poly ‘#0 + #1 + 8’) (poly ‘0 + 4 * #1 + 6’))
    (fun V _ _ e x h => ⟨x, ?_, h⟩) ?_
  · have h' := h; simp at h'
    rw [h'.1]; simpa [vval_tauT, vval, numeral_eq_natCast] using subst_le' (e 0) (e 1)
  wb_auto
  exact wb_exs_bt _ (by simp)
    (tauT (add sepT (poly ‘8’)) (add (mul (poly ‘2’) sepT) (poly ‘20’)))
    (fun V _ _ e x h => by
      have h' := h; simp at h'
      rw [h'.1]; simpa [sepT, vval_tauT, vval, numeral_eq_natCast] using sepBodyVal_le (e 0)) (by wb_auto)

theorem wb_repBodyValGraph : WB M repBodyValGraph.val := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := wb_substsGraph (M := M); have := wb_qqAndDef (M := M); have := wb_iffGraph (M := M)
  have := wb_qqAllDef (M := M); have := wb_qqExsDef (M := M); have := wb_impGraph (M := M)
  simp only [repBodyValGraph, HierarchySymbol.Semiformula.val_mkSigma]
  refine wb_exs_bt _ (by simp) (tauT (poly ‘↑repSubst1Const + #1 + 8’) (poly ‘0 + 4 * #1 + 6’))
    (fun V _ _ e u h => by
      have h' := h; simp at h'
      rw [h'.1]; simpa [vval_tauT, vval, numeral_eq_natCast] using subst_le' ((repSubst1Const : ℕ) : V) (e 1)) ?_
  wb_auto
  refine wb_exs_bt _ (by simp) (tauT (poly ‘↑repSubst2Const + #2 + 8’) (poly ‘0 + 4 * #2 + 6’))
    (fun V _ _ e u h => by
      have h' := h; simp at h'
      rw [h'.1]; simpa [vval_tauT, vval, numeral_eq_natCast] using subst_le' ((repSubst2Const : ℕ) : V) (e 2)) ?_
  wb_auto
  refine wb_exs_bt _ (by simp) (tauT (poly ‘↑repSubst3Const + #3 + 8’) (poly ‘0 + 4 * #3 + 6’))
    (fun V _ _ e u h => by
      have h' := h; simp at h'
      rw [h'.1]; simpa [vval_tauT, vval, numeral_eq_natCast] using subst_le' ((repSubst3Const : ℕ) : V) (e 3)) ?_
  wb_auto
  refine wb_exs_bt _ (by simp) (tauT (poly ‘#1 + ↑repAtomEqCode + 8’) (poly ‘2 * (#1 + ↑repAtomEqCode) + 10’))
    (fun V _ _ e u h => by
      have h' := h; simp at h'
      rw [h'.1]; simpa [vval_tauT, vval, numeral_eq_natCast] using imp_le (le_self_add (a := e 1) (b := ((repAtomEqCode : ℕ) : V))) (le_add_self (a := ((repAtomEqCode : ℕ) : V)) (b := e 1))) ?_
  wb_auto
  refine PRAWitnessTransfer.wb_exs_poly _ (by simp) ‘(6 + #0 + 1) * (6 + #0 + 1) + 1’
    (fun V _ _ e u h => ⟨u, by
      have h' := h; simp at h'
      rw [h'.1]; simpa [qqAll, numeral_eq_natCast] using code2_le 6 (e 0), h⟩) ?_
  wb_auto
  refine PRAWitnessTransfer.wb_exs_poly _ (by simp) ‘(4 + (#4 + #0 + 1) * (#4 + #0 + 1) + 1) * (4 + (#4 + #0 + 1) * (#4 + #0 + 1) + 1) + 1’
    (fun V _ _ e u h => ⟨u, by
      have h' := h; simp at h'
      rw [h'.1]; simpa [qqAnd, numeral_eq_natCast] using code3_le 4 (e 4) (e 0), h⟩) ?_
  wb_auto
  refine PRAWitnessTransfer.wb_exs_poly _ (by simp) ‘(7 + #0 + 1) * (7 + #0 + 1) + 1’
    (fun V _ _ e u h => ⟨u, by
      have h' := h; simp at h'
      rw [h'.1]; simpa [qqExs, numeral_eq_natCast] using code2_le 7 (e 0), h⟩) ?_
  wb_auto
  refine PRAWitnessTransfer.wb_exs_poly _ (by simp) ‘(6 + #0 + 1) * (6 + #0 + 1) + 1’
    (fun V _ _ e u h => ⟨u, by
      have h' := h; simp at h'
      rw [h'.1]; simpa [qqAll, numeral_eq_natCast] using code2_le 6 (e 0), h⟩) ?_
  wb_auto
  refine PRAWitnessTransfer.wb_exs_poly _ (by simp) ‘(4 + (↑repAtomXXCode + #5 + 1) * (↑repAtomXXCode + #5 + 1) + 1) * (4 + (↑repAtomXXCode + #5 + 1) * (↑repAtomXXCode + #5 + 1) + 1) + 1’
    (fun V _ _ e u h => ⟨u, by
      have h' := h; simp at h'
      rw [h'.1]; simpa [qqAnd, numeral_eq_natCast] using code3_le 4 ((repAtomXXCode : ℕ) : V) (e 5), h⟩) ?_
  wb_auto
  refine PRAWitnessTransfer.wb_exs_poly _ (by simp) ‘(7 + #0 + 1) * (7 + #0 + 1) + 1’
    (fun V _ _ e u h => ⟨u, by
      have h' := h; simp at h'
      rw [h'.1]; simpa [qqExs, numeral_eq_natCast] using code2_le 7 (e 0), h⟩) ?_
  wb_auto
  refine wb_exs_bt _ (by simp) (tauT (poly ‘↑repAtomYYCode + #0 + 8’) (poly ‘2 * (↑repAtomYYCode + #0) + 14’))
    (fun V _ _ e u h => by
      have h' := h; simp at h'
      rw [h'.1]; simpa [vval_tauT, vval, numeral_eq_natCast] using iff_le (le_self_add (a := ((repAtomYYCode : ℕ) : V)) (b := e 0)) (le_add_self (a := e 0) (b := ((repAtomYYCode : ℕ) : V)))) ?_
  wb_auto
  refine PRAWitnessTransfer.wb_exs_poly _ (by simp) ‘(6 + #0 + 1) * (6 + #0 + 1) + 1’
    (fun V _ _ e u h => ⟨u, by
      have h' := h; simp at h'
      rw [h'.1]; simpa [qqAll, numeral_eq_natCast] using code2_le 6 (e 0), h⟩) ?_
  wb_auto
  refine PRAWitnessTransfer.wb_exs_poly _ (by simp) ‘(7 + #0 + 1) * (7 + #0 + 1) + 1’
    (fun V _ _ e u h => ⟨u, by
      have h' := h; simp at h'
      rw [h'.1]; simpa [qqExs, numeral_eq_natCast] using code2_le 7 (e 0), h⟩) ?_
  wb_auto
  exact PRAWitnessTransfer.wb_exs_poly _ (by simp) ‘(6 + #0 + 1) * (6 + #0 + 1) + 1’
    (fun V _ _ e u h => ⟨u, by
      have h' := h; simp at h'
      rw [h'.1]; simpa [qqAll, numeral_eq_natCast] using code2_le 6 (e 0), h⟩) (by wb_auto)

/-- The towers of `repBodyVal_le`, in the variable `#0`. -/
noncomputable def repT0 {n : ℕ} : BoundTerm (n + 1) := tauT (poly ‘↑repC + #0 + 8’) (poly ‘4 * #0 + 12’)

noncomputable def repT2 {n : ℕ} : BoundTerm (n + 1) :=
  tauT (add repT0 (poly ‘8’)) (add (mul (poly ‘2’) repT0) (poly ‘20’))

theorem wb_repCh_sigma : WB M repCh.sigma.val := by
  simpa only [repCh, HierarchySymbol.Semiformula.sigma_mkDelta,
    HierarchySymbol.Semiformula.val_mkSigma, schemaSigma] using
    (wb_schemaSigma (M := M) 2 repBodyValGraph wb_repBodyValGraph)

theorem wb_repCh_neg_pi : WB M (∼repCh.pi.val) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := wb_qqAllsDef (M := M); have := wb_isUFormula_neg_pi (M := M); have := wb_shiftGraph (M := M)
  have := wb_bvGraph (M := M); have := wb_fvarVecDef (M := M); have := wb_substsGraph (M := M)
  have := wb_isSemiformula_neg_pi (M := M); have := wb_repBodyValGraph (M := M)
  simp only [repCh, HierarchySymbol.Semiformula.pi_mkDelta, HierarchySymbol.Semiformula.val_mkPi]
  wb_auto
  · exact wb_exs_bt _ (by simp) (tauT (poly ‘#0’) (poly ‘2 * #1’)) (fun V _ _ e x h => by
      have h' := h; simp at h'
      rw [h'.1]; simpa [vval_tauT, vval] using qqAlls_le (e 0) (e 1)) (by wb_auto)
  · exact wb_exs_bt _ (by simp) (tauT (poly ‘(#0 + 2) * (#0 + 2) + 1 + 8’) (poly ‘2 * #0 + 6’))
      (fun V _ _ e x h => by
        have h' := h; simp at h'
        rw [h'.1]
        by_cases hb : IsUFormula ℒₛₑₜ (e 0)
        · simpa [vval_tauT, vval, numeral_eq_natCast] using shift_le (e 0) hb
        · rw [shift_not_uformula hb]; simp) (by wb_auto)
  · exact PRAWitnessTransfer.wb_exs_poly _ (by simp) ‘#0’ (fun V _ _ e x h => ⟨x, by
      have h' := h; simp at h'
      rw [h'.1]; simpa using bv_le_self (e 0), h⟩) (by wb_auto)
  refine wb_exs_bt' _ (by simp) (tauT (poly ‘(#1 + 2) * (#1 + 2) + 1’) (poly ‘2 * #1’))
    (fun V _ _ e x h => ⟨x, ?_, h⟩) ?_
  · have h' := h; simp at h'
    rw [h'.1]; simpa [vval_tauT, vval] using fvarVec_le (e 1) (e 1) le_rfl
  wb_auto
  refine wb_exs_bt' _ (by simp) (tauT (poly ‘#0 + #1 + 8’) (poly ‘0 + 4 * #1 + 6’))
    (fun V _ _ e x h => ⟨x, ?_, h⟩) ?_
  · have h' := h; simp at h'
    rw [h'.1]; simpa [vval_tauT, vval, numeral_eq_natCast] using subst_le' (e 0) (e 1)
  wb_auto
  exact wb_exs_bt _ (by simp)
    (tauT (add repT2 (poly ‘8’)) (add (mul (poly ‘2’) repT2) (poly ‘10’)))
    (fun V _ _ e x h => by
      have h' := h; simp at h'
      rw [h'.1]; simpa [repT2, repT0, vval_tauT, vval, numeral_eq_natCast] using repBodyVal_le (e 0)) (by wb_auto)


/-! ### Foundation's `Δ₁` combinators -/

/-- Both polarities of a `Δ₁` theory recognizer have bounded witnesses. -/
def GoodCh {T : SetTheory} (d : T.Δ₁) (M : Type) [Nonempty M] [Structure language M]
    [Structure.Eq language M] [M↓[language] ⊧* PRA] : Prop :=
  WB M d.ch.sigma.val ∧ WB M (∼d.ch.pi.val)

theorem goodCh_singleton (φ : SetTheorySentence) : GoodCh (Theory.Δ₁.singleton φ) M := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  constructor
  · change WB M (HierarchySymbol.Semiformula.ofZero
      (.mkSigma “x. x = ↑(Encodable.encode φ)” : 𝚺₀.Semisentence 1) 𝚫₁).sigma.val
    simp only [HierarchySymbol.Semiformula.ofZero, HierarchySymbol.Semiformula.sigma_mkDelta,
      HierarchySymbol.Semiformula.val_mkSigma]
    wb_auto
  · change WB M (∼(HierarchySymbol.Semiformula.ofZero
      (.mkSigma “x. x = ↑(Encodable.encode φ)” : 𝚺₀.Semisentence 1) 𝚫₁).pi.val)
    simp only [HierarchySymbol.Semiformula.ofZero, HierarchySymbol.Semiformula.pi_mkDelta,
      HierarchySymbol.Semiformula.val_mkPi, HierarchySymbol.Semiformula.val_mkSigma]
    wb_auto

theorem goodCh_empty : GoodCh (Theory.Δ₁.empty (L := ℒₛₑₜ)) M := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  constructor
  · change WB M (⊥ : 𝚫₁.Semisentence 1).sigma.val
    simp only [HierarchySymbol.Semiformula.sigma_falsum, HierarchySymbol.Semiformula.val_falsum]; wb_auto
  · change WB M (∼(⊥ : 𝚫₁.Semisentence 1).pi.val)
    simp only [HierarchySymbol.Semiformula.pi_falsum, HierarchySymbol.Semiformula.val_falsum]; wb_auto

theorem goodCh_add {T U : SetTheory} (dT : T.Δ₁) (dU : U.Δ₁) (hT : GoodCh dT M) (hU : GoodCh dU M) :
    GoodCh (Theory.Δ₁.add dT dU) M := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := hT.1; have := hT.2; have := hU.1; have := hU.2
  constructor
  · change WB M (dT.ch ⋎ dU.ch).sigma.val
    simp only [HierarchySymbol.Semiformula.sigma_or, HierarchySymbol.Semiformula.val_or]; wb_auto
  · change WB M (∼(dT.ch ⋎ dU.ch).pi.val)
    simp only [HierarchySymbol.Semiformula.pi_or, HierarchySymbol.Semiformula.val_or]; wb_auto

theorem goodCh_ofEq {T U : SetTheory} (dT : T.Δ₁) (h : T = U) (hT : GoodCh dT M) :
    GoodCh (Theory.Δ₁.ofEq dT h) M := hT

theorem goodCh_ofList : ∀ l : List SetTheorySentence, GoodCh (Theory.Δ₁.ofList l) M
  | [] => goodCh_ofEq _ _ goodCh_empty
  | φ :: l => goodCh_ofEq _ _ (goodCh_add _ _ (goodCh_singleton φ) (goodCh_ofList l))

theorem goodCh_ofFinite (T : SetTheory) (h : Set.Finite T) : GoodCh (Theory.Δ₁.ofFinite T h) M :=
  goodCh_ofEq _ _ (goodCh_ofList _)

/-- **The ZFC axiom recognizer has bounded witnesses**, in both polarities. -/
theorem goodCh_zfc : GoodCh ZFC_delta1 M := by
  have hEQ : GoodCh eqAxiom_delta1 M := goodCh_ofFinite _ _
  have hFix : GoodCh zfFixed_delta1 M := goodCh_ofList
    [SetTheory.Axiom.empty, SetTheory.Axiom.extentionality, SetTheory.Axiom.pairing,
      SetTheory.Axiom.union, SetTheory.Axiom.power, SetTheory.Axiom.infinity, SetTheory.Axiom.foundation]
  have hSep : GoodCh separationTheory_delta1 M := ⟨wb_sepCh_sigma, wb_sepCh_neg_pi⟩
  have hRep : GoodCh replacementTheory_delta1 M := ⟨wb_repCh_sigma, wb_repCh_neg_pi⟩
  have hZF : GoodCh ZF_delta1 M :=
    goodCh_add _ _ (goodCh_add _ _ (goodCh_add _ _ hEQ hFix) hSep) hRep
  have hAC : GoodCh AC_delta1 M := goodCh_singleton SetTheory.Axiom.choice
  exact goodCh_add _ _ hZF hAC

end models
end DiophantineConsistency.PRAWitnessZFCAxioms
