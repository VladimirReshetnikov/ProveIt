import IPRADerivations.Algebra.QuadraticIntegerEmbedding

/-!
# The actual zero-radicand projection branch

The d=0 branch of lem:orderedextension assigns (a,b) the original
integer sign of a. Its actual finite projection and sign programs
discard b, and their sign-zero equality is exactly equality of the
first integer value. Ring, order and domain laws follow this proved
projection. No positive-cone closure is applied at radicand zero.
Only one integer ground stage is constructed here.
-/

set_option autoImplicit false
set_option linter.unnecessarySeqFocus false

namespace LeanProofs.IPRA.Algebra.QuadraticZeroProjection

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open QuadraticSignCertificates (first second code tag add negative multiply zeroCode oneCode
  negative_first multiply_first zero_first_value)
open QuadraticConeOrder (equal_of_values equal_symm equal_first add_first)
open QuadraticIntegerEmbedding (integer integer_first integer_second integer_sign integer_positive
  integer_positive_reflect integer_isZero integer_zero_reflect integer_equivalent integer_equivalent_reflect)
open QuadraticIntegerOrder (difference root natural)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def project (x : PTm n) : PTm n := integer (first x)
def sign (x : PTm n) : PTm n := tag (first x)
def positive (x : PTm n) : Fm PTm n := sign x ≐ one
def isZero (x : PTm n) : Fm PTm n := sign x ≐ zero
def equivalent (x y : PTm n) : Fm PTm n := isZero (difference x y)
def less (x y : PTm n) : Fm PTm n := positive (difference y x)
@[simp] theorem subst_project {l : ℕ} (σ : Fin n → PTm l) (x : PTm n) :
    Syn.subst σ (project x) = project (Syn.subst σ x) := by simp [project]
@[simp] theorem subst_sign {l : ℕ} (σ : Fin n → PTm l) (x : PTm n) :
    Syn.subst σ (sign x) = sign (Syn.subst σ x) := by simp [sign]
@[simp] theorem subst_positive {l : ℕ} (σ : Fin n → PTm l) (x : PTm n) :
    (positive x).subst σ = positive (Syn.subst σ x) := by simp [positive]
@[simp] theorem subst_isZero {l : ℕ} (σ : Fin n → PTm l) (x : PTm n) :
    (isZero x).subst σ = isZero (Syn.subst σ x) := by simp [isZero]
@[simp] theorem subst_equivalent {l : ℕ} (σ : Fin n → PTm l) (x y : PTm n) :
    (equivalent x y).subst σ = equivalent (Syn.subst σ x) (Syn.subst σ y) := by simp [equivalent]
@[simp] theorem subst_less {l : ℕ} (σ : Fin n → PTm l) (x y : PTm n) :
    (less x y).subst σ = less (Syn.subst σ x) (Syn.subst σ y) := by simp [less]

theorem sign_project (x : PTm n) : Γ ⊢[PRAAx]
    sign x ≐ QuadraticSignCertificates.sign one (project x) :=
  (integer_sign one (first x) (le_refl one)).eqSymm
theorem project_add (x y : PTm n) : Γ ⊢[PRAAx]
    QuadraticSignCertificates.equal (project (add x y)) (add (project x) (project y)) := by
  apply equal_of_values <;> simp only [project,integer_first,integer_second,add_first,QuadraticConeOrder.add_second] <;> ring
theorem project_negative (x : PTm n) : Γ ⊢[PRAAx]
    QuadraticSignCertificates.equal (project (negative x)) (negative (project x)) := by
  apply equal_of_values <;> simp only [project,integer_first,integer_second,negative_first,QuadraticSignCertificates.negative_second] <;> ring
theorem project_multiply (x y : PTm n) : Γ ⊢[PRAAx]
    QuadraticSignCertificates.equal (project (multiply zero x y)) (multiply one (project x) (project y)) := by
  apply equal_of_values <;> simp only [project,integer_first,integer_second,multiply_first,
    QuadraticSignCertificates.multiply_second,Q.mk_zero,map_zero] <;> ring
theorem project_difference (x y : PTm n) : Γ ⊢[PRAAx]
    QuadraticSignCertificates.equal (project (difference x y)) (difference (project x) (project y)) := by
  apply equal_of_values <;> simp only [project,difference,integer_first,integer_second,add_first,
    QuadraticConeOrder.add_second,negative_first,QuadraticSignCertificates.negative_second] <;> ring

theorem zero_reflect (x : PTm n) (h : Γ ⊢[PRAAx] isZero x) : Γ ⊢[PRAAx] ZT.eq (first x) (ZT.ofNat zero) :=
  integer_zero_reflect one _ (le_refl one) ((sign_project x).eqSymm.eqTrans h)
theorem zero_of_projection (x : PTm n) (h : Γ ⊢[PRAAx] ZT.eq (first x) (ZT.ofNat zero)) : Γ ⊢[PRAAx] isZero x :=
  (sign_project x).eqTrans (integer_isZero one _ (le_refl one) h)
theorem zero_iff (x : PTm n) : Γ ⊢[PRAAx] Fm.iff (isZero x) (ZT.eq (first x) (ZT.ofNat zero)) :=
  .andI (.impI (zero_reflect x Prf.hyp0)) (.impI (zero_of_projection x Prf.hyp0))
theorem positive_reflect (x : PTm n) (h : Γ ⊢[PRAAx] positive x) : Γ ⊢[PRAAx] zle (ZT.ofNat one) (first x) :=
  integer_positive_reflect one _ (le_refl one) ((sign_project x).eqSymm.eqTrans h)
theorem positive_of_projection (x : PTm n) (h : Γ ⊢[PRAAx] zle (ZT.ofNat one) (first x)) : Γ ⊢[PRAAx] positive x :=
  (sign_project x).eqTrans (integer_positive one _ (le_refl one) h)
theorem positive_iff (x : PTm n) : Γ ⊢[PRAAx] Fm.iff (positive x) (zle (ZT.ofNat one) (first x)) :=
  .andI (.impI (positive_reflect x Prf.hyp0)) (.impI (positive_of_projection x Prf.hyp0))

theorem equivalent_reflect (x y : PTm n) (h : Γ ⊢[PRAAx] equivalent x y) : Γ ⊢[PRAAx] ZT.eq (first x) (first y) := by
  have hz := ZT.toZ_eq (zero_reflect _ h)
  apply ZT.derive
  simp only [difference,add_first,negative_first,ZT.toZ_ofNat,Q.mk_zero,map_zero] at hz
  linear_combination hz
theorem equivalent_of_projection (x y : PTm n) (h : Γ ⊢[PRAAx] ZT.eq (first x) (first y)) : Γ ⊢[PRAAx] equivalent x y := by
  apply zero_of_projection
  apply ZT.derive
  rw [difference,add_first,negative_first,ZT.toZ_eq h,ZT.toZ_ofNat]; ipra_simps; ring
theorem equivalent_iff (x y : PTm n) : Γ ⊢[PRAAx] Fm.iff (equivalent x y) (ZT.eq (first x) (first y)) :=
  .andI (.impI (equivalent_reflect _ _ Prf.hyp0)) (.impI (equivalent_of_projection _ _ Prf.hyp0))
theorem equivalent_refl (x : PTm n) : Γ ⊢[PRAAx] equivalent x x := equivalent_of_projection _ _ (ZT.derive rfl)
theorem equivalent_symm (x y : PTm n) (h : Γ ⊢[PRAAx] equivalent x y) : Γ ⊢[PRAAx] equivalent y x :=
  equivalent_of_projection _ _ (ZT.derive (ZT.toZ_eq (equivalent_reflect _ _ h)).symm)
theorem equivalent_trans (x y z : PTm n) (h : Γ ⊢[PRAAx] equivalent x y) (h' : Γ ⊢[PRAAx] equivalent y z) : Γ ⊢[PRAAx] equivalent x z :=
  equivalent_of_projection _ _ (ZT.derive ((ZT.toZ_eq (equivalent_reflect _ _ h)).trans (ZT.toZ_eq (equivalent_reflect _ _ h'))))
theorem equivalent_add (x y u v : PTm n) (h : Γ ⊢[PRAAx] equivalent x y) (h' : Γ ⊢[PRAAx] equivalent u v) : Γ ⊢[PRAAx]
    equivalent (add x u) (add y v) := by
  apply equivalent_of_projection
  apply ZT.derive
  rw [add_first,add_first,ZT.toZ_eq (equivalent_reflect _ _ h),ZT.toZ_eq (equivalent_reflect _ _ h')]
theorem equivalent_negative (x y : PTm n) (h : Γ ⊢[PRAAx] equivalent x y) : Γ ⊢[PRAAx] equivalent (negative x) (negative y) := by
  apply equivalent_of_projection
  apply ZT.derive
  rw [negative_first,negative_first,ZT.toZ_eq (equivalent_reflect _ _ h)]
theorem equivalent_multiply (x y u v : PTm n) (h : Γ ⊢[PRAAx] equivalent x y) (h' : Γ ⊢[PRAAx] equivalent u v) : Γ ⊢[PRAAx]
    equivalent (multiply zero x u) (multiply zero y v) := by
  apply equivalent_of_projection
  apply ZT.derive
  simp only [multiply_first,Q.mk_zero,map_zero]
  rw [ZT.toZ_eq (equivalent_reflect _ _ h),ZT.toZ_eq (equivalent_reflect _ _ h')]
  ring

theorem zero_project (x : PTm n) (h : Γ ⊢[PRAAx] isZero x) : Γ ⊢[PRAAx] QuadraticIntegerOrder.isZero one (project x) :=
  (sign_project _).eqSymm.eqTrans h
theorem zero_of_project (x : PTm n) (h : Γ ⊢[PRAAx] QuadraticIntegerOrder.isZero one (project x)) : Γ ⊢[PRAAx] isZero x :=
  (sign_project _).eqTrans h
theorem positive_project (x : PTm n) (h : Γ ⊢[PRAAx] positive x) : Γ ⊢[PRAAx] QuadraticIntegerOrder.positive one (project x) :=
  (sign_project _).eqSymm.eqTrans h
theorem positive_of_project (x : PTm n) (h : Γ ⊢[PRAAx] QuadraticIntegerOrder.positive one (project x)) : Γ ⊢[PRAAx] positive x :=
  (sign_project _).eqTrans h
theorem positive_add (x y : PTm n) (hx : Γ ⊢[PRAAx] positive x) (hy : Γ ⊢[PRAAx] positive y) : Γ ⊢[PRAAx] positive (add x y) :=
  positive_of_project _ (QuadraticIntegerOrder.positive_value_congr _ _ _ (le_refl one) (equal_symm (project_add _ _))
    (QuadraticIntegerOrder.positive_add _ _ _ (le_refl one) (positive_project _ hx) (positive_project _ hy)))
theorem positive_multiply (x y : PTm n) (hx : Γ ⊢[PRAAx] positive x) (hy : Γ ⊢[PRAAx] positive y) : Γ ⊢[PRAAx] positive (multiply zero x y) :=
  positive_of_project _ (QuadraticIntegerOrder.positive_value_congr _ _ _ (le_refl one) (equal_symm (project_multiply _ _))
    (QuadraticIntegerOrder.positive_multiply _ _ _ (le_refl one) (positive_project _ hx) (positive_project _ hy)))
theorem zero_multiply (x y : PTm n) (hx : Γ ⊢[PRAAx] isZero x) : Γ ⊢[PRAAx] isZero (multiply zero x y) :=
  zero_of_project _ (QuadraticIntegerOrder.zero_value_congr _ _ _ (le_refl one) (equal_symm (project_multiply _ _))
    (QuadraticIntegerOrder.zero_multiply _ _ _ (le_refl one) (zero_project _ hx)))
theorem zero_negative (x : PTm n) (hx : Γ ⊢[PRAAx] isZero x) : Γ ⊢[PRAAx] isZero (negative x) :=
  zero_of_project _ (QuadraticIntegerOrder.zero_value_congr _ _ _ (le_refl one) (equal_symm (project_negative _))
    (QuadraticIntegerOrder.zero_negative _ _ (le_refl one) (zero_project _ hx)))
theorem zero_add (x y : PTm n) (hx : Γ ⊢[PRAAx] isZero x) (hy : Γ ⊢[PRAAx] isZero y) : Γ ⊢[PRAAx] isZero (add x y) :=
  zero_of_project _ (QuadraticIntegerOrder.zero_value_congr _ _ _ (le_refl one) (equal_symm (project_add _ _))
    (QuadraticIntegerOrder.zero_add _ _ _ (le_refl one) (zero_project _ hx) (zero_project _ hy)))
theorem zero_product_reflect (x y : PTm n) (h : Γ ⊢[PRAAx] isZero (multiply zero x y)) : Γ ⊢[PRAAx] isZero x ⋎ isZero y := by
  have hz := QuadraticIntegerOrder.zero_value_congr _ _ _ (le_refl one) (project_multiply x y) (zero_project _ h)
  refine .orE (QuadraticIntegerOrder.zero_product_reflect _ _ _ (le_refl one) hz) ?_ ?_
  · exact .orI₁ (zero_of_project _ Prf.hyp0)
  · exact .orI₂ (zero_of_project _ Prf.hyp0)

theorem sign_congr (x y : PTm n) (h : Γ ⊢[PRAAx] equivalent x y) : Γ ⊢[PRAAx] sign x ≐ sign y :=
  (sign_project _).eqTrans ((QuadraticConeOrder.sign_congr _ _ _ (le_refl one)
    (QuadraticIntegerEmbedding.integer_equal _ _ (equivalent_reflect _ _ h))).eqTrans (sign_project _).eqSymm)
theorem equivalent_project (x y : PTm n) (h : Γ ⊢[PRAAx] equivalent x y) : Γ ⊢[PRAAx]
    QuadraticIntegerOrder.equivalent one (project x) (project y) :=
  QuadraticIntegerOrder.zero_value_congr _ _ _ (le_refl one) (project_difference _ _) (zero_project _ h)
theorem equivalent_of_project (x y : PTm n) (h : Γ ⊢[PRAAx] QuadraticIntegerOrder.equivalent one (project x) (project y)) : Γ ⊢[PRAAx]
    equivalent x y :=
  zero_of_project _ (QuadraticIntegerOrder.zero_value_congr _ _ _ (le_refl one) (equal_symm (project_difference _ _)) h)
theorem less_project (x y : PTm n) (h : Γ ⊢[PRAAx] less x y) : Γ ⊢[PRAAx]
    QuadraticIntegerOrder.less one (project x) (project y) :=
  QuadraticIntegerOrder.positive_value_congr _ _ _ (le_refl one) (project_difference _ _) (positive_project _ h)
theorem less_of_project (x y : PTm n) (h : Γ ⊢[PRAAx] QuadraticIntegerOrder.less one (project x) (project y)) : Γ ⊢[PRAAx]
    less x y :=
  positive_of_project _ (QuadraticIntegerOrder.positive_value_congr _ _ _ (le_refl one) (equal_symm (project_difference _ _)) h)
theorem less_irrefl (x : PTm n) : Γ ⊢[PRAAx] neg (less x x) := by
  refine .impI ?_
  exact .impE (QuadraticIntegerOrder.less_irrefl one (project x) (le_refl one)) (less_project _ _ Prf.hyp0)
theorem less_trans (x y z : PTm n) (hxy : Γ ⊢[PRAAx] less x y) (hyz : Γ ⊢[PRAAx] less y z) : Γ ⊢[PRAAx] less x z :=
  less_of_project _ _ (QuadraticIntegerOrder.less_trans _ _ _ _ (le_refl one) (less_project _ _ hxy) (less_project _ _ hyz))
theorem ordered_trichotomy (x y : PTm n) : Γ ⊢[PRAAx] less x y ⋎ (less y x ⋎ equivalent x y) := by
  refine .orE (QuadraticIntegerOrder.ordered_trichotomy one (project x) (project y) (le_refl one)) ?_ ?_
  · exact .orI₁ (less_of_project _ _ Prf.hyp0)
  · refine .orE Prf.hyp0 ?_ ?_
    · exact .orI₂ (.orI₁ (less_of_project _ _ Prf.hyp0))
    · exact .orI₂ (.orI₂ (equivalent_of_project _ _ Prf.hyp0))
theorem less_translate (x y z : PTm n) (h : Γ ⊢[PRAAx] less x y) : Γ ⊢[PRAAx] less (add x z) (add y z) :=
  less_of_project _ _ (QuadraticIntegerOrder.less_congr _ _ _ _ _ (le_refl one)
    (QuadraticIntegerOrder.coefficient_equal_equivalent _ _ _ (le_refl one) (equal_symm (project_add _ _)))
    (QuadraticIntegerOrder.coefficient_equal_equivalent _ _ _ (le_refl one) (equal_symm (project_add _ _)))
    (QuadraticIntegerOrder.less_translate _ _ _ _ (le_refl one) (less_project _ _ h)))
theorem less_congr (x x' y y' : PTm n) (hx : Γ ⊢[PRAAx] equivalent x x') (hy : Γ ⊢[PRAAx] equivalent y y')
    (h : Γ ⊢[PRAAx] less x y) : Γ ⊢[PRAAx] less x' y' :=
  less_of_project _ _ (QuadraticIntegerOrder.less_congr _ _ _ _ _ (le_refl one)
    (equivalent_project _ _ hx) (equivalent_project _ _ hy) (less_project _ _ h))

theorem scalar_injective (a b : ZT n) (h : Γ ⊢[PRAAx] equivalent (integer a) (integer b)) : Γ ⊢[PRAAx] ZT.eq a b := by
  apply ZT.derive
  have hv := ZT.toZ_eq (equivalent_reflect _ _ h)
  simpa only [integer_first] using hv
theorem scalar_equivalent (a b : ZT n) (h : Γ ⊢[PRAAx] ZT.eq a b) : Γ ⊢[PRAAx] equivalent (integer a) (integer b) := by
  apply equivalent_of_projection
  apply ZT.derive
  rw [integer_first,integer_first]; exact ZT.toZ_eq h
theorem root_isZero : Γ ⊢[PRAAx] isZero (root : PTm n) := by
  apply zero_of_projection
  apply ZT.derive
  simp only [root,QuadraticSignCertificates.naturalPair,QuadraticSignCertificates.first_value,ZT.toZ_ofNat]
theorem root_square : Γ ⊢[PRAAx] equivalent (multiply zero root root) (natural (zero : PTm n)) := by
  apply equivalent_of_projection
  apply ZT.derive
  simp only [multiply_first,root,natural,QuadraticSignCertificates.naturalPair,
    QuadraticSignCertificates.first_value,QuadraticSignCertificates.second_value,ZT.toZ_ofNat,Q.mk_zero,map_zero]
  ring
theorem unique_zero_root (x : PTm n) (h : Γ ⊢[PRAAx] equivalent (multiply zero x x) (natural zero)) : Γ ⊢[PRAAx] equivalent x root := by
  have hz : Γ ⊢[PRAAx] isZero (multiply zero x x) := by
    apply zero_of_projection
    apply ZT.derive
    have hv := ZT.toZ_eq (equivalent_reflect _ _ h)
    simpa only [natural,QuadraticSignCertificates.naturalPair,QuadraticSignCertificates.first_value,ZT.toZ_ofNat,Q.mk_zero,map_zero] using hv
  have hx : Γ ⊢[PRAAx] isZero x := .orE (zero_product_reflect x x hz) Prf.hyp0 Prf.hyp0
  apply equivalent_of_projection
  apply ZT.derive
  exact (ZT.toZ_eq (zero_reflect _ hx)).trans (ZT.toZ_eq (zero_reflect _ root_isZero)).symm

/-! Actual PR1 output: the original first signed pair, its scalar
projection, and the original integer sign. The second coordinate of
the source pair is never used as a validity premise. -/
def output (x : PTm n) : PTm n := pairT (code (first x)) (pairT (project x) (sign x))
def outputF : PR 1 := PTm.toPR (output (var 0))
def run (x : PTm n) : PTm n := ap1 outputF x
@[simp] theorem subst_output {l : ℕ} (σ : Fin n → PTm l) (x : PTm n) :
    Syn.subst σ (output x) = output (Syn.subst σ x) := by simp [output]
@[simp] theorem subst_run {l : ℕ} (σ : Fin n → PTm l) (x : PTm n) :
    Syn.subst σ (run x) = run (Syn.subst σ x) := by simp [run]
theorem program_at (x : PTm n) : Γ ⊢[PRAAx] run x ≐ output x := by
  simpa [run,outputF,ap1] using toPR_eq (Γ := Γ) (output (var 0) : PTm 1) ![x]
theorem returned_coefficient (x : PTm n) : Γ ⊢[PRAAx] fstT (run x) ≐ code (first x) :=
  (congrFst (program_at x)).eqTrans (fst_pair _ _)
theorem returned_projection (x : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run x)) ≐ project x :=
  (congrFst ((congrSnd (program_at x)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_sign (x : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run x)) ≐ sign x :=
  (congrSnd ((congrSnd (program_at x)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)
theorem returned_zero_iff (x : PTm n) : Γ ⊢[PRAAx]
    Fm.iff (sndT (sndT (run x)) ≐ zero) (ZT.eq (first x) (ZT.ofNat zero)) :=
  .andI (.impI (zero_reflect _ ((returned_sign _).wk.eqSymm.eqTrans Prf.hyp0)))
    (.impI ((returned_sign _).wk.eqTrans (zero_of_projection _ Prf.hyp0)))

theorem zero_stage_projection_arithmetic_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (QuadraticSignCertificates.equal (project (add (var 0) (var 1))) (add (project (var 0)) (project (var 1))) ⋏
      (QuadraticSignCertificates.equal (project (negative (var 0))) (negative (project (var 0))) ⋏
        QuadraticSignCertificates.equal (project (multiply zero (var 0) (var 1))) (multiply one (project (var 0)) (project (var 1))))) :=
  closeUniv 2 (.andI (project_add _ _) (.andI (project_negative _) (project_multiply _ _)))
theorem zero_stage_sign_reflection_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (Fm.iff (isZero (var 0)) (ZT.eq (first (var 0)) (ZT.ofNat zero)) ⋏
      Fm.iff (positive (var 0)) (zle (ZT.ofNat one) (first (var 0)))) := closeUniv 1 (.andI (zero_iff _) (positive_iff _))
theorem zero_stage_equality_reflection_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (Fm.iff (equivalent (var 0) (var 1)) (ZT.eq (first (var 0)) (first (var 1)))) := closeUniv 2 (equivalent_iff _ _)
theorem zero_stage_equality_equivalence_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (equivalent (var 0) (var 0) ⋏ ((equivalent (var 0) (var 1) ⟶ equivalent (var 1) (var 0)) ⋏
      (equivalent (var 0) (var 1) ⟶ equivalent (var 1) (var 2) ⟶ equivalent (var 0) (var 2)))) :=
  closeUniv 3 (.andI (equivalent_refl _) (.andI (.impI (equivalent_symm _ _ Prf.hyp0)) (.impI (.impI (equivalent_trans _ _ _ Prf.hyp1 Prf.hyp0)))))
theorem zero_stage_equality_operations_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (equivalent (var 0) (var 1) ⟶ equivalent (var 2) (var 3) ⟶
      (equivalent (add (var 0) (var 2)) (add (var 1) (var 3)) ⋏
        (equivalent (multiply zero (var 0) (var 2)) (multiply zero (var 1) (var 3)) ⋏ equivalent (negative (var 0)) (negative (var 1))))) :=
  closeUniv 4 (.impI (.impI (.andI (equivalent_add _ _ _ _ Prf.hyp1 Prf.hyp0)
    (.andI (equivalent_multiply _ _ _ _ Prf.hyp1 Prf.hyp0) (equivalent_negative _ _ Prf.hyp1)))))
theorem zero_stage_positive_closure_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (positive (var 0) ⟶ positive (var 1) ⟶ (positive (add (var 0) (var 1)) ⋏ positive (multiply zero (var 0) (var 1)))) :=
  closeUniv 2 (.impI (.impI (.andI (positive_add _ _ Prf.hyp1 Prf.hyp0) (positive_multiply _ _ Prf.hyp1 Prf.hyp0))))
theorem zero_stage_zero_ideal_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (isZero (var 0) ⟶ (isZero (negative (var 0)) ⋏ (isZero (multiply zero (var 0) (var 1)) ⋏
      (isZero (var 1) ⟶ isZero (add (var 0) (var 1)))))) :=
  closeUniv 2 (.impI (.andI (zero_negative _ Prf.hyp0) (.andI (zero_multiply _ _ Prf.hyp0) (.impI (zero_add _ _ Prf.hyp1 Prf.hyp0)))))
theorem zero_stage_domain_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (isZero (multiply zero (var 0) (var 1)) ⟶ (isZero (var 0) ⋎ isZero (var 1))) := closeUniv 2 (.impI (zero_product_reflect _ _ Prf.hyp0))
theorem zero_stage_order_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (neg (less (var 0) (var 0)) ⋏ ((less (var 0) (var 1) ⟶ less (var 1) (var 2) ⟶ less (var 0) (var 2)) ⋏
      (less (var 0) (var 1) ⋎ (less (var 1) (var 0) ⋎ equivalent (var 0) (var 1))))) :=
  closeUniv 3 (.andI (less_irrefl _) (.andI (.impI (.impI (less_trans _ _ _ Prf.hyp1 Prf.hyp0))) (ordered_trichotomy _ _)))
theorem zero_stage_root_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (isZero root ⋏ (equivalent (multiply zero root root) (natural zero) ⋏
      (equivalent (multiply zero (var 0) (var 0)) (natural zero) ⟶ equivalent (var 0) root))) :=
  closeUniv 1 (.andI root_isZero (.andI root_square (.impI (unique_zero_root _ Prf.hyp0))))
theorem zero_stage_scalar_injective_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (Fm.iff (equivalent (integer (⟨var 0,var 1⟩ : ZT 4)) (integer (⟨var 2,var 3⟩ : ZT 4)))
      (ZT.eq (⟨var 0,var 1⟩ : ZT 4) (⟨var 2,var 3⟩ : ZT 4))) :=
  closeUniv 4 (.andI (.impI (scalar_injective _ _ Prf.hyp0)) (.impI (scalar_equivalent _ _ Prf.hyp0)))
theorem actual_zero_stage_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (run (var 0) ≐ output (var 0)) := closeUniv 1 (program_at _)
theorem actual_zero_stage_returned_sign_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (Fm.iff (sndT (sndT (run (var 0))) ≐ zero) (ZT.eq (first (var 0)) (ZT.ofNat zero))) := closeUniv 1 (returned_zero_iff _)

end LeanProofs.IPRA.Algebra.QuadraticZeroProjection
