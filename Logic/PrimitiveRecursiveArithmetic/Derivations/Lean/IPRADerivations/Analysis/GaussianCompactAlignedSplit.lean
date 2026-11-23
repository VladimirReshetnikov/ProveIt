import IPRADerivations.Analysis.GaussianCompactAlignedTime

/-!
# Original shared-step splitting from aligned-time observations alone

Only the actual zero-time-distance sample comparison is assumed. The
original inside/grid-value geometry, literal sum split and common-weight
finite sum bound are reused. Empty width-scaled sums are literal zero,
so both widths may be zero without a sampled near-time modulus.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianCompactAlignedSplit

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCompactAlignedTime (alignedSamples)
open GaussianRationalHorner (qmul qadd qzero canonical positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalSyntheticDivision (qmul_congr qadd_congr)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianCompactRiemannName (grid value inside sampleBody sampleData sample_body_at quadrature)
open GaussianCompactRiemannSplit (fullData prefixPart suffixPart weight_shared sum_width_positive)
open GaussianCompactRiemannAdditivity (inside_left inside_right weighted_sum_distance)
open GaussianRationalRiemannRefinement (weight termsDistance)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def positiveInput (F : PR 3) (a C1 C2 E K x : PTm n) : Fm PTm n :=
  le one a ⋏ (le one E ⋏ (le one K ⋏ (le one C1 ⋏ (le one C2 ⋏ alignedSamples F a (C1+C2) E x))))
@[simp] theorem subst_positiveInput {m : ℕ} (σ : Fin n → PTm m) (F : PR 3) (a C1 C2 E K x : PTm n) :
    (positiveInput F a C1 C2 E K x).subst σ = positiveInput F (Syn.subst σ a) (Syn.subst σ C1) (Syn.subst σ C2)
      (Syn.subst σ E) (Syn.subst σ K) (Syn.subst σ x) := by simp [positiveInput]

theorem prefix_term_distance (F : PR 3) (i s a C1 C2 E K x : PTm n) (h : Γ ⊢[PRAAx] positiveInput F a C1 C2 E K x)
    (hi : Γ ⊢[PRAAx] lt i (C1*K)) : Γ ⊢[PRAAx]
    distanceBounded (inst2 (sampleBody F) i (fullData s K a C1 C2 E x))
      (inst2 (sampleBody F) i (sampleData s (C1*K) a C1 E x)) two (unit s) := by
  have ha := h.andE₁
  have e := h.andE₂.andE₁
  have k := h.andE₂.andE₂.andE₁
  have c1 := h.andE₂.andE₂.andE₂.andE₁
  have c2 := h.andE₂.andE₂.andE₂.andE₂.andE₁
  have m := h.andE₂.andE₂.andE₂.andE₂.andE₂
  have bound : Γ ⊢[PRAAx] le i ((C1+C2)*K) := le_trans (le_of_lt hi) (mul_le_mul_right K (le_add_right C1 C2))
  have full := GaussianCompactRiemannName.grid_inside i ((C1+C2)*K) a (C1+C2) E ha e
    (positive_product _ _ (sum_width_positive C1 C2 c1) k) bound
  have part := inside_left a C1 C2 E _ (GaussianCompactRiemannName.grid_inside i (C1*K) a C1 E ha e
    (positive_product _ _ c1 k) (le_of_lt hi))
  have old := GaussianCompactAlignedTime.equal_value_at F s a (C1+C2) E x _ _ m full part (GaussianCompactRiemannSplit.prefix_grid_value i K a C1 C2 E c1 e k)
  exact distance_congr (sample_body_at F i s ((C1+C2)*K) a (C1+C2) E x).eqSymm
    (sample_body_at F i s (C1*K) a C1 E x).eqSymm (.eqRefl _) (.eqRefl _) old

theorem suffix_term_distance (F : PR 3) (i s a C1 C2 E K x : PTm n) (h : Γ ⊢[PRAAx] positiveInput F a C1 C2 E K x)
    (hi : Γ ⊢[PRAAx] lt i (C2*K)) : Γ ⊢[PRAAx]
    distanceBounded (inst2 (offB (sampleBody F)) i (pairT (C1*K) (fullData s K a C1 C2 E x)))
      (inst2 (sampleBody F) i (sampleData s (C2*K) (a+C1) C2 E x)) two (unit s) := by
  have ha := h.andE₁
  have e := h.andE₂.andE₁
  have k := h.andE₂.andE₂.andE₁
  have c1 := h.andE₂.andE₂.andE₂.andE₁
  have c2 := h.andE₂.andE₂.andE₂.andE₂.andE₁
  have m := h.andE₂.andE₂.andE₂.andE₂.andE₂
  have bound : Γ ⊢[PRAAx] le (C1*K+i) ((C1+C2)*K) :=
    le_congr (add_comm _ _) (by ipra_ring) (add_le_add_right (C1*K) (le_of_lt hi))
  have full := GaussianCompactRiemannName.grid_inside (C1*K+i) ((C1+C2)*K) a (C1+C2) E ha e
    (positive_product _ _ (sum_width_positive C1 C2 c1) k) bound
  have part := inside_right a C1 C2 E _ (GaussianCompactRiemannName.grid_inside i (C2*K) (a+C1) C2 E
    (le_trans ha (le_add_right _ _)) e (positive_product _ _ c2 k) (le_of_lt hi))
  have old := GaussianCompactAlignedTime.equal_value_at F s a (C1+C2) E x _ _ m full part (GaussianCompactRiemannSplit.suffix_grid_value i K a C1 C2 E c1 c2 e k)
  have off := (GaussianRationalFiniteProduct.offset_at (Γ := Γ) (sampleBody F) (C1*K) i (fullData s K a C1 C2 E x)).eqTrans
    (sample_body_at F (C1*K+i) s ((C1+C2)*K) a (C1+C2) E x)
  exact distance_congr off.eqSymm (sample_body_at F i s (C2*K) (a+C1) C2 E x).eqSymm (.eqRefl _) (.eqRefl _) old

theorem prefix_distance (F : PR 3) (s a C1 C2 E K x : PTm n) (h : Γ ⊢[PRAAx] positiveInput F a C1 C2 E K x) : Γ ⊢[PRAAx]
    distanceBounded (prefixPart F s K a C1 C2 E x) (quadrature F s (C1*K) a C1 E x) (C1*two) (E*unit s) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] positiveInput F (Syn.shift a) (Syn.shift C1) (Syn.shift C2) (Syn.shift E) (Syn.shift K) (Syn.shift x) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  have terms : Γ ⊢[PRAAx] termsDistance (sampleBody F) (sampleBody F) (C1*K) (fullData s K a C1 C2 E x)
      (sampleData s (C1*K) a C1 E x) two (unit s) := by
    refine .allI (.impI ?_)
    simpa only [Syn.shift,GaussianCompactRiemannSplit.subst_fullData,GaussianCompactRiemannName.subst_sampleData,PTm.subst_mul,
      GaussianCoefficientNameBounds.subst_unit,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using prefix_term_distance F (var 0)
        (Syn.shift s) (Syn.shift a) (Syn.shift C1) (Syn.shift C2) (Syn.shift E) (Syn.shift K) (Syn.shift x) hs.wk Prf.hyp0
  have raw := weighted_sum_distance _ _ C1 E K _ _ two (unit s) h.andE₂.andE₁ h.andE₂.andE₂.andE₁ (unit_positive s) terms
  exact distance_congr (.eqRefl _) (qmul_congr (weight_shared C1 E K h.andE₂.andE₂.andE₂.andE₁ h.andE₂.andE₁ h.andE₂.andE₂.andE₁).eqSymm (.eqRefl _))
    (.eqRefl _) (.eqRefl _) raw

theorem suffix_distance (F : PR 3) (s a C1 C2 E K x : PTm n) (h : Γ ⊢[PRAAx] positiveInput F a C1 C2 E K x) : Γ ⊢[PRAAx]
    distanceBounded (suffixPart F s K a C1 C2 E x) (quadrature F s (C2*K) (a+C1) C2 E x) (C2*two) (E*unit s) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] positiveInput F (Syn.shift a) (Syn.shift C1) (Syn.shift C2) (Syn.shift E) (Syn.shift K) (Syn.shift x) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  have terms : Γ ⊢[PRAAx] termsDistance (offB (sampleBody F)) (sampleBody F) (C2*K) (pairT (C1*K) (fullData s K a C1 C2 E x))
      (sampleData s (C2*K) (a+C1) C2 E x) two (unit s) := by
    refine .allI (.impI ?_)
    simpa only [Syn.shift,GaussianCompactRiemannSplit.subst_fullData,GaussianCompactRiemannName.subst_sampleData,subst_pairT,PTm.subst_mul,PTm.subst_add,
      GaussianCoefficientNameBounds.subst_unit,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using suffix_term_distance F (var 0)
        (Syn.shift s) (Syn.shift a) (Syn.shift C1) (Syn.shift C2) (Syn.shift E) (Syn.shift K) (Syn.shift x) hs.wk Prf.hyp0
  have raw := weighted_sum_distance _ _ C2 E K _ _ two (unit s) h.andE₂.andE₁ h.andE₂.andE₂.andE₁ (unit_positive s) terms
  exact distance_congr (.eqRefl _) (qmul_congr (weight_shared C2 E K h.andE₂.andE₂.andE₂.andE₂.andE₁ h.andE₂.andE₁ h.andE₂.andE₂.andE₁).eqSymm (.eqRefl _))
    (.eqRefl _) (.eqRefl _) raw

/-- Quantitative shared-step additivity of the actual stored compact
quadratures, from actual aligned-time sample comparison alone. -/
theorem positive_split (F : PR 3) (s a C1 C2 E K x : PTm n) (h : Γ ⊢[PRAAx] positiveInput F a C1 C2 E K x) : Γ ⊢[PRAAx]
    distanceBounded (quadrature F s ((C1+C2)*K) a (C1+C2) E x)
      (qadd (quadrature F s (C1*K) a C1 E x) (quadrature F s (C2*K) (a+C1) C2 E x)) (two*(C1+C2)) (E*unit s) := by
  have both := GaussianNameArithmetic.sum_distance _ _ _ _ _ _ _ (positive_product _ _ h.andE₂.andE₁ (unit_positive s))
    (prefix_distance F s a C1 C2 E K x h) (suffix_distance F s a C1 C2 E K x h)
  exact distance_congr (GaussianCompactRiemannSplit.literal_split F s K a C1 C2 E x h.andE₂.andE₂.andE₂.andE₁ h.andE₂.andE₁ h.andE₂.andE₂.andE₁).eqSymm
    (.eqRefl _) (by ipra_ring) (.eqRefl _) both



theorem quadrature_congr (F : PR 3) {p q M V a b C D E G x y : PTm n}
    (hp : Γ ⊢[PRAAx] p ≐ q) (hM : Γ ⊢[PRAAx] M ≐ V) (ha : Γ ⊢[PRAAx] a ≐ b)
    (hC : Γ ⊢[PRAAx] C ≐ D) (hE : Γ ⊢[PRAAx] E ≐ G) (hx : Γ ⊢[PRAAx] x ≐ y) :
    Γ ⊢[PRAAx] quadrature F p M a C E x ≐ quadrature F q V b D G y := by
  simpa only [GaussianCompactRiemannName.subst_quadrature,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.cons_val_succ,Matrix.head_cons,Matrix.tail_cons,
    (show (![p,M,a,C,E,x] : Fin 6 → PTm n) 5 = x from rfl),
    (show (![q,V,b,D,G,y] : Fin 6 → PTm n) 5 = y from rfl)] using
    Prf.eqCongr (Ax := PRAAx) (Γ := Γ) (quadrature F (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6)
      (σ := ![p,M,a,C,E,x]) (σ' := ![q,V,b,D,G,y])
        (fun i => by fin_cases i; exact hp; exact hM; exact ha; exact hC; exact hE; exact hx)

theorem quadrature_empty (F : PR 3) (s a C E x : PTm n) : Γ ⊢[PRAAx]
    quadrature F s zero a C E x ≐ qzero :=
  (qmul_congr (.eqRefl _) (GaussianRationalFiniteSum.sum_zero _ _)).eqTrans
    (GaussianRationalSyntheticDivision.qmul_zero_right _)

theorem quadrature_canonical (F : PR 3) (s M a C E x : PTm n) : Γ ⊢[PRAAx]
    canonical (quadrature F s M a C E x) := GaussianRationalHorner.qmul_canonical _ _

theorem zero_left_identity (F : PR 3) (s a C E K x : PTm n) : Γ ⊢[PRAAx]
    quadrature F s ((zero+C)*K) a (zero+C) E x ≐
      qadd (quadrature F s (zero*K) a zero E x) (quadrature F s (C*K) (a+zero) C E x) := by
  have left : Γ ⊢[PRAAx] quadrature F s (zero*K) a zero E x ≐ qzero :=
    (quadrature_congr (Γ := Γ) F (.eqRefl s) (zero_mul K) (.eqRefl a) (.eqRefl zero) (.eqRefl E) (.eqRefl x)).eqTrans
      (quadrature_empty F s a zero E x)
  have right := quadrature_congr (Γ := Γ) F (.eqRefl s) (.eqRefl (C*K)) (add_zero a) (.eqRefl C) (.eqRefl E) (.eqRefl x)
  have full := quadrature_congr (Γ := Γ) F (.eqRefl s) (congrMul (zero_add C) (.eqRefl K)) (.eqRefl a) (zero_add C) (.eqRefl E) (.eqRefl x)
  exact full.eqTrans ((qadd_congr left right).eqTrans
    (GaussianRationalSyntheticDivision.qzero_add _ (quadrature_canonical F s (C*K) a C E x))).eqSymm

theorem zero_right_identity (F : PR 3) (s a C E K x : PTm n) : Γ ⊢[PRAAx]
    quadrature F s ((C+zero)*K) a (C+zero) E x ≐
      qadd (quadrature F s (C*K) a C E x) (quadrature F s (zero*K) (a+C) zero E x) := by
  have right : Γ ⊢[PRAAx] quadrature F s (zero*K) (a+C) zero E x ≐ qzero :=
    (quadrature_congr (Γ := Γ) F (.eqRefl s) (zero_mul K) (.eqRefl (a+C)) (.eqRefl zero) (.eqRefl E) (.eqRefl x)).eqTrans
      (quadrature_empty F s (a+C) zero E x)
  have full := quadrature_congr (Γ := Γ) F (.eqRefl s) (congrMul (add_zero C) (.eqRefl K)) (.eqRefl a) (add_zero C) (.eqRefl E) (.eqRefl x)
  exact full.eqTrans ((qadd_congr (.eqRefl _) right).eqTrans
    (GaussianRationalLinearProduct.qadd_zero_right _ (quadrature_canonical F s (C*K) a C E x))).eqSymm

def splitLaw (F : PR 3) (s a C1 C2 E K x : PTm n) : Fm PTm n :=
  distanceBounded (quadrature F s ((C1+C2)*K) a (C1+C2) E x)
    (qadd (quadrature F s (C1*K) a C1 E x) (quadrature F s (C2*K) (a+C1) C2 E x))
    (two*(C1+C2)) (E*unit s)
@[simp] theorem subst_splitLaw {m : ℕ} (σ : Fin n → PTm m) (F : PR 3) (s a C1 C2 E K x : PTm n) :
    (splitLaw F s a C1 C2 E K x).subst σ = splitLaw F (Syn.subst σ s) (Syn.subst σ a)
      (Syn.subst σ C1) (Syn.subst σ C2) (Syn.subst σ E) (Syn.subst σ K) (Syn.subst σ x) := by simp [splitLaw]

theorem split_transport (F : PR 3) (s a E K x C1 C2 D1 D2 : PTm n)
    (h1 : Γ ⊢[PRAAx] C1 ≐ D1) (h2 : Γ ⊢[PRAAx] C2 ≐ D2)
    (h : Γ ⊢[PRAAx] splitLaw F s a D1 D2 E K x) : Γ ⊢[PRAAx] splitLaw F s a C1 C2 E K x := by
  have sum := congrAdd h1 h2
  have full := quadrature_congr (Γ := Γ) F (.eqRefl s) (congrMul sum (.eqRefl K)) (.eqRefl a) sum (.eqRefl E) (.eqRefl x)
  have left := quadrature_congr (Γ := Γ) F (.eqRefl s) (congrMul h1 (.eqRefl K)) (.eqRefl a) h1 (.eqRefl E) (.eqRefl x)
  have right := quadrature_congr (Γ := Γ) F (.eqRefl s) (congrMul h2 (.eqRefl K)) (congrAdd (.eqRefl a) h1) h2 (.eqRefl E) (.eqRefl x)
  exact distance_congr full.eqSymm (qadd_congr left right).eqSymm
    (congrMul (.eqRefl two) sum).eqSymm (.eqRefl _) h

theorem distance_of_identity (x y A D : PTm n) (hD : Γ ⊢[PRAAx] le one D) (h : Γ ⊢[PRAAx] x ≐ y) : Γ ⊢[PRAAx]
    distanceBounded x y A D := by
  have old := distance_congr h.eqSymm (.eqRefl y) (.eqRefl zero) (.eqRefl D)
    (GaussianRationalPowerDifference.distance_refl_zero y D hD)
  exact GaussianRationalDistanceOrder.distance_radius_mono _ _ zero D A D hD hD
    (le_congr (by ipra_ring) (.eqRefl _) (zero_le _)) old

def input (F : PR 3) (a C1 C2 E K x : PTm n) : Fm PTm n :=
  le one a ⋏ (le one E ⋏ (le one K ⋏ alignedSamples F a (C1+C2) E x))
@[simp] theorem subst_input {m : ℕ} (σ : Fin n → PTm m) (F : PR 3) (a C1 C2 E K x : PTm n) :
    (input F a C1 C2 E K x).subst σ = input F (Syn.subst σ a) (Syn.subst σ C1) (Syn.subst σ C2)
      (Syn.subst σ E) (Syn.subst σ K) (Syn.subst σ x) := by simp [input]

/-- Actual aligned-time splitting, allowing either width zero. -/
theorem shared_step_additivity (F : PR 3) (s a C1 C2 E K x : PTm n)
    (h : Γ ⊢[PRAAx] input F a C1 C2 E K x) : Γ ⊢[PRAAx] splitLaw F s a C1 C2 E K x := by
  have hd := GaussianRationalHorner.positive_product (Γ := Γ) _ _ h.andE₂.andE₁ (unit_positive s)
  refine .orE (zero_or_succ C1) ?_ ?_
  · exact split_transport F s a E K x C1 C2 zero C2 Prf.hyp0 (.eqRefl C2)
      (distance_of_identity _ _ _ _ hd.wk (zero_left_identity F s a C2 E K x))
  · refine .orE (zero_or_succ C2) ?_ ?_
    · exact split_transport F s a E K x C1 C2 C1 zero (.eqRefl C1) Prf.hyp0
        (distance_of_identity _ _ _ _ hd.wk.wk (zero_right_identity F s a C1 E K x))
    · have h1 : (C2 ≐ succ (pred C2)) :: (C1 ≐ succ (pred C1)) :: Γ ⊢[PRAAx] le one C1 :=
        le_congr (.eqRefl one) Prf.hyp1.eqSymm (zero_lt_succ (pred C1))
      have h2 : (C2 ≐ succ (pred C2)) :: (C1 ≐ succ (pred C1)) :: Γ ⊢[PRAAx] le one C2 :=
        le_congr (.eqRefl one) Prf.hyp0.eqSymm (zero_lt_succ (pred C2))
      exact positive_split F s a C1 C2 E K x
        (.andI h.andE₁.wk.wk (.andI h.andE₂.andE₁.wk.wk (.andI h.andE₂.andE₂.andE₁.wk.wk
          (.andI h1 (.andI h2 h.andE₂.andE₂.andE₂.wk.wk)))))


theorem actual_aligned_time_zero_safe_split_closed (F : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (input F (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      splitLaw F (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) :=
  closeUniv 7 (.impI (shared_step_additivity F _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianCompactAlignedSplit
