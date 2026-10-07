import OAI.Combinatorics.Progressions.Estimates.AllocatedEnormousProfiles
import OAI.Combinatorics.Progressions.Sampling.MixedGridBudget

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

noncomputable def coefficientRowAccuracy (n : ℕ) (η : ℝ) : ℝ := η/(4*(n+1))

theorem coefficientRowAccuracy_pos (n : ℕ) {η : ℝ} (hη : 0 < η) :
    0 < coefficientRowAccuracy n η := by unfold coefficientRowAccuracy; positivity

theorem coefficientRowAccuracy_sum (Q : Type*) [Fintype Q] {η : ℝ} (hη : 0 ≤ η) :
    2 * (∑ _q : Q, coefficientRowAccuracy (Fintype.card Q) η) ≤ η/2 := by
  simp only [coefficientRowAccuracy, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← mul_assoc, ← mul_div_assoc]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4*(Fintype.card Q+1))).mpr
  nlinarith

noncomputable def scalarTupleToleranceCutoff (α T : Type*)
    [Fintype α] [DecidableEq α] [Fintype T] (m : ℕ) (K ε : ℝ) : ℕ :=
  max 1 (max ((Fintype.card α+1)*m)
    (max ⌈2*scalarCubeGridBoundaryConstant α*m/volume.real (scalarCubeDomain α)⌉₊
      ⌈(Fintype.card T+1 : ℝ)*m*K/ε⌉₊))

theorem scalarTupleToleranceCutoff_mono_modulus (α T : Type*)
    [Fintype α] [DecidableEq α] [Fintype T] {m M : ℕ} {K ε : ℝ}
    (hm : m ≤ M) (hK : 0 ≤ K) (hε : 0 ≤ ε) :
    scalarTupleToleranceCutoff α T m K ε ≤ scalarTupleToleranceCutoff α T M K ε := by
  have hB := (scalarCubeGridBoundaryConstant_pos α).le
  have hV := (scalarCubeDomain_volumeReal_pos α).le
  unfold scalarTupleToleranceCutoff
  gcongr

theorem scalarTupleToleranceCutoff_le (α T : Type*)
    [Fintype α] [DecidableEq α] [Fintype T] {m L : ℕ} {K ε : ℝ}
    (hL : 0 < L) (hsize : (Fintype.card α+1)*m ≤ L)
    (hboundary : 2*scalarCubeGridBoundaryConstant α*m/volume.real (scalarCubeDomain α) ≤ L)
    (htest : (Fintype.card T+1 : ℝ)*m*K/ε ≤ L) :
    scalarTupleToleranceCutoff α T m K ε ≤ L := by
  unfold scalarTupleToleranceCutoff
  exact max_le hL (max_le hsize (max_le (Nat.ceil_le.mpr hboundary) (Nat.ceil_le.mpr htest)))

theorem scalarTupleToleranceCutoff_mul (α T : Type*)
    [Fintype α] [DecidableEq α] [Fintype T] {m : ℕ} (hm : 0 < m) (K ε : ℝ) :
    scalarTupleToleranceCutoff α T m K ε ≤ m*scalarTupleToleranceCutoff α T 1 K ε := by
  let L := scalarTupleToleranceCutoff α T 1 K ε
  have hpos : 0 < L := (le_max_left _ _ : 1 ≤ L)
  have hs : (Fintype.card α+1)*1 ≤ L := (le_max_left _ _).trans (le_max_right _ _)
  have hb : ⌈2*scalarCubeGridBoundaryConstant α*1/volume.real (scalarCubeDomain α)⌉₊ ≤ L := by
    simpa only [Nat.cast_one] using
      (max_le_iff.mp (max_le_iff.mp (max_le_iff.mp (le_refl L)).2).2).1
  have ht : ⌈(Fintype.card T+1 : ℝ)*1*K/ε⌉₊ ≤ L := by
    simpa only [Nat.cast_one] using
      (max_le_iff.mp (max_le_iff.mp (max_le_iff.mp (le_refl L)).2).2).2
  apply scalarTupleToleranceCutoff_le α T (Nat.mul_pos hm hpos)
  · simpa only [Nat.mul_one, Nat.one_mul, Nat.mul_comm] using Nat.mul_le_mul_left m hs
  · have hbr := (Nat.le_ceil _).trans (show (⌈2*scalarCubeGridBoundaryConstant α*1 /
        volume.real (scalarCubeDomain α)⌉₊ : ℝ) ≤ L by exact_mod_cast hb)
    calc
      _ = (2*scalarCubeGridBoundaryConstant α*1/volume.real (scalarCubeDomain α)) * m := by ring
      _ ≤ (L : ℝ) * m := mul_le_mul_of_nonneg_right hbr (Nat.cast_nonneg m)
      _ = (m*L : ℕ) := by push_cast; ring
  · have htr := (Nat.le_ceil _).trans (show (⌈(Fintype.card T+1 : ℝ)*1*K/ε⌉₊ : ℝ) ≤ L by exact_mod_cast ht)
    calc
      _ = ((Fintype.card T+1 : ℝ)*1*K/ε) * m := by ring
      _ ≤ (L : ℝ) * m := mul_le_mul_of_nonneg_right htr (Nat.cast_nonneg m)
      _ = (m*L : ℕ) := by push_cast; ring

theorem scalarTupleToleranceCutoff_spec (α T : Type*)
    [Fintype α] [DecidableEq α] [Fintype T] {m : ℕ} {K ε : ℝ}
    {L : T → ℕ} (hε : 0 < ε) (h : ∀ j, scalarTupleToleranceCutoff α T m K ε ≤ L j) :
    (∀ j, 0 < L j) ∧ (∀ j, (Fintype.card α+1)*m ≤ L j) ∧
    (∀ j, scalarCubeGridBoundaryConstant α*((m : ℝ)/L j) < volume.real (scalarCubeDomain α)) ∧
    K * (∑ j, (m : ℝ)/L j) ≤ ε := by
  have hl (j) := (max_le_iff.mp (h j)).1
  have hs (j) := (max_le_iff.mp (max_le_iff.mp (h j)).2).1
  have hr (j) := (max_le_iff.mp (max_le_iff.mp (max_le_iff.mp (h j)).2).2).1
  have ht (j) := (max_le_iff.mp (max_le_iff.mp (max_le_iff.mp (h j)).2).2).2
  have hL (j) : 0 < L j := hl j
  refine ⟨hL, hs, fun j => scalarCubeGrid_small_error_of_length α (hL j)
    ((Nat.le_ceil _).trans (by exact_mod_cast hr j)), ?_⟩
  have hn : (0 : ℝ) < Fintype.card T+1 := by positivity
  have hterm (j) : K*((m : ℝ)/L j) ≤ ε/(Fintype.card T+1) := by
    have hlen : (Fintype.card T+1 : ℝ)*m*K/ε ≤ L j :=
      (Nat.le_ceil _).trans (by exact_mod_cast ht j)
    have hh := (div_le_iff₀ hε).mp hlen
    have hp : (0 : ℝ) < L j := by exact_mod_cast hL j
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hp).mpr
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hn).mpr
    nlinarith
  calc
    _ = ∑ j, K*((m : ℝ)/L j) := Finset.mul_sum ..
    _ ≤ ∑ _j : T, ε/(Fintype.card T+1) := Finset.sum_le_sum (fun j _ => hterm j)
    _ ≤ ε := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hn).mpr
      nlinarith

theorem coefficientComparisonError_le (Q T : Type*) [Fintype Q] [Fintype T]
    {η G D K K₀ mesh : ℝ} {m : ℕ} {L : T → ℕ}
    (hη : 0 < η) (hG : 0 ≤ G) (hD : 0 ≤ D) (hK : K ≤ K₀)
    (hL : K₀*(∑ j, (m : ℝ)/L j) ≤ mixedCoefficientAccuracy G (η/2))
    (hmesh : mesh ≤ outputGridAccuracy G D (η/2)) :
    2 * (∑ _q : Q, coefficientRowAccuracy (Fintype.card Q) η) +
      G * (K*(∑ j, (m : ℝ)/L j) + D*mesh) ≤ η := by
  have hs : 0 ≤ ∑ j, (m : ℝ)/L j := Finset.sum_nonneg (fun _ _ => by positivity)
  have ht := (mul_le_mul_of_nonneg_right hK hs).trans hL
  have ho := outputGridError_le hG hD (half_pos hη).le ht hmesh
  have hr := coefficientRowAccuracy_sum Q hη.le
  linarith

noncomputable def coefficientToleranceScale {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) (b t ε L mesh : ℝ) (d : ℕ) : ℝ :=
  max 1 (max mesh⁻¹ (Real.exp
    (coefficientLogAllowance (Fintype.card I) (Fintype.card (UnselectedColumn s))
      (affineCoefficientCommonBudget (Fintype.card J) (Fintype.card (UnselectedColumn s)) b t) +
      (Fintype.card I : ℝ)*(Fintype.card J+2*b+3)) * (1+ε⁻¹) * L^(d*(Fintype.card I+1))))

theorem coefficientToleranceScale_spec {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) {C R b t ε L mesh H : ℝ} (d : ℕ)
    (hb : 0 ≤ b) (hC0 : 0 ≤ C) (hR0 : 0 ≤ R) (hε : 0 < ε) (hL : 0 ≤ L)
    (hC : C ≤ Real.exp b) (hR : R ≤ Real.exp b) (hmesh : 0 < mesh)
    (h : coefficientToleranceScale s b t ε L mesh d ≤ H) :
    0 < H ∧ 1 ≤ H ∧ 1/H ≤ mesh ∧ coefficientGridReplacementScale s C R b t ε L d ≤ H := by
  obtain ⟨h1, hrest⟩ := max_le_iff.mp h
  obtain ⟨hi, he⟩ := max_le_iff.mp hrest
  have hH : 0 < H := lt_of_lt_of_le zero_lt_one h1
  refine ⟨hH, h1, ?_, (coefficientGridReplacementScale_le s d hb hC0 hR0 hε hL hC hR).trans he⟩
  apply (div_le_iff₀ hH).mpr
  have hh := mul_le_mul_of_nonneg_right hi hmesh.le
  rw [inv_mul_cancel₀ hmesh.ne'] at hh
  linarith

end Erdos3

end

section

namespace Erdos3

noncomputable def maskedProductAccuracy (N : ℕ) (W C η : ℝ) : ℝ :=
  η / (2*((N : ℝ)+1)*(2+W*C)^N)

theorem maskedProductAccuracy_pos (N : ℕ) {W C η : ℝ}
    (hW : 0 ≤ W) (hC : 0 ≤ C) (hη : 0 < η) :
    0 < maskedProductAccuracy N W C η := by
  unfold maskedProductAccuracy
  positivity

theorem maskedProductAccuracy_le_one (N : ℕ) {W C η : ℝ}
    (hW : 0 ≤ W) (hC : 0 ≤ C) (hη : η ≤ 1) :
    maskedProductAccuracy N W C η ≤ 1 := by
  have hbase : (1 : ℝ) ≤ 2+W*C := by nlinarith
  have hpow : (1 : ℝ) ≤ (2+W*C)^N := one_le_pow₀ hbase
  unfold maskedProductAccuracy
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith [Nat.cast_nonneg (α := ℝ) N]

theorem maskedProductAccuracy_error {n N : ℕ} (hn : n ≤ N) {W C η : ℝ}
    (hW : 0 ≤ W) (hC : 0 ≤ C) (hη : 0 < η) (hη1 : η ≤ 1) :
    n * maskedProductAccuracy N W C η *
      (1+W*C+maskedProductAccuracy N W C η)^n ≤ η/2 := by
  have he := maskedProductAccuracy_pos N hW hC hη
  have he1 := maskedProductAccuracy_le_one N hW hC hη1
  have hbase : (1 : ℝ) ≤ 2+W*C := by nlinarith
  have hpow : (1+W*C+maskedProductAccuracy N W C η)^n ≤ (2+W*C)^N :=
    (pow_le_pow_left₀ (by positivity) (by linarith) n).trans (pow_le_pow_right₀ hbase hn)
  have hn' : (n : ℝ) ≤ (N : ℝ)+1 := by exact_mod_cast hn.trans (Nat.le_succ N)
  calc
    _ ≤ ((N : ℝ)+1)*maskedProductAccuracy N W C η*(2+W*C)^N :=
      mul_le_mul (mul_le_mul_of_nonneg_right hn' he.le) hpow (by positivity) (by positivity)
    _ = η/2 := by
      unfold maskedProductAccuracy
      have hb : 2+W*C ≠ 0 := ne_of_gt (by positivity)
      have hN : (N : ℝ)+1 ≠ 0 := ne_of_gt (by positivity)
      field_simp

theorem maskedProductAccuracy_inverse_exp (N : ℕ) {W C η w q E : ℝ}
    (hW : 0 ≤ W) (hC : 0 ≤ C) (hη : 0 < η) (hw : 0 ≤ w) (hq : 0 ≤ q)
    (hWw : W ≤ Real.exp w) (hCq : C ≤ Real.exp q) (hηE : η⁻¹ ≤ Real.exp E) :
    (maskedProductAccuracy N W C η)⁻¹ ≤ Real.exp (E+N+3+N*(2+w+q)) := by
  have hWC : W*C ≤ Real.exp (w+q) := by
    rw [Real.exp_add]
    exact mul_le_mul hWw hCq hC (Real.exp_pos _).le
  have h1 : (1 : ℝ) ≤ Real.exp (w+q) := Real.one_le_exp_iff.mpr (add_nonneg hw hq)
  have h3 : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hb : 2+W*C ≤ Real.exp (2+w+q) := by
    calc
      _ ≤ 3*Real.exp (w+q) := by linarith
      _ ≤ Real.exp 2 * Real.exp (w+q) := mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hf : 2*((N : ℝ)+1) ≤ Real.exp ((N : ℝ)+3) := by
    calc
      _ ≤ Real.exp 3 * Real.exp (N : ℝ) :=
        mul_le_mul (by linarith [Real.add_one_le_exp (3 : ℝ)]) (Real.add_one_le_exp (N : ℝ))
          (by positivity) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hp : (2+W*C)^N ≤ Real.exp (N*(2+w+q)) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by positivity) hb N
  rw [maskedProductAccuracy, inv_div, div_eq_mul_inv]
  calc
    _ ≤ Real.exp ((N : ℝ)+3) * Real.exp (N*(2+w+q)) * Real.exp E :=
      mul_le_mul (mul_le_mul hf hp (by positivity) (Real.exp_pos _).le)
        hηE (inv_nonneg.mpr hη.le) (by positivity)
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

theorem principalAxisTupleIndex_card_le {D : Type*} [Fintype D]
    (B : D → Type*) [∀ d, Fintype (B d)] (h : D → ℕ)
    (P : D → Prop) [DecidablePred P] :
    Fintype.card (PrincipalTupleIndex (fun d : {d // P d} => B d.val) (fun d => h d.val)) ≤
      Fintype.card (PrincipalTupleIndex B h) := by
  apply Fintype.card_le_of_injective
    (fun z : PrincipalTupleIndex (fun d : {d // P d} => B d.val) (fun d => h d.val) =>
      (⟨z.1.val, z.2⟩ : PrincipalTupleIndex B h))
  intro a b hab
  rcases a with ⟨⟨a, ha⟩, x⟩
  rcases b with ⟨⟨b, hb⟩, y⟩
  cases hab
  rfl

theorem scalarTupleToleranceCutoff_card_le (α T V : Type*)
    [Fintype α] [DecidableEq α] [Fintype T] [Fintype V]
    (hcard : Fintype.card T ≤ Fintype.card V) (m : ℕ) {K ε : ℝ}
    (hK : 0 ≤ K) (hε : 0 ≤ ε) :
    scalarTupleToleranceCutoff α T m K ε ≤ scalarTupleToleranceCutoff α V m K ε := by
  unfold scalarTupleToleranceCutoff
  gcongr

noncomputable def maskedJointTupleBudget (α : Type*) [Fintype α] [DecidableEq α]
    (N : ℕ) (W C : ℝ) : ℝ :=
  (W*C)^N * (2*scalarCubeGridBoundaryConstant α / volume.real (scalarCubeDomain α) + N*C)

theorem maskedJointTupleBudget_nonneg (α : Type*) [Fintype α] [DecidableEq α]
    (N : ℕ) {W C : ℝ} (hW : 0 ≤ W) (hC : 0 ≤ C) :
    0 ≤ maskedJointTupleBudget α N W C := by
  have hB := (scalarCubeGridBoundaryConstant_pos α).le
  have hV := (scalarCubeDomain_volumeReal_pos α).le
  unfold maskedJointTupleBudget
  positivity

theorem maskedJointTupleQuadrature_le {D α : Type*} [Fintype D] [Fintype α] [DecidableEq α]
    (B : D → Type*) [∀ d, Fintype (B d)] (h : D → ℕ)
    {n N : ℕ} (hn : n ≤ N) {W : ℝ} (hW : 1 ≤ W) (C : ℝ≥0) (hC : 1 ≤ C)
    (L : PrincipalTupleIndex B h → ℕ) (m : ℕ) :
    W^n * jointTupleQuadratureError (α := α) B h n C C L m ≤
      maskedJointTupleBudget α N W C * ∑ j, (m : ℝ)/L j := by
  have hW0 : 0 ≤ W := zero_le_one.trans hW
  have hC1 : (1 : ℝ) ≤ C := by exact_mod_cast hC
  have hWC : (1 : ℝ) ≤ W*C := by nlinarith [C.coe_nonneg]
  have hB := (scalarCubeGridBoundaryConstant_pos α).le
  have hV := (scalarCubeDomain_volumeReal_pos α).le
  have hfactor : 0 ≤ 2*scalarCubeGridBoundaryConstant α / volume.real (scalarCubeDomain α) + n*(C : ℝ) :=
    by positivity
  have hfac : 2*scalarCubeGridBoundaryConstant α / volume.real (scalarCubeDomain α) + n*(C : ℝ) ≤
      2*scalarCubeGridBoundaryConstant α / volume.real (scalarCubeDomain α) + N*(C : ℝ) := by
    gcongr
  have hsum : 0 ≤ ∑ j : PrincipalTupleIndex B h, (m : ℝ)/L j :=
    Finset.sum_nonneg (fun _ _ => by positivity)
  calc
    _ = ((W*(C : ℝ))^n *
        (2*scalarCubeGridBoundaryConstant α / volume.real (scalarCubeDomain α) + n*(C : ℝ))) *
          ∑ j : PrincipalTupleIndex B h, (m : ℝ)/L j := by
      simp only [jointTupleQuadratureError, mul_pow, div_eq_mul_inv]
      ring
    _ ≤ ((W*(C : ℝ))^N *
        (2*scalarCubeGridBoundaryConstant α / volume.real (scalarCubeDomain α) + N*(C : ℝ))) *
          ∑ j : PrincipalTupleIndex B h, (m : ℝ)/L j :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul (pow_le_pow_right₀ hWC hn) hfac hfactor (by positivity)) hsum
    _ = _ := rfl

end Erdos3

end

end OAI
