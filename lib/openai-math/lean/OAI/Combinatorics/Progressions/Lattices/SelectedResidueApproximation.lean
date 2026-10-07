import Mathlib.Data.ZMod.Basic
import OAI.Combinatorics.Progressions.Estimates.RowShiftTopSymbol
import OAI.Combinatorics.Progressions.Estimates.ShiftedSmoothProductAmplitudeTransfer
import OAI.Combinatorics.Progressions.Estimates.ShiftedSmoothSelectedMarginal
import OAI.Combinatorics.Progressions.Geometry.FiniteSupportApproximation

namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def integerRowShift {K I : Type*} {h : ℕ} {N : I → ℕ}
    (rows : Fin h → K → ℤ) (s : I → ℕ) (x : Fin h → ∀ j, Fin (N j)) : K × I → ℤ :=
  fun z => ∑ i, rows i z.1 * ((s z.2 : ℤ) * (x i z.2).val)

theorem integerRowShift_real {K I : Type*} {h : ℕ} {N : I → ℕ}
    (rows : Fin h → K → ℤ) (s : I → ℕ) (x : Fin h → ∀ j, Fin (N j))
    (b : K × I → ℤ) (k : K) (j : I) :
    (((b + integerRowShift rows s x) (k, j) : ℤ) : ℝ) =
      rowShiftedTuple (fun k j => (b (k, j) : ℝ)) rows
        (fun (y : ∀ j, Fin (N j)) j => (s j : ℝ) * ((y j).val : ℝ)) x k j := by
  simp [integerRowShift, rowShiftedTuple, Finset.sum_apply, zsmul_eq_mul]

theorem integerRowShift_bound {K I : Type*} {h : ℕ} {N : I → ℕ}
    (rows : Fin h → K → ℤ) (s : I → ℕ) (x : Fin h → ∀ j, Fin (N j))
    {C : ℝ} (hC : 0 ≤ C) (hrows : ∀ i k, |(rows i k : ℝ)| ≤ C) (z : K × I) :
    |(integerRowShift rows s x z : ℝ)| ≤ (h : ℝ) * C * ((s z.2 : ℝ) * (N z.2 : ℝ)) := by
  simp only [integerRowShift, Int.cast_sum, Int.cast_mul, Int.cast_natCast]
  calc
    |∑ i, (rows i z.1 : ℝ) * ((s z.2 : ℝ) * ((x i z.2).val : ℝ))| ≤
        ∑ i, |(rows i z.1 : ℝ) * ((s z.2 : ℝ) * ((x i z.2).val : ℝ))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin h, C * ((s z.2 : ℝ) * (N z.2 : ℝ)) := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg (s z.2))
        (Nat.cast_nonneg (x i z.2).val) : (0 : ℝ) ≤ (s z.2 : ℝ) * ((x i z.2).val : ℝ))]
      have hx : ((x i z.2).val : ℝ) ≤ (N z.2 : ℝ) := by exact_mod_cast (x i z.2).isLt.le
      exact mul_le_mul (hrows i z.1)
        (mul_le_mul_of_nonneg_left hx (Nat.cast_nonneg _)) (by positivity) hC
    _ = _ := by simp; ring

theorem integerRowShift_normalized_bound {K I : Type*} [Fintype K] [Fintype I]
    {h : ℕ} {N : I → ℕ} (rows : Fin h → K → ℤ) (s : I → ℕ)
    (x : Fin h → ∀ j, Fin (N j)) (S : K × I → ℝ) (hS : ∀ z, 0 < S z)
    {C ε : ℝ} (hC : 0 ≤ C) (hrows : ∀ i k, |(rows i k : ℝ)| ≤ C) (hε : 0 ≤ ε)
    (hscale : ∀ z, (h : ℝ) * C * ((s z.2 : ℝ) * (N z.2 : ℝ)) ≤ ε * S z) :
    ‖rectangularLatticePoint 0 S (integerRowShift rows s x)‖ ≤ ε := by
  rw [rectangularLatticePoint_zero_origin]
  apply (pi_norm_le_iff_of_nonneg hε).mpr
  intro z
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (hS z)]
  apply (div_le_iff₀ (hS z)).mpr
  exact (integerRowShift_bound rows s x hC hrows z).trans (hscale z)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def residueLatticeArray {K I : Type*} (residue : K × I → ℤ) (modulus : I → ℕ)
    (x : K × I → ℤ) : K × I → ℤ :=
  fun z => residue z + (modulus z.2 : ℤ) * x z

noncomputable def residueProfileCenter {K I : Type*}
    (residue : K × I → ℤ) (modulus : I → ℕ) : K × I → ℝ :=
  fun z => -(residue z : ℝ) / modulus z.2

noncomputable def residueProfileWidth {K I : Type*}
    (modulus : I → ℕ) (V : K × I → ℝ) : K × I → ℝ := fun z => V z / modulus z.2

theorem residueProfileWidth_pos {K I : Type*} (modulus : I → ℕ) (V : K × I → ℝ)
    (hmodulus : ∀ j, 0 < modulus j) (hV : ∀ z, 0 < V z) (z : K × I) :
    0 < residueProfileWidth modulus V z :=
  div_pos (hV z) (by exact_mod_cast hmodulus z.2)

theorem residueLatticeArray_rowShift {K I : Type*} {h : ℕ} {N : I → ℕ}
    (residue : K × I → ℤ) (modulus : I → ℕ) (rows : Fin h → K → ℤ)
    (u : Fin h → ∀ j, Fin (N j)) (x : K × I → ℤ) (k : K) (j : I) :
    ((residueLatticeArray residue modulus (x + integerRowShift rows (fun _ => 1) u) (k, j) : ℤ) : ℝ) =
      rowShiftedTuple (fun k j => (residueLatticeArray residue modulus x (k, j) : ℝ)) rows
        (fun (y : ∀ j, Fin (N j)) j => (modulus j : ℝ) * ((y j).val : ℝ)) u k j := by
  simp only [residueLatticeArray, integerRowShift, rowShiftedTuple, Pi.add_apply,
    Int.cast_add, Int.cast_mul, Int.cast_sum, Int.cast_natCast, Nat.cast_one, one_mul,
    Finset.sum_apply, zsmul_eq_mul]
  rw [mul_add, Finset.mul_sum, ← add_assoc]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.mul_apply, Pi.intCast_apply]
  ring

theorem residueRowShift_normalized_bound {K I : Type*} [Fintype K] [Fintype I]
    {h : ℕ} {N : I → ℕ} (rows : Fin h → K → ℤ) (modulus : I → ℕ)
    (hmodulus : ∀ j, 0 < modulus j) (u : Fin h → ∀ j, Fin (N j))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    {C r : ℝ} (hC : 0 ≤ C) (hrows : ∀ i k, |(rows i k : ℝ)| ≤ C) (hr : 0 ≤ r)
    (hmove : ∀ z, (h : ℝ) * C * ((modulus z.2 : ℝ) * (N z.2 : ℝ)) ≤ r * V z) :
    ‖rectangularLatticePoint 0 (residueProfileWidth modulus V)
      (integerRowShift rows (fun _ => 1) u)‖ ≤ r := by
  apply integerRowShift_normalized_bound rows (fun _ => 1) u _
    (residueProfileWidth_pos modulus V hmodulus hV) hC hrows hr
  intro z
  have hm : (0 : ℝ) < modulus z.2 := by exact_mod_cast hmodulus z.2
  simp only [Nat.cast_one, one_mul, residueProfileWidth]
  rw [← mul_div_assoc, le_div_iff₀ hm]
  calc
    (h : ℝ) * C * (N z.2 : ℝ) * (modulus z.2 : ℝ) =
      (h : ℝ) * C * ((modulus z.2 : ℝ) * (N z.2 : ℝ)) := by ring
    _ ≤ r * V z := hmove z

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem residueProfile_point {K I : Type*} [Fintype K] [Fintype I]
    (residue : K × I → ℤ) (modulus : I → ℕ) (hmodulus : ∀ j, 0 < modulus j)
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z) (x : K × I → ℤ) :
    rectangularLatticePoint (residueProfileCenter residue modulus) (residueProfileWidth modulus V) x =
      fun z => (residueLatticeArray residue modulus x z : ℝ) / V z := by
  funext z
  have hm : (0 : ℝ) < modulus z.2 := by exact_mod_cast hmodulus z.2
  simp only [rectangularLatticePoint, residueProfileCenter, residueProfileWidth,
    residueLatticeArray, Int.cast_add, Int.cast_mul, Int.cast_natCast]
  field_simp [hm.ne', (hV z).ne']
  ring

noncomputable def residueSmoothIndexPMF {K I : Type*} [Fintype K] [Fintype I]
    (residue : K × I → ℤ) (modulus : I → ℕ) (hmodulus : ∀ j, 0 < modulus j)
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue modulus)
      (residueProfileWidth modulus V)) : PMF (K × I → ℤ) :=
  shiftedSmoothProductPMF (residueProfileCenter residue modulus) (residueProfileWidth modulus V)
    (residueProfileWidth_pos modulus V hmodulus hV) hZ

theorem residueSmoothIndexPMF_toReal {K I : Type*} [Fintype K] [Fintype I]
    (residue : K × I → ℤ) (modulus : I → ℕ) (hmodulus : ∀ j, 0 < modulus j)
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue modulus)
      (residueProfileWidth modulus V)) (x : K × I → ℤ) :
    (residueSmoothIndexPMF residue modulus hmodulus V hV hZ x).toReal =
      smoothProductProfile (K × I) (fun z => (residueLatticeArray residue modulus x z : ℝ) / V z) /
        ∑' y, smoothProductProfile (K × I)
          (fun z => (residueLatticeArray residue modulus y z : ℝ) / V z) := by
  simp only [residueSmoothIndexPMF, shiftedSmoothProductPMF_toReal, shiftedSmoothProductMass,
    rectangularWeight, residueProfile_point residue modulus hmodulus V hV]

end Erdos3

end

section

namespace Erdos3

theorem residueLatticeArray_injective {K I : Type*}
    (residue : K × I → ℤ) (modulus : I → ℕ) (hmodulus : ∀ j, 0 < modulus j) :
    Function.Injective (residueLatticeArray residue modulus) := by
  intro x y he
  funext z
  have hm : (modulus z.2 : ℤ) ≠ 0 := by exact_mod_cast (hmodulus z.2).ne'
  exact mul_left_cancel₀ hm (add_left_cancel (congrFun he z))

theorem residueLatticeArray_range {K I : Type*}
    (residue : K × I → ℤ) (modulus : I → ℕ) (y : K × I → ℤ) :
    y ∈ Set.range (residueLatticeArray residue modulus) ↔
      ∀ z, (modulus z.2 : ℤ) ∣ y z - residue z := by
  constructor
  · rintro ⟨x, rfl⟩ z
    exact ⟨x z, by simp only [residueLatticeArray, add_sub_cancel_left]⟩
  · intro h
    classical
    refine ⟨fun z => (h z).choose, ?_⟩
    funext z
    have hz := (h z).choose_spec
    change residue z + (modulus z.2 : ℤ) * (h z).choose = y z
    omega

noncomputable def residueSmoothPMF {K I : Type*} [Fintype K] [Fintype I]
    (residue : K × I → ℤ) (modulus : I → ℕ) (hmodulus : ∀ j, 0 < modulus j)
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue modulus)
      (residueProfileWidth modulus V)) : PMF (K × I → ℤ) :=
  (residueSmoothIndexPMF residue modulus hmodulus V hV hZ).map
    (residueLatticeArray residue modulus)

theorem residueSmoothPMF_at {K I : Type*} [Fintype K] [Fintype I]
    (residue : K × I → ℤ) (modulus : I → ℕ) (hmodulus : ∀ j, 0 < modulus j)
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue modulus)
      (residueProfileWidth modulus V)) (x : K × I → ℤ) :
    (residueSmoothPMF residue modulus hmodulus V hV hZ
        (residueLatticeArray residue modulus x)).toReal =
      smoothProductProfile (K × I) (fun z => (residueLatticeArray residue modulus x z : ℝ) / V z) /
        ∑' y, smoothProductProfile (K × I)
          (fun z => (residueLatticeArray residue modulus y z : ℝ) / V z) := by
  rw [residueSmoothPMF, pmf_map_injective_at _ _ (residueLatticeArray_injective residue modulus hmodulus)]
  exact residueSmoothIndexPMF_toReal residue modulus hmodulus V hV hZ x

theorem residueSmoothPMF_zero_off {K I : Type*} [Fintype K] [Fintype I]
    (residue : K × I → ℤ) (modulus : I → ℕ) (hmodulus : ∀ j, 0 < modulus j)
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue modulus)
      (residueProfileWidth modulus V)) (y : K × I → ℤ)
    (hy : ¬∀ z, (modulus z.2 : ℤ) ∣ y z - residue z) :
    residueSmoothPMF residue modulus hmodulus V hV hZ y = 0 := by
  exact pmf_map_zero_off_range _ _ y (by rwa [residueLatticeArray_range])

theorem residueSmoothPMF_expectation {K I : Type*} [Fintype K] [Fintype I]
    (residue : K × I → ℤ) (modulus : I → ℕ) (hmodulus : ∀ j, 0 < modulus j)
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue modulus)
      (residueProfileWidth modulus V)) (φ : (K × I → ℤ) → ℂ) :
    (∑' y, ((residueSmoothPMF residue modulus hmodulus V hV hZ y).toReal : ℂ) * φ y) =
      ∑' x, ((residueSmoothIndexPMF residue modulus hmodulus V hV hZ x).toReal : ℂ) *
        φ (residueLatticeArray residue modulus x) :=
  pmf_map_injective_expectation _ _ (residueLatticeArray_injective residue modulus hmodulus) φ

end Erdos3

end

section

namespace Erdos3

noncomputable def residueSmoothScalarPMFs {K I : Type*} [Fintype K] [Fintype I]
    (residue : K × I → ℤ) (modulus : I → ℕ) (hmodulus : ∀ j, 0 < modulus j)
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue modulus)
      (residueProfileWidth modulus V)) : K × I → PMF ℤ :=
  fun z => shiftedSmoothCoefficientPMF
    (residueProfileCenter residue modulus z) (residueProfileWidth modulus V z)
    (residueProfileWidth_pos modulus V hmodulus hV z)
    (shiftedSmoothProductMass_coordinate_pos
      (residueProfileCenter residue modulus) (residueProfileWidth modulus V)
      (residueProfileWidth_pos modulus V hmodulus hV) hZ z)

theorem residueSmoothIndexPMF_eq_independent {K I : Type*} [Fintype K] [Fintype I]
    (residue : K × I → ℤ) (modulus : I → ℕ) (hmodulus : ∀ j, 0 < modulus j)
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue modulus)
      (residueProfileWidth modulus V)) :
    residueSmoothIndexPMF residue modulus hmodulus V hV hZ =
      independentProductPMF (residueSmoothScalarPMFs residue modulus hmodulus V hV hZ) :=
  shiftedSmoothProductPMF_eq_independent
    (residueProfileCenter residue modulus) (residueProfileWidth modulus V)
    (residueProfileWidth_pos modulus V hmodulus hV) hZ

theorem residueSmoothIndexPMF_selected_marginal {A K I : Type*}
    [Fintype A] [Fintype K] [Fintype I]
    (residue : K × I → ℤ) (modulus : I → ℕ) (hmodulus : ∀ j, 0 < modulus j)
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue modulus)
      (residueProfileWidth modulus V)) (e : A ↪ K × I) :
    (residueSmoothIndexPMF residue modulus hmodulus V hV hZ).map
      (fun x a => x (e a)) =
      independentProductPMF
        (fun a => residueSmoothScalarPMFs residue modulus hmodulus V hV hZ (e a)) := by
  rw [residueSmoothIndexPMF_eq_independent]
  exact independentProductPMF_marginal _ e e.injective

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem residue_smooth_row_shift_transfer {K I : Type*}
    [Fintype K] [Fintype I] [DecidableEq I] {h : ℕ}
    (N modulus : I → ℕ) (hN : ∀ j, 0 < N j) (hmodulus : ∀ j, 0 < modulus j)
    (rows : Fin h → K → ℤ) (residue : K × I → ℤ)
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue modulus)
      (residueProfileWidth modulus V))
    (hV1 : ∀ z, 1 ≤ residueProfileWidth modulus V z)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmesh : ∀ z, 1 / residueProfileWidth modulus V z ≤ δ)
    (hsmall : (4 : ℝ) ^ Fintype.card (K × I) *
      ((Fintype.card (K × I) : ℝ) * probabilityProfileLipschitz) * δ ≤ 1 / 2)
    {C r B : ℝ} (hC : 0 ≤ C) (hrows : ∀ i k, |(rows i k : ℝ)| ≤ C) (hr : 0 ≤ r)
    (hmove : ∀ z, (h : ℝ) * C * ((modulus z.2 : ℝ) * (N z.2 : ℝ)) ≤ r * V z)
    (Φ : (K → I → ℝ) → ℂ) (hΦ : ∀ b, ‖Φ b‖ ≤ 1)
    (hlocal : ∀ b : K → I → ℝ,
      ‖𝔼 x : Fin h → ∀ j, Fin (N j),
        Φ (rowShiftedTuple b rows
          (fun (y : ∀ j, Fin (N j)) j => (modulus j : ℝ) * ((y j).val : ℝ)) x)‖ ≤ B) :
    ‖∑' x, ((residueSmoothIndexPMF residue modulus hmodulus V hV hZ x).toReal : ℂ) *
      Φ (fun k j => (residueLatticeArray residue modulus x (k, j) : ℝ))‖ ≤
      4 * (3 : ℝ) ^ Fintype.card (K × I) *
        ((Fintype.card (K × I) : ℝ) * probabilityProfileLipschitz) * r + B := by
  let : ∀ j, Nonempty (Fin (N j)) := fun j => ⟨⟨0, hN j⟩⟩
  apply shiftedSmoothProductPMF_shift_transfer (residueProfileCenter residue modulus)
    (residueProfileWidth modulus V) (residueProfileWidth_pos modulus V hmodulus hV)
    hZ hV1 hδ hδ1 hmesh hsmall (integerRowShift (N := N) rows (fun _ => 1))
    (fun x => residueRowShift_normalized_bound rows modulus hmodulus x V hV hC hrows hr hmove)
    (fun x => Φ (fun k j => (residueLatticeArray residue modulus x (k, j) : ℝ))) (fun _ => hΦ _)
  intro x
  simpa only [residueLatticeArray_rowShift] using
    hlocal (fun k j => (residueLatticeArray residue modulus x (k, j) : ℝ))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical NNReal

theorem residue_smooth_row_shift_transfer_lipschitz_amplitude {K I : Type*}
    [Fintype K] [Fintype I] [DecidableEq I] {h : ℕ}
    (N modulus : I → ℕ) (hN : ∀ j, 0 < N j) (hmodulus : ∀ j, 0 < modulus j)
    (rows : Fin h → K → ℤ) (residue : K × I → ℤ)
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue modulus)
      (residueProfileWidth modulus V))
    (hV1 : ∀ z, 1 ≤ residueProfileWidth modulus V z)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmesh : ∀ z, 1 / residueProfileWidth modulus V z ≤ δ)
    (hsmall : (4 : ℝ) ^ Fintype.card (K × I) *
      ((Fintype.card (K × I) : ℝ) * probabilityProfileLipschitz) * δ ≤ 1 / 2)
    {C r B : ℝ} (hC : 0 ≤ C) (hrows : ∀ i k, |(rows i k : ℝ)| ≤ C) (hr : 0 ≤ r)
    (hmove : ∀ z, (h : ℝ) * C * ((modulus z.2 : ℝ) * (N z.2 : ℝ)) ≤ r * V z)
    (Φ : (K → I → ℝ) → ℂ) (hΦ : ∀ b, ‖Φ b‖ ≤ 1)
    (hlocal : ∀ b : K → I → ℝ,
      ‖𝔼 x : Fin h → ∀ j, Fin (N j),
        Φ (rowShiftedTuple b rows
          (fun (y : ∀ j, Fin (N j)) j => (modulus j : ℝ) * ((y j).val : ℝ)) x)‖ ≤ B)
    (F : (K × I → ℝ) → ℂ) (hF : ∀ x, ‖F x‖ ≤ 1)
    {Lip : ℝ≥0} (hLip : LipschitzWith Lip F) :
    ‖∑' x, ((residueSmoothIndexPMF residue modulus hmodulus V hV hZ x).toReal : ℂ) *
      (F (fun z => (residueLatticeArray residue modulus x z : ℝ) / V z) *
        Φ (fun k j => (residueLatticeArray residue modulus x (k, j) : ℝ)))‖ ≤
      4 * (3 : ℝ) ^ Fintype.card (K × I) *
        ((Fintype.card (K × I) : ℝ) * probabilityProfileLipschitz) * r + (Lip : ℝ) * r + B := by
  let : ∀ j, Nonempty (Fin (N j)) := fun j => ⟨⟨0, hN j⟩⟩
  have ht := shiftedSmoothProductPMF_shift_transfer_lipschitz_amplitude
    (residueProfileCenter residue modulus)
    (residueProfileWidth modulus V) (residueProfileWidth_pos modulus V hmodulus hV)
    hZ hV1 hδ hδ1 hmesh hsmall (integerRowShift (N := N) rows (fun _ => 1))
    (fun x => residueRowShift_normalized_bound rows modulus hmodulus x V hV hC hrows hr hmove)
    (fun x => Φ (fun k j => (residueLatticeArray residue modulus x (k, j) : ℝ)))
    (fun _ => hΦ _) (fun x => by
      simpa only [residueLatticeArray_rowShift] using
        hlocal (fun k j => (residueLatticeArray residue modulus x (k, j) : ℝ))) F hF hLip
  simpa only [residueSmoothIndexPMF, residueProfile_point residue modulus hmodulus V hV]
    using ht

end Erdos3

end

section

namespace Erdos3

noncomputable def residueSmoothWeight {K I : Type*} [Fintype K] [Fintype I]
    (residue : K × I → ℤ) (modulus : I → ℕ) (V : K × I → ℝ) (y : K × I → ℤ) : ℝ := by
  classical
  exact if ∀ z, (modulus z.2 : ℤ) ∣ y z - residue z then
    smoothProductProfile (K × I) (fun z => (y z : ℝ) / V z) else 0

theorem residueSmoothWeight_at {K I : Type*} [Fintype K] [Fintype I]
    (residue : K × I → ℤ) (modulus : I → ℕ) (V : K × I → ℝ) (x : K × I → ℤ) :
    residueSmoothWeight residue modulus V (residueLatticeArray residue modulus x) =
      smoothProductProfile (K × I) (fun z => (residueLatticeArray residue modulus x z : ℝ) / V z) := by
  have hc := (residueLatticeArray_range residue modulus _).mp ⟨x, rfl⟩
  simp [residueSmoothWeight, hc]

theorem residueSmoothWeight_mass {K I : Type*} [Fintype K] [Fintype I]
    (residue : K × I → ℤ) (modulus : I → ℕ) (hmodulus : ∀ j, 0 < modulus j)
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z) :
    shiftedSmoothProductMass (residueProfileCenter residue modulus) (residueProfileWidth modulus V) =
      ∑' y, residueSmoothWeight residue modulus V y := by
  have hs : Function.support (residueSmoothWeight residue modulus V) ⊆
      Set.range (residueLatticeArray residue modulus) := by
    intro y hy
    apply (residueLatticeArray_range residue modulus y).mpr
    by_contra hn
    exact hy (by simp only [residueSmoothWeight, hn, ite_false])
  have he := (residueLatticeArray_injective residue modulus hmodulus).tsum_eq hs
  simpa only [shiftedSmoothProductMass, rectangularWeight,
    residueProfile_point residue modulus hmodulus V hV, residueSmoothWeight_at] using he

theorem residueSmoothPMF_conditional_weight {K I : Type*} [Fintype K] [Fintype I]
    (residue : K × I → ℤ) (modulus : I → ℕ) (hmodulus : ∀ j, 0 < modulus j)
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue modulus)
      (residueProfileWidth modulus V)) (y : K × I → ℤ) :
    (residueSmoothPMF residue modulus hmodulus V hV hZ y).toReal =
      residueSmoothWeight residue modulus V y / ∑' z, residueSmoothWeight residue modulus V z := by
  classical
  by_cases hc : ∀ z, (modulus z.2 : ℤ) ∣ y z - residue z
  · obtain ⟨x, rfl⟩ := (residueLatticeArray_range residue modulus y).mpr hc
    rw [residueSmoothWeight_at, ← residueSmoothWeight_mass residue modulus hmodulus V hV]
    have he := residueSmoothPMF_at residue modulus hmodulus V hV hZ x
    simpa only [shiftedSmoothProductMass, rectangularWeight,
      residueProfile_point residue modulus hmodulus V hV] using he
  · simp only [residueSmoothPMF_zero_off residue modulus hmodulus V hV hZ y hc,
      ENNReal.toReal_zero, residueSmoothWeight, hc, ite_false, zero_div]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem rowShiftedTuple_add_base {h : ℕ} {K X V : Type*} [AddCommGroup V]
    (origin base : K → V) (rows : Fin h → K → ℤ) (shift : X → V)
    (x : Fin h → X) :
    rowShiftedTuple (origin + base) rows shift x =
      origin + rowShiftedTuple base rows shift x := by
  funext k
  simp only [rowShiftedTuple, Pi.add_apply, add_assoc]

theorem anchored_residue_smooth_row_shift_transfer {K I : Type*}
    [Fintype K] [Fintype I] [DecidableEq I] {h : ℕ}
    (origin : K → I → ℝ)
    (N modulus : I → ℕ) (hN : ∀ j, 0 < N j) (hmodulus : ∀ j, 0 < modulus j)
    (rows : Fin h → K → ℤ) (residue : K × I → ℤ)
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue modulus)
      (residueProfileWidth modulus V))
    (hV1 : ∀ z, 1 ≤ residueProfileWidth modulus V z)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmesh : ∀ z, 1 / residueProfileWidth modulus V z ≤ δ)
    (hsmall : (4 : ℝ) ^ Fintype.card (K × I) *
      ((Fintype.card (K × I) : ℝ) * probabilityProfileLipschitz) * δ ≤ 1 / 2)
    {C r B : ℝ} (hC : 0 ≤ C) (hrows : ∀ i k, |(rows i k : ℝ)| ≤ C) (hr : 0 ≤ r)
    (hmove : ∀ z, (h : ℝ) * C * ((modulus z.2 : ℝ) * (N z.2 : ℝ)) ≤ r * V z)
    (Φ : (K → I → ℝ) → ℂ) (hΦ : ∀ b, ‖Φ b‖ ≤ 1)
    (hlocal : ∀ b : K → I → ℝ,
      ‖𝔼 x : Fin h → ∀ j, Fin (N j),
        Φ (rowShiftedTuple b rows
          (fun (y : ∀ j, Fin (N j)) j => (modulus j : ℝ) * ((y j).val : ℝ)) x)‖ ≤ B) :
    ‖∑' x, ((residueSmoothIndexPMF residue modulus hmodulus V hV hZ x).toReal : ℂ) *
      Φ (origin + fun k j => (residueLatticeArray residue modulus x (k, j) : ℝ))‖ ≤
      4 * (3 : ℝ) ^ Fintype.card (K × I) *
        ((Fintype.card (K × I) : ℝ) * probabilityProfileLipschitz) * r + B := by
  apply residue_smooth_row_shift_transfer N modulus hN hmodulus rows residue V hV hZ hV1
    hδ hδ1 hmesh hsmall hC hrows hr hmove (fun b => Φ (origin + b)) (fun b => hΦ _)
  intro base
  simpa only [rowShiftedTuple_add_base] using hlocal (origin + base)

end Erdos3

end

section

namespace Erdos3

abbrev ColumnResiduePattern (K I : Type*) (modulus : I → ℕ) :=
  ∀ z : K × I, ZMod (modulus z.2)

def columnResiduePattern {K I : Type*} (modulus : I → ℕ) (x : K × I → ℤ) :
    ColumnResiduePattern K I modulus := fun z => x z

noncomputable def columnResidueRepresentative {K I : Type*} (modulus : I → ℕ)
    (r : ColumnResiduePattern K I modulus) : K × I → ℤ :=
  fun z => (ZMod.intCast_surjective (r z)).choose

theorem columnResidueRepresentative_cast {K I : Type*} (modulus : I → ℕ)
    (r : ColumnResiduePattern K I modulus) (z : K × I) :
    (columnResidueRepresentative modulus r z : ZMod (modulus z.2)) = r z :=
  (ZMod.intCast_surjective (r z)).choose_spec

theorem columnResiduePattern_eq_iff {K I : Type*} (modulus : I → ℕ)
    (r : ColumnResiduePattern K I modulus) (x : K × I → ℤ) :
    columnResiduePattern modulus x = r ↔
      ∀ z, (modulus z.2 : ℤ) ∣ x z - columnResidueRepresentative modulus r z := by
  constructor
  · intro he z
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    rw [Int.cast_sub, columnResidueRepresentative_cast]
    exact sub_eq_zero.mpr (congrFun he z)
  · intro h
    funext z
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (h z)
    rw [Int.cast_sub, columnResidueRepresentative_cast, sub_eq_zero] at hz
    exact hz

theorem residueSmoothWeight_eq_pattern {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (r : ColumnResiduePattern K I modulus)
    (V : K × I → ℝ) (x : K × I → ℤ) :
    residueSmoothWeight (columnResidueRepresentative modulus r) modulus V x =
      if columnResiduePattern modulus x = r then
        smoothProductProfile (K × I) (fun z => (x z : ℝ) / V z) else 0 := by
  classical
  simp only [residueSmoothWeight, ← columnResiduePattern_eq_iff]

end Erdos3

end

section

namespace Erdos3

theorem integerArrayFrame_add {K I : Type*} (anchor z : K × I → ℤ) :
    (fun k i => ((anchor + z) (k,i) : ℝ)) =
      (fun k i => (anchor (k,i) : ℝ)) + (fun k i => (z (k,i) : ℝ)) := by
  funext k i
  simp only [Pi.add_apply, Int.cast_add]

end Erdos3

end

section

namespace Erdos3

theorem residueSmoothWeight_congr {K X : Type*} [Fintype K] [Fintype X]
    (r s : K × X → ℤ) (modulus : X → ℕ) (V : K × X → ℝ)
    (hrs : ∀ z, (modulus z.2 : ℤ) ∣ s z - r z) :
    residueSmoothWeight r modulus V = residueSmoothWeight s modulus V := by
  funext y
  have he : (∀ z, (modulus z.2 : ℤ) ∣ y z - r z) ↔
      ∀ z, (modulus z.2 : ℤ) ∣ y z - s z := by
    constructor
    · intro h z
      have hid : y z - s z = (y z - r z) - (s z - r z) := by ring
      rw [hid]
      exact dvd_sub (h z) (hrs z)
    · intro h z
      have hid : y z - r z = (y z - s z) + (s z - r z) := by ring
      rw [hid]
      exact dvd_add (h z) (hrs z)
  simp only [residueSmoothWeight, he]

theorem residueSmoothMass_congr {K X : Type*} [Fintype K] [Fintype X]
    (r s : K × X → ℤ) (modulus : X → ℕ) (hmodulus : ∀ x, 0 < modulus x)
    (V : K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hrs : ∀ z, (modulus z.2 : ℤ) ∣ s z - r z) :
    shiftedSmoothProductMass (residueProfileCenter r modulus) (residueProfileWidth modulus V) =
      shiftedSmoothProductMass (residueProfileCenter s modulus) (residueProfileWidth modulus V) := by
  rw [residueSmoothWeight_mass r modulus hmodulus V hV,
    residueSmoothWeight_mass s modulus hmodulus V hV, residueSmoothWeight_congr r s modulus V hrs]

theorem residueSmoothPMF_congr {K X : Type*} [Fintype K] [Fintype X]
    (r s : K × X → ℤ) (modulus : X → ℕ) (hmodulus : ∀ x, 0 < modulus x)
    (V : K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hrs : ∀ z, (modulus z.2 : ℤ) ∣ s z - r z)
    (hr : 0 < shiftedSmoothProductMass (residueProfileCenter r modulus) (residueProfileWidth modulus V))
    (hs : 0 < shiftedSmoothProductMass (residueProfileCenter s modulus) (residueProfileWidth modulus V)) :
    residueSmoothPMF r modulus hmodulus V hV hr = residueSmoothPMF s modulus hmodulus V hV hs := by
  ext y
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  simp only [residueSmoothPMF_conditional_weight, residueSmoothWeight_congr r s modulus V hrs]

noncomputable def boundedColumnResidueRepresentative {K X : Type*} (modulus : X → ℕ)
    (r : ColumnResiduePattern K X modulus) : K × X → ℤ :=
  fun z => columnResidueRepresentative modulus r z % (modulus z.2 : ℤ)

theorem boundedColumnResidueRepresentative_congr {K X : Type*} (modulus : X → ℕ)
    (r : ColumnResiduePattern K X modulus) (z : K × X) :
    (modulus z.2 : ℤ) ∣ boundedColumnResidueRepresentative modulus r z - columnResidueRepresentative modulus r z := by
  refine ⟨-(columnResidueRepresentative modulus r z / (modulus z.2 : ℤ)), ?_⟩
  have h := Int.emod_add_mul_ediv (columnResidueRepresentative modulus r z) (modulus z.2 : ℤ)
  unfold boundedColumnResidueRepresentative
  nlinarith

theorem boundedColumnResidueRepresentative_bounds {K X : Type*} (modulus : X → ℕ)
    (hmodulus : ∀ x, 0 < modulus x) (r : ColumnResiduePattern K X modulus) (z : K × X) :
    0 ≤ boundedColumnResidueRepresentative modulus r z ∧
      boundedColumnResidueRepresentative modulus r z < (modulus z.2 : ℤ) := by
  have hq : (0 : ℤ) < modulus z.2 := by exact_mod_cast hmodulus z.2
  exact ⟨Int.emod_nonneg _ hq.ne', Int.emod_lt_of_pos _ hq⟩

theorem residueSmoothPMF_bounded {K X : Type*} [Fintype K] [Fintype X]
    (modulus : X → ℕ) (hmodulus : ∀ x, 0 < modulus x) (r : ColumnResiduePattern K X modulus)
    (V : K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hr : 0 < shiftedSmoothProductMass
      (residueProfileCenter (columnResidueRepresentative modulus r) modulus) (residueProfileWidth modulus V)) :
    ∃ hb : 0 < shiftedSmoothProductMass
        (residueProfileCenter (boundedColumnResidueRepresentative modulus r) modulus) (residueProfileWidth modulus V),
      residueSmoothPMF (columnResidueRepresentative modulus r) modulus hmodulus V hV hr =
        residueSmoothPMF (boundedColumnResidueRepresentative modulus r) modulus hmodulus V hV hb := by
  have he := residueSmoothMass_congr _ _ modulus hmodulus V hV (boundedColumnResidueRepresentative_congr modulus r)
  refine ⟨he ▸ hr, residueSmoothPMF_congr _ _ modulus hmodulus V hV
    (boundedColumnResidueRepresentative_congr modulus r) hr _⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def selectedResidueSmoothWeight {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (x : K × I → ℤ) : ℝ :=
  if columnResiduePattern modulus x ∈ G then
    smoothProductProfile (K × I) (fun z => (x z : ℝ) / V z) else 0

theorem selectedResidueSmoothWeight_eq_sum {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (x : K × I → ℤ) :
    selectedResidueSmoothWeight modulus G V x =
      ∑ r : G, residueSmoothWeight (columnResidueRepresentative modulus r.val) modulus V x := by
  symm
  calc
    _ = ∑ r ∈ G, residueSmoothWeight (columnResidueRepresentative modulus r) modulus V x :=
      Finset.sum_coe_sort G (fun r => residueSmoothWeight (columnResidueRepresentative modulus r) modulus V x)
    _ = _ := by
      simp only [residueSmoothWeight_eq_pattern, Finset.sum_ite_eq, selectedResidueSmoothWeight]

theorem residueSmoothWeight_zero_off {K I : Type*} [Fintype K] [Fintype I]
    (residue : K × I → ℤ) (modulus : I → ℕ) (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (x : K × I → ℤ) (hx : x ∉ rectangularWeightIndices 0 V 1) :
    residueSmoothWeight residue modulus V x = 0 := by
  have hz := rectangularWeight_zero_off_indices (smoothProductProfile (K × I)) 0 V hV
    (smoothProductProfile_zero_outside (K × I)) x hx
  simp only [rectangularWeight, rectangularLatticePoint_zero_origin] at hz
  simp only [residueSmoothWeight, hz, ite_self]

theorem selectedResidueSmoothWeight_nonneg {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (x : K × I → ℤ) : 0 ≤ selectedResidueSmoothWeight modulus G V x := by
  unfold selectedResidueSmoothWeight
  split
  · exact (smoothProductProfile_range (K × I) _).1
  · exact le_rfl

theorem selectedResidueSmoothWeight_zero_off {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (x : K × I → ℤ) (hx : x ∉ rectangularWeightIndices 0 V 1) :
    selectedResidueSmoothWeight modulus G V x = 0 := by
  rw [selectedResidueSmoothWeight_eq_sum]
  simp only [residueSmoothWeight_zero_off _ _ V hV x hx, Finset.sum_const_zero]

theorem selectedResidueSmoothWeight_mass {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z) :
    (∑' x, selectedResidueSmoothWeight modulus G V x) =
      ∑ r : G, ∑' x, residueSmoothWeight (columnResidueRepresentative modulus r.val) modulus V x := by
  simp_rw [selectedResidueSmoothWeight_eq_sum]
  exact finite_supported_weight_sum_tsum _ (rectangularWeightIndices 0 V 1)
    (fun r => residueSmoothWeight_zero_off _ modulus V hV)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem selectedResidueSmoothWeight_summable {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z) : Summable (selectedResidueSmoothWeight modulus G V) :=
  (hasSum_sum_of_ne_finset_zero (selectedResidueSmoothWeight_zero_off modulus G V hV)).summable

theorem selectedResidueSmoothWeight_mass_pos {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus)) (hG : G.Nonempty)
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hc : ∀ r : G, 0 < ∑' x, residueSmoothWeight (columnResidueRepresentative modulus r.val) modulus V x) :
    0 < ∑' x, selectedResidueSmoothWeight modulus G V x := by
  obtain ⟨r, hr⟩ := hG
  rw [selectedResidueSmoothWeight_mass modulus G V hV]
  exact (hc ⟨r, hr⟩).trans_le
    (Finset.single_le_sum (fun s _ => (hc s).le) (Finset.mem_univ (⟨r, hr⟩ : G)))

noncomputable def selectedResidueSmoothPMF {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x) : PMF (K × I → ℤ) :=
  realWeightPMF (selectedResidueSmoothWeight modulus G V)
    (selectedResidueSmoothWeight_nonneg modulus G V)
    (selectedResidueSmoothWeight_summable modulus G V hV) hZ

theorem selectedResidueSmoothPMF_toReal {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x) (x : K × I → ℤ) :
    (selectedResidueSmoothPMF modulus G V hV hZ x).toReal =
      selectedResidueSmoothWeight modulus G V x / ∑' y, selectedResidueSmoothWeight modulus G V y :=
  realWeightPMF_apply _ _ _ _ x

theorem selectedResidueSmoothPMF_mixture {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (hmodulus : ∀ j, 0 < modulus j)
    (G : Finset (ColumnResiduePattern K I modulus)) (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x)
    (hc : ∀ r : G, 0 < shiftedSmoothProductMass
      (residueProfileCenter (columnResidueRepresentative modulus r.val) modulus) (residueProfileWidth modulus V))
    (φ : (K × I → ℤ) → ℂ) :
    (∑' x, ((selectedResidueSmoothPMF modulus G V hV hZ x).toReal : ℂ) * φ x) =
      ∑ r : G, (((∑' y, residueSmoothWeight (columnResidueRepresentative modulus r.val) modulus V y) /
          (∑' y, selectedResidueSmoothWeight modulus G V y) : ℝ) : ℂ) *
        (∑' x, ((residueSmoothPMF (columnResidueRepresentative modulus r.val) modulus hmodulus V hV (hc r) x).toReal : ℂ) * φ x) := by
  have hcell (r : G) : 0 < ∑' x, residueSmoothWeight (columnResidueRepresentative modulus r.val) modulus V x := by
    rw [← residueSmoothWeight_mass _ modulus hmodulus V hV]
    exact hc r
  have ht := selectedResidueSmoothWeight_mass modulus G V hV
  have htotal : 0 < ∑ r : G, ∑' x, residueSmoothWeight (columnResidueRepresentative modulus r.val) modulus V x := by
    rwa [← ht]
  simp_rw [selectedResidueSmoothPMF_toReal, residueSmoothPMF_conditional_weight, ht,
    selectedResidueSmoothWeight_eq_sum]
  exact finite_supported_normalized_mixture _ (rectangularWeightIndices 0 V 1)
    (fun r => residueSmoothWeight_zero_off _ modulus V hV) hcell htotal φ

theorem selectedResidueSmoothPMF_bound_of_cells {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (hmodulus : ∀ j, 0 < modulus j)
    (G : Finset (ColumnResiduePattern K I modulus)) (hG : G.Nonempty)
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hc : ∀ r : G, 0 < shiftedSmoothProductMass
      (residueProfileCenter (columnResidueRepresentative modulus r.val) modulus) (residueProfileWidth modulus V))
    (φ : (K × I → ℤ) → ℂ) {ε : ℝ}
    (hφ : ∀ r : G,
      ‖∑' x, ((residueSmoothPMF (columnResidueRepresentative modulus r.val) modulus hmodulus V hV (hc r) x).toReal : ℂ) * φ x‖ ≤ ε) :
    ∃ hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x,
      ‖∑' x, ((selectedResidueSmoothPMF modulus G V hV hZ x).toReal : ℂ) * φ x‖ ≤ ε := by
  have hcell (r : G) : 0 < ∑' x, residueSmoothWeight (columnResidueRepresentative modulus r.val) modulus V x := by
    rw [← residueSmoothWeight_mass _ modulus hmodulus V hV]
    exact hc r
  have hZ := selectedResidueSmoothWeight_mass_pos modulus G hG V hV hcell
  have ht := selectedResidueSmoothWeight_mass modulus G V hV
  have htotal : 0 < ∑ r : G, ∑' x, residueSmoothWeight (columnResidueRepresentative modulus r.val) modulus V x := by
    rwa [← ht]
  refine ⟨hZ, ?_⟩
  simp_rw [selectedResidueSmoothPMF_toReal, ht, selectedResidueSmoothWeight_eq_sum]
  apply finite_supported_normalized_mixture_bound _ (rectangularWeightIndices 0 V 1)
    (fun r => residueSmoothWeight_zero_off _ modulus V hV) hcell htotal φ
  intro r
  simpa only [residueSmoothPMF_conditional_weight] using hφ r

end Erdos3

end

section

namespace Erdos3

theorem selectedResidueSmoothPMF_approximation {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x)
    (w f g : (K × I → ℤ) → ℂ) {η : ℝ} (hη : 0 ≤ η)
    (hw : ∀ x ∈ rectangularWeightIndices 0 V 1, ‖w x‖ ≤ 1)
    (he : ∀ x ∈ rectangularWeightIndices 0 V 1, ‖f x - g x‖ ≤ η) :
    ‖(∑' x, ((selectedResidueSmoothPMF modulus G V hV hZ x).toReal : ℂ) * (w x * f x)) -
      ∑' x, ((selectedResidueSmoothPMF modulus G V hV hZ x).toReal : ℂ) * (w x * g x)‖ ≤ η := by
  simp_rw [selectedResidueSmoothPMF_toReal]
  exact normalized_finite_weight_approximation _ (rectangularWeightIndices 0 V 1)
    (selectedResidueSmoothWeight_nonneg modulus G V)
    (selectedResidueSmoothWeight_zero_off modulus G V hV) hZ w f g hη hw he

theorem selectedResidueSmoothPMF_projection_approximation {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x)
    (w f f₀ g₀ g : (K × I → ℤ) → ℂ) {η ε : ℝ} (hη : 0 ≤ η)
    (hw : ∀ x ∈ rectangularWeightIndices 0 V 1, ‖w x‖ ≤ 1)
    (hf : ∀ x ∈ rectangularWeightIndices 0 V 1, ‖f x - f₀ x‖ ≤ η)
    (hg : ∀ x ∈ rectangularWeightIndices 0 V 1, ‖g₀ x - g x‖ ≤ η)
    (hproject : ‖(∑' x, ((selectedResidueSmoothPMF modulus G V hV hZ x).toReal : ℂ) * (w x * f₀ x)) -
      ∑' x, ((selectedResidueSmoothPMF modulus G V hV hZ x).toReal : ℂ) * (w x * g₀ x)‖ ≤ ε) :
    ‖(∑' x, ((selectedResidueSmoothPMF modulus G V hV hZ x).toReal : ℂ) * (w x * f x)) -
      ∑' x, ((selectedResidueSmoothPMF modulus G V hV hZ x).toReal : ℂ) * (w x * g x)‖ ≤ 2 * η + ε := by
  have hfirst := selectedResidueSmoothPMF_approximation modulus G V hV hZ w f f₀ hη hw hf
  have hlast := selectedResidueSmoothPMF_approximation modulus G V hV hZ w g₀ g hη hw hg
  let E (a : (K × I → ℤ) → ℂ) :=
    ∑' x, ((selectedResidueSmoothPMF modulus G V hV hZ x).toReal : ℂ) * (w x * a x)
  have htri := norm_sub_le_norm_sub_add_norm_sub (E f) (E f₀) (E g)
  have htri' := norm_sub_le_norm_sub_add_norm_sub (E f₀) (E g₀) (E g)
  change ‖E f - E f₀‖ ≤ η at hfirst
  change ‖E g₀ - E g‖ ≤ η at hlast
  change ‖E f₀ - E g₀‖ ≤ ε at hproject
  change ‖E f - E g‖ ≤ 2 * η + ε
  linarith

end Erdos3

end

end OAI
