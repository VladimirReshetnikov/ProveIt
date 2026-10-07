-- Modified for ProveIt: added `import OAI.Compat.*` lines (backported names); see lib/openai-math/README.md.
import OAI.Combinatorics.Progressions.Estimates.MinkowskiSecondInduction
import OAI.Combinatorics.Progressions.Fourier.ExponentialBohrVolume
import OAI.Compat.BigOperators

namespace OAI

section

open scoped BigOperators Matrix Pointwise

namespace Erdos3.BohrProgression

open Erdos3.BohrLattice.BoxCertificate
open Erdos3.BohrLattice.MinkowskiSecondBox

noncomputable section

noncomputable def indexedCyclicCharacter {N : ℕ}
    (Gamma : Finset (ZMod N)) : Fin (Gamma.card + 1) → ZMod N :=
  Fin.cases 1 fun i => (Gamma.equivFin.symm i : Gamma)

@[simp] lemma indexedCyclicCharacter_zero {N : ℕ}
    (Gamma : Finset (ZMod N)) : indexedCyclicCharacter Gamma 0 = 1 := rfl

lemma indexedCyclicCharacter_succ_mem {N : ℕ}
    (Gamma : Finset (ZMod N)) (i : Fin Gamma.card) :
    indexedCyclicCharacter Gamma i.succ ∈ Gamma := by
  change ((Gamma.equivFin.symm i : Gamma) : ZMod N) ∈ Gamma
  exact (Gamma.equivFin.symm i).property

def bohrLatticeMatrixInt {N : ℕ} (Gamma : Finset (ZMod N)) :
    Matrix (Fin (Gamma.card + 1)) (Fin (Gamma.card + 1)) ℤ :=
  fun i j => if j = 0 then ((indexedCyclicCharacter Gamma i).val : ℤ)
    else if i = j then (N : ℤ) else 0

def bohrLatticeMatrix {N : ℕ} (Gamma : Finset (ZMod N)) :
    Matrix (Fin (Gamma.card + 1)) (Fin (Gamma.card + 1)) ℝ :=
  (bohrLatticeMatrixInt Gamma).map (Int.castRingHom ℝ)

@[simp] lemma bohrLatticeMatrixInt_zero_succ {N : ℕ}
    (Gamma : Finset (ZMod N)) (j : Fin Gamma.card) :
    bohrLatticeMatrixInt Gamma 0 j.succ = 0 := by
  simp [bohrLatticeMatrixInt, (Fin.succ_ne_zero j).symm]

@[simp] lemma bohrLatticeMatrix_zero_zero {N : ℕ}
    (Gamma : Finset (ZMod N)) (hN : 1 < N) :
    bohrLatticeMatrix Gamma 0 0 = 1 := by
  simp [bohrLatticeMatrix, bohrLatticeMatrixInt, ZMod.val_one'' (by omega : N ≠ 1)]

@[simp] lemma bohrLatticeMatrix_zero_succ {N : ℕ}
    (Gamma : Finset (ZMod N)) (j : Fin Gamma.card) :
    bohrLatticeMatrix Gamma 0 j.succ = 0 := by
  simp [bohrLatticeMatrix]

@[simp] lemma bohrLatticeMatrix_succ_succ {N : ℕ}
    (Gamma : Finset (ZMod N)) (i j : Fin Gamma.card) :
    bohrLatticeMatrix Gamma i.succ j.succ =
      if i = j then (N : ℝ) else 0 := by
  simp [bohrLatticeMatrix, bohrLatticeMatrixInt, Fin.succ_inj]

lemma det_bohrLatticeMatrix {N : ℕ} (Gamma : Finset (ZMod N)) (hN : 1 < N) :
    (bohrLatticeMatrix Gamma).det = (N : ℝ) ^ Gamma.card := by
  have hminor :
      (bohrLatticeMatrix Gamma).submatrix Fin.succ (Fin.succAbove 0) =
        Matrix.diagonal (fun _ : Fin Gamma.card => (N : ℝ)) := by
    ext i j
    rw [Matrix.diagonal_apply]
    simp [Matrix.submatrix]
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  simp only [bohrLatticeMatrix_zero_zero Gamma hN, bohrLatticeMatrix_zero_succ]
  rw [hminor]
  rw [Matrix.det_diagonal]
  simp

lemma det_bohrLatticeMatrix_ne_zero {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) :
    (bohrLatticeMatrix Gamma).det ≠ 0 := by
  rw [det_bohrLatticeMatrix Gamma hN]
  positivity

noncomputable def bohrLatticeBasis {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) :
    Module.Basis (Fin (Gamma.card + 1)) ℝ
      (Fin (Gamma.card + 1) → ℝ) :=
  matrixBasis (bohrLatticeMatrix Gamma)
    (det_bohrLatticeMatrix_ne_zero Gamma hN)

@[simp] lemma bohrLatticeBasis_apply {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N)
    (j i : Fin (Gamma.card + 1)) :
    bohrLatticeBasis Gamma hN j i = bohrLatticeMatrix Gamma i j := by
  exact congrFun (matrixBasis_apply (bohrLatticeMatrix Gamma)
    (det_bohrLatticeMatrix_ne_zero Gamma hN) j) i

def bohrLatticePoint {N : ℕ} (Gamma : Finset (ZMod N))
    (z : Fin (Gamma.card + 1) → ℤ) : Fin (Gamma.card + 1) → ℤ :=
  Matrix.mulVec (bohrLatticeMatrixInt Gamma) z

lemma intCastVec_bohrLatticePoint {N : ℕ} (Gamma : Finset (ZMod N))
    (z : Fin (Gamma.card + 1) → ℤ) :
    intCastVec (bohrLatticePoint Gamma z) =
      Matrix.mulVec (bohrLatticeMatrix Gamma) (intCastVec z) := by
  funext i
  simp [bohrLatticePoint, bohrLatticeMatrix, Matrix.mulVec, dotProduct,
    intCastVec]

lemma bohrLatticePoint_zero {N : ℕ} (Gamma : Finset (ZMod N)) (hN : 1 < N)
    (z : Fin (Gamma.card + 1) → ℤ) :
    bohrLatticePoint Gamma z 0 = z 0 := by
  simp [bohrLatticePoint, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
    bohrLatticeMatrixInt, ZMod.val_one'' (by omega : N ≠ 1),
    (fun x : Fin Gamma.card => (Fin.succ_ne_zero x).symm)]

lemma bohrLatticePoint_cast_coordinate {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (z : Fin (Gamma.card + 1) → ℤ)
    (hN : 1 < N)
    (i : Fin (Gamma.card + 1)) :
    (bohrLatticePoint Gamma z i : ZMod N) =
      (bohrLatticePoint Gamma z 0 : ZMod N) *
        indexedCyclicCharacter Gamma i := by
  rw [bohrLatticePoint_zero Gamma hN]
  simp only [bohrLatticePoint, Matrix.mulVec, dotProduct]
  rw [Fin.sum_univ_succ]
  simp only [bohrLatticeMatrixInt]
  by_cases hi : i = 0
  · subst i
    simp
  · simp [mul_comm]

structure CyclicCenteredGAP (N : ℕ) where
  rank : ℕ
  step : Fin rank → ZMod N
  radius : Fin rank → ℕ

namespace CyclicCenteredGAP

abbrev Param {N : ℕ} (Q : CyclicCenteredGAP N) :=
  (i : Fin Q.rank) → Fin (2 * Q.radius i + 1)

def coeff {N : ℕ} (Q : CyclicCenteredGAP N) (x : Q.Param)
    (i : Fin Q.rank) : ℤ := (x i : ℤ) - Q.radius i

def eval {N : ℕ} (Q : CyclicCenteredGAP N) (x : Q.Param) : ZMod N :=
  ∑ i, (Q.coeff x i : ZMod N) * Q.step i

noncomputable def carrier {N : ℕ} (Q : CyclicCenteredGAP N) : Finset (ZMod N) :=
  (Finset.univ : Finset Q.Param).image Q.eval

def Proper {N : ℕ} (Q : CyclicCenteredGAP N) : Prop :=
  Function.Injective Q.eval

lemma card_carrier_of_proper {N : ℕ} (Q : CyclicCenteredGAP N)
    (hQ : Q.Proper) :
    Q.carrier.card = ∏ i, (2 * Q.radius i + 1) := by
  rw [carrier, Finset.card_image_of_injective _ hQ, Finset.card_univ]
  simp [Param]

lemma coeff_abs_le {N : ℕ} (Q : CyclicCenteredGAP N)
    (x : Q.Param) (i : Fin Q.rank) :
    |Q.coeff x i| ≤ (Q.radius i : ℤ) := by
  change |(x i : ℤ) - Q.radius i| ≤ (Q.radius i : ℤ)
  rw [abs_le]
  have hi := (x i).isLt
  change (x i : ℕ) < 2 * Q.radius i + 1 at hi
  constructor <;> omega

lemma coeff_sub_abs_le_two_mul {N : ℕ} (Q : CyclicCenteredGAP N)
    (x y : Q.Param) (i : Fin Q.rank) :
    |Q.coeff x i - Q.coeff y i| ≤ (2 * Q.radius i : ℕ) := by
  calc
    |Q.coeff x i - Q.coeff y i| ≤
        |Q.coeff x i| + |Q.coeff y i| := abs_sub _ _
    _ ≤ (Q.radius i : ℤ) + Q.radius i :=
      add_le_add (Q.coeff_abs_le x i) (Q.coeff_abs_le y i)
    _ = (2 * Q.radius i : ℕ) := by push_cast; ring

end CyclicCenteredGAP

noncomputable def bohrSuccessiveCertificate {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) (R : ℝ) (hR : 0 < R) :
    SuccessiveProductCertificate
      (Submodule.span ℤ (Set.range (bohrLatticeBasis Gamma hN))).toAddSubgroup
      (fun _ => R)
      (minkowskiSecondConstant (Gamma.card + 1) *
        |(Matrix.of (bohrLatticeBasis Gamma hN)).det| *
          (∏ _i : Fin (Gamma.card + 1), R)⁻¹) :=
  Classical.choice
    (realBox_has_minkowskiSecondCertificate
      (bohrLatticeBasis Gamma hN) (fun _ => R) (fun _ => hR))

noncomputable def bohrCertificateCoeff {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) (R : ℝ) (hR : 0 < R)
    (i : Fin (Gamma.card + 1)) : Fin (Gamma.card + 1) → ℤ :=
  Classical.choose
    ((Submodule.mem_span_range_iff_exists_fun ℤ).mp
      ((bohrSuccessiveCertificate Gamma hN R hR).point_mem i))

lemma bohrCertificateCoeff_spec {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) (R : ℝ) (hR : 0 < R)
    (i : Fin (Gamma.card + 1)) :
    ∑ j, bohrCertificateCoeff Gamma hN R hR i j •
        bohrLatticeBasis Gamma hN j =
      (bohrSuccessiveCertificate Gamma hN R hR).point i :=
  Classical.choose_spec
    ((Submodule.mem_span_range_iff_exists_fun ℤ).mp
      ((bohrSuccessiveCertificate Gamma hN R hR).point_mem i))

noncomputable def bohrCertificatePoint {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) (R : ℝ) (hR : 0 < R)
    (i : Fin (Gamma.card + 1)) : Fin (Gamma.card + 1) → ℤ :=
  bohrLatticePoint Gamma (bohrCertificateCoeff Gamma hN R hR i)

lemma intCastVec_bohrCertificatePoint {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) (R : ℝ) (hR : 0 < R)
    (i : Fin (Gamma.card + 1)) :
    intCastVec (bohrCertificatePoint Gamma hN R hR i) =
      (bohrSuccessiveCertificate Gamma hN R hR).point i := by
  rw [bohrCertificatePoint, intCastVec_bohrLatticePoint]
  rw [← bohrCertificateCoeff_spec Gamma hN R hR i]
  funext k
  simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply]
  apply Finset.sum_congr rfl
  intro j hj
  rw [bohrLatticeBasis_apply]
  simp [intCastVec, mul_comm]

lemma bohrCertificatePoint_independent {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) (R : ℝ) (hR : 0 < R) :
    LinearIndependent ℝ (fun i =>
      intCastVec (bohrCertificatePoint Gamma hN R hR i)) := by
  simpa only [intCastVec_bohrCertificatePoint] using
    (bohrSuccessiveCertificate Gamma hN R hR).independent

lemma bohrCertificate_scale_pos {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) (R : ℝ) (hR : 0 < R)
    (i : Fin (Gamma.card + 1)) :
    0 < (bohrSuccessiveCertificate Gamma hN R hR).scale i := by
  let C := bohrSuccessiveCertificate Gamma hN R hR
  have hs := C.scale_nonneg i
  refine hs.lt_of_ne ?_
  intro hz
  have hpzero : C.point i = 0 := by
    have hm := C.mem_scaledBox i
    rw [← hz, zero_smul] at hm
    ext j
    have hlo := hm.1 j
    have hhi := hm.2 j
    simp only [Pi.zero_apply, neg_zero] at hlo hhi
    exact le_antisymm hhi hlo
  exact C.independent.ne_zero i hpzero

noncomputable def bohrProgressionRadius {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) (R : ℝ) (hR : 0 < R)
    (i : Fin (Gamma.card + 1)) : ℕ :=
  ⌊((4 * (Gamma.card + 1) : ℝ) *
      (bohrSuccessiveCertificate Gamma hN R hR).scale i)⁻¹⌋₊

noncomputable def bohrCyclicProgression {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) (R : ℝ) (hR : 0 < R) :
    CyclicCenteredGAP N where
  rank := Gamma.card + 1
  step i := (bohrCertificatePoint Gamma hN R hR i 0 : ZMod N)
  radius := bohrProgressionRadius Gamma hN R hR

lemma bohrProgressionRadius_mul_scale_le {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) (R : ℝ) (hR : 0 < R)
    (i : Fin (Gamma.card + 1)) :
    (bohrProgressionRadius Gamma hN R hR i : ℝ) *
        (bohrSuccessiveCertificate Gamma hN R hR).scale i ≤
      1 / (4 * (Gamma.card + 1) : ℝ) := by
  let s := (bohrSuccessiveCertificate Gamma hN R hR).scale i
  have hs : 0 < s := bohrCertificate_scale_pos Gamma hN R hR i
  have hm : (0 : ℝ) < 4 * (Gamma.card + 1) := by positivity
  have hfloor :
      (bohrProgressionRadius Gamma hN R hR i : ℝ) ≤
        ((4 * (Gamma.card + 1) : ℝ) * s)⁻¹ := by
    apply Nat.floor_le
    positivity
  calc
    (bohrProgressionRadius Gamma hN R hR i : ℝ) * s ≤
        ((4 * (Gamma.card + 1) : ℝ) * s)⁻¹ * s :=
      mul_le_mul_of_nonneg_right hfloor hs.le
    _ = 1 / (4 * (Gamma.card + 1) : ℝ) := by
      field_simp

lemma abs_intCast_bohrCertificatePoint_le {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) (R : ℝ) (hR : 0 < R)
    (i j : Fin (Gamma.card + 1)) :
    |(bohrCertificatePoint Gamma hN R hR i j : ℝ)| ≤
      (bohrSuccessiveCertificate Gamma hN R hR).scale i * R := by
  let C := bohrSuccessiveCertificate Gamma hN R hR
  have hm := C.mem_scaledBox i
  have hlo := hm.1 j
  have hhi := hm.2 j
  rw [← intCastVec_bohrCertificatePoint Gamma hN R hR i] at hlo hhi
  change -(C.scale i * R) ≤
      (bohrCertificatePoint Gamma hN R hR i j : ℝ) at hlo
  change (bohrCertificatePoint Gamma hN R hR i j : ℝ) ≤
      C.scale i * R at hhi
  exact (abs_le.mpr ⟨hlo, hhi⟩)

def bohrCertificateCombination {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) (R : ℝ) (hR : 0 < R)
    (u : Fin (Gamma.card + 1) → ℤ) : Fin (Gamma.card + 1) → ℤ :=
  fun j => ∑ i, u i * bohrCertificatePoint Gamma hN R hR i j

lemma bohrCertificateCombination_cast_coordinate {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) (R : ℝ) (hR : 0 < R)
    (u : Fin (Gamma.card + 1) → ℤ) (j : Fin (Gamma.card + 1)) :
    (bohrCertificateCombination Gamma hN R hR u j : ZMod N) =
      (bohrCertificateCombination Gamma hN R hR u 0 : ZMod N) *
        indexedCyclicCharacter Gamma j := by
  simp only [bohrCertificateCombination, Int.cast_sum, Int.cast_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  have hp := bohrLatticePoint_cast_coordinate Gamma
    (bohrCertificateCoeff Gamma hN R hR i) hN j
  change (bohrCertificatePoint Gamma hN R hR i j : ZMod N) =
    (bohrCertificatePoint Gamma hN R hR i 0 : ZMod N) *
      indexedCyclicCharacter Gamma j at hp
  rw [hp]
  ring

lemma abs_intCast_bohrCertificateCombination_le {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) (R : ℝ) (hR : 0 < R)
    (a : ℕ) (u : Fin (Gamma.card + 1) → ℤ)
    (hu : ∀ i, |u i| ≤ (a * bohrProgressionRadius Gamma hN R hR i : ℕ))
    (j : Fin (Gamma.card + 1)) :
    |(bohrCertificateCombination Gamma hN R hR u j : ℝ)| ≤
      (a : ℝ) * R / 4 := by
  let m := Gamma.card + 1
  have hm : (0 : ℝ) < m := by positivity
  have hR0 : 0 ≤ R := hR.le
  have hterm (i : Fin m) :
      |(u i : ℝ) *
          (bohrCertificatePoint Gamma hN R hR i j : ℝ)| ≤
        (a : ℝ) * R / (4 * m : ℝ) := by
    rw [abs_mul]
    have huR : |(u i : ℝ)| ≤
        (a : ℝ) * bohrProgressionRadius Gamma hN R hR i := by
      rw [← Int.cast_abs]
      exact_mod_cast hu i
    calc
      |(u i : ℝ)| *
          |(bohrCertificatePoint Gamma hN R hR i j : ℝ)| ≤
        ((a : ℝ) * bohrProgressionRadius Gamma hN R hR i) *
          ((bohrSuccessiveCertificate Gamma hN R hR).scale i * R) := by
            gcongr
            exact abs_intCast_bohrCertificatePoint_le Gamma hN R hR i j
      _ = (a : ℝ) *
          ((bohrProgressionRadius Gamma hN R hR i : ℝ) *
            (bohrSuccessiveCertificate Gamma hN R hR).scale i) * R := by ring
      _ ≤ (a : ℝ) * (1 / (4 * m : ℝ)) * R := by
        gcongr
        simpa [m, Nat.cast_add, Nat.cast_one] using
          bohrProgressionRadius_mul_scale_le Gamma hN R hR i
      _ = (a : ℝ) * R / (4 * m : ℝ) := by ring
  have hcast : (bohrCertificateCombination Gamma hN R hR u j : ℝ) =
      ∑ i, (u i : ℝ) *
        (bohrCertificatePoint Gamma hN R hR i j : ℝ) := by
    simp [bohrCertificateCombination]
  rw [hcast]
  calc
    |∑ i, (u i : ℝ) *
        (bohrCertificatePoint Gamma hN R hR i j : ℝ)| ≤
      ∑ i, |(u i : ℝ) *
        (bohrCertificatePoint Gamma hN R hR i j : ℝ)| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin m, ((a : ℝ) * R / (4 * m : ℝ)) := by
      exact Finset.sum_le_sum fun i hi => hterm i
    _ = (a : ℝ) * R / 4 := by
      simp [m]
      field_simp

lemma eval_bohrCyclicProgression {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) (R : ℝ) (hR : 0 < R)
    (x : (bohrCyclicProgression Gamma hN R hR).Param) :
    (bohrCyclicProgression Gamma hN R hR).eval x =
      (bohrCertificateCombination Gamma hN R hR
        ((bohrCyclicProgression Gamma hN R hR).coeff x) 0 : ZMod N) := by
  simp only [CyclicCenteredGAP.eval, bohrCyclicProgression,
    bohrCertificateCombination, Int.cast_sum, Int.cast_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rfl

lemma int_eq_zero_of_cast_zmod_eq_zero_of_abs_lt {N : ℕ} [NeZero N]
    {t : ℤ} (ht0 : (t : ZMod N) = 0) (htN : |(t : ℝ)| < N) : t = 0 := by
  have hdvd : (N : ℤ) ∣ t :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd t N).mp ht0
  have habs : (t.natAbs : ℝ) = |(t : ℝ)| := by
    calc
      (t.natAbs : ℝ) = (((t.natAbs : ℕ) : ℤ) : ℝ) := by norm_num
      _ = ((|t| : ℤ) : ℝ) := by rw [Int.natCast_natAbs]
      _ = |(t : ℝ)| := Int.cast_abs
  have hnat : t.natAbs < N := by
    exact_mod_cast (habs.trans_lt htN)
  apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd
  simpa using hnat

theorem bohrCyclicProgression_proper {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) (R : ℝ) (hR : 0 < R)
    (hsmall : R < 2 * N) :
    (bohrCyclicProgression Gamma hN R hR).Proper := by
  let Q := bohrCyclicProgression Gamma hN R hR
  intro x y hxy
  let u : Fin (Gamma.card + 1) → ℤ := fun i => Q.coeff x i - Q.coeff y i
  let v := bohrCertificateCombination Gamma hN R hR u
  have hu (i : Fin (Gamma.card + 1)) :
      |u i| ≤ (2 * bohrProgressionRadius Gamma hN R hR i : ℕ) := by
    exact CyclicCenteredGAP.coeff_sub_abs_le_two_mul Q x y i
  have hv0cast : (v 0 : ZMod N) = 0 := by
    have hx := eval_bohrCyclicProgression Gamma hN R hR x
    have hy := eval_bohrCyclicProgression Gamma hN R hR y
    have hvsub : (v 0 : ZMod N) =
        (bohrCyclicProgression Gamma hN R hR).eval x -
          (bohrCyclicProgression Gamma hN R hR).eval y := by
      rw [hx, hy]
      simp only [v, u, bohrCertificateCombination, Int.cast_sum, Int.cast_mul,
        Int.cast_sub]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hvsub, hxy, sub_self]
  have hvcast (j : Fin (Gamma.card + 1)) : (v j : ZMod N) = 0 := by
    rw [bohrCertificateCombination_cast_coordinate Gamma hN R hR u j,
      hv0cast, zero_mul]
  have hvabs (j : Fin (Gamma.card + 1)) : |(v j : ℝ)| ≤ R / 2 := by
    convert abs_intCast_bohrCertificateCombination_le Gamma hN R hR 2 u hu j
      using 1; norm_num; ring
  have hvzero : v = 0 := by
    funext j
    apply int_eq_zero_of_cast_zmod_eq_zero_of_abs_lt (hvcast j)
    exact (hvabs j).trans_lt (by linarith)
  have hsum : ∑ i, (u i : ℝ) •
      intCastVec (bohrCertificatePoint Gamma hN R hR i) = 0 := by
    funext j
    have hj := congrFun hvzero j
    have hjR : (v j : ℝ) = 0 := by exact_mod_cast hj
    simpa [v, bohrCertificateCombination, intCastVec] using hjR
  have huR : ∀ i, (u i : ℝ) = 0 :=
    (Fintype.linearIndependent_iff.mp
      (bohrCertificatePoint_independent Gamma hN R hR)) _ hsum
  have hu0 : u = 0 := by
    funext i
    change u i = 0
    exact_mod_cast huR i
  funext i
  apply Fin.ext
  have hi0 : u i = 0 := by
    change u i = (0 : Fin (Gamma.card + 1) → ℤ) i
    exact congrFun hu0 i
  have hi : (x i : ℤ) = (y i : ℤ) := by
    dsimp only [u, Q] at hi0
    simp only [CyclicCenteredGAP.coeff] at hi0
    omega
  exact_mod_cast hi

lemma matrixOf_bohrLatticeBasis {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) :
    Matrix.of (bohrLatticeBasis Gamma hN) =
      (bohrLatticeMatrix Gamma)ᵀ := by
  ext i j
  rw [Matrix.of_apply, Matrix.transpose_apply]
  exact bohrLatticeBasis_apply Gamma hN i j

lemma abs_det_matrixOf_bohrLatticeBasis {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) :
    |(Matrix.of (bohrLatticeBasis Gamma hN)).det| =
      (N : ℝ) ^ Gamma.card := by
  rw [matrixOf_bohrLatticeBasis Gamma hN,
    Matrix.det_transpose, det_bohrLatticeMatrix Gamma hN, abs_of_nonneg]
  positivity

lemma inv_scale_le_two_mul_bohrProgressionRadius_add_one
    {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) (R : ℝ) (hR : 0 < R)
    (i : Fin (Gamma.card + 1)) :
    (((4 * (Gamma.card + 1) : ℝ) *
        (bohrSuccessiveCertificate Gamma hN R hR).scale i)⁻¹) ≤
      2 * (bohrProgressionRadius Gamma hN R hR i : ℝ) + 1 := by
  have hlt := Nat.lt_floor_add_one
    (((4 * (Gamma.card + 1) : ℝ) *
      (bohrSuccessiveCertificate Gamma hN R hR).scale i)⁻¹)
  change (((4 * (Gamma.card + 1) : ℝ) *
      (bohrSuccessiveCertificate Gamma hN R hR).scale i)⁻¹) <
    (bohrProgressionRadius Gamma hN R hR i : ℝ) + 1 at hlt
  have hradius : 0 ≤ (bohrProgressionRadius Gamma hN R hR i : ℝ) := by
    positivity
  linarith

theorem bohrCyclicProgression_card_lower_bound {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) (R : ℝ) (hR : 0 < R)
    (hsmall : R < 2 * N) :
    ((((4 * (Gamma.card + 1) : ℝ) ^ (Gamma.card + 1)) *
        (minkowskiSecondConstant (Gamma.card + 1) *
          (N : ℝ) ^ Gamma.card *
            (R ^ (Gamma.card + 1))⁻¹))⁻¹) ≤
      ((bohrCyclicProgression Gamma hN R hR).carrier.card : ℝ) := by
  let c : ℝ := 4 * (Gamma.card + 1)
  let B : ℝ := minkowskiSecondConstant (Gamma.card + 1) *
    |(Matrix.of (bohrLatticeBasis Gamma hN)).det| *
      (∏ _i : Fin (Gamma.card + 1), R)⁻¹
  have hc : 0 < c := by positivity
  have hscale (i : Fin (Gamma.card + 1)) :
      0 < (bohrSuccessiveCertificate Gamma hN R hR).scale i := by
    exact bohrCertificate_scale_pos Gamma hN R hR i
  have hprodscale : 0 <
      ∏ i, (bohrSuccessiveCertificate Gamma hN R hR).scale i := by
    exact Finset.prod_pos fun i _ => hscale i
  have hB : 0 < B := by
    simp only [B, abs_det_matrixOf_bohrLatticeBasis Gamma hN,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    unfold minkowskiSecondConstant
    positivity
  have hcertificate :
      (∏ i, (bohrSuccessiveCertificate Gamma hN R hR).scale i) ≤ B := by
    exact (bohrSuccessiveCertificate Gamma hN R hR).product_le
  have hreciprocal : (c ^ (Gamma.card + 1) * B)⁻¹ ≤
      (c ^ (Gamma.card + 1) *
        ∏ i, (bohrSuccessiveCertificate Gamma hN R hR).scale i)⁻¹ := by
    apply (inv_le_inv₀ (mul_pos (pow_pos hc _) hB)
      (mul_pos (pow_pos hc _) hprodscale)).2
    exact mul_le_mul_of_nonneg_left hcertificate (pow_nonneg hc.le _)
  have hproduct :
      (c ^ (Gamma.card + 1) *
        ∏ i, (bohrSuccessiveCertificate Gamma hN R hR).scale i)⁻¹ ≤
      ∏ i : Fin (Gamma.card + 1),
        (2 * (bohrProgressionRadius Gamma hN R hR i : ℝ) + 1) := by
    calc
      (c ^ (Gamma.card + 1) *
          ∏ i, (bohrSuccessiveCertificate Gamma hN R hR).scale i)⁻¹ =
          (∏ i : Fin (Gamma.card + 1),
            c * (bohrSuccessiveCertificate Gamma hN R hR).scale i)⁻¹ := by
            congr 1
            rw [Finset.prod_mul_distrib]
            simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ = ∏ i : Fin (Gamma.card + 1),
          (c * (bohrSuccessiveCertificate Gamma hN R hR).scale i)⁻¹ := by
            rw [Finset.prod_inv_distrib]
      _ ≤ ∏ i : Fin (Gamma.card + 1),
          (2 * (bohrProgressionRadius Gamma hN R hR i : ℝ) + 1) := by
            apply Finset.prod_le_prod₀
            · intro i hi
              exact inv_nonneg.mpr (mul_nonneg hc.le
                ((bohrSuccessiveCertificate Gamma hN R hR).scale_nonneg i))
            · intro i hi
              simpa [c] using
                inv_scale_le_two_mul_bohrProgressionRadius_add_one
                  Gamma hN R hR i
  have hcard := CyclicCenteredGAP.card_carrier_of_proper
    (bohrCyclicProgression Gamma hN R hR)
    (bohrCyclicProgression_proper Gamma hN R hR hsmall)
  have hBform : B = minkowskiSecondConstant (Gamma.card + 1) *
      (N : ℝ) ^ Gamma.card * (R ^ (Gamma.card + 1))⁻¹ := by
    simp [B, abs_det_matrixOf_bohrLatticeBasis Gamma hN,
      Finset.prod_const]
  calc
    ((((4 * (Gamma.card + 1) : ℝ) ^ (Gamma.card + 1)) *
        (minkowskiSecondConstant (Gamma.card + 1) *
          (N : ℝ) ^ Gamma.card *
            (R ^ (Gamma.card + 1))⁻¹))⁻¹) =
        (c ^ (Gamma.card + 1) * B)⁻¹ := by
      rw [hBform]
    _ ≤ (c ^ (Gamma.card + 1) *
        ∏ i, (bohrSuccessiveCertificate Gamma hN R hR).scale i)⁻¹ :=
      hreciprocal
    _ ≤ ∏ i : Fin (Gamma.card + 1),
        (2 * (bohrProgressionRadius Gamma hN R hR i : ℝ) + 1) := hproduct
    _ = ((bohrCyclicProgression Gamma hN R hR).carrier.card : ℝ) := by
      rw [hcard]
      norm_cast

end

end Erdos3.BohrProgression

end

section

namespace Erdos3.BohrProgression

open scoped BigOperators
open BohrLattice.MinkowskiSecondBox

theorem bohrCyclicProgression_carrier_subset {N : ℕ} [NeZero N]
    (B : CyclicBohr.Set N) (hN : 1 < N) (R : ℝ) (hR : 0 < R)
    (hsmall : 2 * R ≤ B.radius * N) :
    (bohrCyclicProgression B.frequencies hN R hR).carrier ⊆ B.carrier := by
  intro z hz
  obtain ⟨x, _hx, rfl⟩ := Finset.mem_image.mp hz
  rw [CyclicBohr.Set.mem_carrier]
  intro k hk
  let Γ := B.frequencies
  let i : Fin Γ.card := Γ.equivFin ⟨k, hk⟩
  let u : Fin (Γ.card + 1) → ℤ :=
    (bohrCyclicProgression Γ hN R hR).coeff x
  let v := bohrCertificateCombination Γ hN R hR u
  have hu (j : Fin (Γ.card + 1)) :
      |u j| ≤ (bohrProgressionRadius Γ hN R hR j : ℕ) :=
    CyclicCenteredGAP.coeff_abs_le (bohrCyclicProgression Γ hN R hR) x j
  have heval : (bohrCyclicProgression Γ hN R hR).eval x = (v 0 : ZMod N) :=
    eval_bohrCyclicProgression Γ hN R hR x
  have hchar : indexedCyclicCharacter Γ i.succ = k := by
    change ((Γ.equivFin.symm i : Γ) : ZMod N) = k
    simp [i]
  have hvchar : k * (bohrCyclicProgression Γ hN R hR).eval x =
      (v i.succ : ZMod N) := by
    rw [bohrCertificateCombination_cast_coordinate Γ hN R hR u i.succ,
      hchar, heval, mul_comm]
  have hvabs : |(v i.succ : ℝ)| ≤ R / 4 := by
    simpa using abs_intCast_bohrCertificateCombination_le Γ hN R hR 1 u
      (by simpa using hu) i.succ
  refine (CyclicBohr.norm_one_sub_character_le_of_mul_eq_intCast
    k _ (v i.succ) hvchar).trans ?_
  have hNpos : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  apply (div_le_iff₀ hNpos).2
  nlinarith

theorem exists_proper_progression_subset {N : ℕ} [NeZero N]
    (B : CyclicBohr.Set N) (hB : 0 < B.radius) (hB1 : B.radius ≤ 1)
    (hN : 1 < N) :
    ∃ Q : CyclicCenteredGAP N,
      Q.rank = B.rank + 1 ∧ Q.Proper ∧ Q.carrier ⊆ B.carrier ∧
      (N : ℝ) * (B.radius / (8 * (B.rank + 1))) ^ (B.rank + 1) /
        minkowskiSecondConstant (B.rank + 1) ≤ (Q.carrier.card : ℝ) := by
  let R := B.radius * N / 2
  have hNpos : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hR : 0 < R := by dsimp [R]; positivity
  have hsmall : R < 2 * N := by dsimp [R]; nlinarith
  refine ⟨bohrCyclicProgression B.frequencies hN R hR, rfl,
    bohrCyclicProgression_proper B.frequencies hN R hR hsmall,
    bohrCyclicProgression_carrier_subset B hN R hR (by dsimp [R]; linarith), ?_⟩
  have hcard := bohrCyclicProgression_card_lower_bound B.frequencies hN R hR hsmall
  have hn : (0 : ℝ) < B.rank + 1 := by positivity
  have hc : 0 < minkowskiSecondConstant (B.rank + 1) := by
    unfold minkowskiSecondConstant
    positivity
  have heq :
      (N : ℝ) * (B.radius / (8 * (B.rank + 1))) ^ (B.rank + 1) /
          minkowskiSecondConstant (B.rank + 1) =
        (((4 * (B.rank + 1) : ℝ) ^ (B.rank + 1)) *
          (minkowskiSecondConstant (B.rank + 1) * (N : ℝ) ^ B.rank *
            (R ^ (B.rank + 1))⁻¹))⁻¹ := by
    dsimp [R]
    simp only [div_pow, mul_pow, pow_succ, mul_inv_rev, inv_inv]
    field_simp
    rw [show (8 : ℝ) ^ B.rank = (2 : ℝ) ^ B.rank * 4 ^ B.rank by
      rw [← mul_pow]; norm_num]
    ring
  rw [heq]
  exact hcard

end Erdos3.BohrProgression

end

section

namespace Erdos3.BohrProgression

open BohrLattice.MinkowskiSecondBox

lemma minkowskiSecondConstant_le_exp (m : ℕ) :
    minkowskiSecondConstant m ≤ Real.exp (2 * (m : ℝ) ^ 2) := by
  have hidx : m * (m - 1) / 2 ≤ m * m :=
    (Nat.div_le_self _ _).trans (Nat.mul_le_mul_left m (Nat.sub_le m 1))
  have hcast : ((m * (m - 1) / 2 : ℕ) : ℝ) ≤ (m : ℝ) ^ 2 := by
    rw [pow_two]
    exact_mod_cast hidx
  calc
    minkowskiSecondConstant m = (2 : ℝ) ^ (m * (m - 1) / 2) := rfl
    _ ≤ Real.exp 2 ^ (m * (m - 1) / 2) := by
      apply pow_le_pow_left₀ (by norm_num)
      linarith [Real.add_one_le_exp (2 : ℝ)]
    _ = Real.exp (((m * (m - 1) / 2 : ℕ) : ℝ) * 2) :=
      (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp (2 * (m : ℝ) ^ 2) := by
      apply Real.exp_le_exp.mpr
      linarith

lemma progression_size_factor_lower_bound (m : ℕ) (hm : 0 < m)
    {w δ : ℝ} (hδ : Real.exp (-w) ≤ δ) :
    Real.exp (-((m : ℝ) * w + 10 * (m : ℝ) ^ 2)) ≤
      (δ / (8 * m)) ^ m / minkowskiSecondConstant m := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hden : (0 : ℝ) < 8 * m := by positivity
  have hrecip : Real.exp (-(8 * m : ℝ)) ≤ (8 * m : ℝ)⁻¹ := by
    rw [Real.exp_neg]
    apply (inv_le_inv₀ (Real.exp_pos _) hden).2
    linarith [Real.add_one_le_exp (8 * m : ℝ)]
  have hbase : Real.exp (-(w + 8 * m)) ≤ δ / (8 * m) := by
    calc
      Real.exp (-(w + 8 * m)) = Real.exp (-w) * Real.exp (-(8 * m : ℝ)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ δ * (8 * m : ℝ)⁻¹ :=
        mul_le_mul hδ hrecip (Real.exp_pos _).le ((Real.exp_pos _).le.trans hδ)
      _ = δ / (8 * m) := by rw [div_eq_mul_inv]
  have hpower : Real.exp (-((m : ℝ) * w + 8 * (m : ℝ) ^ 2)) ≤
      (δ / (8 * m)) ^ m := by
    calc
      _ = Real.exp (-(w + 8 * m)) ^ m := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      _ ≤ _ := pow_le_pow_left₀ (Real.exp_pos _).le hbase _
  have hc : 0 < minkowskiSecondConstant m := by
    unfold minkowskiSecondConstant
    positivity
  have hinv : Real.exp (-(2 * (m : ℝ) ^ 2)) ≤ (minkowskiSecondConstant m)⁻¹ := by
    rw [Real.exp_neg]
    exact (inv_le_inv₀ (Real.exp_pos _) hc).2 (minkowskiSecondConstant_le_exp m)
  calc
    _ = Real.exp (-((m : ℝ) * w + 8 * (m : ℝ) ^ 2)) *
        Real.exp (-(2 * (m : ℝ) ^ 2)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ (δ / (8 * m)) ^ m * (minkowskiSecondConstant m)⁻¹ :=
      mul_le_mul hpower hinv (Real.exp_pos _).le ((Real.exp_pos _).le.trans hpower)
    _ = _ := by simp only [div_eq_mul_inv]

theorem exists_large_proper_progression {N : ℕ} [NeZero N]
    (B : CyclicBohr.Set N) (hB : 0 < B.radius) (hB1 : B.radius ≤ 1)
    (hN : 1 < N) {w : ℝ} (hwidth : Real.exp (-w) ≤ B.radius) :
    ∃ Q : CyclicCenteredGAP N,
      Q.rank = B.rank + 1 ∧ Q.Proper ∧ Q.carrier ⊆ B.carrier ∧
      Real.exp (-(((B.rank : ℝ) + 1) * w + 10 * ((B.rank : ℝ) + 1) ^ 2)) * N ≤
        (Q.carrier.card : ℝ) := by
  obtain ⟨Q, hr, hQ, hsub, hcard⟩ := exists_proper_progression_subset B hB hB1 hN
  refine ⟨Q, hr, hQ, hsub, ?_⟩
  have hfactor := progression_size_factor_lower_bound (B.rank + 1) (by omega) hwidth
  push_cast at hfactor
  calc
    _ ≤ ((B.radius / (8 * ((B.rank : ℝ) + 1))) ^ (B.rank + 1) /
        minkowskiSecondConstant (B.rank + 1)) * N :=
      mul_le_mul_of_nonneg_right hfactor (Nat.cast_nonneg N)
    _ = _ := by ring
    _ ≤ _ := hcard

end Erdos3.BohrProgression

end

section

namespace Erdos3.BohrProgression

namespace CyclicCenteredGAP

def zero (N : ℕ) : CyclicCenteredGAP N where
  rank := 0
  step := Fin.elim0
  radius := Fin.elim0

lemma zero_proper (N : ℕ) : (zero N).Proper := by
  intro x y _
  funext i
  exact Fin.elim0 i

@[simp] lemma zero_carrier (N : ℕ) : (zero N).carrier = {0} := by
  have heval : (zero N).eval = fun _ => 0 := by
    funext x
    unfold eval
    exact Finset.sum_eq_zero fun i _ => Fin.elim0 i
  rw [carrier, heval]
  exact Finset.image_const ⟨(fun i => Fin.elim0 i), Finset.mem_univ _⟩ 0

end CyclicCenteredGAP

theorem exists_large_proper_progression_all {N : ℕ} [NeZero N]
    (B : CyclicBohr.Set N) (hB : 0 < B.radius) (hB1 : B.radius ≤ 1)
    {w : ℝ} (hw : 0 ≤ w) (hwidth : Real.exp (-w) ≤ B.radius) :
    ∃ Q : CyclicCenteredGAP N,
      Q.rank ≤ B.rank + 1 ∧ Q.Proper ∧ Q.carrier ⊆ B.carrier ∧
      Real.exp (-(((B.rank : ℝ) + 1) * w + 10 * ((B.rank : ℝ) + 1) ^ 2)) * N ≤
        (Q.carrier.card : ℝ) := by
  by_cases hN : 1 < N
  · obtain ⟨Q, hr, hQ, hsub, hcard⟩ := exists_large_proper_progression B hB hB1 hN hwidth
    exact ⟨Q, hr.le, hQ, hsub, hcard⟩
  · have hNeq : N = 1 := by have := NeZero.pos N; omega
    subst N
    refine ⟨CyclicCenteredGAP.zero 1, by simp [CyclicCenteredGAP.zero],
      CyclicCenteredGAP.zero_proper 1, ?_, ?_⟩
    · intro x hx
      rw [CyclicCenteredGAP.zero_carrier, Finset.mem_singleton] at hx
      subst x
      exact B.zero_mem
    · simp only [CyclicCenteredGAP.zero_carrier, Finset.card_singleton, Nat.cast_one,
        mul_one]
      apply Real.exp_le_one_iff.mpr
      have : 0 ≤ ((B.rank : ℝ) + 1) * w + 10 * ((B.rank : ℝ) + 1) ^ 2 := by positivity
      linarith

theorem exists_proper_progression_of_quartic_bounds {N : ℕ} [NeZero N]
    (B : CyclicBohr.Set N) {C p : ℝ} (hC : 0 ≤ C) (hp : 0 ≤ p)
    (hB : 0 < B.radius) (hB1 : B.radius ≤ 1)
    (hrank : (B.rank : ℝ) ≤ 1 + C * (p + 1) ^ 4)
    (hwidth : Real.exp (-(C * (p + 1))) ≤ B.radius) :
    ∃ Q : CyclicCenteredGAP N,
      (Q.rank : ℝ) ≤ 2 + C * (p + 1) ^ 4 ∧ Q.Proper ∧ Q.carrier ⊆ B.carrier ∧
      Real.exp (-(11 * (C + 2) ^ 2 * (p + 1) ^ 8)) * N ≤ (Q.carrier.card : ℝ) := by
  obtain ⟨Q, hr, hQ, hsub, hcard⟩ := exists_large_proper_progression_all B hB hB1
    (by positivity : 0 ≤ C * (p + 1)) hwidth
  have hrR : (Q.rank : ℝ) ≤ B.rank + 1 := by exact_mod_cast hr
  refine ⟨Q, by linarith, hQ, hsub, ?_⟩
  let u := p + 1
  let m := (B.rank : ℝ) + 1
  have hu : 1 ≤ u := by dsimp [u]; linarith
  have hu4 : 1 ≤ u ^ 4 := one_le_pow₀ hu
  have huu4 : u ≤ u ^ 4 := by
    simpa only [pow_one] using pow_le_pow_right₀ hu (by decide : 1 ≤ (4 : ℕ))
  have hm0 : 0 ≤ m := by dsimp [m]; positivity
  have hm : m ≤ (C + 2) * u ^ 4 := by dsimp [m]; nlinarith
  have hw : C * u ≤ (C + 2) * u ^ 4 := by nlinarith
  have hprod : m * (C * u) ≤ ((C + 2) * u ^ 4) ^ 2 := by
    simpa only [pow_two] using mul_le_mul hm hw (by positivity : 0 ≤ C * u)
      (by positivity : 0 ≤ (C + 2) * u ^ 4)
  have hsquare : m ^ 2 ≤ ((C + 2) * u ^ 4) ^ 2 :=
    pow_le_pow_left₀ hm0 hm 2
  have hcost : m * (C * u) + 10 * m ^ 2 ≤ 11 * (C + 2) ^ 2 * u ^ 8 := by
    calc
      _ ≤ 11 * ((C + 2) * u ^ 4) ^ 2 := by linarith
      _ = _ := by ring
  apply le_trans (b := Real.exp (-(m * (C * u) + 10 * m ^ 2)) * N) ?_ hcard
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg N)
  apply Real.exp_le_exp.mpr
  linarith

end Erdos3.BohrProgression

end

end OAI
