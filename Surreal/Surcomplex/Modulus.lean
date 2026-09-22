import Surreal.Foundations.SignSequenceRoots
import Surreal.Surcomplex.TopologicalField
import Surreal.Algebra.Geometry

/-!
# The actual surreal-valued surcomplex modulus

The genetic square-root theorem supplies the precise hypothesis needed
by the existing ordered quadratic geometry. This instantiates all of
`a:prop:triangle`, the area clause of `trigonometry:thm:heron`, and the
inequality clause of `trigonometry:thm:ptolemy` on the concrete surcomplex
field, without assuming the still separate real-closedness theorem.

The modulus-ball neighborhood and entourage bases identify this actual
modulus with the previously constructed fine topology and uniformity.
No real-valued norm or metric is introduced.
-/

universe u

namespace Surreal.Foundations.SignSequence

/-- The required square-root property follows from the genetic construction. -/
instance signSequenceHasNonnegSquareRoots : HasNonnegSquareRoots SignSequence.{u} where
  exists_nonneg_sq := exists_nonneg_sq _

end Surreal.Foundations.SignSequence

namespace Surreal.Surcomplex

open Foundations Set Filter Topology Uniformity

noncomputable section

/-- The nonnegative square root of the actual norm square, valued in surreals. -/
def modulus (z : Surcomplex.{u}) : SignSequence.{u} := Complexify.modulus z

theorem modulus_nonneg (z : Surcomplex.{u}) : 0 ≤ modulus z :=
  Complexify.modulus_nonneg z

@[simp] theorem modulus_sq (z : Surcomplex.{u}) : modulus z ^ 2 = normSq z :=
  Complexify.modulus_sq z

theorem modulus_eq_of_nonneg_sq {z : Surcomplex.{u}} {r : SignSequence.{u}}
    (hr : 0 ≤ r) (hsq : r ^ 2 = normSq z) : modulus z = r :=
  Complexify.modulus_eq_of_nonneg_sq hr hsq

@[simp] theorem modulus_zero : modulus (0 : Surcomplex.{u}) = 0 := Complexify.modulus_zero
@[simp] theorem modulus_one : modulus (1 : Surcomplex.{u}) = 1 := Complexify.modulus_one
@[simp] theorem modulus_I : modulus (I : Surcomplex.{u}) = 1 := Complexify.modulus_I

@[simp] theorem modulus_eq_zero_iff (z : Surcomplex.{u}) : modulus z = 0 ↔ z = 0 :=
  Complexify.modulus_eq_zero_iff z

theorem modulus_pos {z : Surcomplex.{u}} (hz : z ≠ 0) : 0 < modulus z :=
  Complexify.modulus_pos hz

@[simp] theorem modulus_conj (z : Surcomplex.{u}) : modulus (conj z) = modulus z :=
  Complexify.modulus_conj z

@[simp] theorem modulus_neg (z : Surcomplex.{u}) : modulus (-z) = modulus z :=
  Complexify.modulus_neg z

@[simp] theorem modulus_ofReal (x : SignSequence.{u}) : modulus (ofReal x) = |x| :=
  Complexify.modulus_algebraMap x

theorem modulus_mul (z w : Surcomplex.{u}) : modulus (z * w) = modulus z * modulus w :=
  Complexify.modulus_mul z w

theorem modulus_add_le (z w : Surcomplex.{u}) : modulus (z + w) ≤ modulus z + modulus w :=
  Complexify.modulus_add_le z w

theorem abs_re_le_modulus (z : Surcomplex.{u}) : |z.re| ≤ modulus z :=
  Complexify.abs_re_le_modulus z

theorem abs_im_le_modulus (z : Surcomplex.{u}) : |z.im| ≤ modulus z :=
  Complexify.abs_im_le_modulus z

/-- The modulus form of inversion, including the field's zero convention. -/
theorem inv_eq_modulus (z : Surcomplex.{u}) : z⁻¹ = (modulus z ^ 2)⁻¹ • conj z :=
  Complexify.inv_eq_modulus z

theorem modulus_add_eq_iff_pos_quotient {z w : Surcomplex.{u}} (hz : z ≠ 0) (hw : w ≠ 0) :
    modulus (z + w) = modulus z + modulus w ↔
      ∃ r : SignSequence.{u}, 0 < r ∧ z / w = ofReal r :=
  by simpa only [modulus, ofReal, add_comm] using Complexify.modulus_add_eq_iff_pos_quotient hw hz

/-- Ptolemy's inequality for the actual surreal-valued lengths. -/
theorem ptolemy (a b c d : Surcomplex.{u}) :
    modulus (a - c) * modulus (b - d) ≤
      modulus (a - b) * modulus (c - d) + modulus (a - d) * modulus (b - c) :=
  Complexify.ptolemy a b c d

/-- The area of a surcomplex triangle with vertices `0`, `z`, `w`. -/
def triangleArea (z w : Surcomplex.{u}) : SignSequence.{u} := Complexify.triangleArea z w

theorem triangleArea_nonneg (z w : Surcomplex.{u}) : 0 ≤ triangleArea z w :=
  Complexify.triangleArea_nonneg z w

/-- Heron's area identity on the concrete surcomplex field, including
degenerate triangles; radius and angle claims remain separate. -/
theorem heron (z w : Surcomplex.{u}) :
    let a := modulus (z - w)
    let b := modulus w
    let c := modulus z
    let s := (a + b + c) / 2
    triangleArea z w ^ 2 = s * (s - a) * (s - b) * (s - c) :=
  Complexify.heron z w

/-- For nonnegative radii, the square comparison is exactly the modulus comparison. -/
theorem modulus_lt_iff_normSq_lt_sq {z : Surcomplex.{u}} {r : SignSequence.{u}} (hr : 0 ≤ r) :
    modulus z < r ↔ normSq z < r ^ 2 := by
  rw [← modulus_sq]
  exact (sq_lt_sq₀ (modulus_nonneg z) hr).symm

/-- The previously constructed squared-radius ball is the actual modulus ball. -/
theorem fineBall_eq_modulus (a : Surcomplex.{u}) {r : SignSequence.{u}} (hr : 0 < r) :
    fineBall a r = {z | modulus (z - a) < r} := by
  ext z
  exact (modulus_lt_iff_normSq_lt_sq hr.le).symm

/-- Positive surreal modulus balls generate the native fine topology. -/
theorem nhds_hasBasis_modulus (a : Surcomplex.{u}) :
    (𝓝 a).HasBasis (fun r : SignSequence.{u} => 0 < r)
      (fun r => {z : Surcomplex.{u} | modulus (z - a) < r}) := by
  apply (nhds_hasBasis_fineBall a).to_hasBasis
  · intro r hr
    exact ⟨r, hr, (fineBall_eq_modulus a hr).ge⟩
  · intro r hr
    exact ⟨r, hr, (fineBall_eq_modulus a hr).le⟩

/-- Positive surreal modulus tolerances also generate the native Cauchy uniformity. -/
theorem uniformity_hasBasis_modulus_sub :
    (𝓤 Surcomplex.{u}).HasBasis (fun r : SignSequence.{u} => 0 < r)
      (fun r => {p : Surcomplex.{u} × Surcomplex.{u} | modulus (p.1 - p.2) < r}) := by
  apply uniformity_hasBasis_normSq_sub.to_hasBasis
  · intro r hr
    exact ⟨r, hr, fun _ hp => (modulus_lt_iff_normSq_lt_sq hr.le).mp hp⟩
  · intro r hr
    exact ⟨r, hr, fun _ hp => (modulus_lt_iff_normSq_lt_sq hr.le).mpr hp⟩

/-- The reverse triangle estimate uses the same surreal-valued modulus. -/
theorem abs_sub_modulus_le (z w : Surcomplex.{u}) :
    |modulus z - modulus w| ≤ modulus (z - w) := by
  have hz := modulus_add_le (z - w) w
  have hw := modulus_add_le (w - z) z
  have hsymm : modulus (w - z) = modulus (z - w) := by
    rw [← neg_sub z w, modulus_neg]
  rw [sub_add_cancel] at hz hw
  rw [hsymm] at hw
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The actual modulus is continuous into the native surreal order topology. -/
@[continuity] theorem continuous_modulus :
    Continuous (modulus : Surcomplex.{u} → SignSequence.{u}) := by
  apply continuous_iff_continuousAt.mpr
  intro a
  apply (SignSequence.nhds_hasBasis_abs_sub (modulus a)).tendsto_right_iff.mpr
  intro r hr
  have hball : ∀ᶠ z in 𝓝 a, modulus (z - a) < r := (nhds_hasBasis_modulus a).mem_of_mem hr
  exact hball.mono
    (fun z hz => (abs_sub_modulus_le z a).trans_lt hz)

end

end Surreal.Surcomplex
