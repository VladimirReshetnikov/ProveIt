import OAI.Combinatorics.Progressions.Polynomial.PolynomialShearAffineExponential

namespace OAI

section

namespace Erdos3

open MvPolynomial

variable {σ R : Type*} [CommRing R]

noncomputable def weightedPolynomialEndDrop (w : σ → ℕ) (s k : ℕ) :
    Submodule R (Module.End R (weightedSupportLE (R := R) w s)) where
  carrier := {F | ∀ n r (P : weightedSupportLE (R := R) w s),
    (P : MvPolynomial σ R) ∈ weightedSupportDrop w n r →
      (F P : MvPolynomial σ R) ∈ weightedSupportDrop w n (r + k)}
  zero_mem' := fun n r _P _h => (weightedSupportDrop w n (r + k)).zero_mem
  add_mem' := fun hF hG n r P h => (weightedSupportDrop w n (r + k)).add_mem
    (hF n r P h) (hG n r P h)
  smul_mem' := fun c _F hF n r P h => (weightedSupportDrop w n (r + k)).smul_mem c
    (hF n r P h)

theorem weightedPolynomialEndDrop_antitone (w : σ → ℕ) (s : ℕ) :
    Antitone (weightedPolynomialEndDrop (R := R) w s) := by
  intro a b hab F hF n r P hP
  exact weightedSupportDrop_antitone (Nat.add_le_add_left hab r) (hF n r P hP)

theorem weightedPolynomialEndDrop_mul (w : σ → ℕ) (s a b : ℕ)
    {F G : Module.End R (weightedSupportLE (R := R) w s)}
    (hF : F ∈ weightedPolynomialEndDrop w s a) (hG : G ∈ weightedPolynomialEndDrop w s b) :
    F * G ∈ weightedPolynomialEndDrop w s (a + b) := by
  intro n r P hP
  have h := hF n (r + b) (G P) (hG n r P hP)
  change (F (G P) : MvPolynomial σ R) ∈ weightedSupportDrop w n (r + (a + b))
  simpa only [Nat.add_assoc, Nat.add_comm b a] using h

theorem weightedPolynomialEndDrop_one (w : σ → ℕ) (s : ℕ) :
    (1 : Module.End R (weightedSupportLE (R := R) w s)) ∈ weightedPolynomialEndDrop w s 0 := by
  intro n r P hP
  change (P : MvPolynomial σ R) ∈ weightedSupportDrop w n (r + 0)
  simpa only [Nat.add_zero] using hP

theorem weightedPolynomialEndDrop_terminal (w : σ → ℕ) (s : ℕ)
    {F : Module.End R (weightedSupportLE (R := R) w s)}
    (hF : F ∈ weightedPolynomialEndDrop w s (s + 1)) : F = 0 := by
  apply LinearMap.ext
  intro P
  apply Subtype.ext
  have h := hF s 0 P (by simpa only [weightedSupportDrop_zero] using P.property)
  exact weightedSupportDrop_eq_zero (by omega) h

noncomputable def weightedPolynomialEndAlgebra (w : σ → ℕ) (s : ℕ) :
    Subalgebra R (Module.End R (weightedSupportLE (R := R) w s)) :=
  (weightedPolynomialEndDrop w s 0).toSubalgebra (weightedPolynomialEndDrop_one w s)
    (fun _ _ hF hG => weightedPolynomialEndDrop_mul w s 0 0 hF hG)

noncomputable instance weightedPolynomialEndAlgebraRing (w : σ → ℕ) (s : ℕ) :
    Ring (weightedPolynomialEndAlgebra (R := R) w s) :=
  @Subalgebra.toRing R (Module.End R (weightedSupportLE (R := R) w s)) _ _ _
    (weightedPolynomialEndAlgebra w s)

theorem polynomialShearEnd_mem_drop (w : σ → ℕ) (s k : ℕ)
    {D : PolynomialShearLieAlgebra w R} (hD : D ∈ polynomialShearLayer (R := R) w k) :
    polynomialShearEnd D s ∈ weightedPolynomialEndDrop w s k := by
  intro n r P hP
  exact weightedDerivation_apply w D.val k hD hP

noncomputable def weightedPolynomialEndLayer (w : σ → ℕ) (s k : ℕ) :
    Submodule ℚ (weightedPolynomialEndAlgebra (R := ℚ) w s) :=
  (weightedPolynomialEndDrop w s k).comap (weightedPolynomialEndAlgebra w s).val.toLinearMap

noncomputable def weightedPolynomialEndFiltration (w : σ → ℕ) (s : ℕ) :
    NilpotentAlgebraFiltration (weightedPolynomialEndAlgebra (R := ℚ) w s) s where
  layer := weightedPolynomialEndLayer w s
  antitone := by
    intro a b hab F hF
    exact weightedPolynomialEndDrop_antitone w s hab hF
  zero_eq_top := by
    apply top_unique
    intro F hF
    exact F.property
  mul_mem := by
    intro a b F G hF hG
    exact weightedPolynomialEndDrop_mul w s a b hF hG
  terminal := by
    apply bot_unique
    intro F hF
    change F = 0
    exact Subtype.ext (weightedPolynomialEndDrop_terminal w s hF)

end Erdos3

end

end OAI
