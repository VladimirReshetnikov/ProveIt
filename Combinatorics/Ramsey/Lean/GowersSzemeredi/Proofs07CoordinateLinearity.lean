import GowersSzemeredi.Sections06_07

/-! Progression-coordinate affine maps need not be affine in the ambient
integer variable modulo the target modulus. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def IntAmbientLinearOn {N : Nat} (P : IntAP) (A : Finset Int)
    (phi : Int → ZMod N) : Prop :=
  ∃ a b : ZMod N, ∀ x ∈ P.carrier, x ∈ A → phi x = a * (x : ZMod N) + b

theorem progression_coordinate_linearity_counterexample :
    ∃ R : IntAP, ∃ phi : Int → ZMod 3,
      R.IsProper ∧ IntAPLinearOn R R.carrier phi ∧ ¬ IntAmbientLinearOn R R.carrier phi := by
  classical
  let R : IntAP := ⟨0, 3, 2⟩
  let phi : Int → ZMod 3 := fun x ↦ if x = 3 then 1 else 0
  have hcar : R.carrier = {0, 3} := by
    simp [R, IntAP.carrier, Fin.univ_succ]
  have hR : R.IsProper := by
    refine ⟨by norm_num [R], ?_⟩
    change R.carrier.card = 2
    rw [hcar]
    norm_num
  have hlinear : IntAPLinearOn R R.carrier phi := by
    refine ⟨1, 0, fun i _ ↦ ?_⟩
    fin_cases i <;> norm_num [R, phi]
  refine ⟨R, phi, hR, hlinear, ?_⟩
  rintro ⟨a, b, hab⟩
  have h0 : (0 : Int) ∈ R.carrier := by rw [hcar]; simp
  have h3 : (3 : Int) ∈ R.carrier := by rw [hcar]; simp
  have e0 := hab 0 h0 h0
  have e3 := hab 3 h3 h3
  norm_num [phi] at e0 e3
  have hz : (3 : ZMod 3) = 0 := by decide
  rw [hz, mul_zero, zero_add] at e3
  exact zero_ne_one (e0.trans e3.symm)

end LeanProofs.GowersSzemeredi
