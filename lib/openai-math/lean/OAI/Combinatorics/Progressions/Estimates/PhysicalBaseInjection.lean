import OAI.Combinatorics.Progressions.Lattices.AffineOneSiteNormalizedLaw

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

theorem physicalAffineSite_baseArrayJoin_apply {K I : Type*} [Fintype K]
    (root : K → ℤ) (tail : K × I → ℤ) (base : I → ℤ) (i : I) :
    physicalAffineSite root (baseArrayJoin tail base) i =
      (base i : ℝ) + ∑ k, (root k : ℝ) * (tail (k,i) : ℝ) := by
  simp only [physicalAffineSite, integerSiteValue, Fintype.sum_option, Finset.sum_apply,
    baseArrayJoin, zsmul_eq_mul, Pi.mul_apply, Pi.intCast_apply, Int.cast_one, one_mul]

theorem physicalAffineSite_base_injective {K I : Type*} [Fintype K]
    (root : K → ℤ) (tail : K × I → ℤ) :
    Function.Injective (fun base => physicalAffineSite root (baseArrayJoin tail base)) := by
  intro b c he
  funext i
  have h := congrFun he i
  simp only [physicalAffineSite_baseArrayJoin_apply] at h
  exact_mod_cast add_right_cancel h

theorem residueLatticeArray_baseArrayJoin {K I : Type*}
    (residue : Option K × I → ℤ) (modulus : I → ℕ) (tail : K × I → ℤ) (base : I → ℤ) :
    residueLatticeArray residue modulus (baseArrayJoin tail base) =
      baseArrayJoin (fun k => residue (some k.1,k.2) + (modulus k.2 : ℤ)*tail k)
        (fun i => residue (none,i) + (modulus i : ℤ)*base i) := by
  funext z
  rcases z with ⟨k,i⟩
  cases k <;> rfl

theorem physicalAffineSite_residue_base_injective {K I : Type*} [Fintype K]
    (root : K → ℤ) (residue : Option K × I → ℤ)
    (modulus : I → ℕ) (hmodulus : ∀ i, 0 < modulus i) (tail : K × I → ℤ) :
    Function.Injective (fun base =>
      physicalAffineSite root (residueLatticeArray residue modulus (baseArrayJoin tail base))) := by
  intro b c he
  funext i
  have h := congrFun he i
  simp only [residueLatticeArray_baseArrayJoin, physicalAffineSite_baseArrayJoin_apply] at h
  have hb : residue (none,i) + (modulus i : ℤ)*b i =
      residue (none,i) + (modulus i : ℤ)*c i := by exact_mod_cast add_right_cancel h
  exact mul_left_cancel₀ (by exact_mod_cast (hmodulus i).ne' : (modulus i : ℤ) ≠ 0)
    (add_left_cancel hb)

end Erdos3.BooleanCubeKernel

end

end OAI
