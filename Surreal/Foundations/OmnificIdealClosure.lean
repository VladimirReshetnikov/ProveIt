import Surreal.Algebra.IdealCongruenceClosure
import Surreal.Foundations.OmnificCongruenceTopology
import Surreal.Foundations.OmnificSmallQuotients

/-!
# Finite-congruence closure of every omnific ideal

The full assertion `osq:thm:closure`, for ideals of the actual omnific ring.
The manuscript's intersection agrees with native topological closure and
equals the inverse image of the ideal of integer constant coefficients.
-/

universe u
namespace Surreal.Foundations.SignSequence
noncomputable section

/-- The finite-congruence closure defined by all positive ordinary integer moduli. -/
def omnificFiniteCongruenceClosure (J : Ideal OmnificInteger.{u}) : Ideal OmnificInteger :=
  ⨅ n : {n : ℕ // 0 < n}, J ⊔ omnificCongruenceIdeal n

/-- Every positive ordinary congruence ideal contains the purely infinite ideal. -/
theorem omnificPurelyInfiniteIdeal_le_congruence (n : {n : ℕ // 0 < n}) :
    omnificPurelyInfiniteIdeal.{u} ≤ omnificCongruenceIdeal n := by
  rw [← iInf_omnific_int_multiples]
  exact iInf_le _ n

/-- Taking all finite congruences adds exactly the purely infinite ideal. -/
theorem omnificFiniteCongruenceClosure_eq_sup (J : Ideal OmnificInteger.{u}) :
    omnificFiniteCongruenceClosure J = J ⊔ omnificPurelyInfiniteIdeal := by
  apply le_antisymm
  · by_cases hzero : J.map omnificConstantCoeff = ⊥
    · have hJ : J ≤ omnificPurelyInfiniteIdeal :=
        (Ideal.map_eq_bot_iff_le_ker omnificConstantCoeff).mp hzero
      rw [sup_eq_right.mpr hJ, ← iInf_omnific_int_multiples]
      apply le_iInf
      intro n
      exact (iInf_le _ n).trans (sup_le
        (hJ.trans (omnificPurelyInfiniteIdeal_le_congruence n)) le_rfl)
    · let d := Ideal.absNorm (J.map omnificConstantCoeff)
      have hd : d ≠ 0 := by
        intro hz
        have he := Int.ideal_span_absNorm_eq_self (J.map omnificConstantCoeff)
        change Ideal.span ({(d : ℤ)} : Set ℤ) = J.map omnificConstantCoeff at he
        rw [hz, Int.natCast_zero, Ideal.span_singleton_eq_bot.mpr rfl] at he
        exact hzero he.symm
      let n : {n : ℕ // 0 < n} := ⟨d, Nat.pos_of_ne_zero hd⟩
      apply (iInf_le _ n).trans
      apply sup_le le_sup_left
      rw [sup_comm, ← omnific_comap_map_constant]
      apply Ideal.span_le.mpr
      intro x hx
      obtain rfl := Set.mem_singleton_iff.mp hx
      change omnificConstantCoeff (omnificIntCast (d : ℤ)) ∈ J.map omnificConstantCoeff
      rw [omnificConstantCoeff_intCast, ← Int.ideal_span_absNorm_eq_self (J.map omnificConstantCoeff)]
      exact Ideal.mem_span_singleton_self _
  · apply le_iInf
    intro n
    exact sup_le_sup_left (omnificPurelyInfiniteIdeal_le_congruence n) J

/-- The closure is precisely the inverse image of the ordinary constant ideal. -/
theorem omnificFiniteCongruenceClosure_eq_comap (J : Ideal OmnificInteger.{u}) :
    omnificFiniteCongruenceClosure J = (J.map omnificConstantCoeff).comap omnificConstantCoeff := by
  rw [omnificFiniteCongruenceClosure_eq_sup, omnific_comap_map_constant, sup_comm]

/-- For a specified ordinary image ideal, the manuscript's displayed closure formula holds. -/
theorem omnificFiniteCongruenceClosure_eq_modulus (J : Ideal OmnificInteger.{u}) (d : ℕ)
    (hd : J.map omnificConstantCoeff = Ideal.span {(d : ℤ)}) :
    omnificFiniteCongruenceClosure J = (Ideal.span {(d : ℤ)}).comap omnificConstantCoeff := by
  rw [omnificFiniteCongruenceClosure_eq_comap, hd]

/-- The algebraic intersection is the native closure in the omnific congruence topology. -/
theorem omnificCongruenceTopology_closure_ideal (J : Ideal OmnificInteger.{u}) :
    @closure OmnificInteger omnificCongruenceTopology (J : Set OmnificInteger) =
      (omnificFiniteCongruenceClosure J : Set OmnificInteger) :=
  IdealCongruenceTopology.closure_ideal omnificCongruenceIdeal omnificCongruenceIdeal_directed J

/-- Finite-congruence density is equivalent to having every ordinary integer constant. -/
theorem omnificFiniteCongruenceClosure_eq_top_iff (J : Ideal OmnificInteger.{u}) :
    omnificFiniteCongruenceClosure J = ⊤ ↔ J.map omnificConstantCoeff = ⊤ := by
  rw [omnificFiniteCongruenceClosure_eq_comap, Ideal.comap_eq_top_iff]

/-- The same criterion characterizes native topological density. -/
theorem omnificCongruenceTopology_dense_iff (J : Ideal OmnificInteger.{u}) :
    @Dense OmnificInteger omnificCongruenceTopology (J : Set OmnificInteger) ↔
      J.map omnificConstantCoeff = ⊤ := by
  letI := omnificCongruenceTopology.{u}
  rw [dense_iff_closure_eq, omnificCongruenceTopology_closure_ideal]
  change (omnificFiniteCongruenceClosure J : Set OmnificInteger) =
    (⊤ : Ideal OmnificInteger) ↔ _
  rw [SetLike.coe_set_eq, omnificFiniteCongruenceClosure_eq_top_iff]

/-- The zero ideal has purely infinite finite-congruence closure. -/
theorem omnificFiniteCongruenceClosure_bot :
    omnificFiniteCongruenceClosure (⊥ : Ideal OmnificInteger.{u}) = omnificPurelyInfiniteIdeal := by
  rw [omnificFiniteCongruenceClosure_eq_sup, bot_sup_eq]

end
end Surreal.Foundations.SignSequence
