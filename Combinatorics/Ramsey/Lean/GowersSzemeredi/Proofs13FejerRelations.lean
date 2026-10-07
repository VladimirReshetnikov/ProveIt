import GowersSzemeredi.Proofs13FejerKernel
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Expect

/-! Exact finite Fourier expansion of products of Fejer weights. The mean
over two scalar seeds counts the simultaneous feature and phase relations. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

def fejerPairRelation {N L : Nat} {I : Type*} [Fintype I] [DecidableEq I]
    (v : I → Fin L × Fin L) (w : I → ZMod N) : ZMod N :=
  ∑ i, ((v i).1 - (v i).2 : ZMod N) * w i

private theorem fejer_prod_exponential {N : Nat} [NeZero N]
    {I : Type*} [Fintype I] (f : I → ZMod N) :
    ∏ i, exponential (f i) = exponential (∑ i, f i) := by
  classical
  symm
  induction (Finset.univ : Finset I) using Finset.induction_on with
  | empty => simp [exponential]
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi]
      rw [show exponential (f i + ∑ x ∈ s, f x) =
        exponential (f i) * exponential (∑ x ∈ s, f x) from
        AddChar.map_add_eq_mul (ZMod.stdAddChar (N := N)) _ _, ih]

theorem finiteFejerKernel_product_expansion {N L : Nat} [NeZero N]
    {I : Type*} [Fintype I] [DecidableEq I] (phi feature : I → ZMod N) (a b : ZMod N) :
    (∏ i, (finiteFejerKernel L (a * phi i + b * feature i) : Complex)) =
      (((L : Complex) ^ 2)⁻¹) ^ Fintype.card I *
        ∑ v : I → Fin L × Fin L,
          exponential (a * fejerPairRelation v phi + b * fejerPairRelation v feature) := by
  classical
  have hpair (x : ZMod N) : (finiteFejerKernel L x : Complex) =
      ((L : Complex) ^ 2)⁻¹ * ∑ p : Fin L × Fin L,
        exponential (((p.1 : ZMod N) - (p.2 : ZMod N)) * x) := by
    rw [finiteFejerKernel_expansion, Fintype.sum_prod_type]
  simp_rw [hpair]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.prod_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro v _
  rw [fejer_prod_exponential]
  congr 1
  simp only [fejerPairRelation, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem fejer_expect_exponential_mul {N : Nat} [NeZero N] (x : ZMod N) :
    (𝔼 u : ZMod N, exponential (x * u)) = if x = 0 then 1 else 0 := by
  have hs : (∑ u : ZMod N, exponential (x * u)) = if x = 0 then (N : Complex) else 0 := by
    simpa [exponential, mul_comm] using AddChar.sum_mulShift x (ZMod.isPrimitive_stdAddChar N)
  rw [Finset.expect_eq_sum_div_card, Finset.card_univ, ZMod.card, hs]
  split_ifs <;> simp [NeZero.ne N]

theorem fejer_seed_orthogonality {N : Nat} [NeZero N] (x y : ZMod N) :
    (𝔼 c : ZMod N × ZMod N, exponential (c.1 * x + c.2 * y)) =
      if x = 0 ∧ y = 0 then 1 else 0 := by
  rw [← Finset.univ_product_univ, Finset.expect_product]
  have hadd (s t : ZMod N) : exponential (s + t) = exponential s * exponential t :=
    AddChar.map_add_eq_mul (ZMod.stdAddChar (N := N)) s t
  simp_rw [hadd, ← Finset.mul_expect, ← Finset.expect_mul]
  simp_rw [mul_comm _ x, mul_comm _ y, fejer_expect_exponential_mul]
  split_ifs <;> simp_all

theorem finiteFejerKernel_mean_product {N L : Nat} [NeZero N]
    {I : Type*} [Fintype I] [DecidableEq I] (phi feature : I → ZMod N) :
    (𝔼 c : ZMod N × ZMod N,
      ∏ i, (finiteFejerKernel L (c.1 * phi i + c.2 * feature i) : Complex)) =
      (((L : Complex) ^ 2)⁻¹) ^ Fintype.card I *
        (countWhere (fun v : I → Fin L × Fin L =>
          fejerPairRelation v phi = 0 ∧ fejerPairRelation v feature = 0) : Complex) := by
  classical
  simp_rw [finiteFejerKernel_product_expansion]
  rw [← Finset.mul_expect, Finset.expect_sum_comm]
  simp_rw [fejer_seed_orthogonality]
  congr 1
  simp only [countWhere, Finset.cast_card, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro v _
  split_ifs <;> simp_all

theorem finiteFejerKernel_mean_product_real {N L : Nat} [NeZero N]
    {I : Type*} [Fintype I] [DecidableEq I] (phi feature : I → ZMod N) :
    (𝔼 c : ZMod N × ZMod N,
      ∏ i, finiteFejerKernel L (c.1 * phi i + c.2 * feature i)) =
      (((L : Real) ^ 2)⁻¹) ^ Fintype.card I *
        (countWhere (fun v : I → Fin L × Fin L =>
          fejerPairRelation v phi = 0 ∧ fejerPairRelation v feature = 0) : Real) := by
  apply Complex.ofReal_injective
  change Complex.ofRealHom _ = Complex.ofRealHom _
  rw [map_expect Complex.ofRealHom]
  simp only [map_prod, map_mul, map_pow, map_inv₀, map_natCast]
  exact finiteFejerKernel_mean_product phi feature

end LeanProofs.GowersSzemeredi
