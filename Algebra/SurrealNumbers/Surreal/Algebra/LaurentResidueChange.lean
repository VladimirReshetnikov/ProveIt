import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Tactic.LinearCombination
import Surreal.Surcomplex.Basic

/-!
# Formal residue calculus in `K((X))`

This file formalizes the formal residue calculus of
`docs/surcomplex/analysis/article.tex`, Section "Formal residues in `K((X))`":
`b:formalprimitive`, `b:reschange`, `b:localargument`, the first clause of `b:formalres`,
and the formal identity of `b:lagrange`. The source field is `K = No[i]`; every result is
proved for an arbitrary field (of characteristic zero where division by integers is used).
The main results are then instantiated at the actual surcomplex numbers
`Surreal.Surcomplex`: `surcomplex_residue_derivative`, `surcomplex_exists_derivative_eq_iff`,
`surcomplex_residue_derivative_div`, `surcomplex_residue_comp_mul_derivative_of_eq`,
`surcomplex_residue_comp_mul_derivative_of_coeff_one`, `surcomplex_lagrange_burmann` and
`surcomplex_lagrange_burmann_inverse`. The remaining generic statements (for example
`residueQuotientEquiv`, `residue_derivative_div_single_mul` for the source form `F = X^m U`,
`residue_comp_mul_derivative`, `lagrange_burmann` and `lagrange_burmann_substInv`) have no
separate `surcomplex_*` version; they apply at `K = Surreal.Surcomplex` as stated.

The Laurent field is Mathlib's `K⸨X⸩ = HahnSeries ℤ K`, the residue `Res_{X=0}` is the
coefficient of `X⁻¹` (`residue`), and `d/dX` is Mathlib's `LaurentSeries.derivative`. The
Leibniz rule is proved here (`derivative_mul`), which packages `d/dX` as a `K`-derivation.

* `b:formalres`, first clause: `residue_derivative`, over any field.
* `b:formalprimitive`: `exists_derivative_eq_iff` (a primitive exists iff the residue is
  zero, the primitive being the termwise one) and `residueQuotientEquiv`, the isomorphism
  `K((X)) dX / d K((X)) ≃ K` induced by the residue, sending the class of `dX/X` to `1`.
* `b:localargument`: `residue_derivative_div_single_mul` for `F = X^m U`, `U(0) ≠ 0`,
  `m ∈ ℤ`, and `residue_derivative_div` for every nonzero `F`, with `m` its order.
* `b:reschange`: for a power series `g` the composition `A(g(X))` is `comp A g`, defined as
  `g^a P(g)` for `A = X^a P` with `a` the order of `A`. For `g(0) = 0`, `g ≠ 0` it does not
  depend on the representation (`comp_single_mul`) and is a ring endomorphism extending
  power-series substitution (`compRingHom`). The change of variables
  `Res A(g(X)) g'(X) dX = m Res A(Y) dY` holds with `m` the order of `g`
  (`residue_comp_mul_derivative`), in the source form `g = c X^m u`, `c ≠ 0`, `m ≥ 1`,
  `u(0) = 1` (`residue_comp_mul_derivative_of_eq`), and for `m = 1`
  (`residue_comp_mul_derivative_of_coeff_one`).
* `b:lagrange`, formal identity: for `F = a_1 X + ⋯` with `a_1 ≠ 0` and any `G` with
  `G(0) = 0` and `G(F(X)) = X`, `[Y^n] H(G(Y)) = (1/n) [X^{n-1}] H'(X) (X/F(X))^n` for `n ≥ 1`
  (`lagrange_burmann` in `K((X))`, `lagrange_burmann_powerSeries` with `X/F` the power series
  `(a_1 + a_2 X + ⋯)⁻¹`), its case `H = X` (`lagrange_burmann_inverse`), and the version with
  the inverse supplied by Mathlib's `PowerSeries.substInvOfIsUnit`
  (`lagrange_burmann_substInv`).

Pending, none of it formalized here:
* the removability clause of `b:formalres` (a finite-meromorphic germ bounded on a small
  punctured fine ball has zero principal part), which needs the realization theorem
  `b:realization` and estimates on small fine balls;
* the claim of `b:lagrange` that the identities hold for realized germ-analytic germs, which
  needs `b:realization` and the inverse function theorem `b:inverse`;
* the identification of this formal residue with the actual local residue of a Laurent germ
  (`b:residue-discipline`);
* the formal Cauchy identity `b:eq-formalCauchy` in `K((X))[[Y]]`.
-/

universe u

namespace Surreal.LaurentResidue

open PowerSeries HahnSeries
open scoped LaurentSeries

noncomputable section

variable {K : Type*} [Field K]

/-- The formal residue `Res_{X=0}`: the coefficient of `X⁻¹` of a Laurent series. -/
def residue : K⸨X⸩ →ₗ[K] K where
  toFun f := f.coeff (-1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The residue is the coefficient of `X⁻¹`. -/
@[simp] theorem residue_apply (f : K⸨X⸩) : residue f = f.coeff (-1) := rfl

/-- A power series has zero residue. -/
@[simp] theorem residue_ofPowerSeries (P : K⟦X⟧) :
    residue (ofPowerSeries ℤ K P) = 0 := by
  rw [residue_apply, PowerSeries.coeff_coe, if_pos (by norm_num)]

/-- The Laurent derivative maps a power series to its power-series derivative. -/
theorem derivative_ofPowerSeries (P : K⟦X⟧) :
    LaurentSeries.derivative K (ofPowerSeries ℤ K P) = ofPowerSeries ℤ K (d⁄dX K P) := by
  ext n
  rw [LaurentSeries.derivative_apply, LaurentSeries.hasseDeriv_coeff, Nat.cast_one,
    Ring.choose_one_right, PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  rcases n with k | k
  · rw [Int.ofNat_eq_natCast, if_neg (by lia), if_neg (by lia), coeff_derivative, zsmul_eq_mul,
      show ((k : ℤ) + 1).natAbs = k + 1 by lia, show (k : ℤ).natAbs = k by lia]
    push_cast
    ring
  · rw [if_pos (Int.negSucc_lt_zero k)]
    rcases k with _ | k
    · simp
    · rw [if_pos (by lia), smul_zero]

/-- Differentiating after multiplying by a monomial. -/
theorem derivative_single_mul (a : ℤ) (f : K⸨X⸩) :
    LaurentSeries.derivative K (single a 1 * f) =
      single a 1 * (LaurentSeries.derivative K f + (a : K⸨X⸩) * single (-1) 1 * f) := by
  ext n
  rw [LaurentSeries.derivative_apply, LaurentSeries.hasseDeriv_coeff, coeff_single_mul,
    coeff_single_mul, one_mul, one_mul, coeff_add, LaurentSeries.derivative_apply,
    LaurentSeries.hasseDeriv_coeff, mul_assoc, ← map_intCast (HahnSeries.C (R := K) (Γ := ℤ)),
    C_mul_eq_smul, HahnSeries.coeff_smul, coeff_single_mul, one_mul, Nat.cast_one,
    Ring.choose_one_right, Ring.choose_one_right, zsmul_eq_mul, zsmul_eq_mul, smul_eq_mul]
  have h1 : n + 1 - a = n - a + 1 := by ring
  have h2 : n - a - -1 = n - a + 1 := by ring
  rw [h1, h2]
  push_cast
  ring

/-- Every Laurent series is a monomial `X^a` times a power series. -/
theorem exists_single_mul (f : K⸨X⸩) :
    ∃ (a : ℤ) (P : K⟦X⟧), f = single a 1 * ofPowerSeries ℤ K P :=
  ⟨f.order, f.powerSeriesPart, (LaurentSeries.single_order_mul_powerSeriesPart f).symm⟩

/-- The derivative of `X^a P`: `X^a (P' + a X⁻¹ P)`. -/
theorem derivative_single_mul_ofPowerSeries (a : ℤ) (P : K⟦X⟧) :
    LaurentSeries.derivative K (single a 1 * ofPowerSeries ℤ K P) =
      single a 1 * (ofPowerSeries ℤ K (d⁄dX K P) +
        (a : K⸨X⸩) * single (-1) 1 * ofPowerSeries ℤ K P) := by
  rw [derivative_single_mul, derivative_ofPowerSeries]

/-- The Leibniz rule for the Laurent derivative. -/
theorem derivative_mul (f g : K⸨X⸩) :
    LaurentSeries.derivative K (f * g) =
      f * LaurentSeries.derivative K g + g * LaurentSeries.derivative K f := by
  obtain ⟨a, P, rfl⟩ := exists_single_mul f
  obtain ⟨b, Q, rfl⟩ := exists_single_mul g
  have hab : (single (a + b) 1 : K⸨X⸩) = single a 1 * single b 1 := by
    rw [single_mul_single, mul_one]
  have hfg : single a 1 * ofPowerSeries ℤ K P * (single b 1 * ofPowerSeries ℤ K Q) =
      single (a + b) 1 * ofPowerSeries ℤ K (P * Q) := by
    rw [hab, map_mul]
    ring
  rw [hfg, derivative_single_mul_ofPowerSeries, derivative_single_mul_ofPowerSeries,
    derivative_single_mul_ofPowerSeries, Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add,
    map_mul, map_mul, map_mul, hab]
  push_cast
  ring

/-- The formal derivative `d/dX` on `K((X))` as a `K`-linear map; its underlying function is
Mathlib's `LaurentSeries.derivative K`. -/
def derivativeₗ : K⸨X⸩ →ₗ[K] K⸨X⸩ where
  toFun := LaurentSeries.derivative K
  map_add' f g := (LaurentSeries.derivative K).map_add f g
  map_smul' r f := (LaurentSeries.derivative K).map_smul r f

/-- The linear map `derivativeₗ` is `LaurentSeries.derivative`. -/
@[simp] theorem derivativeₗ_apply (f : K⸨X⸩) :
    derivativeₗ f = LaurentSeries.derivative K f := rfl

/-- The formal derivative `d/dX` on `K((X))`, packaged as a `K`-derivation. -/
def derivation : Derivation K K⸨X⸩ K⸨X⸩ where
  toFun := LaurentSeries.derivative K
  map_add' f g := (LaurentSeries.derivative K).map_add f g
  map_smul' r f := by
    ext n
    rw [Algebra.smul_def r f, HahnSeries.algebraMap_apply', PowerSeries.algebraMap_eq,
      ofPowerSeries_C, HahnSeries.C_mul_eq_smul]
    simp only [LaurentSeries.derivative_apply, LaurentSeries.hasseDeriv_coeff,
      HahnSeries.coeff_smul, RingHom.id_apply, smul_eq_mul, zsmul_eq_mul]
    ring
  map_one_eq_zero' := by
    change LaurentSeries.derivative K 1 = 0
    rw [← map_one (ofPowerSeries ℤ K), derivative_ofPowerSeries, Derivation.map_one_eq_zero,
      map_zero]
  leibniz' f g := by
    change LaurentSeries.derivative K (f * g) =
      f • LaurentSeries.derivative K g + g • LaurentSeries.derivative K f
    rw [smul_eq_mul, smul_eq_mul]
    exact derivative_mul f g

/-- The derivation `derivation` is `LaurentSeries.derivative`. -/
@[simp] theorem derivation_apply (f : K⸨X⸩) :
    derivation f = LaurentSeries.derivative K f := rfl

/-- `b:formalres`, first clause: the residue of a derivative is zero. -/
theorem residue_derivative (f : K⸨X⸩) : residue (LaurentSeries.derivative K f) = 0 := by
  rw [residue_apply, LaurentSeries.derivative_apply,
    LaurentSeries.hasseDeriv_coeff, Nat.cast_one, Ring.choose_one_right, neg_add_cancel,
    zero_smul]

/-- The residue of a monomial `c X^a`. -/
@[simp] theorem residue_single (a : ℤ) (c : K) :
    residue (single a c : K⸨X⸩) = if a = -1 then c else 0 := by
  rw [residue_apply, coeff_single]
  simp only [eq_comm]

/-- The residue is onto `K`, attained by `c X⁻¹`. -/
theorem residue_surjective : Function.Surjective (residue (K := K)) := fun c =>
  ⟨single (-1) c, by rw [residue_single, if_pos rfl]⟩

/-- The coefficients of the termwise primitive vanish below `ord α + 1`. -/
theorem coeff_primitive_aux (α : K⸨X⸩) :
    BddBelow (Function.support fun n : ℤ => if n = 0 then 0 else α.coeff (n - 1) / n) := by
  refine ⟨α.order + 1, fun n hn => ?_⟩
  rw [Function.mem_support] at hn
  by_contra h
  apply hn
  rw [coeff_eq_zero_of_lt_order (by lia), zero_div, ite_self]

/-- The termwise primitive `∑_{n ≠ -1} a_n X^{n+1}/(n+1)` of `∑ a_n X^n`. -/
def primitive (α : K⸨X⸩) : K⸨X⸩ :=
  ofSuppBddBelow (fun n => if n = 0 then 0 else α.coeff (n - 1) / n) (coeff_primitive_aux α)

/-- The coefficients of the termwise primitive. -/
theorem coeff_primitive (α : K⸨X⸩) (n : ℤ) :
    (primitive α).coeff n = if n = 0 then 0 else α.coeff (n - 1) / n := rfl

section CharZero

variable [CharZero K]

/-- A Laurent series with zero residue is the derivative of its termwise primitive. -/
theorem derivative_primitive {α : K⸨X⸩} (h : residue α = 0) :
    LaurentSeries.derivative K (primitive α) = α := by
  ext n
  rw [LaurentSeries.derivative_apply, LaurentSeries.hasseDeriv_coeff,
    Nat.cast_one, Ring.choose_one_right, coeff_primitive]
  by_cases hn : n + 1 = 0
  · rw [if_pos hn, smul_zero]
    obtain rfl : n = -1 := by lia
    exact h.symm
  · rw [if_neg hn, add_sub_cancel_right, zsmul_eq_mul, mul_div_cancel₀]
    exact_mod_cast hn

/-- `b:formalprimitive`: a Laurent differential `α dX` has a primitive in `K((X))` if and
only if its residue vanishes. -/
theorem exists_derivative_eq_iff (α : K⸨X⸩) :
    (∃ f : K⸨X⸩, LaurentSeries.derivative K f = α) ↔ residue α = 0 := by
  constructor
  · rintro ⟨f, rfl⟩
    exact residue_derivative f
  · intro h
    exact ⟨primitive α, derivative_primitive h⟩

/-- The exact differentials are precisely the kernel of the residue. -/
theorem range_derivative_eq_ker_residue :
    LinearMap.range (derivativeₗ (K := K)) = LinearMap.ker (residue (K := K)) := by
  ext α
  rw [LinearMap.mem_range, LinearMap.mem_ker]
  exact exists_derivative_eq_iff α

/-- `b:formalprimitive`, second form: `K((X)) dX / d K((X)) ≃ K · dX/X`, the isomorphism being
the residue. -/
def residueQuotientEquiv :
    (K⸨X⸩ ⧸ LinearMap.range (derivativeₗ (K := K))) ≃ₗ[K] K :=
  (Submodule.quotEquivOfEq _ _ range_derivative_eq_ker_residue).trans
    (residue.quotKerEquivOfSurjective residue_surjective)

/-- The quotient isomorphism is the residue on representatives. -/
@[simp] theorem residueQuotientEquiv_mk (α : K⸨X⸩) :
    residueQuotientEquiv (Submodule.Quotient.mk α) = residue α := rfl

/-- The class of `dX/X` corresponds to `1`. -/
theorem residueQuotientEquiv_mk_single :
    residueQuotientEquiv (Submodule.Quotient.mk (single (-1) (1 : K))) = 1 := by
  rw [residueQuotientEquiv_mk, residue_single, if_pos rfl]

end CharZero

/-! ### Logarithmic derivatives and the local argument principle -/

/-- Multiplication by an integer scales the residue. -/
theorem residue_intCast_mul (m : ℤ) (f : K⸨X⸩) : residue ((m : K⸨X⸩) * f) = m * residue f := by
  rw [← map_intCast (HahnSeries.C (R := K) (Γ := ℤ)), C_mul_eq_smul, map_smul, smul_eq_mul]

/-- Multiplication by a constant scales the residue. -/
theorem residue_C_mul (c : K) (f : K⸨X⸩) : residue (HahnSeries.C c * f) = c * residue f := by
  rw [C_mul_eq_smul, map_smul, smul_eq_mul]

/-- `X^m U` with `U(0) ≠ 0` has order exactly `m`. -/
theorem order_single_mul_ofPowerSeries (m : ℤ) {U : K⟦X⟧} (hU : constantCoeff U ≠ 0) :
    (single m 1 * ofPowerSeries ℤ K U).order = m := by
  have hcoeff : ∀ n, (single m (1 : K) * ofPowerSeries ℤ K U).coeff n =
      (ofPowerSeries ℤ K U).coeff (n - m) := fun n => by
    rw [coeff_single_mul, one_mul]
  have hm : (single m (1 : K) * ofPowerSeries ℤ K U).coeff m ≠ 0 := by
    rwa [hcoeff, sub_self, PowerSeries.coeff_coe, if_neg (lt_irrefl 0), Int.natAbs_zero,
      coeff_zero_eq_constantCoeff_apply]
  have hne : single m (1 : K) * ofPowerSeries ℤ K U ≠ 0 := fun h => hm (by rw [h, coeff_zero])
  refine le_antisymm (order_le_of_coeff_ne_zero hm) ?_
  by_contra hlt
  apply coeff_order_eq_zero.not.2 hne
  rw [hcoeff, PowerSeries.coeff_coe, if_pos (by lia)]

/-- The Laurent image of a power-series unit is inverted by the power-series inverse. -/
theorem ofPowerSeries_inv {U : K⟦X⟧} (hU : constantCoeff U ≠ 0) :
    (ofPowerSeries ℤ K U)⁻¹ = ofPowerSeries ℤ K U⁻¹ := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← map_mul, PowerSeries.mul_inv_cancel U hU, map_one]

/-- `b:localargument` in the form `F = X^m U`, `U(0) ≠ 0`: `Res F'/F dX = m`. -/
theorem residue_derivative_div_single_mul (m : ℤ) {U : K⟦X⟧} (hU : constantCoeff U ≠ 0) :
    residue (LaurentSeries.derivative K (single m (1 : K) * ofPowerSeries ℤ K U) /
      (single m (1 : K) * ofPowerSeries ℤ K U)) = m := by
  have hs : (single m (1 : K) : K⸨X⸩) ≠ 0 := single_ne_zero one_ne_zero
  have hU0 : U ≠ 0 := fun h => hU (by rw [h, map_zero])
  have hU' : ofPowerSeries ℤ K U ≠ 0 := (map_ne_zero_iff _ ofPowerSeries_injective).2 hU0
  rw [derivative_single_mul_ofPowerSeries, mul_div_mul_left _ _ hs, add_div, mul_div_assoc,
    div_self hU', mul_one, div_eq_mul_inv, ofPowerSeries_inv hU, ← map_mul, map_add,
    residue_ofPowerSeries, zero_add, residue_intCast_mul, residue_single,
    if_pos rfl, mul_one]

/-- `b:localargument`: for every nonzero Laurent series `F`, `Res F'/F dX` is the order of `F`,
a zero order when positive and minus a pole order when negative. -/
theorem residue_derivative_div (F : K⸨X⸩) (hF : F ≠ 0) :
    residue (LaurentSeries.derivative K F / F) = F.order := by
  have hU : constantCoeff F.powerSeriesPart ≠ 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, LaurentSeries.powerSeriesPart_coeff, Nat.cast_zero,
      add_zero]
    exact coeff_order_eq_zero.not.2 hF
  have h := residue_derivative_div_single_mul F.order hU
  rwa [LaurentSeries.single_order_mul_powerSeriesPart] at h

/-- For `j ≠ -1`, the differential `f^j df` is exact, hence has zero residue. -/
theorem residue_zpow_mul_derivative [CharZero K] (f : K⸨X⸩) {j : ℤ} (hj : j ≠ -1) :
    residue (f ^ j * LaurentSeries.derivative K f) = 0 := by
  have h := residue_derivative (f ^ (j + 1))
  rw [← derivation_apply, Derivation.leibniz_zpow, add_sub_cancel_right, smul_eq_mul,
    map_zsmul, derivation_apply, zsmul_eq_mul, mul_eq_zero, Int.cast_eq_zero] at h
  rcases h with h | h
  · exact absurd (by lia : j = -1) hj
  · exact h

/-- The residue of `f^j df` for a nonzero `f`: it is `ord f` for `j = -1` and zero otherwise. -/
theorem residue_zpow_mul_derivative_eq [CharZero K] {f : K⸨X⸩} (hf : f ≠ 0) (j : ℤ) :
    residue (f ^ j * LaurentSeries.derivative K f) = f.order * residue (single j (1 : K)) := by
  rw [residue_single]
  by_cases hj : j = -1
  · subst hj
    rw [if_pos rfl, mul_one, zpow_neg_one, inv_mul_eq_div]
    exact residue_derivative_div f hf
  · rw [if_neg hj, mul_zero]
    exact residue_zpow_mul_derivative f hj

/-! ### Composition with a power series -/

/-- The composition `A(g(X))` of a Laurent series `A` with a power series `g`: writing
`A = X^a P` with `a` the order of `A` and `P(0) ≠ 0` (for `A ≠ 0`; `comp 0 g = 0`), it is
`g^a · P(g)`. It is the
substitution of Laurent series when `g(0) = 0` and `g ≠ 0`; see `comp_single_mul`. -/
def comp (A : K⸨X⸩) (g : K⟦X⟧) : K⸨X⸩ :=
  ofPowerSeries ℤ K g ^ A.order * ofPowerSeries ℤ K (A.powerSeriesPart.subst g)

/-- Every Laurent series is `X^{-N}` times a power series for some natural `N`. -/
theorem exists_single_neg_mul (A : K⸨X⸩) :
    ∃ (N : ℕ) (B : K⟦X⟧), A = single (-(N : ℤ)) 1 * ofPowerSeries ℤ K B := by
  obtain ⟨a, P, rfl⟩ := exists_single_mul A
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg a
  · refine ⟨0, X ^ n * P, ?_⟩
    rw [Nat.cast_zero, neg_zero, single_zero_one, one_mul, map_mul, ofPowerSeries_X_pow]
  · exact ⟨n, P, rfl⟩

/-- Independence of the representation: for any way of writing `A = X^a P`, the composition
`A(g(X))` is `g^a · P(g)`. -/
theorem comp_single_mul {g : K⟦X⟧} (hg0 : constantCoeff g = 0) (hg : g ≠ 0) (a : ℤ)
    (P : K⟦X⟧) :
    comp (single a 1 * ofPowerSeries ℤ K P) g =
      ofPowerSeries ℤ K g ^ a * ofPowerSeries ℤ K (P.subst g) := by
  have hG : ofPowerSeries ℤ K g ≠ 0 := (map_ne_zero_iff _ ofPowerSeries_injective).2 hg
  have hsub : HasSubst g := HasSubst.of_constantCoeff_zero' hg0
  have hs : (single a (1 : K) : K⸨X⸩) ≠ 0 := single_ne_zero one_ne_zero
  by_cases hP : P = 0
  · subst hP
    have h0 : ((0 : K⟦X⟧).subst g : K⟦X⟧) = 0 := by rw [← coe_substAlgHom hsub, map_zero]
    simp [comp, h0]
  obtain ⟨A, hA⟩ : ∃ A : K⸨X⸩, A = single a (1 : K) * ofPowerSeries ℤ K P := ⟨_, rfl⟩
  rw [← hA]
  have hA0 : A ≠ 0 := by
    rw [hA]
    exact mul_ne_zero hs ((map_ne_zero_iff _ ofPowerSeries_injective).2 hP)
  have hcoeff : ∀ n, A.coeff n = (ofPowerSeries ℤ K P).coeff (n - a) := fun n => by
    rw [hA, coeff_single_mul, one_mul]
  have hle : a ≤ A.order := by
    by_contra hlt
    apply coeff_order_eq_zero.not.2 hA0
    rw [hcoeff, PowerSeries.coeff_coe, if_pos (by lia)]
  obtain ⟨k, hk⟩ : ∃ k : ℕ, A.order = a + k := ⟨(A.order - a).toNat, by lia⟩
  have hPQ : P = X ^ k * A.powerSeriesPart := by
    apply ofPowerSeries_injective (Γ := ℤ)
    calc ofPowerSeries ℤ K P = single (-a) 1 * A := by
          rw [hA, ← mul_assoc, single_mul_single, neg_add_cancel, mul_one, single_zero_one,
            one_mul]
      _ = single (-a) 1 * (single (a + k) 1 * ofPowerSeries ℤ K A.powerSeriesPart) := by
          rw [← hk, LaurentSeries.single_order_mul_powerSeriesPart]
      _ = ofPowerSeries ℤ K (X ^ k * A.powerSeriesPart) := by
          rw [← mul_assoc, single_mul_single, mul_one, map_mul, ofPowerSeries_X_pow,
            neg_add_cancel_left]
  rw [comp, hPQ, subst_mul hsub, subst_pow hsub, subst_X hsub, map_mul, map_pow, ← mul_assoc,
    ← zpow_natCast, ← zpow_add₀ hG, ← hk]

/-- Composition restricts to substitution on power series. -/
theorem comp_ofPowerSeries {g : K⟦X⟧} (hg0 : constantCoeff g = 0) (hg : g ≠ 0) (P : K⟦X⟧) :
    comp (ofPowerSeries ℤ K P) g = ofPowerSeries ℤ K (P.subst g) := by
  have h := comp_single_mul hg0 hg 0 P
  rwa [single_zero_one, one_mul, zpow_zero, one_mul] at h

/-- Composition sends the monomial `X^a` to `g^a`. -/
theorem comp_single {g : K⟦X⟧} (hg0 : constantCoeff g = 0) (hg : g ≠ 0) (a : ℤ) :
    comp (single a (1 : K)) g = ofPowerSeries ℤ K g ^ a := by
  have hsub : HasSubst g := HasSubst.of_constantCoeff_zero' hg0
  have h := comp_single_mul hg0 hg a 1
  have h1 : ((1 : K⟦X⟧).subst g : K⟦X⟧) = 1 := by rw [← coe_substAlgHom hsub, map_one]
  rwa [(ofPowerSeries ℤ K).map_one, mul_one, h1, (ofPowerSeries ℤ K).map_one, mul_one] at h

/-- Raising the pole order of a representation: `X^{-N} P = X^{-(N+M)} (X^M P)`. -/
theorem single_neg_mul_eq (N M : ℕ) (P : K⟦X⟧) :
    single (-(N : ℤ)) (1 : K) * ofPowerSeries ℤ K P =
      single (-((N + M : ℕ) : ℤ)) 1 * ofPowerSeries ℤ K (X ^ M * P) := by
  rw [map_mul, ofPowerSeries_X_pow, ← mul_assoc, single_mul_single, mul_one,
    show -((N + M : ℕ) : ℤ) + (M : ℤ) = -(N : ℤ) by push_cast; ring]

/-- Composition with `g` is additive. -/
theorem comp_add {g : K⟦X⟧} (hg0 : constantCoeff g = 0) (hg : g ≠ 0) (A B : K⸨X⸩) :
    comp (A + B) g = comp A g + comp B g := by
  have hsub : HasSubst g := HasSubst.of_constantCoeff_zero' hg0
  obtain ⟨N, P, rfl⟩ := exists_single_neg_mul A
  obtain ⟨M, Q, rfl⟩ := exists_single_neg_mul B
  rw [single_neg_mul_eq N M P, single_neg_mul_eq M N Q, Nat.add_comm M N, ← mul_add,
    ← map_add (ofPowerSeries ℤ K), comp_single_mul hg0 hg, comp_single_mul hg0 hg,
    comp_single_mul hg0 hg, subst_add hsub, map_add, mul_add]

/-- Composition with `g` is multiplicative. -/
theorem comp_mul {g : K⟦X⟧} (hg0 : constantCoeff g = 0) (hg : g ≠ 0) (A B : K⸨X⸩) :
    comp (A * B) g = comp A g * comp B g := by
  have hsub : HasSubst g := HasSubst.of_constantCoeff_zero' hg0
  have hG : ofPowerSeries ℤ K g ≠ 0 := (map_ne_zero_iff _ ofPowerSeries_injective).2 hg
  obtain ⟨a, P, rfl⟩ := exists_single_mul A
  obtain ⟨b, Q, rfl⟩ := exists_single_mul B
  have hab : (single (a + b) 1 : K⸨X⸩) = single a 1 * single b 1 := by
    rw [single_mul_single, mul_one]
  have e : single a (1 : K) * ofPowerSeries ℤ K P * (single b 1 * ofPowerSeries ℤ K Q) =
      single (a + b) 1 * ofPowerSeries ℤ K (P * Q) := by
    rw [hab, map_mul]
    ring
  rw [e, comp_single_mul hg0 hg, comp_single_mul hg0 hg, comp_single_mul hg0 hg,
    subst_mul hsub, map_mul, zpow_add₀ hG]
  ring

/-- The Laurent substitution `A(Y) ↦ A(g(X))` for `g(0) = 0`, `g ≠ 0`, as a ring endomorphism of
`K((X))`; it extends power-series substitution and sends `X` to `g`. -/
def compRingHom {g : K⟦X⟧} (hg0 : constantCoeff g = 0) (hg : g ≠ 0) : K⸨X⸩ →+* K⸨X⸩ where
  toFun A := comp A g
  map_one' := by
    have h := comp_single hg0 hg 0
    rwa [single_zero_one, zpow_zero] at h
  map_mul' A B := comp_mul hg0 hg A B
  map_zero' := by
    have h := comp_ofPowerSeries hg0 hg 0
    have h0 : ((0 : K⟦X⟧).subst g : K⟦X⟧) = 0 := by
      rw [← coe_substAlgHom (HasSubst.of_constantCoeff_zero' hg0), map_zero]
    rwa [map_zero, h0, map_zero] at h
  map_add' A B := comp_add hg0 hg A B

/-- The ring endomorphism `compRingHom` is `comp`. -/
@[simp] theorem compRingHom_apply {g : K⟦X⟧} (hg0 : constantCoeff g = 0) (hg : g ≠ 0)
    (A : K⸨X⸩) : compRingHom hg0 hg A = comp A g := rfl

/-- A power series without constant term is `X` times its shift. -/
theorem ofPowerSeries_eq_single_one_mul {F : K⟦X⟧} (hF0 : constantCoeff F = 0) :
    ofPowerSeries ℤ K F =
      single 1 1 * ofPowerSeries ℤ K (PowerSeries.mk fun p => coeff (p + 1) F) := by
  conv_lhs => rw [eq_X_mul_shift_add_const F, hF0, map_zero, add_zero]
  rw [map_mul, ofPowerSeries_X]

/-- The shift `a_1 + a_2 X + ⋯` of `F` has constant coefficient `a_1`. -/
theorem constantCoeff_shift (F : K⟦X⟧) :
    constantCoeff (PowerSeries.mk fun p => coeff (p + 1) F) = coeff 1 F := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_mk, zero_add]

/-- A local coordinate `F = a_1 X + a_2 X^2 + ⋯` with `a_1 ≠ 0` has order one. -/
theorem order_ofPowerSeries_eq_one {F : K⟦X⟧} (hF0 : constantCoeff F = 0)
    (hF1 : coeff 1 F ≠ 0) : (ofPowerSeries ℤ K F).order = 1 := by
  rw [ofPowerSeries_eq_single_one_mul hF0, order_single_mul_ofPowerSeries]
  rwa [constantCoeff_shift]

/-- `X/F(X)` as a power series: the inverse of the shift `a_1 + a_2 X + ⋯` of `F`. -/
theorem single_one_div_ofPowerSeries {F : K⟦X⟧} (hF0 : constantCoeff F = 0)
    (hF1 : coeff 1 F ≠ 0) :
    single 1 (1 : K) / ofPowerSeries ℤ K F =
      ofPowerSeries ℤ K (PowerSeries.mk fun p => coeff (p + 1) F)⁻¹ := by
  rw [ofPowerSeries_eq_single_one_mul hF0, div_mul_cancel_left₀ (single_ne_zero one_ne_zero),
    ofPowerSeries_inv (by rwa [constantCoeff_shift])]

section CharZero

variable [CharZero K]

/-- The inductive core of `b:reschange`, for `A = X^{-N} B`. -/
theorem residue_comp_mul_derivative_aux {g : K⟦X⟧} (hg0 : constantCoeff g = 0) (hg : g ≠ 0)
    (N : ℕ) (B : K⟦X⟧) :
    residue (ofPowerSeries ℤ K g ^ (-(N : ℤ)) * ofPowerSeries ℤ K (B.subst g) *
        ofPowerSeries ℤ K (d⁄dX K g)) =
      (ofPowerSeries ℤ K g).order * residue (single (-(N : ℤ)) 1 * ofPowerSeries ℤ K B) := by
  have hG : ofPowerSeries ℤ K g ≠ 0 := (map_ne_zero_iff _ ofPowerSeries_injective).2 hg
  have hsub : HasSubst g := HasSubst.of_constantCoeff_zero' hg0
  induction N generalizing B with
  | zero =>
    rw [Nat.cast_zero, neg_zero, zpow_zero, one_mul, single_zero_one, one_mul, ← map_mul,
      residue_ofPowerSeries, residue_ofPowerSeries, mul_zero]
  | succ N ih =>
    obtain ⟨B₁, b, rfl⟩ : ∃ B₁ b, B = X * B₁ + PowerSeries.C b :=
      ⟨_, _, eq_X_mul_shift_add_const B⟩
    set G := ofPowerSeries ℤ K g
    have hGG : G ^ (-((N + 1 : ℕ) : ℤ)) * G = G ^ (-(N : ℤ)) := by
      rw [← zpow_add_one₀ hG]
      congr 1
      push_cast
      ring
    have hss : (single (-((N + 1 : ℕ) : ℤ)) (1 : K) : K⸨X⸩) * single 1 1 =
        single (-(N : ℤ)) 1 := by
      rw [single_mul_single, mul_one, show -((N + 1 : ℕ) : ℤ) + 1 = -(N : ℤ) by push_cast; ring]
    have hL : G ^ (-((N + 1 : ℕ) : ℤ)) *
        ofPowerSeries ℤ K ((X * B₁ + PowerSeries.C b).subst g) =
        G ^ (-(N : ℤ)) * ofPowerSeries ℤ K (B₁.subst g) +
          HahnSeries.C b * G ^ (-((N + 1 : ℕ) : ℤ)) := by
      rw [subst_add hsub, subst_mul hsub, subst_X hsub, subst_C, ← PowerSeries.C_apply, map_add,
        map_mul, ofPowerSeries_C, mul_add, ← mul_assoc, hGG]
      ring
    have hR : single (-((N + 1 : ℕ) : ℤ)) (1 : K) *
        ofPowerSeries ℤ K (X * B₁ + PowerSeries.C b) =
        single (-(N : ℤ)) 1 * ofPowerSeries ℤ K B₁ +
          HahnSeries.C b * single (-((N + 1 : ℕ) : ℤ)) 1 := by
      rw [map_add, map_mul, ofPowerSeries_X, ofPowerSeries_C, mul_add, ← mul_assoc, hss]
      ring
    rw [hL, hR, add_mul, map_add, map_add, ih, mul_assoc, residue_C_mul, residue_C_mul,
      ← derivative_ofPowerSeries, residue_zpow_mul_derivative_eq hG]
    ring

/-- `b:reschange`, general form: for a nonzero power series `g` with `g(0) = 0`, of order `m`,
and every Laurent series `A`, `Res_{X=0} A(g(X)) g'(X) dX = m · Res_{Y=0} A(Y) dY`. -/
theorem residue_comp_mul_derivative {g : K⟦X⟧} (hg0 : constantCoeff g = 0) (hg : g ≠ 0)
    (A : K⸨X⸩) :
    residue (comp A g * ofPowerSeries ℤ K (d⁄dX K g)) =
      (ofPowerSeries ℤ K g).order * residue A := by
  obtain ⟨N, B, rfl⟩ := exists_single_neg_mul A
  rw [comp_single_mul hg0 hg]
  exact residue_comp_mul_derivative_aux hg0 hg N B

/-- `b:reschange`: for `g(X) = c X^m (1 + O(X))` with `c ≠ 0` and `m ≥ 1`, and every
`A(Y) ∈ K((Y))`, `Res_{X=0} A(g(X)) g'(X) dX = m · Res_{Y=0} A(Y) dY`. -/
theorem residue_comp_mul_derivative_of_eq {g u : K⟦X⟧} {c : K} {m : ℕ} (hc : c ≠ 0)
    (hm : 1 ≤ m) (hu : constantCoeff u = 1) (hg : g = PowerSeries.C c * X ^ m * u)
    (A : K⸨X⸩) :
    residue (comp A g * ofPowerSeries ℤ K (d⁄dX K g)) = m * residue A := by
  have hU : constantCoeff (PowerSeries.C c * u) ≠ 0 := by
    rwa [map_mul, constantCoeff_C, hu, mul_one]
  have hG : ofPowerSeries ℤ K g =
      single (m : ℤ) 1 * ofPowerSeries ℤ K (PowerSeries.C c * u) := by
    rw [hg, map_mul, map_mul, map_mul, ofPowerSeries_X_pow]
    ring
  have hord : (ofPowerSeries ℤ K g).order = m := by
    rw [hG, order_single_mul_ofPowerSeries _ hU]
  have hg0 : constantCoeff g = 0 := by
    rw [hg, map_mul, map_mul, map_pow, constantCoeff_X, zero_pow (by lia), mul_zero, zero_mul]
  have hgne : g ≠ 0 := by
    intro h
    rw [h, map_zero, HahnSeries.order_zero] at hord
    lia
  rw [residue_comp_mul_derivative hg0 hgne, hord, Int.cast_natCast]

/-- `b:reschange`, the case `m = 1`: residues are invariant under an invertible local
coordinate change `g = a_1 X + a_2 X^2 + ⋯`, `a_1 ≠ 0`. -/
theorem residue_comp_mul_derivative_of_coeff_one {g : K⟦X⟧} (hg0 : constantCoeff g = 0)
    (hg1 : coeff 1 g ≠ 0) (A : K⸨X⸩) :
    residue (comp A g * ofPowerSeries ℤ K (d⁄dX K g)) = residue A := by
  have hgne : g ≠ 0 := fun h => hg1 (by rw [h, map_zero])
  rw [residue_comp_mul_derivative hg0 hgne, order_ofPowerSeries_eq_one hg0 hg1, Int.cast_one,
    one_mul]

/-! ### Lagrange–Bürmann inversion -/

/-- `b:lagrange`, formal identity. Let `F = a_1 X + a_2 X^2 + ⋯` with `a_1 ≠ 0` and let `G` be
a power series with `G(0) = 0` and `G(F(X)) = X`. For `n ≥ 1` and every `H ∈ K[[X]]`,
`[Y^n] H(G(Y)) = (1/n) [X^{n-1}] H'(X) (X/F(X))^n`, the right side computed in `K((X))`. -/
theorem lagrange_burmann {F G : K⟦X⟧} (hF0 : constantCoeff F = 0) (hF1 : coeff 1 F ≠ 0)
    (hG0 : constantCoeff G = 0) (hGF : G.subst F = X) (H : K⟦X⟧) {n : ℕ} (hn : 1 ≤ n) :
    coeff n (H.subst G) = (n : K)⁻¹ *
      (ofPowerSeries ℤ K (d⁄dX K H) * (single 1 1 / ofPowerSeries ℤ K F) ^ n).coeff
        ((n : ℤ) - 1) := by
  have hsubF : HasSubst F := HasSubst.of_constantCoeff_zero' hF0
  have hsubG : HasSubst G := HasSubst.of_constantCoeff_zero' hG0
  have hFne : F ≠ 0 := fun h => hF1 (by rw [h, map_zero])
  have hn0 : (n : K) ≠ 0 := by exact_mod_cast (by lia : n ≠ 0)
  -- Change of variables `Y = F(X)` with `m = 1`, applied to `A(Y) = H(G(Y)) Y^{-n-1}`.
  have h12 : coeff n (H.subst G) = residue (ofPowerSeries ℤ K F ^ (-(n : ℤ) - 1) *
      ofPowerSeries ℤ K H * ofPowerSeries ℤ K (d⁄dX K F)) := by
    have h := residue_comp_mul_derivative hF0 hFne
      (single (-(n : ℤ) - 1) 1 * ofPowerSeries ℤ K (H.subst G))
    rw [comp_single_mul hF0 hFne, subst_comp_subst_apply hsubG hsubF, hGF, X_subst,
      order_ofPowerSeries_eq_one hF0 hF1, Int.cast_one, one_mul] at h
    rw [h, residue_apply, coeff_single_mul, one_mul,
      show (-1 : ℤ) - (-(n : ℤ) - 1) = n by ring, ofPowerSeries_apply_coeff]
  -- The residue of `d(H F^{-n})` vanishes.
  have h3 : residue (ofPowerSeries ℤ K F ^ (-(n : ℤ)) * ofPowerSeries ℤ K (d⁄dX K H)) =
      n * residue (ofPowerSeries ℤ K F ^ (-(n : ℤ) - 1) * ofPowerSeries ℤ K H *
        ofPowerSeries ℤ K (d⁄dX K F)) := by
    have h := residue_derivative (ofPowerSeries ℤ K F ^ (-(n : ℤ)) * ofPowerSeries ℤ K H)
    rw [derivative_mul, derivative_ofPowerSeries,
      ← derivation_apply (ofPowerSeries ℤ K F ^ (-(n : ℤ))), Derivation.leibniz_zpow,
      derivation_apply, derivative_ofPowerSeries, smul_eq_mul, zsmul_eq_mul, map_add,
      show ∀ x y z c : K⸨X⸩, x * (c * (y * z)) = c * (y * x * z) from fun _ _ _ _ => by ring,
      residue_intCast_mul] at h
    push_cast at h
    linear_combination h
  -- `H'(X) (X/F)^n = X^n · F^{-n} H'(X)`.
  have h4 : (ofPowerSeries ℤ K (d⁄dX K H) * (single 1 1 / ofPowerSeries ℤ K F) ^ n).coeff
      ((n : ℤ) - 1) = residue (ofPowerSeries ℤ K F ^ (-(n : ℤ)) *
        ofPowerSeries ℤ K (d⁄dX K H)) := by
    have e : ofPowerSeries ℤ K (d⁄dX K H) * (single 1 (1 : K) / ofPowerSeries ℤ K F) ^ n =
        single (n : ℤ) 1 * (ofPowerSeries ℤ K F ^ (-(n : ℤ)) * ofPowerSeries ℤ K (d⁄dX K H)) := by
      rw [div_pow, ← ofPowerSeries_X, ← map_pow, ofPowerSeries_X_pow, zpow_neg, zpow_natCast,
        div_eq_mul_inv]
      ring
    rw [e, coeff_single_mul, one_mul, residue_apply, show (n : ℤ) - 1 - n = -1 by ring]
  rw [h12, h4, h3, ← mul_assoc, inv_mul_cancel₀ hn0, one_mul]

/-- `b:lagrange` in power-series form: `[Y^n] H(G(Y)) = (1/n) [X^{n-1}] H'(X) (X/F(X))^n`,
where `X/F(X)` is the power series `(a_1 + a_2 X + ⋯)⁻¹`. -/
theorem lagrange_burmann_powerSeries {F G : K⟦X⟧} (hF0 : constantCoeff F = 0)
    (hF1 : coeff 1 F ≠ 0) (hG0 : constantCoeff G = 0) (hGF : G.subst F = X) (H : K⟦X⟧)
    {n : ℕ} (hn : 1 ≤ n) :
    coeff n (H.subst G) =
      (n : K)⁻¹ * coeff (n - 1) (d⁄dX K H * (PowerSeries.mk fun p => coeff (p + 1) F)⁻¹ ^ n) := by
  rw [lagrange_burmann hF0 hF1 hG0 hGF H hn, single_one_div_ofPowerSeries hF0 hF1, ← map_pow,
    ← map_mul, show (n : ℤ) - 1 = ((n - 1 : ℕ) : ℤ) by lia, ofPowerSeries_apply_coeff]

/-- `b:lagrange`, the coefficients of the inverse: `[Y^n] G = (1/n) [X^{n-1}] (X/F(X))^n`. -/
theorem lagrange_burmann_inverse {F G : K⟦X⟧} (hF0 : constantCoeff F = 0)
    (hF1 : coeff 1 F ≠ 0) (hG0 : constantCoeff G = 0) (hGF : G.subst F = X) {n : ℕ}
    (hn : 1 ≤ n) :
    coeff n G = (n : K)⁻¹ * coeff (n - 1) ((PowerSeries.mk fun p => coeff (p + 1) F)⁻¹ ^ n) := by
  have h := lagrange_burmann_powerSeries hF0 hF1 hG0 hGF X hn
  rwa [subst_X (HasSubst.of_constantCoeff_zero' hG0), derivative_X, one_mul] at h

/-- `b:lagrange` with the compositional inverse supplied by Mathlib: `G = F^{-1}` exists as
`PowerSeries.substInvOfIsUnit`, and satisfies both `G(F(X)) = X` and `F(G(Y)) = Y`. -/
theorem lagrange_burmann_substInv {F : K⟦X⟧} (hF0 : constantCoeff F = 0)
    (hF1 : coeff 1 F ≠ 0) (H : K⟦X⟧) {n : ℕ} (hn : 1 ≤ n) :
    coeff n (H.subst (F.substInvOfIsUnit (isUnit_iff_ne_zero.2 hF1))) =
      (n : K)⁻¹ * coeff (n - 1) (d⁄dX K H * (PowerSeries.mk fun p => coeff (p + 1) F)⁻¹ ^ n) :=
  lagrange_burmann_powerSeries hF0 hF1 (constantCoeff_substInvOfIsUnit _ _)
    (subst_substInvOfIsUnit_left F hF0 _) H hn

end CharZero

/-! ### The actual surcomplex numbers `No[i]` -/

/-- `b:formalres`, first clause, over the actual surcomplex numbers `K = No[i]`: the residue of
a derivative is zero. -/
theorem surcomplex_residue_derivative (f : LaurentSeries Surcomplex.{u}) :
    residue (LaurentSeries.derivative Surcomplex.{u} f) = 0 :=
  residue_derivative f

/-- `b:formalprimitive` over the actual surcomplex numbers `K = No[i]`. -/
theorem surcomplex_exists_derivative_eq_iff (α : LaurentSeries Surcomplex.{u}) :
    (∃ f : LaurentSeries Surcomplex.{u}, LaurentSeries.derivative Surcomplex.{u} f = α) ↔
      residue α = 0 :=
  exists_derivative_eq_iff α

/-- `b:localargument` over the actual surcomplex numbers `K = No[i]`, for every nonzero `F`,
with `m` the order of `F`. -/
theorem surcomplex_residue_derivative_div (F : LaurentSeries Surcomplex.{u}) (hF : F ≠ 0) :
    residue (LaurentSeries.derivative Surcomplex.{u} F / F) = F.order :=
  residue_derivative_div F hF

/-- `b:reschange` over the actual surcomplex numbers `K = No[i]`. -/
theorem surcomplex_residue_comp_mul_derivative_of_eq {g u : PowerSeries Surcomplex.{u}}
    {c : Surcomplex.{u}} {m : ℕ} (hc : c ≠ 0) (hm : 1 ≤ m) (hu : constantCoeff u = 1)
    (hg : g = PowerSeries.C c * X ^ m * u) (A : LaurentSeries Surcomplex.{u}) :
    residue (comp A g * ofPowerSeries ℤ Surcomplex.{u} (d⁄dX Surcomplex.{u} g)) =
      m * residue A :=
  residue_comp_mul_derivative_of_eq hc hm hu hg A

/-- `b:reschange`, the case `m = 1`, over the actual surcomplex numbers `K = No[i]`: residues
are invariant under an invertible local coordinate change `g = a_1 X + a_2 X^2 + ⋯`. -/
theorem surcomplex_residue_comp_mul_derivative_of_coeff_one {g : PowerSeries Surcomplex.{u}}
    (hg0 : constantCoeff g = 0) (hg1 : coeff 1 g ≠ 0) (A : LaurentSeries Surcomplex.{u}) :
    residue (comp A g * ofPowerSeries ℤ Surcomplex.{u} (d⁄dX Surcomplex.{u} g)) = residue A :=
  residue_comp_mul_derivative_of_coeff_one hg0 hg1 A

/-- `b:lagrange`, formal identity, over the actual surcomplex numbers `K = No[i]`. -/
theorem surcomplex_lagrange_burmann {F G : PowerSeries Surcomplex.{u}}
    (hF0 : constantCoeff F = 0) (hF1 : coeff 1 F ≠ 0) (hG0 : constantCoeff G = 0)
    (hGF : G.subst F = X) (H : PowerSeries Surcomplex.{u}) {n : ℕ} (hn : 1 ≤ n) :
    coeff n (H.subst G) = (n : Surcomplex.{u})⁻¹ *
      coeff (n - 1) (d⁄dX Surcomplex.{u} H * (PowerSeries.mk fun p => coeff (p + 1) F)⁻¹ ^ n) :=
  lagrange_burmann_powerSeries hF0 hF1 hG0 hGF H hn

/-- `b:lagrange`, the coefficients of the inverse, over the actual surcomplex numbers
`K = No[i]`: `[Y^n] G = (1/n) [X^{n-1}] (X/F(X))^n`. -/
theorem surcomplex_lagrange_burmann_inverse {F G : PowerSeries Surcomplex.{u}}
    (hF0 : constantCoeff F = 0) (hF1 : coeff 1 F ≠ 0) (hG0 : constantCoeff G = 0)
    (hGF : G.subst F = X) {n : ℕ} (hn : 1 ≤ n) :
    coeff n G = (n : Surcomplex.{u})⁻¹ *
      coeff (n - 1) ((PowerSeries.mk fun p => coeff (p + 1) F)⁻¹ ^ n) :=
  lagrange_burmann_inverse hF0 hF1 hG0 hGF hn

end

end Surreal.LaurentResidue
