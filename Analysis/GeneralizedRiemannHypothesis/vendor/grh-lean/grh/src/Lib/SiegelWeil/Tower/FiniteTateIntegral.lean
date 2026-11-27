import Lib.ClassField.Avatar.HeckeBaseChange
import Lib.ClassField.HeckeCharacter.TameModulus
import Lib.SiegelWeil.Tower.RealConeIntegral

/-!
# Products of `L`-values and Tate's integral at the finite places

This file defines the product `L_*` of partial Hecke `L`-values of a split tame character and the
factor `L♯`, a single value `|L^S(z, ν)|` times powers of the `q_w`. It proves the recursions for
`L_*`, in which `L♯ ^ 2` is the factor. It defines the finite factor `New.Exchange.lineFinFactor` of
the datum along the line. For `x > 1` it computes Tate's integral over the finite ideles as a
partial `L`-value. It also proves a lemma that unfolds a sum over `Eˣ` against the integral over the
idele classes, in the variable `a` or `ā⁻¹` of either side of Poisson's formula.

## Main definitions and results

* `New.Exchange.lValueProd_succ`: The recursion `L_*(z + 1) = L♯(z + 1) ^ 2 * L_*(z)` for natural
  `z`.
* `New.Exchange.integral_finTateIntegrand`: For `x > 1` and a Haar measure `ρ`, Tate's integrand
  `finTateIntegrand 𝔠 x` over the finite ideles is integrable. It is the finite factor times the
  base change of `ν = 𝔠.character` times the `x`-th power of the module. Its integral is the partial
  `L`-value `L^S(x, ν)`, for `S = 𝔠.ramifiedPlaces`, times the `ρ`-volume of the unit ideles
  `idelesUnitOff ∅`.

Notions from other files:
* `𝔠 : SplitTameChar E μ` is a character `𝔠.character` of `[U(1)]` of positive weight `μ`, tamely
  ramified exactly on a finite set `𝔠.ramifiedPlaces` of places disjoint from its conjugate;
  `𝔠.semilocalChar` is `t ↦ ν(t / t̄)` on the product `LocProd 𝔠.ramifiedPlaces` of the completions
  at `𝔠.ramifiedPlaces`.

## Relation to the literature

Known; see `Lib.SiegelWeil.Tower.LargeSideConstantTerm` for sources.
-/

noncomputable section

namespace New.Exchange

open MeasureTheory Measure WeilData SemilocalField Space Fintype Real Complex Set
open NumberField (InfinitePlace)

section

variable {E : Type} [Field E] [CMType E] {μ : InfinitePlace E → ℤ} (𝔠 : SplitTameChar E μ)

/-! ### Products of `L`-values -/

/-- For a set `S` of finite places of `E`, with residue cardinalities `q_w`, and a character `ν` of
`[U(1)]`, the product `L_*(e) = ∏_{w ∈ S} q_w ^ (e ^ 2) ∏_{1 ≤ z ≤ e} |L^S(z, ν)| ^ 2`, where
`L^S(z, ν) = ν.L S z` is the Euler product of the base change of `ν` outside `S ∪ S̄`. -/
def lValueProd (S : Set (FinPlace E)) (ν : AutChar E) (e : ℕ) : ℝ :=
  (∏ᶠ w ∈ S, FinPlace.q w : ℕ) ^ e ^ 2 * ∏ z ∈ Finset.Icc 1 e, ‖ν.L S z‖ ^ 2

/-- `L_*(e)` for the character `𝔠.character` and its set `𝔠.ramifiedPlaces` of ramified places,
extended to every integer `e` by `L_*(-e) = L_*(e)⁻¹`. -/
def lValueProdInt (e : ℤ) : ℝ := lValueProd 𝔠.ramifiedPlaces 𝔠.character e.toNat / lValueProd
  𝔠.ramifiedPlaces 𝔠.character (-e).toNat

/-- `L♯(z) = |L^S(z, ν)| ∏_{w ∈ S} q_w ^ (z - 1/2)` for `ν = 𝔠.character` and
`S = 𝔠.ramifiedPlaces`. It is used only for `z ≥ 1`, as `𝔠.character.L` is an Euler product and not
its analytic continuation. -/
def lSharp (z : ℝ) : ℝ := ‖𝔠.character.L 𝔠.ramifiedPlaces z‖ * ∏ w : 𝔠.ramifiedPlaces,
  (w.val.q : ℝ) ^ (z - 1 / 2)

theorem SplitTameChar.weight_ne_zero (𝔠 : SplitTameChar E μ) : μ ≠ 0 := fun h ↦
  (𝔠.weight_pos (Classical.arbitrary _)).ne' (congrFun h _)

/-- The partial `L`-function of a split tame character has no zero on `[1, ∞)`, because the weight
of the character is not zero. -/
theorem SplitTameChar.L_ne_zero {z : ℝ} (hz : 1 ≤ z) : 𝔠.character.L 𝔠.ramifiedPlaces z ≠ 0 :=
  𝔠.hasWeight.L_ne_zero 𝔠.ramifiedPlaces.finite_toSet 𝔠.weight_ne_zero hz

theorem lSharp_pos {z : ℝ} (hz : 1 ≤ z) : 0 < lSharp 𝔠 z :=
  mul_pos (norm_pos_iff.2 (𝔠.L_ne_zero hz))
    (Finset.prod_pos fun w _ ↦ rpow_pos_of_pos (by simp [FinPlace.q_bounds]) _)

/-- The recursion `L_*(z + 1) = L♯(z + 1) ^ 2 * L_*(z)` for natural `z`. -/
theorem lValueProd_succ (z : ℕ) :
    lValueProd 𝔠.ramifiedPlaces 𝔠.character (z + 1) = lSharp 𝔠 (z + 1) ^ 2 * lValueProd
      𝔠.ramifiedPlaces 𝔠.character z := by
  let Q : ℝ := ∏ w : 𝔠.ramifiedPlaces, (w.val.q : ℝ)
  have h_norm : ((∏ᶠ w ∈ (𝔠.ramifiedPlaces : Set (FinPlace E)), FinPlace.q w : ℕ) : ℝ) = Q := by
    rw [finprod_mem_coe_finset, Nat.cast_prod, ← Finset.prod_coe_sort]
  have h_power : (Q ^ ((z : ℝ) + 1 - 1 / 2)) ^ 2 = Q ^ (2 * z + 1) := by
    rw [← rpow_mul_natCast (by positivity), ← rpow_natCast]
    grind
  rw [lValueProd, lValueProd, lSharp, finsetProd_rpow _ _ fun w _ ↦ Nat.cast_nonneg _, mul_pow,
    h_power, h_norm, Finset.prod_Icc_succ_top (by simp), Nat.cast_succ]
  ring

theorem lValueProd_pos (e : ℕ) : 0 < lValueProd 𝔠.ramifiedPlaces 𝔠.character e := by
  induction e with
  | zero => simp [lValueProd]
  | succ e ih => simp [lValueProd_succ, ih, pow_pos (lSharp_pos 𝔠 (z := e + 1) (by simp))]

theorem lValueProdInt_pos (e : ℤ) : 0 < lValueProdInt 𝔠 e :=
  div_pos (lValueProd_pos 𝔠 _) (lValueProd_pos 𝔠 _)

theorem lValueProdInt_natCast (z : ℕ) : lValueProdInt 𝔠 z = lValueProd 𝔠.ramifiedPlaces 𝔠.character
  z := by
  simp [lValueProdInt, lValueProd]

theorem lValueProdInt_neg_natCast (z : ℕ) :
    lValueProdInt 𝔠 (-z) = (lValueProd 𝔠.ramifiedPlaces 𝔠.character z)⁻¹ := by
  simp [lValueProdInt, lValueProd]

/-- For a split tame character `𝔠` of `[U(1)]` over the CM field `E`, with character
`ν = 𝔠.character` and ramified set `S = 𝔠.ramifiedPlaces`, this gives a recursion for every natural
`z`. The value `lValueProdInt 𝔠 (z + 1)`, written `L_*(z + 1)`, equals `L♯(z + 1)² · L_*(z)`. Here
`L♯(z) = |L^S(z, ν)| ∏_{w ∈ S} q_w ^ (z - 1/2)` is `lSharp 𝔠 z`, and `L_*` is extended to all
integers by `L_*(-e) = L_*(e)⁻¹`. -/
theorem lValueProdInt_succ (z : ℕ) :
    lValueProdInt 𝔠 (z + 1) = lSharp 𝔠 (z + 1) ^ 2 * lValueProdInt 𝔠 z := by
  rw [← Int.natCast_succ, lValueProdInt_natCast, lValueProdInt_natCast, lValueProd_succ]

/-- For natural `z`, `L_*(-z) = L♯(z + 1) ^ 2 * L_*(-z - 1)`, which computes `L_*` at the
nonpositive integers by downward recursion. Here `L_*` (`lValueProdInt`) is the value for the
character `𝔠.character` and its set `𝔠.ramifiedPlaces` of ramified places, extended to all integers
by `L_*(-e) = L_*(e)⁻¹`. Also `L♯(z) = |L^S(z, ν)| ∏_{w ∈ S} q_w ^ (z - 1/2)` (`lSharp`). -/
theorem lValueProdInt_neg (z : ℕ) :
    lValueProdInt 𝔠 (-z) = lSharp 𝔠 (z + 1) ^ 2 * lValueProdInt 𝔠 (-(z + 1)) := by
  rw [← Int.natCast_succ, lValueProdInt_neg_natCast, lValueProdInt_neg_natCast, lValueProd_succ,
    mul_inv, mul_inv_cancel_left₀ (pow_pos (lSharp_pos 𝔠 (by simp)) 2).ne']

/-! ### Tate's integral at the finite places -/

open scoped Classical in
/-- The finite factor of the datum along the line, shifted by `p`. Let `S = 𝔠.ramifiedPlaces` and
let `χ = 𝔠.semilocalChar` be the tame character on the completions at `S`. At a finite adele `a`
that is integral off `S ∪ S̄` the value is `χ⁻¹(a) χ(ā p)`, read as `0` unless `a` and `ā p` are
units at `S` (the quotient by `0` is `0`). At other adeles it is `0`. -/
def lineFinFactor (p : LocProd 𝔠.ramifiedPlaces) (a : 𝔸f E) : ℂ :=
  if idem (conjClosure (𝔠.ramifiedPlaces : Set (FinPlace E)))ᶜ * a ∈ Ô E then
    invOnUnits 𝔠.semilocalChar (evalPlaces 𝔠.ramifiedPlaces a) / invOnUnits 𝔠.semilocalChar
      (evalPlaces 𝔠.ramifiedPlaces (star a) * p)
  else 0

lemma lineFinFactor_zero (p : LocProd 𝔠.ramifiedPlaces) : lineFinFactor 𝔠 p 0 = 0 := by
  simp [lineFinFactor, invOnUnits, IsIntegralUnit]

/-- There is a finite idele `c` of module `∏_{w ∈ S} q_w⁻¹`, `S = 𝔠.ramifiedPlaces`, such that the
finite factor shifted by the uniformisers `ϖ` at `S` is the translate by `c` of the unshifted
one. -/
lemma exists_lineFinFactor_uniformizer_eq : ∃ c : (𝔸f E)ˣ,
    finIdeleAbs c⁻¹ = ∏ w : 𝔠.ramifiedPlaces, (w.val.q : ℝ) ∧
    ∀ a : 𝔸f E, lineFinFactor 𝔠 ϖ.val a = lineFinFactor 𝔠 1 (a * c) := by
  classical
  -- `c` is `1` at the places outside `S̄`, and `c̄` is the uniformiser at `S`.
  obtain ⟨c, hc_one, hc_star, hc_abs⟩ := exists_idele_star_eq_uniformizer 𝔠
  have hc_eval : evalPlaces 𝔠.ramifiedPlaces c = 1 := funext fun w ↦
    hc_one w (𝔠.star_notMem w w.prop)
  refine ⟨c, hc_abs, fun a ↦ ?_⟩
  -- Off `S̄` the components of `c` are `1`, so `c` does not change the integrality condition.
  have h_int : idem (conjClosure (𝔠.ramifiedPlaces : Set (FinPlace E)))ᶜ * (a * c) ∈ Ô E ↔
      idem (conjClosure (𝔠.ramifiedPlaces : Set (FinPlace E)))ᶜ * a ∈ Ô E := by
    simp +contextual [idem_mul_mem_Ô, finAdele_mul_apply, hc_one]
  simp only [lineFinFactor, h_int, map_mul, star_mul', hc_eval, hc_star, mul_one]

/-- On the support of the finite factor an adele is integral off `S ∪ S̄` and a unit at `S ∪ S̄`,
where `S = 𝔠.ramifiedPlaces`. -/
lemma valuation_of_lineFinFactor_ne_zero {a : 𝔸f E} (ha : lineFinFactor 𝔠 1 a ≠ 0) :
    (∀ w ∉ conjClosure (𝔠.ramifiedPlaces : Set (FinPlace E)), Valued.v (a w) ≤ 1) ∧
      ∀ w ∈ conjClosure (𝔠.ramifiedPlaces : Set (FinPlace E)), Valued.v (a w) = 1 := by
  -- The condition of the `if` holds, and numerator and denominator are both nonzero.
  obtain ⟨h_int, h_unit, h_unit_star⟩ : idem (conjClosure (𝔠.ramifiedPlaces : Set (FinPlace E)))ᶜ *
    a ∈ Ô E ∧
      IsIntegralUnit (evalPlaces 𝔠.ramifiedPlaces a) ∧ IsIntegralUnit
        (evalPlaces 𝔠.ramifiedPlaces (star a)) := by
    simp only [lineFinFactor, invOnUnits, mul_one] at ha
    grind
  rw [isIntegralUnit_iff_v_eq_one] at h_unit h_unit_star
  refine ⟨idem_mul_mem_Ô.1 h_int, fun w hw ↦ hw.elim (fun hw ↦ h_unit ⟨w, hw⟩) fun hw ↦ ?_⟩
  -- The valuation of `a` at `w` is that of `ā` at the conjugate place, which lies in `S`.
  have h_star : Valued.v ((star a) (star w)) = 1 := h_unit_star ⟨star w, hw⟩
  rwa [v_star_apply, star_star] at h_star

/-- On the finite ideles that are units at all places, the finite factor is the inverse of the
finite part of the base change `x ↦ ν(x / x̄)` of `ν = 𝔠.character`. -/
lemma lineFinFactor_mul_finPart {u : (𝔸f E)ˣ} (hu : u ∈ idelesUnitOff ∅) :
    lineFinFactor 𝔠 1 u * 𝔠.character.baseChange.finPart u = 1 := by
  rw [lineFinFactor, ite_eq_left (idem_mul_mem_Ô.2 fun w _ ↦
    (mem_idelesUnitOff.1 hu w (by simp)).le),
    mul_one, div_mul_eq_mul_div, 𝔠.invOnUnits_mul_finPart_div_star_eq_one hu]

/-- On integral adeles the finite factor depends only on the components at `S ∪ S̄`,
`S = 𝔠.ramifiedPlaces`. -/
lemma lineFinFactor_congr {a a' : 𝔸f E} (ha : a ∈ Ô E) (ha' : a' ∈ Ô E)
    (h_eq : ∀ w ∈ conjClosure (𝔠.ramifiedPlaces : Set (FinPlace E)), a' w = a w) :
    lineFinFactor 𝔠 1 a' = lineFinFactor 𝔠 1 a := by
  have h_eval : evalPlaces 𝔠.ramifiedPlaces a' = evalPlaces 𝔠.ramifiedPlaces a := funext fun w ↦
    h_eq w (by simp)
  have h_eval_star : evalPlaces 𝔠.ramifiedPlaces (star a') = evalPlaces 𝔠.ramifiedPlaces (star a) :=
    funext fun w ↦ by simp [evalPlaces, evalAt_apply, finAdele_star_apply, h_eq]
  have h_int {x : 𝔸f E} (hx : x ∈ Ô E) :
      idem (conjClosure (𝔠.ramifiedPlaces : Set (FinPlace E)))ᶜ * x ∈ Ô E :=
    idem_mul_mem_Ô.2 fun w _ ↦ mem_Ô.1 hx w
  rw [lineFinFactor, lineFinFactor, ite_eq_left (h_int ha), ite_eq_left (h_int ha'), h_eval,
    h_eval_star]

/-- The integrand of Tate's integral over the finite ideles: the finite factor times the base change
of `𝔠.character` times the `x`-th power of the module. -/
def finTateIntegrand (x : ℝ) (a : (𝔸f E)ˣ) : ℂ :=
  lineFinFactor 𝔠 1 a * 𝔠.character.baseChange.finPart a * (finIdeleAbs a ^ x : ℝ)

lemma measureReal_idelesUnitOff_empty_pos (ρ : Measure (𝔸f E)ˣ) [IsHaarMeasure ρ] :
    0 < ρ.real (idelesUnitOff (K := E) ∅) :=
  ENNReal.toReal_pos ((isOpen_idelesUnitOff ∅).measure_ne_zero ρ ⟨1, one_mem _⟩)
    isCompact_idelesUnitOff_empty.measure_ne_top

/-- For `x > 1` and a Haar measure `ρ`, Tate's integrand `finTateIntegrand 𝔠 x` over the finite
ideles is integrable. It is the finite factor times the base change of `ν = 𝔠.character` times the
`x`-th power of the module. Its integral is the partial `L`-value `L^S(x, ν)`, for
`S = 𝔠.ramifiedPlaces`, times the `ρ`-volume of the unit ideles `idelesUnitOff ∅`. -/
lemma integral_finTateIntegrand (ρ : Measure (𝔸f E)ˣ) [IsHaarMeasure ρ] {x : ℝ} (hx : 1 < x) :
    Integrable (finTateIntegrand 𝔠 x) ρ ∧
      ∫ a : (𝔸f E)ˣ, finTateIntegrand 𝔠 x a ∂ρ = 𝔠.character.L 𝔠.ramifiedPlaces x * ρ.real
        (idelesUnitOff (K := E) ∅) := by
  -- The finite factor satisfies the three conditions on the test function of Tate's integral.
  obtain ⟨-, h_tate⟩ := 𝔠.hasWeight.isHeckeOfType.tate_integral (conjClosure 𝔠.ramifiedPlaces)
    (fun a ↦ lineFinFactor 𝔠 1 a) univ ρ isOpen_univ (mem_univ 1)
    (h_supp := fun a ↦ valuation_of_lineFinFactor_ne_zero 𝔠)
    (h_units := fun u hu ↦ by simp [lineFinFactor_mul_finPart 𝔠 hu])
    (h_local := fun a a' ↦ lineFinFactor_congr 𝔠)
  unfold finTateIntegrand AutChar.L
  simpa only [inter_univ] using h_tate x hx

/-- The partial `L`-function of a split tame character is continuous on `[1, ∞)`, as a character of
nonzero weight is not trivial. -/
lemma continuousOn_L : ContinuousOn (𝔠.character.L 𝔠.ramifiedPlaces) (Ici 1) := by
  have h_hecke : IsHeckeOfType 𝔠.character.baseChange.finPart (2 • μ) := 𝔠.hasWeight.isHeckeOfType
  exact (h_hecke.exists_hasPrimeDensity (by simp [Finite.star])
    (h_hecke.ne_one (smul_ne_zero two_ne_zero 𝔠.weight_ne_zero))).1

/-! ### Unfolding over the idele classes -/

variable (E) in
/-- The variable of Tate's integral on the two sides of Poisson's formula: `a` itself for
`β = true`, and `ā⁻¹` for `β = false`. -/
def poissonVariable (β : Bool) : (𝔸 E)ˣ ≃ₜ* (𝔸 E)ˣ :=
  cond β (.refl (𝔸 E)ˣ) ⟨.inv (𝔸 E)ˣ * starMulAut, continuous_star.inv, continuous_inv.star⟩

lemma poissonVariable_true (a : (𝔸 E)ˣ) : poissonVariable E true a = a := rfl

lemma poissonVariable_false (a : (𝔸 E)ˣ) : poissonVariable E false a = (star a)⁻¹ := rfl

/-- The base change `x ↦ ν(x / x̄)` of a character `ν` of `[U(1)]` has the same value at `a` and at
the Poisson variable `poissonVariable E β a`, which is `a` or `ā⁻¹`. -/
lemma baseChange_poissonVariable (ν : AutChar E) (β : Bool) (a : (𝔸 E)ˣ) :
    ν.baseChange.val (poissonVariable E β a) = ν.baseChange.val a := by
  cases β
  · have h_div : divStar (star a)⁻¹ = divStar a :=
      Subtype.ext (by simp [coe_divStar, mul_comm, ← star_inv])
    exact congrArg ν.val h_div
  · rw [poissonVariable_true]

lemma ideleAbs_poissonVariable_false (a : (𝔸 E)ˣ) :
    ideleAbs (poissonVariable E false a) = (ideleAbs a)⁻¹ := by
  rw [poissonVariable_false, map_inv, ideleAbs_star]

variable (E) in
/-- The isomorphism that splits an idele into its archimedean and its finite part. -/
def ideleParts : (𝔸 E)ˣ ≃ₜ* (InfinitePlace E → ℂ)ˣ × (𝔸f E)ˣ :=
  { MulEquiv.prodUnits, Homeomorph.prodUnits with }

lemma realIdele_mul_finIdeleIncl_ideleParts (a : (𝔸 E)ˣ) :
    realIdele (ideleParts E a).1 * finIdeleIncl (ideleParts E a).2 = a :=
  Units.ext (Prod.fst_mul_snd _)

variable (E) in
/-- Haar measure on the ideles, read in the variable `a` or `ā⁻¹` of either side of Poisson's
formula and split by `ideleParts` into the archimedean and the finite part, is the product of the
Haar measure `haar` on the archimedean ideles and a Haar measure `ρ` on the finite ideles. -/
lemma exists_haar_ideleParts (β : Bool) : ∃ ρ : Measure (𝔸f E)ˣ, IsHaarMeasure ρ ∧
    MeasurePreserving ((poissonVariable E β).trans (ideleParts E)) haar (haar.prod ρ) := by
  -- The image of Haar measure is a positive multiple of the product of two Haar measures.
  let e : (𝔸 E)ˣ ≃ₜ* (InfinitePlace E → ℂ)ˣ × (𝔸f E)ˣ := (poissonVariable E β).trans (ideleParts E)
  let m : Measure ((InfinitePlace E → ℂ)ˣ × (𝔸f E)ˣ) := haar.prod haar
  have : IsHaarMeasure m := prod.instIsHaarMeasure haar haar
  let c : NNReal := haarScalarFactor (haar.map e) m
  have h_map : haar.map e = haar.prod (c • haar) :=
    (isMulLeftInvariant_eq_smul (haar.map e) m).trans (prod_smul_right c).symm
  exact ⟨c • haar, .nnreal_smul haar (haarScalarFactor_pos_of_isHaarMeasure (haar.map e) m).ne',
    by fun_prop, h_map⟩

/-- The principal idele of a unit of `E`. -/
abbrev principalAdeleUnit (ξ : Eˣ) : (𝔸 E)ˣ := ξ.map (toAdele (E := E)).toMonoidHom

variable (E) in
/-- The principal ideles can be listed by a bijection `J` from `Eˣ` so that the Poisson variable
(`a` or `ā⁻¹`) at the idele `J ξ` is the principal idele of `ξ`. -/
lemma exists_equiv_principalAdeleUnits (β : Bool) : ∃ J : Eˣ ≃ principalAdeleUnits E,
    ∀ ξ : Eˣ, poissonVariable E β (J ξ) = principalAdeleUnit ξ := by
  let J : Eˣ ≃ principalAdeleUnits E :=
    .ofInjective principalAdeleUnit (Units.map_injective (toAdele (E := E)).injective)
  cases β
  · -- List by `ξ ↦ ξ̄⁻¹`; conjugation commutes with the embedding of `E` in the adeles.
    refine ⟨(Equiv.inv Eˣ * starMulAut.toEquiv).trans J, fun ξ ↦ ?_⟩
    have h_star : star (principalAdeleUnit (star ξ)⁻¹) = (principalAdeleUnit ξ)⁻¹ :=
      Units.ext (eq_star_of_eq_star (star_toAdele _).symm).symm
    change poissonVariable E false (principalAdeleUnit (star ξ)⁻¹) = principalAdeleUnit ξ
    rw [poissonVariable_false, h_star, inv_inv]
  · exact ⟨J, fun ξ ↦ rfl⟩

/-- A measure-preserving map `φ : X₁ × X₂ → Z₁ × Z₂` stays measure preserving when two parameters
`y₁` and `y₂` are carried along. -/
lemma measurePreserving_prod_parameters {X₁ X₂ Y₁ Y₂ Z₁ Z₂ : Type} [MeasurableSpace X₁]
    [MeasurableSpace X₂] [MeasurableSpace Y₁] [MeasurableSpace Y₂] [MeasurableSpace Z₁]
    [MeasurableSpace Z₂] {ξ₁ : Measure X₁} {ξ₂ : Measure X₂} {ζ₁ : Measure Z₁} {ζ₂ : Measure Z₂}
    [SFinite ξ₁] [SFinite ξ₂] [SFinite ζ₁] [SFinite ζ₂] {φ : X₁ × X₂ → Z₁ × Z₂}
    (hφ : MeasurePreserving φ (ξ₁.prod ξ₂) (ζ₁.prod ζ₂)) (m₁ : Measure Y₁) (m₂ : Measure Y₂)
    [SFinite m₁] [SFinite m₂] :
    MeasurePreserving
      (fun ((((x₁, y₁), y₂), x₂) : ((X₁ × Y₁) × Y₂) × X₂) ↦
        ((y₁, y₂, (φ (x₁, x₂)).1), (φ (x₁, x₂)).2))
      (((ξ₁.prod m₁).prod m₂).prod ξ₂) ((m₁.prod (m₂.prod ζ₁)).prod ζ₂) := by
  have h_source : MeasurePreserving (fun (((x₁, y₁), y₂), x₂) ↦ ((y₁, y₂), x₁, x₂))
      (((ξ₁.prod m₁).prod m₂).prod ξ₂) ((m₁.prod m₂).prod (ξ₁.prod ξ₂)) :=
    (measurePreserving_prodAssoc (m₁.prod m₂) ξ₁ ξ₂).comp
      ((measurePreserving_swap.comp (measurePreserving_prodAssoc ξ₁ m₁ m₂)).prod (.id ξ₂))
  have h_target : MeasurePreserving (fun ((y₁, y₂), z₁, z₂) ↦ ((y₁, y₂, z₁), z₂))
      ((m₁.prod m₂).prod (ζ₁.prod ζ₂)) ((m₁.prod (m₂.prod ζ₁)).prod ζ₂) :=
    ((measurePreserving_prodAssoc m₁ m₂ ζ₁).prod (.id ζ₂)).comp
      (measurePreserving_prodAssoc (m₁.prod m₂) ζ₁ ζ₂).symm
  exact h_target.comp (((MeasurePreserving.id (m₁.prod m₂)).prod hφ).comp h_source)

/-- Unfolding a sum over `Eˣ` against the integral over the idele classes (computed by the
measure `quotMeasure` on the ideles), with parameters in two further measure spaces `Y₁` and `Y₂`.
Suppose that Haar measure on the ideles, read in the variable `poissonVariable E β a` (`a` or `ā⁻¹`)
and split by `ideleParts` into the archimedean and the finite part, is the product of Haar measure
and `ρ`. If the term at `ξ` of `Θ` is a product `Z * ζ` of integrable functions of the two parts of
`ξ * poissonVariable E β a * c`, then `Θ` is integrable and its integral is the product of the
integrals of `Z` and `ζ`. -/
lemma integral_ideleClass_tsum {β : Bool} {ρ : Measure (𝔸f E)ˣ} [SFinite ρ]
    (hρ : MeasurePreserving ((poissonVariable E β).trans (ideleParts E)) haar (haar.prod ρ))
    {Y₁ Y₂ : Type} [MeasurableSpace Y₁] [MeasurableSpace Y₂] {m₁ : Measure Y₁} {m₂ : Measure Y₂}
    [SFinite m₁] [SFinite m₂] {Z : Y₁ × Y₂ × (InfinitePlace E → ℂ)ˣ → ℂ} {ζ : (𝔸f E)ˣ → ℂ}
    (hZ : Integrable Z (m₁.prod (m₂.prod haar))) (hζ : Integrable ζ ρ) (c : (𝔸 E)ˣ)
    {Θ : ((𝔸 E)ˣ × Y₁) × Y₂ → ℂ}
    (hΘ : ∀ (a : (𝔸 E)ˣ) (y₁ : Y₁) (y₂ : Y₂), Θ ((a, y₁), y₂) = ∑' ξ : Eˣ,
      Z (y₁, y₂, (ideleParts E (principalAdeleUnit ξ * poissonVariable E β a * c)).1) *
        ζ (ideleParts E (principalAdeleUnit ξ * poissonVariable E β a * c)).2) :
    Integrable Θ ((((principalAdeleUnits E).quotMeasure haar).prod m₁).prod m₂) ∧
      ∫ p : ((𝔸 E)ˣ × Y₁) × Y₂, Θ p ∂(((principalAdeleUnits E).quotMeasure haar).prod m₁).prod m₂ =
        (∫ p : Y₁ × Y₂ × (InfinitePlace E → ℂ)ˣ, Z p ∂m₁.prod (m₂.prod haar)) *
          ∫ a : (𝔸f E)ˣ, ζ a ∂ρ := by
  let j : (𝔸 E)ˣ ≃ₜ* (𝔸 E)ˣ := poissonVariable E β
  set m := (((principalAdeleUnits E).quotMeasure haar).prod m₁).prod m₂
  -- The idele classes times the principal ideles give the ideles; translate, then split.
  let φ (q : (𝔸 E)ˣ × principalAdeleUnits E) : (InfinitePlace E → ℂ)ˣ × (𝔸f E)ˣ :=
    ideleParts E (j (q.2 • q.1 * j.symm c))
  let T : (((𝔸 E)ˣ × Y₁) × Y₂) × principalAdeleUnits E →
      (Y₁ × Y₂ × (InfinitePlace E → ℂ)ˣ) × (𝔸f E)ˣ :=
    fun (((a, y₁), y₂), ξ) ↦ ((y₁, y₂, (φ (a, ξ)).1), (φ (a, ξ)).2)
  have hφ : MeasurePreserving φ (((principalAdeleUnits E).quotMeasure haar).prod count)
      (haar.prod ρ) := hρ.comp (measurePreserving_orbitMeasure.mul_right _ (j.symm c))
  have hT : MeasurePreserving T (m.prod count) ((m₁.prod (m₂.prod haar)).prod ρ) :=
    measurePreserving_prod_parameters hφ m₁ m₂
  obtain ⟨J, hJ⟩ := exists_equiv_principalAdeleUnits E β
  have h_sum : Θ = fun p ↦ ∫ ξ, Z (T (p, ξ)).1 * ζ (T (p, ξ)).2 ∂count := by
    funext ⟨⟨a, y₁⟩, y₂⟩
    rw [hΘ, integral_count_eq_tsum, ← J.tsum_eq]
    simp [T, φ, Subgroup.smul_def, hJ, j]
  obtain ⟨h_int, h_value⟩ : Integrable (fun q ↦ Z (T q).1 * ζ (T q).2) (m.prod count) ∧
      ∫ p, ∫ ξ, Z (T (p, ξ)).1 * ζ (T (p, ξ)).2 ∂count ∂m =
        ∫ z, Z z.1 * ζ z.2 ∂(m₁.prod (m₂.prod haar)).prod ρ := hT.fubini (hZ.mul_prod hζ)
  rw [h_sum, ← integral_prod_mul]
  exact ⟨h_int.integral_prod_left, h_value⟩

end

end New.Exchange

end
