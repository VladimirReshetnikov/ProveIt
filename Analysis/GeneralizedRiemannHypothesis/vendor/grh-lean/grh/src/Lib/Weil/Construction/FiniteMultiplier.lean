import Lib.Adelic.Adeles.LocalFactors

/-!
# Finite Heisenberg datum, its lattice vacuum and the finite multiplier

This file treats the finite part of the standard Heisenberg model on vectors `ι → 𝔸f E` of finite
adeles of a CM field `E`. The elements `j`, `α` and the character `υ` come from `New.WeilData`, and
`New.ψf` is the standard character. We write `Ô` for `New.Ô E`, `ψ₀` for the complex character
`New.stdLattice.selfDualAddChar E`, z ↦ `ψf (j α ᾱ z)`, `x* y` for `star x ⬝ᵥ y`, and `c₀` for the
integral element `WeilData.traceOne` of `E`, which satisfies `c₀ + star c₀ = 1`. This file builds
the finite Heisenberg datum and its vacuum on the standard lattice. It defines the finite multiplier
`Δ_f` through saturating matrices and proves its laws on the finite unitary group `New.Gf`. It also
proves a lemma that fixes a sign by a congruence modulo `4`.

## Main definitions and results

* `New.stdLattice.isVacuum_finVac`: `New.stdLattice.finVac` is a vacuum (`New.Heisenberg.IsVacuum`)
  for `New.stdLattice.finHeisenberg`. The convolution identity follows from
  `New.stdLattice.finVac_add` and the self-duality of the lattice.
* `New.glMultiplier`, `New.glMultiplier_mul_diagGL_mul`: the multiplier on `GL_ι(𝔸_f)` and its value
  in terms of elementary divisors, from which its laws are read off.
* `New.finMultiplier`: its restriction to the finite unitary group `New.Gf`, with
  `New.finMultiplier_inv`, `New.norm_finMultiplier_sq`, `New.upsilon_mul_finMultiplier` and
  `New.finMultiplier_eq_of_supportedOn`.

Notions from other files:
* `New.WeilData`: Weil data on a CM field E with a primitive 5040th root of unity, so that E/E⁺ is
  unramified at the finite places. They consist of ȷ in E with ȷ = −ȷ̄, Im τȷ > 0 for every τ in the
  CM type and (1 − ȷ⁻¹)/2 integral; a finite idele α for which the completed integers Ô are
  self-dual under (z, u) ↦ ψ_f(ȷαᾱzu); and a splitting character υ equal to −1 at uniformisers of
  the places w with w = w̄.
* `New.Heisenberg.IsVacuum`: a vacuum for β and μ is a continuous, integrable, even, real function e
  with e(0) = 1 and ∫ e(z)e(x−y−z)β(z,y)β(z+y,x) dμ(z) = e(y)e(x).

## Relation to the literature

Known; see `Lib.Weil.MixedModel.ZeroTerm` for sources.
-/

noncomputable section

/-!
## A sign from a real sum of roots of unity over orbits of order four

`New.eq_one_of_apply_apply_eq_neg` determines a sign from a Gauss-type sum by a congruence modulo
`4`.
-/

section GaussSumSign

open Finset IsPrimitiveRoot

/-- Let `X` be a finite abelian group without `2`-torsion and `f : X → X` a map with
`f (f x) = -x`, so that off `0` the orbits of `f` have four points. Let `F : X → ℂ` be invariant
under `f`, with roots of unity as values, `F 0 = 1` and real sum. Let `r ≡ 1` modulo `4`. If
`‖c‖ = 1` and `c * r ^ a = (∑ x, F x) * r ^ b`, then `c = 1`: the sum is `1` plus `4` times an
algebraic integer, which rules out `c = -1`. -/
lemma New.eq_one_of_apply_apply_eq_neg {X : Type*} [AddCommGroup X] [Fintype X]
    (h_tors : ∀ x : X, -x = x → x = 0) {f : X → X} (h_sq : ∀ x : X, f (f x) = -x)
    {F : X → ℂ} (h_inv : ∀ x : X, F (f x) = F x) (h_order : ∀ x : X, IsOfFinOrder (F x))
    (h_zero : F 0 = 1) (h_real : IsSelfAdjoint (∑ x : X, F x)) {r : ℤ} (hr : r ≡ 1 [ZMOD 4])
    {a b : ℕ} {c : ℂ} (hc : ‖c‖ = 1) (h_eq : c * r ^ a = (∑ x : X, F x) * r ^ b) :
    c = 1 := by
  classical
  -- As ∑F is real, c is real, so c = ±1. If c = -1, then r^b·z = -(r^a + r^b)/4 for
  -- z = (∑_{x ≠ 0} F x)/4. But z is an algebraic integer, so 4 ∣ r^a + r^b ≡ 2 mod 4.
  by_contra hne
  have pow_mod (n : ℕ) : r ^ n % 4 = 1 := by simpa using (hr.pow n).eq
  -- Conjugating `h_eq` replaces c by c̄ = c⁻¹ and fixes the rest, so c⁻¹ = c.
  have conj_eq : c⁻¹ * (r : ℂ) ^ a = (∑ x : X, F x) * (r : ℂ) ^ b := by
    simpa [star_mul', ← c.inv_eq_conj hc, h_real.star_eq, mul_comm] using congrArg star h_eq
  have r_ne : (r : ℂ) ≠ 0 := Int.cast_ne_zero.2 fun h ↦ by simp [h, Int.ModEq] at hr
  have inv_eq : c⁻¹ = c := mul_right_cancel₀ (pow_ne_zero a r_ne) (conj_eq.trans h_eq.symm)
  have c_sq : c * c = 1 := by
    rw [← inv_mul_cancel₀ (norm_ne_zero_iff.1 (hc.trans_ne one_ne_zero)), inv_eq]
  have c_neg : c = -1 := (mul_self_eq_one_iff.1 c_sq).resolve_left hne
  set z : ℂ := (∑ x ∈ univ.erase (0 : X), F x) / 4 with hz
  have sum_eq : ∑ x : X, F x = 1 + 4 * z := by
    rw [hz, ← add_sum_erase univ F (mem_univ 0), h_zero]
    ring
  have rational : r ^ b • z = ((r ^ a + r ^ b) / -4 : ℚ) := by
    rw [sum_eq, c_neg] at h_eq
    push_cast [zsmul_eq_mul]
    linear_combination (-1 / 4 : ℂ) * h_eq
  -- Off zero the orbits have four elements and F is constant on them: z is a sum of values of F.
  have integral : IsIntegral ℤ z := by
    let orbit (x : X) : Finset X := {x, f x, -x, -f x}
    rw [hz, sum_div, ← sum_fiberwise_of_maps_to fun _ ↦ mem_image_of_mem orbit]
    refine .sum _ (forall_mem_image.2 fun y hy ↦ ?_)
    have hy_ne : y ≠ 0 := ne_of_mem_erase hy
    -- The map `f` is odd and `orbit x` is the orbit `x`, `f x`, `f² x`, `f³ x` of `x` under `f`.
    have h_odd (x : X) : f (-x) = -f x := by rw [← h_sq x, h_sq (f x)]
    have orbit_map (x : X) : orbit (f x) = orbit x := by grind
    have orbit_neg (x : X) : orbit (-x) = orbit x := by rw [← h_sq, orbit_map, orbit_map]
    have f_zero : f 0 = 0 := h_tors _ (by rw [← h_odd, neg_zero])
    have hfy_ne : f y ≠ 0 := fun h ↦ hy_ne (by simpa [h, f_zero] using h_sq y)
    have fibre : {x ∈ univ.erase (0 : X) | orbit x = orbit y} = orbit y := by
      refine Subset.antisymm (fun x hx ↦ ?_) fun x hx ↦ ?_
      · simp [← (mem_filter.1 hx).2, orbit]
      · simp only [orbit, mem_insert, mem_singleton] at hx
        obtain rfl | rfl | rfl | rfl := hx <;> simp [hy_ne, hfy_ne, orbit_map, orbit_neg]
    -- A coincidence among the four points would give `-y = y` or `-f y = f y`.
    have h_card : (orbit y).card = 4 := by
      have neg_ne : -y ≠ y := mt (h_tors y) hy_ne
      have neg_map_ne : -f y ≠ f y := mt (h_tors (f y)) hfy_ne
      exact card_eq_four.2 ⟨y, f y, -y, -f y, by grind⟩
    have h_neg (x : X) : F (-x) = F x := by rw [← h_sq, h_inv, h_inv]
    have h_const : ∀ x ∈ orbit y, F x = F y := by simp [orbit, h_inv, h_neg]
    have fibre_sum : ∑ x ∈ orbit y, F x / 4 = F y := by
      simp [← sum_div, sum_congr rfl h_const, h_card]
    simpa only [fibre, fibre_sum] using isIntegral (.orderOf (F y)) (h_order y).orderOf_pos
  -- A rational algebraic integer is an integer.
  obtain ⟨k, hk⟩ : ∃ k : ℤ, k = r ^ b • z :=
    (integral.zsmul _).mem_range_ratCast_iff.1 ⟨_, rational.symm⟩
  have four_dvd : r ^ a + r ^ b = -4 * k := by
    apply Int.cast_injective (α := ℂ)
    push_cast [← hk] at rational ⊢
    linear_combination 4 * rational
  -- But r ≡ 1 gives r^a + r^b ≡ 2 mod 4.
  have two_mod : (r ^ a + r ^ b) % 4 = 2 := by simp [Int.add_emod, pow_mod]
  omega

end GaussSumSign

namespace New.stdLattice

/-!
## The standard lattice, the character ψ₀ and the finite Heisenberg datum

* `New.stdLattice.semichar`, `New.stdLattice.finVac`: the function `x ↦ ψ₀ (c₀ x* x / 2)`, and the
  same function set to `0` off the lattice.
-/

section FiniteHeisenberg

open NumberField Matrix AddChar Circle WeilData

variable (E ι : Type*) [Field E] [CMType E] [WeilData E] [Fintype ι]

/-! ### The lattice and the character -/

/-- The standard lattice Ô^ι, as an additive subgroup of the finite adelic vectors indexed by ι. -/
def _root_.New.stdLattice (E ι : Type*) [Field E] [NumberField E] :
    AddSubgroup (ι → 𝔸f E) := (intVectors (Ô E) ι).toAddSubgroup

/-- The character `z ↦ ψf (j α ᾱ z)` of the finite adeles, with complex values. -/
def selfDualAddChar : AddChar (𝔸f E) ℂ :=
  coeHom.compAddChar ((ψf E).mulShift (algebraMap E (𝔸f E) j * α.1 * star α.1))

variable {E ι}

/-- The integer c₀ of the Weil data (c₀ + c̄₀ = 1), viewed as a finite adele of E. -/
def traceOneAdele : 𝔸f E := (WeilData.traceOne : E)

/-- The number ½, viewed as a finite adele of E. -/
def half {E : Type*} [Field E] [NumberField E] : 𝔸f E := (2⁻¹ : E)

lemma selfDualAddChar_apply (z : 𝔸f E) : selfDualAddChar E z = ψf E
  (algebraMap E (𝔸f E) j * α.val * star α.val * z) :=
  rfl

@[simp]
lemma norm_selfDualAddChar (z : 𝔸f E) : ‖selfDualAddChar E z‖ = 1 := norm_coe _

@[fun_prop]
lemma continuous_selfDualAddChar : Continuous (selfDualAddChar E) :=
  continuous_ψf.subtype_val.comp (continuous_const_mul _)

/-- Let E be a CM field with Weil data (ȷ = −ȷ̄, finite idele α). Let ψ₀ = `selfDualAddChar E` be
the complex character z ↦ ψ_f(ȷαᾱz) of the finite adeles. Then ψ₀(z̄) = ψ₀(−z) for every finite
adele z, because `ȷ α ᾱ` is purely imaginary. -/
lemma selfDualAddChar_star (z : 𝔸f E) : selfDualAddChar E (star z) = selfDualAddChar E (-z) := by
  rw [selfDualAddChar_apply, selfDualAddChar_apply, ← ψf_star]
  simp [mul_right_comm]

/-- The ring `Ô E` of integral finite adeles is its own dual for the pairing
`selfDualAddChar E (z * u)`. -/
lemma forall_selfDualAddChar_mul_eq_one_iff (z : 𝔸f E) :
    (∀ u ∈ Ô E, selfDualAddChar E (z * u) = 1) ↔ z ∈ Ô E := by
  -- The left side says that `d j α ᾱ z` is integral for all `d` in the different.
  simp_rw [selfDualAddChar_apply, ← mul_assoc, coe_eq_one, mul_comm (_ * z),
    forall_ψf_mul_eq_one_iff]
  -- The different is generated in `Ô E` by an idele `t`, and `t j α ᾱ` is a unit at every place.
  obtain ⟨-, -, -, t, -, h_val, h_gen⟩ :=
    exists_reduction_and_idele_generator (I := differentIdeal ℤ (𝓞 E)) differentIdeal_ne_bot
  refine (h_gen _).trans ?_
  set c : 𝔸f E := algebraMap E (𝔸f E) j * α.1 * star α.1
  have h_dual (w : FinPlace E) : Valued.v (c w) =
      WithZero.exp (multiplicity w.1 (differentIdeal ℤ (𝓞 E)) : ℤ) := WeilData.self_dual w
  -- At each place `w` the valuations of `t` and of `c = j α ᾱ` cancel.
  have h_unit (w : FinPlace E) : Valued.v (t.val w) * Valued.v (c w) = 1 := by
    rw [h_val, h_dual, ← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]
  simp [mem_Ô, ← mul_assoc, h_unit]

lemma traceOneAdele_mem : traceOneAdele ∈ Ô E := algebraMap_mem_Ô.mpr isIntegral_traceOne

@[simp]
lemma traceOneAdele_add_star : traceOneAdele + star traceOneAdele = (1 : 𝔸f E) := by
  simp [traceOneAdele, WeilData.traceOne, ← map_add, ← add_div]

omit [WeilData E] in
lemma two_mul_half : 2 * half = (1 : 𝔸f E) := by norm_num [half, two_mul, ← map_add]

omit [WeilData E] in
lemma star_half : star (half : 𝔸f E) = half := by simp [half]

attribute [grind .] traceOneAdele_add_star two_mul_half star_half

lemma selfDualAddChar_eq_one_of_mem {o : 𝔸f E} (ho : o ∈ Ô E) : selfDualAddChar E o = 1 := by
  simpa using (forall_selfDualAddChar_mul_eq_one_iff o).2 ho 1 (one_mem _)

/-- If `a = b + (t + star t) + o` with `o` integral, then `selfDualAddChar E` takes the same value
at `a` and `b`: it does not see a trace `t + star t` or an integral summand. -/
lemma selfDualAddChar_congr {a b o : 𝔸f E} (t : 𝔸f E) (ho : o ∈ Ô E)
    (h_eq : a = b + (t + star t) + o) :
    selfDualAddChar E a = selfDualAddChar E b := by
  have h_trace : selfDualAddChar E t * selfDualAddChar E (star t) = 1 := by
    simp [selfDualAddChar_star, ← map_add_eq_mul]
  simp [h_eq, map_add_eq_mul, h_trace, selfDualAddChar_eq_one_of_mem ho]

/-! ### The vacuum and the Heisenberg datum -/

/-- For a finite adelic vector x, the complex number ψ₀(c₀ x* x / 2). It equals ψ_f(−y* y / 4) at
y = αx (`New.stdLattice.semichar_eq_ψf`) and is a sign on the lattice Ô^ι. -/
def semichar (x : ι → 𝔸f E) : ℂ := selfDualAddChar E (traceOneAdele * half * star x ⬝ᵥ x)

/-- Let E be a CM field with Weil data and x a finite adelic vector indexed by ι. Then `semichar x`,
defined as ψ₀(c₀ x* x / 2), equals `ψf (-y* y / 4)` at the rescaled vector `y = α x`. Here `ψf` is
the standard additive character of the finite adeles, α is the finite idele from the Weil data, and
¼ is written as `half * half`. -/
lemma semichar_eq_ψf (x : ι → 𝔸f E) :
    semichar x = ψf E (-(half * half * star ((α.val : 𝔸f E) • x) ⬝ᵥ ((α.val : 𝔸f E) • x))) := by
  set N : 𝔸f E := half * half * star ((α.val : 𝔸f E) • x) ⬝ᵥ ((α.val : 𝔸f E) • x) with hN
  set J : 𝔸f E := algebraMap E (𝔸f E) j with hJ
  have h_field : (j : E) * WeilData.traceOne = 2⁻¹ * (j - 1) := by grind [WeilData.traceOne]
  have h_traceOne : J * traceOneAdele = half * (J - 1) := by
    simpa [traceOneAdele, half] using congrArg (algebraMap E (𝔸f E)) h_field
  have h_arg : J * α.val * star α.val * (traceOneAdele * half * star x ⬝ᵥ x) = -N + J * N := by
    rw [hN, star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    linear_combination (α.val * star α.val * half * star x ⬝ᵥ x) * h_traceOne
  have h_real : star N = N := by rw [hN, star_mul', star_mul', star_half, ← star_dotProduct]
  have h_imaginary : ψf E (J * N) = 1 := by
    rw [← ψf_inv_two_mul_add_star]
    simp [hJ, h_real]
  rw [semichar, selfDualAddChar_apply, h_arg, map_add_eq_mul, h_imaginary, mul_one]

lemma isOfFinOrder_semichar (x : ι → 𝔸f E) : IsOfFinOrder (semichar x) := by
  simpa only [semichar, selfDualAddChar_apply] using isOfFinOrder_ψf _

lemma semichar_eq_one_of_dotProduct_self_eq_zero {x : ι → 𝔸f E} (hx : star x ⬝ᵥ x = 0) :
    semichar x = 1 := by simp [semichar, hx]

open scoped Classical in
/-- The finite vacuum: `semichar x = ψ₀ (c₀ x* x / 2)` on the lattice `Ô ^ ι` and `0` off it. -/
def finVac (x : ι → 𝔸f E) : ℂ :=
  if x ∈ stdLattice E ι then selfDualAddChar E (traceOneAdele * half * star x ⬝ᵥ x) else 0

lemma finVac_of_mem {x : ι → 𝔸f E} (hx : x ∈ stdLattice E ι) : finVac x = semichar x :=
  ite_eq_left hx

lemma finVac_of_notMem {x : ι → 𝔸f E} (hx : x ∉ stdLattice E ι) : finVac x = 0 := ite_eq_right hx

variable (E ι)

/-- The Heisenberg datum on finite adelic vectors with bicharacter `β x y = ψ₀ (y* x / 2)`. -/
def finHeisenberg : Heisenberg (ι → 𝔸f E) where
  β x y := selfDualAddChar E (half * star y ⬝ᵥ x)
  add_left := by simp [mul_add, map_add_eq_mul]
  add_right := by simp [mul_add, map_add_eq_mul]
  self_eq_one x := by
    -- As `traceOneAdele + star traceOneAdele = 1`, the self-conjugate `half * star x ⬝ᵥ x` is a
    -- trace `t + star t`.
    rw [selfDualAddChar_congr (b := 0) (traceOneAdele * half * star x ⬝ᵥ x) (zero_mem _),
      map_zero_eq_one]
    simp [half, ← star_dotProduct, ← add_mul]
  norm_eq_one x y := norm_selfDualAddChar (half * star y ⬝ᵥ x)
  cont := by fun_prop

end FiniteHeisenberg

/-!
## The twisted lattice indicator as a vacuum

* `New.stdLattice.mem_stdLattice_iff_selfDualAddChar`, `New.integral_selfDualAddChar_stdLattice`:
  the lattice is self-dual for `selfDualAddChar (y* x)`, so `y ↦ selfDualAddChar (x* y)` integrates
  over it to `1` or `0` as `x` lies in it or not.
-/

section FiniteVacuum

open NumberField MeasureTheory Measure Matrix AddChar Heisenberg

section

variable {E ι : Type*} [Field E] [NumberField E]

/-! ### The lattice and its measure -/

open scoped Classical in
lemma isOpen_stdLattice [Fintype ι] : (stdLattice E ι).IsOpen := isOpen_intVectors isOpen_Ô

end

variable {E ι : Type*} [Field E] [CMType E]

lemma mem_stdLattice {x : ι → 𝔸f E} : x ∈ stdLattice E ι ↔ ∀ i : ι, x i ∈ Ô E := .rfl

lemma isCompact_stdLattice : IsCompact (stdLattice E ι).carrier :=
  isCompact_pi_infinite fun _ ↦ isCompact_Ô

variable [Fintype ι]

variable (E) in
/-- The Haar measure on n-tuples of finite adeles of E that gives the lattice Ô^n mass one. -/
noncomputable def _root_.New.latticeMeasure (n : Type*) [Fintype n] : Measure (n → 𝔸f E) :=
  addHaarMeasure ⟨⟨stdLattice E n, isCompact_stdLattice⟩, by simp [isOpen_stdLattice.interior_eq]⟩
  deriving IsAddHaarMeasure

/-- For a CM field E, the Haar measure `latticeMeasure` on ι-tuples of finite adeles of E, which is
normalised so that Ô^ι has mass one, gives the standard lattice Ô^ι (`stdLattice E ι`) measure 1. -/
@[simp]
lemma _root_.New.latticeMeasure_stdLattice : latticeMeasure E ι (stdLattice E ι) = 1 :=
  addHaarMeasure_self

/-- An element `g` of the finite unitary group `New.Gf` preserves the form `x* y`. -/
@[simp]
lemma star_mulVec_dotProduct_mulVec [DecidableEq ι] (g : Gf E ι) (x y : ι → 𝔸f E) :
    star (g.val.val *ᵥ x) ⬝ᵥ g.val.val *ᵥ y = star x ⬝ᵥ y := by
  simpa using U.form_mulVec_mulVec g x y

omit [Fintype ι] in
lemma smul_mem_stdLattice {x : ι → 𝔸f E} {r : 𝔸f E} (hr : r ∈ Ô E) (hx : x ∈ stdLattice E ι) :
    r • x ∈ stdLattice E ι := fun i ↦ mul_mem hr (hx i)

/-- For `y` and `z` in the lattice `Ô ^ ι`, the product `z* y` is integral. -/
lemma star_dotProduct_mem {y z : ι → 𝔸f E} (hy : y ∈ stdLattice E ι) (hz : z ∈ stdLattice E ι) :
    star z ⬝ᵥ y ∈ Ô E := sum_mem fun i _ ↦ mul_mem (star_mem_Ô (hz i)) (hy i)

/-! ### The vacuum and self-duality -/

variable [WeilData E]

/-- Let ψ₀(z) = ψ_f(ȷαᾱz) be the self-dual character of the finite adeles
(`New.stdLattice.selfDualAddChar`), and let `c₀` be the integer of the Weil data with c₀ + c̄₀ = 1
(`traceOneAdele`). For finite adelic vectors `x` and `y`, `semichar x * semichar y * β x y = ψ₀ (c̄₀
y* x) * semichar (x + y)`, where `semichar x = ψ₀ (c₀ x* x / 2)` and `β x y = ψ₀ (y* x / 2)` is the
bicharacter of `New.stdLattice.finHeisenberg`. -/
lemma semichar_add (x y : ι → 𝔸f E) :
    semichar x * semichar y * (finHeisenberg E ι).β x y =
      selfDualAddChar E (star traceOneAdele * star y ⬝ᵥ x) * semichar (x + y) := by
  -- Both sides are values of `selfDualAddChar E`; the arguments differ by a trace `t + star t`,
  -- which `selfDualAddChar E` kills.
  simp only [semichar, finHeisenberg, ← map_add_eq_mul, star_add, dotProduct_add, add_dotProduct]
  apply selfDualAddChar_congr (-traceOneAdele * half * star x ⬝ᵥ y) (zero_mem _)
  -- The terms in `star x ⬝ᵥ y` cancel; for `star y ⬝ᵥ x` use `2 * half = 1` and
  -- `traceOneAdele + star traceOneAdele = 1`.
  grind [star_half, star_dotProduct, star_neg, star_mul']

/-- For `y` in the lattice `New.stdLattice E ι` and any `x`,
`finVac x * finVac y * β x y = finVac (x + y)`, where `β` is the bicharacter of
`New.stdLattice.finHeisenberg`. -/
lemma finVac_add {y : ι → 𝔸f E} (x : ι → 𝔸f E) (hy : y ∈ stdLattice E ι) :
    finVac x * finVac y * (finHeisenberg E ι).β x y = finVac (x + y) := by
  by_cases hx : x ∈ stdLattice E ι
  · -- On the lattice the factor in `semichar_add` is `selfDualAddChar E` of an integral element,
    -- hence `1`.
    have h_one : selfDualAddChar E (star traceOneAdele * star y ⬝ᵥ x) = 1 :=
      selfDualAddChar_eq_one_of_mem (mul_mem (star_mem_Ô traceOneAdele_mem)
        (star_dotProduct_mem hx hy))
    simp [finVac_of_mem, hx, hy, add_mem hx hy, semichar_add, h_one]
  · have h_add : x + y ∉ stdLattice E ι := mt (add_mem_cancel_right hy).1 hx
    rw [finVac_of_notMem hx, finVac_of_notMem h_add, zero_mul, zero_mul]

lemma semichar_mul_self {y : ι → 𝔸f E} (hy : y ∈ stdLattice E ι) :
    semichar y * semichar y = 1 := by
  -- This is `finVac_add` for `-y` and `y`, as `β y y = 1`.
  simpa [hy, semichar, finVac, self_eq_one] using finVac_add (-y) hy

/-- The lattice `Ô ^ ι` is its own dual for the pairing `ψ₀ (y* x)`: `x` lies in it if and only if
the pairing of `x` with every lattice vector `y` is trivial. -/
lemma mem_stdLattice_iff_selfDualAddChar {x : ι → 𝔸f E} :
    x ∈ stdLattice E ι ↔ ∀ y ∈ stdLattice E ι, selfDualAddChar E (star y ⬝ᵥ x) = 1 := by
  classical
  refine ⟨fun hx y hy ↦ selfDualAddChar_eq_one_of_mem (star_dotProduct_mem hx hy), fun h i ↦ ?_⟩
  -- Test against `y = star (Pi.single i u)` and use that `Ô E` is its own dual for
  -- `selfDualAddChar E`.
  refine (forall_selfDualAddChar_mul_eq_one_iff _).1 fun u hu ↦ ?_
  have h_mem : star (Pi.single i u) ∈ stdLattice E ι := by
    simp [mem_stdLattice, Pi.single_apply, ite_mem, hu, star_mem_Ô]
  simpa [mul_comm] using h _ h_mem

open scoped Classical in
/-- The integral of `y ↦ selfDualAddChar (x* y)` over the lattice `New.stdLattice E ι`, for
`New.latticeMeasure`, is `1` if `x` lies in the lattice and `0` otherwise. -/
lemma _root_.New.integral_selfDualAddChar_stdLattice (x : ι → 𝔸f E) :
    ∫ y : ι → 𝔸f E in stdLattice E ι, selfDualAddChar E (star x ⬝ᵥ y) ∂latticeMeasure E ι =
      if x ∈ stdLattice E ι then 1 else 0 := by
  -- The integrand is a character, trivial on the lattice exactly when `x` lies in it; apply
  -- orthogonality of characters (`setIntegral_char`).
  have h_triv : (∀ y ∈ stdLattice E ι, selfDualAddChar E (star x ⬝ᵥ y) = 1) ↔ x ∈ stdLattice E
    ι := by
    simp [star_dotProduct x, selfDualAddChar_star, map_neg_eq_inv,
      ← mem_stdLattice_iff_selfDualAddChar]
  rw [setIntegral_char isOpen_stdLattice fun y y' ↦ by rw [dotProduct_add, map_add_eq_mul]]
  simp [h_triv, real_def]

open scoped Classical in
/-- The function `New.stdLattice.finVac` is a vacuum for the Heisenberg datum
`New.stdLattice.finHeisenberg` with respect to the measure `New.latticeMeasure`. -/
instance isVacuum_finVac : (finHeisenberg E ι).IsVacuum (latticeMeasure E ι) finVac := by
  have even (x : ι → 𝔸f E) : finVac (-x) = finVac x := by simp [finVac]
  have cont : Continuous (finVac : (ι → 𝔸f E) → ℂ) :=
    IsClopen.continuous_indicator ⟨isCompact_stdLattice.isClosed, isOpen_stdLattice⟩ (by fun_prop)
  have vac_sq (x : ι → 𝔸f E) (hx : x ∈ stdLattice E ι) : finVac x * finVac x = 1 := by
    rw [finVac_of_mem hx, semichar_mul_self hx]
  -- `finVac` is real because its values are `0` and `±1`.
  have real (x : ι → 𝔸f E) : starRingEnd ℂ (finVac x) = finVac x := by
    by_cases hx : x ∈ stdLattice E ι
    · obtain h | h := mul_self_eq_one_iff.1 (vac_sq x hx) <;> simp [h]
    · simp [finVac_of_notMem hx]
  refine ⟨cont, by simp [finVac], even, real, fun y x ↦ ?_,
    cont.integrable_of_hasCompactSupport (.intro isCompact_stdLattice fun x ↦ finVac_of_notMem)⟩
  -- On the lattice the integrand is a constant times the character
  -- `z ↦ selfDualAddChar E (star x ⬝ᵥ z)`: expand `finVac (x - y - z)` by `finVac_add`; the factors
  -- `β z y` and `β y z` cancel.
  set H : Heisenberg (ι → 𝔸f E) := finHeisenberg E ι
  have integrand (z : ι → 𝔸f E) (hz : z ∈ stdLattice E ι) :
      finVac z * (H.β z y * (H.β (z + y) x * finVac (x - (z + y)))) =
        finVac (x - y) / H.β x y * selfDualAddChar E (star x ⬝ᵥ z) := by
    have h_shift : finVac (x - (z + y)) = finVac (x - y) * finVac z * H.β (x - y) (-z) := by
      rw [← even z, finVac_add (x - y) (neg_mem hz), ← sub_eq_add_neg, sub_sub, add_comm y z]
    have β_sq : H.β z x ^ 2 = selfDualAddChar E (star x ⬝ᵥ z) := by
      simp [H, finHeisenberg, sq, ← map_add_eq_mul, ← two_mul, ← mul_assoc, two_mul_half]
    rw [h_shift, ← β_sq, H.add_left z y x, sub_eq_add_neg x y, add_left, beta_neg_right x z,
      beta_neg_right (-y) z, beta_neg_right z y, div_eq_mul_inv,
        inv_eq_of_mul_eq_one_right (beta_mul_beta x y)]
    calc _ = finVac z * finVac z * (H.β z y * H.β y z) *
          (finVac (x + -y) * H.β y x * H.β z x ^ 2) := by ring
      _ = finVac (x + -y) * H.β y x * H.β z x ^ 2 := by simp [vac_sq z hz, beta_mul_beta]
  -- Off the lattice it vanishes, and the character integrates to `1` or `0` as `x` is in it or not.
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz ↦ by simp [finVac_of_notMem hz],
    setIntegral_congr_fun isOpen_stdLattice.measurableSet integrand, integral_const_mul,
    integral_selfDualAddChar_stdLattice x]
  -- For `x` in the lattice this is `finVac_add` for `-y` and `x`; otherwise both sides are `0`.
  split_ifs with hx
  · rw [mul_one, ← neg_add_eq_sub, ← finVac_add (-y) hx, even, beta_neg_left,
      mul_div_cancel_right₀ _ (beta_ne_zero x y)]
  · simp [finVac_of_notMem hx]

end FiniteVacuum

end New.stdLattice

/-!
## The finite multiplier Δ_f and its laws

The finite part `Δ_f` of the multiplier that normalises the Weil representation. For `g` in
`GL_ι(𝔸_f)` choose `u` with `u Ô^ι = Ô^ι ∩ g⁻¹ Ô^ι`; then `Δ_f g = χ_f (det u)`, where
`χ_f = υ |·|^(-1/2)` and `υ` is the splitting character of the Weil data `New.WeilData`.

* `New.IsSaturating`, `New.IsSaturating.exists_isSaturating`: the relation between `g` and `u`, in a
  form that makes sense over any subring of a ring, and the existence of `u`.
* `New.glMultiplier`, `New.IsSaturating.glMultiplier_eq`, `New.glMultiplier_mul_of_mem`: the
  multiplier on `GL_ι(𝔸_f)`; it does not depend on `u` and is bi-invariant under `GL_ι(Ô)`.
* `New.glMultiplier_mul_diagGL_mul`: its value in terms of the elementary divisors of `g`.

Notions from other files:
* `New.cutGL`: For an idempotent e of the commutative ring A, the endomorphism g ↦ e·g + (1−e)·1 of
  GL_n(A).
-/

namespace New

section

variable {E ι κ B B' : Type*} [Ring B] [Ring B'] {S : Subring B} {g u : Bˣ}

/-! ### Saturating matrices -/

/-- Units `g`, `u` of a ring satisfy this relation over a subring `S` when `u` and `g u` lie in `S`
and `u⁻¹ = l + m g` for some `l`, `m` in `S`. For matrices and the lattice `Λ` of vectors with
entries in the subring this implies `u Λ = Λ ∩ g⁻¹ Λ`. -/
def IsSaturating (S : Subring B) (g u : Bˣ) : Prop :=
  ↑u ∈ S ∧ g.val * u ∈ S ∧ ∃ l ∈ S, ∃ m ∈ S, ↑u⁻¹ = l + m * g

lemma IsSaturating.inv_mul_mem (h : IsSaturating S g u) {x : B} (hx : x ∈ S)
    (hgx : g.val * x ∈ S) : u⁻¹.val * x ∈ S := by
  obtain ⟨-, -, l, hl, m, hm, hlm⟩ := h
  simpa [hlm, add_mul, mul_assoc] using add_mem (mul_mem hl hx) (mul_mem hm hgx)

/-- A ring homomorphism `f` that maps the subring `S` into `S'` carries a unit `u` that saturates
`g` over `S` (`New.IsSaturating`) to a unit that saturates `f g` over `S'`. -/
lemma IsSaturating.map_of_le_comap (h : IsSaturating S g u) (f : B →+* B') {S' : Subring B'}
    (h_le : S ≤ Subring.comap f S') : IsSaturating S' (g.map f) (u.map f) := by
  obtain ⟨hu, hgu, l, hl, m, hm, hlm⟩ := h
  exact ⟨h_le hu, by simpa using h_le hgu, f l, h_le hl, f m, h_le hm, by simp [hlm]⟩

/-- If `u` saturates `g`, then `g u` saturates `g⁻¹`: for lattices, `g (Λ ∩ g⁻¹ Λ) = Λ ∩ g Λ`. -/
lemma IsSaturating.inv (h : IsSaturating S g u) : IsSaturating S g⁻¹ (g * u) := by
  obtain ⟨hu, hgu, l, hl, m, hm, hlm⟩ := h
  exact ⟨hgu, by simpa using hu, m, hm, l, hl, by simp [hlm, add_mul, add_comm]⟩

/-- If `u` saturates `g`, and `k`, `k'` and their inverses lie in `S`, then `k'⁻¹ u` saturates
`k g k'`. -/
lemma IsSaturating.mul_of_mem (h : IsSaturating S g u) {k k' : Bˣ} (hk : k.val ∈ S)
    (hk_inv : k⁻¹.val ∈ S) (hk' : k'.val ∈ S) (hk'_inv : k'⁻¹.val ∈ S) :
    IsSaturating S (k * g * k') (k'⁻¹ * u) := by
  obtain ⟨hu, hgu, l, hl, m, hm, hlm⟩ := h
  exact ⟨mul_mem hk'_inv hu, by simpa [mul_assoc] using mul_mem hk hgu, l * k', mul_mem hl hk',
    m * k⁻¹, mul_mem hm hk_inv, by simp [hlm, add_mul, mul_assoc]⟩

lemma IsSaturating.of_mem (hg : ↑g ∈ S) : IsSaturating S g 1 :=
  ⟨one_mem S, by simpa using hg, 1, one_mem S, 0, zero_mem S, by simp⟩

lemma IsSaturating.val_mem (h : IsSaturating S g u) : u.val ∈ S := h.1

lemma IsSaturating.mul_val_mem (h : IsSaturating S g u) : g.val * u.val ∈ S := h.2.1

open MeasureTheory Matrix ComplexConjugate NumberField GeneralLinearGroup WeilData stdLattice Valued
  IsSaturating

variable [Field E] [NumberField E] [Fintype ι] [DecidableEq ι] [Fintype κ]
  (g : GL ι (𝔸f E)) {u b b' k k' : GL ι (𝔸f E)} {w : FinPlace E}

@[local simp]
lemma mem_subring_matrix_iff {x : Matrix ι ι B} : x ∈ S.matrix ↔ ∀ i j : ι, x i j ∈ S := .rfl

/-- The norm of the idele that is `x` at the place `w` and `1` elsewhere
(`New.locFullIdele`) is the absolute value of `x` in the completion at `w`. -/
lemma ideleAbs_locFullIdele (w : FinPlace E) (x : (LocField w)ˣ) :
    ideleAbs (locFullIdele w x) = ‖x.val‖ := finIdeleAbs_locIdele x

/-- If `u` saturates `b` over integral matrices (`New.IsSaturating`), then at every finite place
`w` the component of `u` saturates the component of `b` over `O_w`. -/
lemma IsSaturating.map_evalAt (h : IsSaturating (Ô E).matrix b u) (w : FinPlace E) :
    IsSaturating (LocInt w).matrix (b.map (evalAt w)) (u.map (evalAt w)) :=
  h.map_of_le_comap (evalAt w).mapMatrix fun _ hx i j ↦ mem_Ô.1 (hx i j) w

/-- Two matrices that saturate the same matrix `x` over the integers `O_w` of the completion at
`w` (`New.IsSaturating`) have determinants of the same valuation. -/
lemma IsSaturating.v_det_eq {x y z : GL ι (LocField w)}
    (hy : IsSaturating (LocInt w).matrix x y) (hz : IsSaturating (LocInt w).matrix x z) :
    v y.val.det = v z.val.det := by
  -- They differ by an element of GL(O_w), whose determinant has valuation 1.
  have h_mem : y⁻¹ * z ∈ intGL ι (LocInt w).toSubring := by
    rw [mem_intGL, _root_.mul_inv_rev, inv_inv]
    exact ⟨hy.inv_mul_mem hz.val_mem hz.mul_val_mem, hz.inv_mul_mem hy.val_mem hy.mul_val_mem⟩
  exact eq_of_inv_mul_eq_one (by simpa using (mem_intGL_iff_det.1 h_mem).2)

/-- If `u` saturates `b` over integral matrices and `k`, `k'` lie in `GL_ι(Ô)`, then `k'⁻¹ * u`
saturates `k * b * k'`. -/
lemma IsSaturating.mul_of_mem_intGL (h : IsSaturating (Ô E).matrix b u) (hk : k ∈ intGL ι (Ô E))
    (hk' : k' ∈ intGL ι (Ô E)) : IsSaturating (Ô E).matrix (k * b * k') (k'⁻¹ * u) :=
  h.mul_of_mem (mem_intGL.1 hk).1 (mem_intGL.1 hk).2 (mem_intGL.1 hk').1 (mem_intGL.1 hk').2

/-! ### Elementary divisors -/

/-- Elementary divisors over `Ô`: every `g` in `GL_ι(𝔸_f)` is `k * diag(d) * k'` with `k`, `k'` in
`GL_ι(Ô)` and ideles `d i`. -/
lemma exists_eq_mul_diagGL_mul :
    ∃ k ∈ intGL ι (Ô E), ∃ k' ∈ intGL ι (Ô E), ∃ d : ι → (𝔸f E)ˣ, g = k * diagGL d * k' := by
  obtain ⟨k, hk, k', hk', d, hg⟩ := isValuationPair_Ô.smith_normal_form g.val
  lift d to ι → (𝔸f E)ˣ using by simpa [hg] using g.det.isUnit
  exact ⟨k, hk, k', hk', d, Units.ext hg⟩

/-- The denominator of a finite idele `x`: the idele with component `1` where `x` is integral and
`x⁻¹` elsewhere. If `x` has order `μ` at `w`, its denominator has order `max 0 (-μ)` there. -/
def denominatorIdele (x : (𝔸f E)ˣ) : (𝔸f E)ˣ where
  val := idem {w : FinPlace E | v (x.val w) ≤ 1} +
    idem {w : FinPlace E | v (x.val w) ≤ 1}ᶜ * x⁻¹.val
  inv := idem {w : FinPlace E | v (x.val w) ≤ 1} + idem {w : FinPlace E | v (x.val w) ≤ 1}ᶜ * x.val
  val_inv := by grind [idem_compl, idem_mul_self, Units.inv_mul]
  inv_val := by grind [idem_compl, idem_mul_self, Units.inv_mul]

/-- The inverse of the denominator of `x` is `1` where `x` is integral and `x` elsewhere. -/
lemma coe_inv_denominatorIdele (x : (𝔸f E)ˣ) :
    (denominatorIdele x)⁻¹.val =
      idem {w : FinPlace E | v (x.val w) ≤ 1} + idem {w : FinPlace E | v (x.val w) ≤ 1}ᶜ * x.val :=
      rfl

/-- The valuation of the denominator of `x` at `w` is the inverse of `max 1 |x_w|`. -/
lemma v_denominatorIdele (x : (𝔸f E)ˣ) (w : FinPlace E) :
    v ((denominatorIdele x).val w) = (max 1 (v (x.val w)))⁻¹ := by
  have h_inv : x⁻¹.val w = (x.val w)⁻¹ := map_units_inv (evalAt w) x
  by_cases h_int : v (x.val w) ≤ 1 <;> simp [denominatorIdele, h_int, h_inv, le_of_not_ge]

/-- For finite ideles `d i`, the diagonal matrix of their denominators (`New.denominatorIdele`)
saturates the diagonal matrix of the `d i` over integral matrices (`New.IsSaturating`). -/
lemma isSaturating_diagGL (d : ι → (𝔸f E)ˣ) :
    IsSaturating (Ô E).matrix (diagGL d) (diagGL fun i : ι ↦ denominatorIdele (d i)) := by
  have h_diag {a : ι → 𝔸f E} (ha : ∀ i : ι, a i ∈ Ô E) : diagonal a ∈ (Ô E).matrix :=
    fun i j ↦ by simp [diagonal_apply, ite_mem, ha]
  -- The inverse of the denominator of `d i` is `1` on the set `S i` and `d i` off it.
  let S (i : ι) : Set (FinPlace E) := {w : FinPlace E | v ((d i).val w) ≤ 1}
  have h_integral (i : ι) : (denominatorIdele (d i)).val ∈ Ô E :=
    mem_Ô.2 fun w ↦ (v_denominatorIdele (d i) w).trans_le (inv_le_one_of_one_le₀ (le_max_left _ _))
  refine ⟨h_diag h_integral, ?_, _, h_diag fun i ↦ idem_mem_Ô (S i),
    _, h_diag fun i ↦ idem_mem_Ô (S i)ᶜ, ?_⟩
  · rw [coe_diagGL, coe_diagGL, diagonal_mul_diagonal]
    refine h_diag fun i ↦ mem_Ô.2 fun w ↦ ?_
    have h_le : v ((d i).val w) * (max 1 (v ((d i).val w)))⁻¹ ≤ 1 :=
      mul_inv_le_one_of_le₀ (le_max_right _ _) zero_le
    simpa [v_denominatorIdele] using h_le
  · rw [← map_inv, coe_diagGL, coe_diagGL, diagonal_mul_diagonal, diagonal_add]
    exact congrArg diagonal (funext fun i ↦ coe_inv_denominatorIdele (d i))

/-- If `u` saturates `k * diag(d) * k'` over integral matrices, with `k`, `k'` in `GL_ι(Ô)`, then
the valuation of `det u` at `w` is the product of the inverses of `max 1 |(d i)_w|`, which are the
valuations of the denominators of the `d i`. -/
lemma IsSaturating.v_det_eq_prod (hk : k ∈ intGL ι (Ô E)) (hk' : k' ∈ intGL ι (Ô E))
    {d : ι → (𝔸f E)ˣ} (h : IsSaturating (Ô E).matrix (k * diagGL d * k') u) (w : FinPlace E) :
    v (u.val.det w) = ∏ i : ι, (max 1 (v ((d i).val w)))⁻¹ := by
  have h_unit : v (k'⁻¹.map (evalAt w)).val.det = 1 :=
    (mem_intGL_iff_det.1 (mem_intGL_Ô.1 (inv_mem hk') w)).2
  calc v (u.val.det w) = v (u.map (evalAt w)).val.det := congrArg v ((evalAt w).map_det u.val)
    _ = v ((k'⁻¹ * diagGL fun i : ι ↦ denominatorIdele (d i)).map (evalAt w)).val.det :=
      (h.map_evalAt w).v_det_eq (((isSaturating_diagGL d).mul_of_mem_intGL hk hk').map_evalAt w)
    _ = ∏ i : ι, (max 1 (v ((d i).val w)))⁻¹ := by
      rw [map_mul, Units.val_mul, det_mul, map_mul, h_unit, one_mul]
      simp [← RingHom.mapMatrix_apply, ← RingHom.map_det, v_denominatorIdele]

/-! ### The chosen saturating matrix -/

/-- Let `g` be an invertible `ι × ι` matrix over the finite adeles of the number field `E`. Some
invertible `u` saturates `g` over the matrices with entries in `Ô E` (`New.IsSaturating`): `u` and
`g * u` are integral and `u⁻¹ = l + m * g` for integral `l`, `m`. Thus `u Ô^ι = Ô^ι ∩ g⁻¹ Ô^ι`. -/
lemma IsSaturating.exists_isSaturating :
    ∃ u : (Matrix ι ι (𝔸f E))ˣ, IsSaturating (Ô E).matrix g u := by
  -- For `g = k * diag(d) * k'` take `k'⁻¹` times the diagonal matrix of the denominators.
  obtain ⟨k, hk, k', hk', d, rfl⟩ := exists_eq_mul_diagGL_mul g
  exact ⟨_, (isSaturating_diagGL d).mul_of_mem_intGL hk hk'⟩

/-- For g in GL_ι(𝔸_f), a chosen u in GL_ι(𝔸_f) that saturates g over integral matrices
(`New.IsSaturating`): u and gu are integral, and u⁻¹ = l + mg for some integral matrices l, m. -/
def saturatingElem : Subtype (IsSaturating (Ô E).matrix g) :=
  (nonempty_subtype.mpr (IsSaturating.exists_isSaturating g)).some

/-- Let u be the matrix `New.saturatingElem` chosen for b, with uÔ^ι = Ô^ι ∩ b⁻¹Ô^ι. If y saturates
the component of b at w over O_w (`New.IsSaturating`), then det u at w and det y have the same
valuation. -/
lemma IsSaturating.v_det_saturatingElem {b : GL ι (𝔸f E)} {w : FinPlace E} {y : GL ι (LocField w)}
    (h : IsSaturating (LocInt w).matrix (b.map (evalAt w)) y) :
    v ((saturatingElem b).val.val.det w) = v y.val.det := by
  simpa [← evalAt_apply, RingHom.map_det] using
    ((saturatingElem b).property.map_evalAt w).v_det_eq h

/-- If the component of `b` at `w` is `1`, then the determinant of the matrix `New.saturatingElem`
chosen for `b` has valuation `1` at `w`. -/
lemma v_det_saturatingElem_eq_one (hb : b.map (evalAt w) = 1) :
    v ((saturatingElem b).val.val.det w) = 1 := by
  have h_sat : IsSaturating (LocInt w).matrix (b.map (evalAt w)) 1 := .of_mem (by simp [hb])
  simpa using h_sat.v_det_saturatingElem

end

open MeasureTheory Matrix ComplexConjugate NumberField GeneralLinearGroup WeilData stdLattice Valued
  IsSaturating

attribute [local simp] mem_subring_matrix_iff

variable {E ι κ B : Type*} [Ring B] {S : Subring B} [Field E] [CMType E] [Fintype ι] [DecidableEq ι]
  [Fintype κ] (g : GL ι (𝔸f E)) {u b b' k k' : GL ι (𝔸f E)} {w : FinPlace E} [WeilData E]

/-! ### The multiplier on `GL_ι(𝔸_f)` -/

/-- The homomorphism x ↦ υ(x)|x|^(−1/2) from the ideles of E to ℂ, with υ the splitting
character and |x| the idele norm. -/
@[local simp]
def chiAdelic : (𝔸 E)ˣ →* ℂ where
  toFun x := υ.1 x * (↑√(ideleAbs x))⁻¹
  map_one' := by simp
  map_mul' := by simp [field]

/-- The character x ↦ υ(x)|x|^(−1/2) of the finite ideles of E, x being extended by 1 at
infinity. -/
def chiFin : (𝔸f E)ˣ →* ℂ := chiAdelic (E := E).comp finIdeleIncl

/-- The character `χ_f = υ |·|^(-1/2)` of the finite ideles (`New.chiFin`) takes the same value on
two finite ideles that have the same valuation at every finite place. -/
lemma chiFin_congr {x y : (𝔸f E)ˣ} (h_val : ∀ w : FinPlace E, v (x.val w) = v (y.val w)) :
    chiFin x = chiFin y := by
  simp [chiFin, upsilon_eq_prod_mul_of_v_eq y, ideleAbs, FinitePlace.norm_def, h_val]

/-- For g in GL_ι(𝔸_f), Δ_f(g) = χ_f(det u), where u is the matrix `New.saturatingElem` chosen for
g, with uÔ^ι = Ô^ι ∩ g⁻¹Ô^ι. -/
def glMultiplier : ℂ := chiFin (GeneralLinearGroup.det (saturatingElem g).val)

lemma IsSaturating.glMultiplier_eq (h : IsSaturating (Ô E).matrix b u) :
    glMultiplier b = chiFin u.det := by
  refine chiFin_congr fun w ↦ ?_
  simpa [← evalAt_apply, RingHom.map_det] using (h.map_evalAt w).v_det_saturatingElem

lemma chiFin_det_eq_one_of_mem (hk : k ∈ intGL ι (Ô E)) : chiFin k.det = 1 := by
  refine (chiFin_congr fun w ↦ ?_).trans chiFin.map_one
  simpa [← evalAt_apply, RingHom.map_det] using (mem_intGL_iff_det.1 (mem_intGL_Ô.1 hk w)).2

/-- Let `g`, `k`, `k'` be in `GL_ι(𝔸_f)` for the finite adeles of `E`, with `k` and `k'` in the
integral subgroup `GL_ι(Ô)`. Then the multiplier `Δ_f` (`New.glMultiplier`) takes the same value
at `k * g * k'` and at `g`. -/
lemma glMultiplier_mul_of_mem (hk : k ∈ intGL ι (Ô E)) (hk' : k' ∈ intGL ι (Ô E)) :
    glMultiplier (k * g * k') = glMultiplier g := by
  obtain ⟨u, h⟩ := IsSaturating.exists_isSaturating g
  rw [(h.mul_of_mem_intGL hk hk').glMultiplier_eq, h.glMultiplier_eq, map_mul, map_mul,
    chiFin_det_eq_one_of_mem (inv_mem hk'), one_mul]

/-! ### The formula in the elementary divisors, and the laws -/

/-- The multiplier in terms of elementary divisors: if `k`, `k'` lie in `GL_ι(Ô)`, the multiplier of
`k * diag(d) * k'` is the product of `χ_f` at the denominators of the `d i`. As `χ_f` depends only
on orders (`New.chiFin_congr`), this is `∏_w χ_f(ϖ_w) ^ (∑_i max 0 (-μ_{w,i}))`, where `μ_{w,i}` is
the order of `d i` at `w`. -/
theorem glMultiplier_mul_diagGL_mul (hk : k ∈ intGL ι (Ô E)) (hk' : k' ∈ intGL ι (Ô E))
    (d : ι → (𝔸f E)ˣ) :
    glMultiplier (k * diagGL d * k') = ∏ i : ι, chiFin (denominatorIdele (d i)) := by
  have h_det : (diagGL fun i : ι ↦ denominatorIdele (d i)).det = ∏ i : ι, denominatorIdele (d i) :=
    Units.ext (by simp)
  rw [glMultiplier_mul_of_mem _ hk hk', (isSaturating_diagGL d).glMultiplier_eq, h_det, map_prod]

/-- Let `den x` be the denominator of a finite idele `x` (`New.denominatorIdele`). Then
`χ_f (den x⁻¹) = χ_f x * χ_f (den x)` for `χ_f = υ |·|^(-1/2)`: this is the identity
`max 0 μ = μ + max 0 (-μ)` for the orders `μ` of `x`. -/
lemma chiFin_denominatorIdele_inv (x : (𝔸f E)ˣ) :
    chiFin (denominatorIdele x⁻¹) = chiFin x * chiFin (denominatorIdele x) := by
  refine (chiFin_congr fun w ↦ ?_).trans (chiFin.map_mul x (denominatorIdele x))
  have h_inv : x⁻¹.val w = (x.val w)⁻¹ := map_units_inv (evalAt w) x
  have h_ne : v (x.val w) ≠ 0 := by simpa using (x.isUnit.map (evalAt w)).ne_zero
  have h_max : max 1 (v (x.val w))⁻¹ = (v (x.val w))⁻¹ * max 1 (v (x.val w)) := by
    rw [mul_max, mul_one, inv_mul_cancel₀ h_ne, max_comm]
  simp [v_denominatorIdele, h_inv, h_max, mul_comm]

/-- The character `χ_f = υ |·|^(-1/2)` of the finite ideles turns the conjugation of `E` into
complex conjugation, as `υ (star x)` is the inverse of `υ x` on the unit circle. -/
lemma chiFin_star (x : (𝔸f E)ˣ) : chiFin (star x) = conj (chiFin x) := by
  have h_incl : finIdeleIncl (star x) = star (finIdeleIncl x) :=
    Units.ext (Prod.ext (star_one _).symm rfl)
  simp [chiFin, h_incl, chiAdelic, ← Circle.coe_inv_eq_conj, ← υ_star]

/-- For a finite idele `x`, the value of `χ_f = υ |·|^(-1/2)` at the denominator
(`New.denominatorIdele`) of `star x` is the complex conjugate of its value at the denominator of
`x`. -/
lemma chiFin_denominatorIdele_star (x : (𝔸f E)ˣ) :
    chiFin (denominatorIdele (star x)) = conj (chiFin (denominatorIdele x)) := by
  rw [← chiFin_star]
  exact chiFin_congr fun w ↦ by simp only [v_denominatorIdele, Units.coe_star, v_star_apply]

/-- For an invertible matrix `g` over the finite adeles of `E`, Δ_f(g⁻¹) = υ(det g)|det g|^(−1/2)
Δ_f(g), where `chiFin` is the character x ↦ υ(x)|x|^(−1/2) with υ the splitting character of the
Weil data. Here Δ_f(g) = χ_f(det u) (`New.glMultiplier`), where `u` is the chosen matrix with
uÔ^ι = Ô^ι ∩ g⁻¹Ô^ι. -/
lemma glMultiplier_inv : glMultiplier g⁻¹ = chiFin g.det * glMultiplier g := by
  obtain ⟨k, hk, k', hk', d, rfl⟩ := exists_eq_mul_diagGL_mul g
  have h_inv : (k * diagGL d * k')⁻¹ = k'⁻¹ * diagGL d⁻¹ * k⁻¹ := by simp [map_inv, mul_assoc]
  have h_det : chiFin (k * diagGL d * k').det = ∏ i : ι, chiFin (d i) := by
    have h_diag : (diagGL d).det = ∏ i : ι, d i := Units.ext (by simp)
    simp [chiFin_det_eq_one_of_mem hk, chiFin_det_eq_one_of_mem hk', h_diag]
  rw [h_inv, glMultiplier_mul_diagGL_mul (inv_mem hk') (inv_mem hk), h_det,
    glMultiplier_mul_diagGL_mul hk hk', ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ ↦ chiFin_denominatorIdele_inv (d i)

/-- An invertible matrix `g` over the finite adeles and its transpose have the same elementary
divisors, hence the same multiplier `Δ_f` (`New.glMultiplier`). -/
lemma glMultiplier_transposeGL : glMultiplier (transposeGL g) = glMultiplier g := by
  obtain ⟨k, hk, k', hk', d, rfl⟩ := exists_eq_mul_diagGL_mul g
  have h_transpose : transposeGL (k * diagGL d * k') = transposeGL k' * diagGL d * transposeGL k :=
    Units.ext (by simp [mul_assoc])
  rw [h_transpose, glMultiplier_mul_diagGL_mul hk hk', glMultiplier_mul_diagGL_mul
    ((transposeGL_mem_intGL_iff k').2 hk') ((transposeGL_mem_intGL_iff k).2 hk)]

/-- If `u` saturates `b`, then `New.glMultiplier` of the transpose of `b` is also `χ_f (det u)`. -/
lemma IsSaturating.glMultiplier_transpose (h : IsSaturating (Ô E).matrix b u)
    (h_transpose : b'.val = bᵀ) : glMultiplier b' = chiFin u.det := by
  have hb' : b' = transposeGL b := Units.ext h_transpose
  rw [hb', glMultiplier_transposeGL, h.glMultiplier_eq]

/-- For `γ` in `GL_ι` over the finite adeles of the CM field `E`, applying the conjugation of `E`
entrywise to `γ` replaces its multiplier Δ_f(γ) (`New.glMultiplier`) by the complex conjugate. Here
Δ_f(γ) = χ_f(det u), where χ_f(x) = υ(x)|x|^(−1/2) (`New.chiFin`) and `u` is the chosen matrix with
uÔ^ι = Ô^ι ∩ γ⁻¹Ô^ι. -/
lemma glMultiplier_map_star (γ : GL ι (𝔸f E)) :
    glMultiplier (γ.map (starRingEnd (𝔸f E))) = conj (glMultiplier γ) := by
  obtain ⟨k, hk, k', hk', d, rfl⟩ := exists_eq_mul_diagGL_mul γ
  have h_mem {x : GL ι (𝔸f E)} (hx : x ∈ intGL ι (Ô E)) :
      x.map (starRingEnd (𝔸f E)) ∈ intGL ι (Ô E) :=
    mem_intGL.2 ⟨fun i j ↦ star_mem_Ô ((mem_intGL.1 hx).1 i j),
      fun i j ↦ star_mem_Ô ((mem_intGL.1 hx).2 i j)⟩
  have h_diag : (diagGL d).map (starRingEnd (𝔸f E)) = diagGL fun i : ι ↦ star (d i) :=
    Units.ext (diagonal_map (star_zero _))
  rw [map_mul, map_mul, h_diag, glMultiplier_mul_diagGL_mul (h_mem hk) (h_mem hk')]
  simp [glMultiplier_mul_diagGL_mul hk hk', chiFin_denominatorIdele_star]

/-- Let E be a CM field with Weil data and `b` an element of `GL_ι(𝔸_f)`. The multiplier `Δ_f`
(`New.glMultiplier`) of the conjugate transpose `star b` is the complex conjugate of `Δ_f b`. Here
Δ_f(b) = χ_f(det u), where u is the chosen matrix with uÔ^ι = Ô^ι ∩ b⁻¹Ô^ι, χ_f = υ|·|^(−1/2), and
υ is the splitting character of the Weil data. -/
lemma glMultiplier_star : glMultiplier (star b) = conj (glMultiplier b) := by
  have h_star : star b = transposeGL (b.map (starRingEnd (𝔸f E))) := Units.ext rfl
  rw [h_star, glMultiplier_transposeGL, glMultiplier_map_star]

/-- Let `b`, `b'` be invertible `ι × ι` matrices over the finite adeles of `E` such that at every
finite place at least one of them has component `1`. Then the multiplier `Δ_f` (`New.glMultiplier`)
satisfies `Δ_f (b * b') = Δ_f b * Δ_f b'`. Here `Δ_f g = χ_f (det u)`, where `u` is a chosen matrix
with `u Ô^ι = Ô^ι ∩ g⁻¹ Ô^ι`. -/
lemma glMultiplier_mul_of_map_evalAt_eq_one
    (h_supp : ∀ x : FinPlace E, b.map (evalAt x) = 1 ∨ b'.map (evalAt x) = 1) :
    glMultiplier (b * b') = glMultiplier b * glMultiplier b' := by
  -- The valuation at `w` of the determinant of the chosen matrix depends only on the component at
  -- `w`, and it is `1` for the component `1`.
  rw [glMultiplier, glMultiplier, glMultiplier, ← map_mul]
  refine chiFin_congr fun w ↦ ?_
  have h_local {x y : GL ι (𝔸f E)} (hxy : x.map (evalAt w) = y.map (evalAt w)) :
      v ((saturatingElem x).val.val.det w) = v ((saturatingElem y).val.val.det w) := by
    obtain ⟨u, hu⟩ : ∃ u : GL ι (𝔸f E), IsSaturating (Ô E).matrix y u := exists_isSaturating y
    have h_sat : IsSaturating (LocInt w).matrix (x.map (evalAt w)) (u.map (evalAt w)) := by
      simpa only [hxy] using hu.map_evalAt w
    rw [h_sat.v_det_saturatingElem, (hu.map_evalAt w).v_det_saturatingElem]
  obtain hb | hb' := h_supp w
  · have h_comp : (b * b').map (evalAt w) = b'.map (evalAt w) := by rw [map_mul, hb, one_mul]
    simp [h_local h_comp, v_det_saturatingElem_eq_one hb]
  · have h_comp : (b * b').map (evalAt w) = b.map (evalAt w) := by rw [map_mul, hb', mul_one]
    simp [h_local h_comp, v_det_saturatingElem_eq_one hb']

omit [WeilData E] in
/-- For a bijection `e : n ≃ ι ⊕ κ` and `x`, `y` in `GL_ι(Ô)`, `GL_κ(Ô)`, the block diagonal
matrix of `x` and `y`, relabelled along `e`, lies in `GL_n(Ô)`. -/
lemma reindexGL_blockGL_mem_intGL [DecidableEq κ] {n : Type*} [Fintype n] [DecidableEq n]
    (e : n ≃ ι ⊕ κ) {x : GL ι (𝔸f E)} {y : GL κ (𝔸f E)} (hx : x ∈ intGL ι (Ô E))
    (hy : y ∈ intGL κ (Ô E)) : reindexGL e.symm (blockGL (x, y)) ∈ intGL n (Ô E) := by
  simp only [mem_intGL, ← map_inv] at hx hy ⊢
  -- Without `-coe_units_inv` the entries of `x⁻¹` become those of a matrix inverse.
  simp [hx, hy, e.forall_congr_left, -coe_units_inv]

/-- For an invertible finite adelic matrix h over the CM field E with Weil data, write
Δ_f(h) = `glMultiplier h`, which is χ_f(det u) for a matrix u with uÔ^ι = Ô^ι ∩ h⁻¹Ô^ι, where
χ_f = υ|·|^(-1/2). Δ_f is multiplicative on blocks: if an invertible finite adelic matrix G is,
after reindexing by a bijection e, block diagonal with invertible blocks g and g′, then
Δ_f(G) = Δ_f(g)Δ_f(g′). -/
lemma glMultiplier_fromBlocks [DecidableEq κ] (g' : GL κ (𝔸f E)) {n : Type*} [Fintype n]
    [DecidableEq n] (e : n ≃ ι ⊕ κ) {G : GL n (𝔸f E)}
    (h_block : G.val = (fromBlocks g.val 0 0 g'.val).submatrix e e) :
    glMultiplier G = glMultiplier g * glMultiplier g' := by
  -- The elementary divisors of `G` are those of `g` together with those of `g'`.
  obtain ⟨k₁, hk₁, l₁, hl₁, d₁, rfl⟩ := exists_eq_mul_diagGL_mul g
  obtain ⟨k₂, hk₂, l₂, hl₂, d₂, rfl⟩ := exists_eq_mul_diagGL_mul g'
  let block : GL ι (𝔸f E) × GL κ (𝔸f E) →* GL n (𝔸f E) :=
    (reindexGL e.symm).toMonoidHom.comp blockGL
  have h_diag : block (diagGL d₁, diagGL d₂) = diagGL (Sum.elim d₁ d₂ ∘ e) :=
    Units.ext (by simp [block, fromBlocks_diagonal, e.forall_congr_left])
  have hG : G = block (k₁, k₂) * diagGL (Sum.elim d₁ d₂ ∘ e) * block (l₁, l₂) := by
    rw [← h_diag, ← map_mul, ← map_mul]
    exact Units.ext (h_block.trans (by simp [block]))
  rw [hG, glMultiplier_mul_diagGL_mul (k := block (k₁, k₂)) (k' := block (l₁, l₂))
      (reindexGL_blockGL_mem_intGL e hk₁ hk₂) (reindexGL_blockGL_mem_intGL e hl₁ hl₂),
    glMultiplier_mul_diagGL_mul hk₁ hl₁, glMultiplier_mul_diagGL_mul hk₂ hl₂]
  -- The product over `n` is the product over `ι ⊕ κ`, which splits into two products.
  simpa using e.prod_comp fun j : ι ⊕ κ ↦ chiFin (denominatorIdele (Sum.elim d₁ d₂ j))

/-- Let E be a CM field with Weil data and `b` an element of `GL_ι(𝔸_f)`. Let `Δ_f b` = χ_f(det u),
where u is the chosen matrix with uÔ^ι = Ô^ι ∩ b⁻¹Ô^ι, `χ_f = υ |·|^(-1/2)` on finite ideles
(extended by 1 at infinity), and υ is the splitting character of the Weil data. The product of `Δ_f`
at the conjugate transpose of `b⁻¹` and `Δ_f b` is `‖Δ_f b‖ ^ 2` times the complex conjugate of
`χ_f (det b)`. -/
lemma glMultiplier_star_inv_mul :
    glMultiplier (star b⁻¹) * glMultiplier b = ‖glMultiplier b‖ ^ 2 * conj (chiFin b.det) := by
  rw [glMultiplier_star, glMultiplier_inv, map_mul, mul_assoc, Complex.conj_mul', mul_comm]

/-- Let `b` in `GL_ι(𝔸_f)` be `1` away from the place `w`, and let `y` saturate the component of
`b` at `w` over `O_w`, so that `det y` has order `n = -log (v (det y))`, which is not negative.
Then `Δ_f b = (υ.atUniformizer w * √q) ^ n`, where `υ.atUniformizer w` is the value of `υ` at a
uniformiser of `w` and `q = w.q` is the size of the residue field. -/
lemma glMultiplier_eq_pow_of_local {y : (Matrix ι ι (LocField w))ˣ}
    (h_away : ∀ x : FinPlace E, x ≠ w → b.map (evalAt x) = 1)
    (h_sat : IsSaturating (LocInt w).matrix (b.map (evalAt w)) y) :
    glMultiplier b = (υ.atUniformizer w * √w.q) ^ (-(v y.val.det).log).toNat := by
  set n : ℕ := (-(v y.val.det).log).toNat
  -- The determinant of the chosen matrix has the valuations of the idele that is ϖ_w ^ n at w
  -- and 1 elsewhere.
  have h_val (x : FinPlace E) :
      v ((det (saturatingElem b).val).val x) = v ((locIdele w (uniformizer w) ^ n).val x) := by
    obtain rfl | hx := eq_or_ne x w
    · have h_le : v y.val.det ≤ 1 := (v.mem_integer_iff _).1 (IsIntMatrix.det_mem h_sat.val_mem)
      simp [h_sat.v_det_saturatingElem, n, det_ne_zero, WithZero.log_le_iff_le_exp, h_le]
    · simpa [hx] using v_det_saturatingElem_eq_one (h_away x hx)
  -- At the local idele of ϖ_w the character `χ_f` has the value `υ(ϖ_w) √q_w`, as |ϖ_w|⁻¹ = q_w.
  have h_norm : ‖(uniformizer w).val‖⁻¹ = w.q := by simp [norm_locField_eq_q_zpow]
  have h_unif : chiFin (locIdele w (uniformizer w)) = υ.atUniformizer w * √w.q := by
    change υ.atUniformizer w * (↑√(ideleAbs (locFullIdele w (uniformizer w))))⁻¹ = υ.atUniformizer w
      * √w.q
    rw [ideleAbs_locFullIdele, ← h_norm, Real.sqrt_inv, Complex.ofReal_inv]
  rw [glMultiplier, chiFin_congr h_val, map_pow, h_unif]

omit [WeilData E] in
/-- Let `g`, `u` be invertible `ι × ι` matrices over the finite adeles `𝔸f E`, with `u` saturating
`g` over integral matrices (`New.IsSaturating`): `u` and `g u` have entries in `Ô`, and
`u⁻¹ = l + m g` for some matrices `l`, `m` over `Ô`. Then the vectors `x` of the lattice `Ô^ι`
(`New.stdLattice`) with `g x` in `Ô^ι` are exactly those with `u⁻¹ x` in `Ô^ι`, that is,
`Ô^ι ∩ g⁻¹ Ô^ι = u Ô^ι`. -/
lemma IsSaturating.setOf_mulVec_mem_stdLattice (h : IsSaturating (Ô E).matrix g u) :
    {x : ι → 𝔸f E | g *ᵥ x ∈ stdLattice E ι ∧ x ∈ stdLattice E ι} =
      u⁻¹.val.mulVec ⁻¹' stdLattice E ι := by
  ext x
  refine ⟨fun ⟨hgx, hx⟩ ↦ ?_, fun hx ↦ ?_⟩
  · obtain ⟨-, -, l, hl, m, hm, hlm⟩ := h
    have h_eq : u⁻¹.val *ᵥ x = l *ᵥ x + m *ᵥ g.val *ᵥ x := by rw [hlm, add_mulVec, mulVec_mulVec]
    rw [Set.mem_preimage, h_eq]
    exact add_mem (IsIntMatrix.mulVec hl hx) (IsIntMatrix.mulVec hm hgx)
  · have h_gx : (g.val * u.val) *ᵥ u⁻¹.val *ᵥ x ∈ stdLattice E ι :=
      IsIntMatrix.mulVec h.mul_val_mem hx
    have h_x : u.val *ᵥ u⁻¹.val *ᵥ x ∈ stdLattice E ι := IsIntMatrix.mulVec h.val_mem hx
    exact ⟨by simpa using h_gx, by simpa using h_x⟩

/-- For `g` in `GL_ι(𝔸_f)` with multiplier `Δ_f g` (`New.glMultiplier`), the set of `x` in `Ô^ι`
with `g x` in `Ô^ι` has volume `(‖Δ_f g‖ ^ 2)⁻¹` for `New.latticeMeasure`, the Haar measure giving
the lattice `Ô^ι` mass one. -/
lemma latticeMeasure_inter_eq_glMultiplier :
    (latticeMeasure E ι).real {x : ι → 𝔸f E | g *ᵥ x ∈ stdLattice E ι ∧ x ∈ stdLattice E ι} =
      (‖glMultiplier g‖ ^ 2)⁻¹ := by
  -- The set is `u • stdLattice E ι` for a saturating `u`, so its volume is `|det u|`.
  obtain ⟨u, h⟩ := IsSaturating.exists_isSaturating g
  rw [Measure.real, h.setOf_mulVec_mem_stdLattice, h.glMultiplier_eq,
    ← Measure.map_apply (by fun_prop) isOpen_stdLattice.measurableSet, map_mulVec_haar_finAdele]
  -- Both sides are `|det u|`: the modulus of `χ_f` is `|·|^(-1/2)`.
  simp [chiFin, finIdeleAbs, Circle.norm_coe]

/-- For an invertible `ι × ι` matrix `γ` over the finite adeles of `E` the squared modulus of the
multiplier `Δ_f γ` (`New.glMultiplier`) is the index of `Ô^ι ∩ γ⁻¹ Ô^ι` in `Ô^ι`, where `Ô^ι` is
the lattice `stdLattice E ι` of integral vectors. -/
lemma norm_glMultiplier_sq (γ : GL ι (𝔸f E)) :
    ‖glMultiplier γ‖ ^ 2 = ((stdLattice E ι).comap γ.val.mulVecLin).relIndex (stdLattice E ι) := by
  -- Both sides are the inverse of the volume of `γ⁻¹ Ô^ι ∩ Ô^ι`.
  let Λ : AddSubgroup (ι → 𝔸f E) := (stdLattice E ι).comap γ.val.mulVecLin.toAddMonoidHom
  have h_vol : latticeMeasure E ι (Λ ∩ stdLattice E ι) = (↑(Λ.relIndex (stdLattice E ι)))⁻¹ :=
    measure_inter_eq_inv_relIndex_add isCompact_stdLattice
      (isOpen_stdLattice.preimage (f := γ.val.mulVec) (by fun_prop)) _ latticeMeasure_stdLattice
  apply inv_injective
  calc (‖glMultiplier γ‖ ^ 2)⁻¹ = (latticeMeasure E ι (Λ ∩ stdLattice E ι)).toReal :=
      (latticeMeasure_inter_eq_glMultiplier γ).symm
    _ = (Λ.relIndex (stdLattice E ι) : ℝ)⁻¹ := by simp [h_vol]

/-! ### The multiplier on the finite unitary group -/

/-- For g in the finite adelic unitary group, Δ_f(g) is `New.glMultiplier` of its underlying
invertible matrix. -/
def finMultiplier (g : Gf E ι) : ℂ := glMultiplier g.val

/-- Let `g` be in the finite adelic unitary group `Gf E ι`, that is, `g` is in `GL_ι(𝔸_f)` with
`gᴴ g = 1`. The multiplier `Δ_f` (`finMultiplier`, which is `glMultiplier` of the underlying matrix)
satisfies `Δ_f g⁻¹ = conj (Δ_f g)`, the complex conjugate of `Δ_f g`. -/
lemma finMultiplier_inv (g : Gf E ι) : finMultiplier g⁻¹ = conj (finMultiplier g) := by
  -- The inverse of a unitary matrix is its conjugate transpose.
  have h_inv : g⁻¹.val = star g.val := Units.ext (U.inv_val_eq_conjTranspose g)
  rw [finMultiplier, h_inv, glMultiplier_star, finMultiplier]

variable {E : Type*} [Field E] [NumberField E] [IsCMField E] in
/-- Let `γ` be in the group `New.Gf E ι` of unitary `ι × ι` matrices over the finite adeles of the
CM field `E` and let `y` saturate `γ` over integral matrices. At every finite place `w` the
valuation of `det γ * det y` is that of the conjugate of `det y`: the elementary divisors of
`γ⁻¹ = γ*` are the conjugates of those of `γ`. -/
lemma IsSaturating.v_det_mul_v_det (γ : Gf E ι) {y : GL ι (𝔸f E)}
    (hy : IsSaturating (Ô E).matrix γ.val y) (w : FinPlace E) :
    v (γ.val.val.det w) * v (y.val.det w) = v (y.val.det (star w)) := by
  obtain ⟨k, hk, k', hk', d, hγ⟩ := exists_eq_mul_diagGL_mul γ.val
  have h_mem {x : GL ι (𝔸f E)} (hx : x ∈ intGL ι (Ô E)) : star x ∈ intGL ι (Ô E) :=
    mem_intGL.2 ⟨fun i j ↦ star_mem_Ô ((mem_intGL.1 hx).1 j i),
      fun i j ↦ star_mem_Ô ((mem_intGL.1 hx).2 j i)⟩
  have h_inv : γ.val⁻¹ = star k' * diagGL (star d) * star k := by
    have h_star : γ.val⁻¹ = star γ.val := Units.ext (U.inv_val_eq_conjTranspose γ)
    have h_diag : star (diagGL d) = diagGL (star d) := Units.ext (diagonal_conjTranspose _)
    rw [h_star, hγ, star_mul, star_mul, h_diag, mul_assoc]
  -- As `y` saturates `γ`, the product `γ * y` saturates `γ⁻¹`.
  have hy_inv : IsSaturating (Ô E).matrix (star k' * diagGL (star d) * star k) (γ.val * y) := by
    simpa only [h_inv] using hy.inv
  have hy_diag : IsSaturating (Ô E).matrix (k * diagGL d * k') y := by rwa [← hγ]
  calc v (γ.val.val.det w) * v (y.val.det w) = v ((γ.val * y).val.det w) := by simp
    _ = ∏ i : ι, (max 1 (v ((star (d i)).val w)))⁻¹ := hy_inv.v_det_eq_prod (h_mem hk') (h_mem hk) w
    _ = ∏ i : ι, (max 1 (v ((d i).val (star w))))⁻¹ := by simp only [Units.coe_star, v_star_apply]
    _ = v (y.val.det (star w)) := (hy_diag.v_det_eq_prod hk hk' (star w)).symm

/-- The multiplier is `1` on the stabiliser `stdLevel E ι` of the standard lattice. -/
lemma finMultiplier_eq_one_of_mem {k : Gf E ι} (hk : k ∈ stdLevel E ι) : finMultiplier k = 1 := by
  have h_sat : IsSaturating (Ô E).matrix k.val 1 := .of_mem (mem_stdLevel.1 hk)
  simp [finMultiplier, h_sat.glMultiplier_eq]

lemma finMultiplier_ne_zero (g : Gf E ι) : finMultiplier g ≠ 0 := (chiFin.toHomUnits _).ne_zero

/-- Let E be a CM field with Weil data and g an element of the finite adelic unitary group (gᴴg = 1
in GL_ι(𝔸_f)). Let Δ_f(g) = χ_f(det u), where u is the chosen matrix with uÔ^ι = Ô^ι ∩ g⁻¹Ô^ι,
χ_f = υ|·|^(−1/2), and υ is the splitting character of the Weil data. Then |Δ_f(g)|² equals the
index of Ô^ι ∩ g⁻¹Ô^ι in Ô^ι. -/
lemma norm_finMultiplier_sq (g : Gf E ι) :
    ‖finMultiplier g‖ ^ 2 =
      ((stdLattice E ι).comap g.val.val.mulVecLin).relIndex (stdLattice E ι) :=
  norm_glMultiplier_sq g.val

variable {E : Type*} [Field E] [NumberField E] [IsCMField E] in
lemma Gf.finIdeleAbs_det (g : Gf E ι) : finIdeleAbs g.val.det = 1 := by
  have h_det : (g.val.det : 𝔸f E) ∈ unitary (𝔸f E) := (U.det (by simp) g).prop
  -- The idele with finite part `det g` is `1` at the infinite places, so it is unitary too.
  exact ideleAbs_eq_one_of_mem_unitary ⟨Prod.ext ((mul_one _).trans (star_one _)) h_det.1,
    Prod.ext ((one_mul _).trans (star_one _)) h_det.2⟩

/-- Let E be a CM field with Weil data and g an element of the finite adelic unitary group G_f
(matrices g in GL_ι(𝔸_f) with gᴴg = 1). Let Δ_f(g) = χ_f(det u), where u is the chosen matrix with
uÔ^ι = Ô^ι ∩ g⁻¹Ô^ι, χ_f = υ|·|^(−1/2) on finite ideles, and υ is the splitting character of the
Weil data. Then υ(det g)·Δ_f(g) is the complex conjugate of Δ_f(g), where det g is read as an idele
with component 1 at the infinite places. -/
lemma upsilon_mul_finMultiplier (g : Gf E ι) :
    υ.val (finIdeleIncl g.val.det) * finMultiplier g = conj (finMultiplier g) := by
  -- Both sides are `Δ_f(g⁻¹) = χ_f(det g) Δ_f(g)`, as `det g` has idele norm `1`.
  have h_abs : ideleAbs (finIdeleIncl g.val.det) = 1 := g.finIdeleAbs_det
  rw [← finMultiplier_inv g]
  simp [finMultiplier, glMultiplier_inv, chiFin, h_abs]

/-- Let E be a CM field with Weil data, S a set of finite places disjoint from its conjugate S̄, and
g an element of the finite adelic unitary group G_f (matrices g in GL_ι(𝔸_f) with gᴴg = 1) whose
component is 1 at every place outside S ∪ S̄. Let `a = cutGL _ g` be the invertible matrix equal to
g at the places of S and to 1 elsewhere. Then `finMultiplier g` (that is, Δ_f of g viewed in
GL_ι(𝔸_f)) equals |Δ_f(a)|² · conj χ_f(det a), where Δ_f(h) = `glMultiplier h` is χ_f(det u) for a
matrix u with uÔ^ι = Ô^ι ∩ h⁻¹Ô^ι, and χ_f = υ|·|^(-1/2) is `New.chiFin`, with υ the splitting
character of the Weil data. -/
lemma finMultiplier_eq_of_supportedOn {S : Set (FinPlace E)} (hS : Set.IsConjDisjoint S)
    {g : Gf E ι} (hg : g ∈ Gf.supportedOn ι S) :
    let a : GL ι (𝔸f E) := cutGL (idem_mul_self S) g.val
    finMultiplier g = ‖glMultiplier a‖ ^ 2 * conj (chiFin a.det) := by
  classical
  -- `g = star a⁻¹ * a`, where `a` lives above `S` and `star a⁻¹` above the conjugate places.
  intro a
  have h_disj (w : FinPlace E) (hw : w ∈ S) : star w ∉ S := Set.disjoint_left.1 hS hw
  have h_a (w : FinPlace E) : a.map (evalAt w) = if w ∈ S then g.atPlace w else 1 :=
    map_evalAt_cutGL w S _
  -- Unitarity determines `g` at `w` from `g` at `star w`.
  have h_star (w : FinPlace E) :
      (star a⁻¹).map (evalAt w) = if star w ∈ S then g.atPlace w else 1 := by
    by_cases hw : star w ∈ S <;> simp [h_a, hw, Units.ext_iff, evalAt_star_GL (star_star _),
      g.atPlace_star (star_star w), -star_inv, -coe_units_inv]
  have h_supp (w : FinPlace E) : (star a⁻¹).map (evalAt w) = 1 ∨ a.map (evalAt w) = 1 := by
    grind
  have h_eq : g.val = star a⁻¹ * a := by
    refine GL_ext_evalAt fun w ↦ ?_
    change g.atPlace w = (star a⁻¹ * a).map (evalAt w)
    rw [map_mul, h_star, h_a]
    by_cases hw : w ∈ S <;> simp +contextual [hw, h_disj, Gf.mem_supportedOn.1 hg]
  rw [finMultiplier, h_eq, glMultiplier_mul_of_map_evalAt_eq_one h_supp, glMultiplier_star_inv_mul]

end New

namespace New.stdLattice

end New.stdLattice

end
