import Lib.Base

/-!
# Adic completeness: p-adic tools, extension by continuity, topological bases

This file collects tools on adic completeness over a commutative ring. It covers normed fields over
`ℚ_[p]`, divisibility by powers of an element `π`, maps of adic completions, monoid actions by ring
endomorphisms, extension of linear maps by adic continuity, and topological bases. In the results on
topological bases, `I` is an ideal of `S`, often `I = (p, z)`, and `M` is an `S`-module. For
`c : New.Lift.AdicBasis I M`, the `c.b i` are its vectors and the `c.coord i` its coordinate forms.

## Main definitions and results

* `New.shiftDiff`: the operator `(x_j) ↦ (x_j - π x_{j+1})` on sequences. By
  `New.isPrecomplete_of_shiftDiff_surjective`, if it is onto for `π = x` and for `π = y`, then
  `(x, y)`-adic Cauchy sequences converge.
* `New.Adic.ringHom_ext_of_approx`: two ring maps `F`, `G` from `A` to a `p`-adically separated ring
  are equal if every element of `A` is congruent, modulo each power of `p`, to an element on which
  they agree.
* `New.adicMap`: a ring map that carries `I` into `J` induces a map of adic completions.
* `New.exists_adic_extension`: a linear map `g` into an `I`-adically complete module extends along a
  map `β` with dense image, if `β f ∈ I ^ (n + n) • ⊤` implies `g f ∈ I ^ n • ⊤` for all `n`.
* `New.Lift.exists_adicBasis`: an `I`-adic topological basis of `M` over `S` exists when
  `I = (p, z)` is maximal, `S` is `I`-adically complete, `p` is zero or injective on `M`, and `z` is
  injective on `M / p M`. It may be taken to contain given vectors independent modulo `I M`.
* `New.free_finite_of_rank_le`: over a ring `S` that is complete for a maximal ideal `(p, z)`, a
  separated module of finite rank on which `p, z` behave as a regular sequence (or `p = 0` and `z`
  is regular) is finite and free. The proof uses the topological basis of
  `New.Lift.exists_adicBasis`.

Notions of this file:
* `New.Lift.AdicBasis`: a topological basis of `M` over `S` for the `I`-adic topology: vectors `b i`
  whose finite combinations are dense, with linear forms `coord i` on `M` that read off the
  coefficients of a finite combination.

## Relation to the literature

Known; see `Lib.PadicComparison.Completion` for sources.
-/

noncomputable section

/-!
## p-adic normed fields and divisibility by powers of π

* `New.PadicField`: normed fields over `ℚ_[p]`. `New.norm_p_eq_inv` gives the norm of `p` there,
  and `Nat.Coprime.norm_natCast_eq_one` that of natural numbers prime to `p`.
* `New.valRingCp`: the ring of integers of `ℂ_p`, a valuation ring with fraction field `ℂ_p`.
* `New.pow_dvd_of_map`, `New.smodEq_span_pow_iff_dvd`, `New.eq_of_forall_pow_dvd_sub`,
  `New.isUnit_of_dvd_sub`: divisibility by powers of `π`, and its use in `π`-adically separated or
  complete rings.
-/

namespace New

open Ideal Padic

/-- The statement that p is prime, as a class that fixes the prime p in scope. -/
class ThePrime (p : outParam ℕ) : Prop extends Fact p.Prime

/-! ### Normed fields over `ℚ_[p]` -/

/-- A normed field F that is a normed algebra over Q_p, not necessarily complete; the prime p is
read off from F (an `outParam`). -/
class PadicField (F : Type*) (p : outParam ℕ) [Fact p.Prime] [NormedField F] extends
  NormedAlgebra ℚ_[p] F

/-- For a prime ℓ, a choice of ring isomorphism ιℓ from ℂ to the algebraic closure of Q_ℓ. -/
class PadicIso (ℓ : outParam ℕ) [Fact ℓ.Prime] where
  /-- A ring isomorphism from ℂ to the algebraic closure of ℚ_ℓ. -/
  ιℓ : ℂ ≃+* PadicAlgCl ℓ

export PadicIso (ιℓ)

/-- A p-adic place of ℂ: a choice of ring homomorphism ιₚ from ℂ to C_p. -/
class PadicPlace (p : outParam ℕ) [Fact p.Prime] where
  /-- A ring homomorphism from ℂ to ℂ_p. -/
  ιₚ : ℂ →+* ℂ_[p]

export PadicPlace (ιₚ)

variable {R : Type*} (N : Type*) [CommRing R] [AddCommGroup N] [Module R N] {π x y : R}
  {p n : ℕ} [Fact p.Prime] {F : Type*} [NormedField F] [PadicField F p] {S : Type*} [CommRing S]

noncomputable instance : PadicField ℂ_[p] p where

noncomputable instance : PadicField (PadicAlgCl p) p where

lemma norm_p_eq_inv : ‖(p : F)‖ = (↑p)⁻¹ := by
  simpa using norm_algebraMap' F (p : ℚ_[p])

lemma norm_p_lt_one : ‖(p : F)‖ < 1 := by simp [norm_p_eq_inv, ← norm_p]

/-- The ring of integers of `ℂ_p`: the elements of norm at most one. It has the same elements as
Mathlib's `PadicComplexInt p`; here membership is the inequality `‖x‖ ≤ 1` by definition. -/
noncomputable def valRingCp (p : ℕ) [Fact p.Prime] : Subring ℂ_[p] :=
  (NormedField.valuation (K := ℂ_[p])).integer

@[simp]
lemma mem_valRingCp {x : ℂ_[p]} : x ∈ valRingCp p ↔ ‖x‖ ≤ 1 := Iff.rfl

@[simp]
lemma valRingCp.algebraMap_apply (x : valRingCp p) : algebraMap (valRingCp p) ℂ_[p] x = x := rfl

lemma valRingCp.dvd_iff_norm_le (x y : valRingCp p) : x ∣ y ↔ ‖(y : ℂ_[p])‖ ≤ ‖(x : ℂ_[p])‖ :=
  (Valuation.integer.integers (NormedField.valuation (K := ℂ_[p]))).dvd_iff_le

lemma valRingCp.isClosed : IsClosed (valRingCp p : Set ℂ_[p]) :=
  isClosed_Iic.preimage continuous_norm

instance : ValuationRing (valRingCp p) :=
  inferInstanceAs (ValuationRing (NormedField.valuation (K := ℂ_[p])).integer)

instance : IsFractionRing (valRingCp p) ℂ_[p] :=
  inferInstanceAs (IsFractionRing (NormedField.valuation (K := ℂ_[p])).integer ℂ_[p])

instance : IsLocalRing (valRingCp p) := ValuationRing.isLocalRing (valRingCp p)

instance : IsIntegrallyClosed (valRingCp p) :=
  inferInstanceAs (IsIntegrallyClosed (NormedField.valuation (K := ℂ_[p])).integer)

instance : Module.Flat (valRingCp p) ℂ_[p] :=
  IsLocalization.flat ℂ_[p] (nonZeroDivisors (valRingCp p))

/-- A natural number prime to `p` has norm one in every normed field over `ℚ_[p]`. -/
lemma _root_.Nat.Coprime.norm_natCast_eq_one (h_coprime : p.Coprime n) (F : Type*)
    [NormedField F] [PadicField F p] : ‖(n : F)‖ = 1 := by
  simpa [norm_natCast_eq_one_iff.mpr h_coprime] using norm_algebraMap' F (n : ℚ_[p])

/-! ### Divisibility by powers and adic completeness -/

/-- Let T map a commutative ring R to a commutative ring S with T(πa) = ϖT(a) for all a. Let ϖ be a
non-zero-divisor, and let ϖ ∣ T(a) imply π ∣ a for all a. Then ϖ^n ∣ T(x) implies π^n ∣ x. -/
lemma pow_dvd_of_map {ϖ : S} {T : R → S} (hT : ∀ a : R, T (π * a) = ϖ * T a)
    (hϖ : ϖ ∈ nonZeroDivisors S) (h_one : ∀ a : R, ϖ ∣ T a → π ∣ a) (h_pow : ϖ ^ n ∣ T x) :
    π ^ n ∣ x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    -- `x = π * b`, and `ϖ` cancels in `ϖ ^ (n + 1) ∣ T x = ϖ * T b`
    obtain ⟨b, rfl⟩ : π ∣ x := h_one x ((dvd_pow_self ϖ n.succ_ne_zero).trans h_pow)
    rw [hT, pow_succ', dvd_cancel_left_mem_nonZeroDivisors hϖ] at h_pow
    simpa [pow_succ'] using mul_dvd_mul_left π (ih h_pow)

/-- In a commutative ring, x and y are congruent modulo the submodule (π)^n of the ring if and only
if π^n divides x − y. -/
lemma smodEq_span_pow_iff_dvd :
    x ≡ y [SMOD ((span {π} : Ideal R) ^ n • ⊤ : Ideal R)] ↔ π ^ n ∣ x - y := by
  simp [SModEq.sub_mem, span_singleton_pow, mem_span_singleton]

/-- In a ring that is separated for `(π)`, two elements congruent modulo every power of `π` are
equal. -/
lemma eq_of_forall_pow_dvd_sub (π : R) [IsHausdorff (span {π}) R]
    (h_dvd : ∀ n : ℕ, π ^ n ∣ x - y) : x = y :=
  IsHausdorff.eq_iff_smodEq.2 fun n ↦ smodEq_span_pow_iff_dvd.2 (h_dvd n)

/-- In a ring that is complete for `(π)`, an element congruent to a unit modulo `π` is a unit. -/
lemma isUnit_of_dvd_sub [IsAdicComplete (span {π}) R] (hy : IsUnit y) (h_dvd : π ∣ x - y) :
    IsUnit x := by
  -- `x - y` lies in the Jacobson radical, so `(x - y) * y⁻¹ + 1 = x * y⁻¹` is a unit
  have h_jac : x - y ∈ jacobson ⊥ :=
    IsAdicComplete.le_jacobson_bot (span {π}) (mem_span_singleton.2 h_dvd)
  simpa [sub_mul] using mem_jacobson_bot.1 h_jac ↑hy.unit⁻¹

omit [Fact p.Prime] in
/-- An `S`-algebra that is `p`-adically complete as a ring is `p`-adically complete as an
`S`-module. -/
lemma isAdicComplete_over_base [Algebra S R] (h_complete : IsAdicComplete (span {(p : R)}) R) :
    IsAdicComplete (span {(p : S)}) R :=
  (IsAdicComplete.map_algebraMap_iff (S := R) (span {(p : S)}) R).1
    (by simpa [map_span] using h_complete)

/-- The operator `(x_j) ↦ (x_j - π x_{j+1})` on sequences in an `R`-module `N`. -/
def shiftDiff (π : R) (x : ℕ → N) (j : ℕ) : N := x j - π • x (j + 1)

lemma shiftDiff_apply (π : R) (u : ℕ → N) (j : ℕ) : shiftDiff N π u j = u j - π • u (j + 1) := rfl

/-- Let R be a commutative ring with elements x and y. Write `shiftDiff R π` for the operator
(a_j) ↦ (a_j − π a_{j+1}) on sequences in R. If it is surjective for π = x and for π = y, then R
is precomplete for the ideal (x, y): every (x, y)-adic Cauchy sequence has a limit. -/
lemma isPrecomplete_of_shiftDiff_surjective (hx : (shiftDiff R x).Surjective)
    (hy : (shiftDiff R y).Surjective) : IsPrecomplete (span {x, y}) R := by
  -- For a Cauchy sequence `f`, write `f (2n) - f (2n+2) = u n * x ^ n + v n * y ^ n` and solve
  -- `shiftDiff x U = u`, `shiftDiff y V = v`. Then `f (2n) - U n * x ^ n - V n * y ^ n` does not
  -- depend on `n`, and this constant is the limit.
  refine ⟨fun f hf ↦ ?_⟩
  simp only [SModEq.sub_mem, smul_eq_mul, mul_top] at hf ⊢
  -- `(x, y) ^ (n + n)` is contained in `(x ^ n, y ^ n)`
  have h_step (n : ℕ) : ∃ u v : R, u * x ^ n + v * y ^ n = f (n + n) - f (n + n + 2) := by
    have h_mem : f (n + n) - f (n + n + 2) ∈ (span {x} ⊔ span {y}) ^ (n + n) := by
      simp [← span_insert, hf]
    simpa [span_singleton_pow, ← span_insert, mem_span_pair] using sup_pow_add_le_pow_sup_pow h_mem
  choose u v huv using h_step
  obtain ⟨U, hU⟩ : ∃ U : ℕ → R, shiftDiff R x U = u := hx u
  obtain ⟨V, hV⟩ : ∃ V : ℕ → R, shiftDiff R y V = v := hy v
  have h_const (n : ℕ) : f 0 - U 0 - V 0 = f (n + n) - U n * x ^ n - V n * y ^ n := by
    induction n with
    | zero => simp
    | succ n ih =>
      -- the sums telescope: `u n * x ^ n = U n * x ^ n - U (n + 1) * x ^ (n + 1)`, and likewise
      -- for `y`
      have hu : u n = U n - x * U (n + 1) := by simp [← hU, shiftDiff_apply]
      have hv : v n = V n - y * V (n + 1) := by simp [← hV, shiftDiff_apply]
      grind
  refine ⟨f 0 - U 0 - V 0, fun n ↦ ?_⟩
  rw [show f n - (f 0 - U 0 - V 0) = f n - f (n + n) + U n * x ^ n + V n * y ^ n by grind]
  have h_mem {a b : R} (ha : a ∈ ({x, y} : Set R)) : b * a ^ n ∈ span {x, y} ^ n :=
    mul_mem_left _ _ (pow_mem_pow (subset_span ha) n)
  exact add_mem (add_mem (hf (by simp)) (h_mem (by simp))) (h_mem (by simp))

end New

/-! ## Ring maps to a p-adically separated ring that agree on a dense set -/

/-- Let `F` and `G` be ring maps from `A` to a `p`-adically separated ring `R`. If every element of
`A` is congruent, modulo each power of `p`, to an element on which `F` and `G` agree, then
`F = G`. -/
lemma New.Adic.ringHom_ext_of_approx {p : ℕ} {A R : Type*} [CommRing A] [CommRing R]
    [IsHausdorff (.span {(p : R)}) R] {F G : A →+* R}
    (h_approx : ∀ (a : A) (n : ℕ), ∃ b : A, F b = G b ∧ (p : A) ^ n ∣ a - b) : F = G := by
  refine F.ext fun a ↦ eq_of_forall_pow_dvd_sub p fun n ↦ ?_
  obtain ⟨b, hb, c, hc⟩ := h_approx a n
  have h_diff : F a - G a = (p : R) ^ n * (F c - G c) := by
    simp [sub_eq_iff_eq_add.mp hc, hb, mul_sub]
  exact ⟨F c - G c, h_diff⟩

namespace New

/-!
## Maps of adic completions and monoid actions by ring endomorphisms

* `New.PrincipalCompletion R π`: the `π`-adic completion of a ring `R`.
* `New.Adic.pow_dvd_iff_evalₐ_eq_zero`, `New.Adic.exists_approx`, `New.Adic.pow_dvd_iff`,
  `New.Adic.eq_zero_of_forall_pow_dvd`: the `π`-adic completion of `R` in terms of divisibility by
  powers of `π`.
* `New.actionOfHoms`, `New.extendAction`, `New.locAction`, `New.wittAction`: an action of a monoid
  `M` by ring endomorphisms, from a multiplicative family, and its extension along a ring map, to a
  localisation and to Witt vectors.
-/

section RingActions

open Ideal MulSemiringAction AdicCompletion IsLocalization Algebra algebraMap

variable (M : Type*) {R : Type*} {S : Type*} [Monoid M] [CommRing R] [MulSemiringAction M R]
  [CommRing S] {I : Ideal R} {J : Ideal S} (f : R →+* S) {π : R}

/-- For a ring homomorphism f: R → S carrying the ideal I into J, the induced ring homomorphism
from the I-adic completion of R to the J-adic completion of S. -/
@[irreducible]
def adicMap (h : I ≤ comap f J) : AdicCompletion I R →+* AdicCompletion J S :=
  -- the component in `S / J ^ n` is the image of the component in `R / I ^ n`
  liftRingHom J (fun n ↦ (quotientMap (J ^ n) f (by grw [← le_comap_pow, ← h])).comp (evalₐ I n))
    fun {m n} hmn ↦ by
      -- these components are compatible because those of `x` are
      ext x
      obtain ⟨a, rfl⟩ := AdicCompletion.mk_surjective I R x
      have h_sub : a n - a m ∈ I ^ m := by simpa using SModEq.sub_mem.1 (a.2 hmn).symm
      simpa [Quotient.factorPow, Ideal.Quotient.eq] using
        le_comap_pow f m (pow_right_mono h m h_sub)

/-- For a ring map `f : R → S` carrying the ideal `I` into `J`, the component of `adicMap f h x` in
`S / J ^ n` is the image of the component of `x` in `R / I ^ n`. -/
@[simp]
lemma evalₐ_adicMap (h : I ≤ comap f J) (n : ℕ) (x : AdicCompletion I R) :
    evalₐ J n (adicMap f h x) = quotientMap (J ^ n) f (by grw [h, le_comap_pow]) (evalₐ I n x) := by
  rw [adicMap]
  generalize_proofs
  exact evalₐ_liftRingHom _ _ (by assumption) n x

/-- For a ring map `f : R → S` carrying `I` into `J`, the induced map `adicMap f h` of adic
completions sends the image of `x : R` to the image of `f x`. -/
@[simp]
lemma adicMap_algebraMap (h : I ≤ comap f J) (x : R) :
    adicMap f h (x : AdicCompletion I R) = (f x : AdicCompletion J S) :=
  ext_evalₐ (by simp)

variable {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra A R]
  (i : R →+* B) (f : M → B →+* B) (m : M)

/-! ### Actions of a monoid by ring endomorphisms -/

/-- The action of a monoid M on a ring B by ring endomorphisms given by a family f(m) with f(1)
the identity and f(ab) = f(a)∘f(b). -/
abbrev actionOfHoms (h_one : f 1 = 1) (h_mul : ∀ a b : M, f (a * b) = f a * f b) :
    MulSemiringAction M B :=
  { MulSemiringAction.compHom B { toFun := f, map_one' := h_one, map_mul' := h_mul } with
    smul := fun m ↦ f m }

@[simp]
lemma smul_natCast' (n : ℕ) : m • (n : R) = n := smul_algebraMap m n

/-- The M-action on B given by endomorphisms f(m) compatible with the action on R along i: R →
B, when endomorphisms of B are determined on the image of i. -/
abbrev extendAction (hf : ∀ (m : M) (a : R), f m (i a) = i (m • a))
    (h_ext : ∀ {F G : B →+* B}, (∀ a : R, F (i a) = G (i a)) → F = G) :
    MulSemiringAction M B :=
  actionOfHoms M f (h_ext (by simp [hf])) fun a b ↦ h_ext (by simp [hf, mul_smul])

/-- The action of M on the localisation B of R away from x extending the action on R, given that
each m sends x to an element invertible in B. -/
abbrev locAction (x : R) [Algebra R B] [Away x B]
    (h_unit : ∀ m : M, IsUnit ((algebraMap R B).comp (toRingHom M R m) x)) :
    MulSemiringAction M B :=
  extendAction M (algebraMap R B) (fun m ↦ Away.lift x (h_unit m)) (by simp) fun h_eq ↦
    ringHom_ext (Submonoid.powers x) (RingHom.ext h_eq)

/-- A ring action of `M` on `R` induces an action of `M` on the Witt vectors `WittVector p R`. Each
element acts by mapping Witt vector coordinates through its ring endomorphism of `R`. -/
instance (priority := 50) wittAction (p : ℕ) [Fact p.Prime] :
    MulSemiringAction M (WittVector p R) :=
  actionOfHoms M (WittVector.map <| toRingHom M R ·) (by aesop) (by aesop (add simp mul_smul))

variable {M} [SMul M A]

instance : SMulDistribClass M R R := ⟨smul_mul'⟩

/-- Let `M` act on `A` and on the `A`-algebra `R`. If `m • (a • r) = (m • a) • (m • r)`, then the
algebra map `A → R` is equivariant. -/
@[simp]
lemma smul_algebraMap_eq_algebraMap_smul [SMulDistribClass M A R] (a : A) :
    m • (a : R) = ↑(m • a) :=
  (algebraMap.smul' m a R).symm

/-- In a tower `A → B → R` with actions of `M`, if the actions on `A` and `B` are compatible and
the map `B → R` is equivariant, then the actions on `A` and `R` are compatible. -/
lemma smulDistribClass_of_tower [Algebra A B] [Algebra B R] [IsScalarTower A B R]
    [MulSemiringAction M B] [SMulDistribClass M A B]
    (h_equiv : ∀ {m : M} (b : B), m • (b : R) = ↑(m • b)) :
    SMulDistribClass M A R where
  smul_distrib_smul m a r := by
    simp [smul_def, IsScalarTower.algebraMap_apply A B R, h_equiv]

/-- The `π`-adic completion of a ring `R`: its completion at the principal ideal `(π)`. -/
abbrev PrincipalCompletion.{u} (R : Type u) [CommRing R] (π : R) : Type u :=
  AdicCompletion (span {π}) R

namespace Adic

variable (x : PrincipalCompletion R π)

/-! ### The completion at a principal ideal -/

/-- For an element `π` of a commutative ring `R`, an element `x` of the `π`-adic completion
(`PrincipalCompletion R π`, that is `AdicCompletion (span {π}) R`) is divisible by the image of
`π ^ n` if and only if its image in `R / π ^ n` is zero. -/
@[local simp]
lemma pow_dvd_iff_evalₐ_eq_zero (n : ℕ) :
    (π : AdicCompletion (span {π}) R) ^ n ∣ x ↔ evalₐ (span {π}) n x = 0 := by
  -- Mathlib: for a finitely generated ideal `I`, the kernel of the `n`-th component is `I ^ n • ⊤`.
  have h_ker : span {π} ^ n • (⊤ : Submodule R (AdicCompletion (span {π}) R)) =
      LinearMap.ker (eval (span {π}) R n) := pow_smul_top_eq_ker_eval ⟨{π}, by simp⟩
  simpa [evalₐ, -quotientEquivAlgOfEq_coe_eq_factorₐ, span_singleton_pow, map_span,
    mem_span_singleton] using! SetLike.ext_iff.1 h_ker x

/-- Every element of the `π`-adic completion is congruent modulo `π ^ n` to an element of `R`. -/
lemma exists_approx (n : ℕ) : ∃ y : R, (π : AdicCompletion (span {π}) R) ^ n ∣ x - y :=
  ⟨(evalₐ (span {π}) n x).out, by simp⟩

variable {x} {X : Type*} [AddCommGroup X] [Module R X]

/-- For elements `π` and `y` of a commutative ring `R`, the image of `y` in the `π`-adic completion
`PrincipalCompletion R π` is divisible by the image of `π ^ n` if and only if `π ^ n ∣ y` in
`R`. -/
lemma pow_dvd_iff {n : ℕ} {y : R} :
    (π : PrincipalCompletion R π) ^ n ∣ (y : PrincipalCompletion R π) ↔ π ^ n ∣ y := by
  simp [Quotient.eq_zero_iff_mem, span_singleton_pow, mem_span_singleton]

lemma eq_zero_of_forall_pow_dvd (h_dvd : ∀ n : ℕ, (π : AdicCompletion (span {π}) R) ^ n ∣ x) :
    x = 0 :=
  ext_evalₐ fun n ↦ by simpa using (pow_dvd_iff_evalₐ_eq_zero x n).1 (h_dvd n)

lemma isAdicComplete :
    IsAdicComplete (span {(π : PrincipalCompletion R π)}) (PrincipalCompletion R π) := by
  simpa [map_span] using isAdicComplete_self (span {π}) ⟨{π}, by simp⟩

/-- Let `X` be a module over a commutative ring `R`. If a natural number `n` acts injectively on
`X`, then it acts injectively on the `n`-adic completion of `X`. -/
lemma isSMulRegular_completion {n : ℕ} (h_reg : IsSMulRegular X n) :
    IsSMulRegular (AdicCompletion (span {(n : R)}) X) n := by
  -- Multiplication by `n` is an isomorphism `e` of `X` onto `n X`. On completions it becomes
  -- the isomorphism induced by `e` followed by the injection of the completion of `n X`.
  let J : Ideal R := span {(n : R)}
  have h_range : LinearMap.range (n : Module.End R X) = J ^ 1 • ⊤ := by
    ext
    simp [J, Submodule.ideal_span_singleton_smul, Submodule.pointwise_smul_def,
      Nat.cast_smul_eq_nsmul]
  let e : X ≃ₗ[R] ↥(J ^ 1 • (⊤ : Submodule R X)) :=
    .ofInjective (n : Module.End R X) h_reg ≪≫ₗ .ofEq _ _ h_range
  -- both sides are determined by their effect on Cauchy sequences, where they agree termwise
  have h_comp : ofPowSMul J X 1 ∘ congr J e = fun x ↦ n • x := map_ext _ fun _ ↦ rfl
  rw [IsSMulRegular, ← h_comp]
  exact (ofPowSMul_injective _ 1).comp (congr _ e).injective

end Adic

end RingActions

/-!
## Extension by adic continuity and topological bases over a (p, z)-adic ring

The basis of `New.Lift.exists_adicBasis` lifts a basis of `M / I M`. By
`New.comap_span_pow_smul_le`, used twice, a combination that lies in `(p ^ n, z ^ n) M` has its
coefficients in `(p ^ n, z ^ n)`. This gives continuity.
-/

section AdicExtension

open Quot Ideal Submodule Finsupp AdicCompletion SModEq Function Module

variable {S F M : Type*} [CommRing S] [AddCommGroup F] [Module S F] [AddCommGroup M] [Module S M]
  {C : Type*} [AddCommGroup C] [Module S C] (I : Ideal S) [IsAdicComplete I C] (β : F →ₗ[S] M)
instance [IsPrecomplete I S] [Module.Finite S M] : IsPrecomplete I M := by
  -- `M → Ŝ ⊗ M` is onto since `S → Ŝ` is, and `Ŝ ⊗ M` maps onto the completion of the finite `M`.
  refine of_surjective_iff.mp fun x ↦ ?_
  simpa using (ofTensorProduct_surjective_of_finite I M).comp
    (TensorProduct.mk_surjective S M _ (of_surjective I S)) x

/-- A module that embeds linearly in a product of copies of an `I`-adically separated module is
`I`-adically separated. -/
lemma isHausdorff_of_injective_pi [IsHausdorff I F] {ι : Type*} (f : M →ₗ[S] ι → F)
    (hf : Function.Injective f) : IsHausdorff I M := by
  -- If `x` and `y` agree in the completion of `M`, so do the coordinates of `f x` and `f y`.
  refine of_injective_iff.mp fun x y hxy ↦ hf (funext fun i ↦ ?_)
  have h_coord : of I F ((LinearMap.proj i ∘ₗ f) x) = of I F ((LinearMap.proj i ∘ₗ f) y) := by
    rw [← map_of, ← map_of, hxy]
  exact of_inj.mp h_coord

/-- A finite free module over an `I`-adically complete ring is `I`-adically complete. -/
lemma isAdicComplete_of_free [IsAdicComplete I S] [Free S M] [Module.Finite S M] :
    IsAdicComplete I M :=
  have := isHausdorff_of_injective_pi I _ (Free.chooseBasis S M).equivFun.injective
  {}

/-- Let C be I-adically complete, β: F → M have I-adically dense image, and g: F → C satisfy
g(f) ∈ I^n C whenever β(f) ∈ I^{2n} M. Then g = G ∘ β for some S-linear G: M → C. -/
lemma exists_adic_extension (I : Ideal S) [IsAdicComplete I C] (β : F →ₗ[S] M)
    (g : F →ₗ[S] C) (h_dense : Surjective (mkQ (I • ⊤) ∘ₗ β))
    (h_cont : ∀ n : ℕ, Submodule.comap β (I ^ (n + n) • ⊤) ≤ Submodule.comap g (I ^ n • ⊤)) :
    ∃ G : M →ₗ[S] C, ∀ f : F, G (β f) = g f := by
  -- Pass to completions: `β` becomes onto, its kernel is killed by the completed `g`, and the
  -- completion of `C` is `C`.
  have hsurj : Surjective (AdicCompletion.map I β) := map_surjective_of_mkQ_comp_surjective h_dense
  have hker : LinearMap.ker (AdicCompletion.map I β) ≤ LinearMap.ker (AdicCompletion.map I g) := by
    refine (mk_surjective I F).forall.2 fun a ha ↦ ext fun n ↦ ?_
    have hβ : β (a (n + n)) ∈ I ^ (n + n) • (⊤ : Submodule S M) :=
      (Submodule.Quotient.mk_eq_zero _).1 (congrArg (·.1 (n + n)) ha)
    exact calc
      g (a n) ≡ g (a (n + n)) [SMOD I ^ n • ⊤] := (a.map I g).2 le_add_self
      _ ≡ 0 [SMOD I ^ n • ⊤] := zero.2 (mem_comap.1 (h_cont n hβ))
  -- `e` identifies the completion of `M` with a quotient of that of `F`; `G` is the induced map.
  let e : (AdicCompletion I F ⧸ LinearMap.ker (AdicCompletion.map I β)) ≃ₗ[AdicCompletion I S]
      AdicCompletion I M := LinearMap.quotKerEquivOfSurjective _ hsurj
  let G : AdicCompletion I M →ₗ[AdicCompletion I S] AdicCompletion I C :=
    liftQ _ (AdicCompletion.map I g) hker ∘ₗ e.symm.toLinearMap
  exact ⟨(ofLinearEquiv I C).symm.toLinearMap ∘ₗ G.restrictScalars S ∘ₗ of I M, fun f ↦ by
    simp [G, e, ← map_of, LinearEquiv.symm_apply_eq]⟩

/-- An element lies in `(a, b) M` if and only if it has the form `a • u + b • v`. -/
lemma mem_span_pair_smul_top {a b : S} {x : M} :
    x ∈ (Ideal.span {a, b} : Ideal S) • (⊤ : Submodule S M) ↔ ∃ u v : M, a • u + b • v = x := by
  simp [mem_singleton_set_smul, Ideal.span_insert, sup_smul, span_smul_eq, mem_sup]

/-- Let `β : F → M` be linear. Suppose that `β x ∈ (a, t) M` implies `x ∈ (a, t) F`, and that
`t • y ∈ a M` implies `y ∈ a M` or `t = 0`. Then `β x ∈ (t ^ n, a) M` implies
`x ∈ (t ^ n, a) F`. -/
lemma comap_span_pow_smul_le (β : F →ₗ[S] M) {a : S} (t : S)
    (h_one : Submodule.comap β (Ideal.span {a, t} • ⊤) ≤ Ideal.span {a, t} • ⊤)
    (h_div : ∀ y w : M, a • w = t • y → t = 0 ∨ ∃ c : M, a • c = y) (n : ℕ) :
    Submodule.comap β (Ideal.span {t ^ n, a} • ⊤) ≤ Ideal.span {t ^ n, a} • ⊤ := by
  simp only [IsConcreteLE.le_iff, Submodule.mem_comap, mem_span_pair_smul_top] at h_one ⊢
  induction n with
  | zero => exact fun x _ ↦ ⟨x, 0, by simp⟩
  | succ n ih =>
    rintro x ⟨v, u, hx⟩
    -- From `β x = t ^ (n + 1) • v + a • u` the case of the first power gives `x = a • u' + t • c`.
    obtain ⟨u', c, rfl⟩ :=
      h_one (x := x) ⟨u, t ^ n • v, by simp [← hx, add_comm, pow_succ', mul_smul]⟩
    have hrel : a • (u - β u') = t • (β c - t ^ n • v) := by
      grind [smul_sub, map_smul, pow_succ', mul_smul]
    -- By `h_div`, either `t = 0`, and `x = a • u'`, or `β c - t ^ n • v` is a multiple of `a`.
    obtain rfl | ⟨w, hw⟩ := h_div _ _ hrel
    · exact ⟨0, u', by simp⟩
    -- Now `β c = t ^ n • v + a • w`, so `c = t ^ n • m + a • m'` by induction.
    obtain ⟨m, m', rfl⟩ := ih (x := c) ⟨v, w, by simp [hw]⟩
    exact ⟨m, u' + t • m', by module⟩

/-- Suppose that `z • a ∈ p M` implies `a ∈ p M`, and that `p` is zero or acts injectively on `M`.
If `p • y ∈ z ^ n M`, then `p = 0` or `y ∈ z ^ n M`. -/
lemma eq_zero_or_exists_pow_smul_eq {p z : S}
    (hz : ∀ a b : M, z • a = p • b → ∃ c : M, a = p • c)
    (hp : ∀ a : M, p • a = 0 → p = 0 ∨ a = 0) (n : ℕ) (y w : M) (h_eq : z ^ n • w = p • y) :
    p = 0 ∨ ∃ c : M, z ^ n • c = y := by
  induction n generalizing y w with
  | zero => simp
  | succ n ih =>
    -- `z • z ^ n • w = p • y` gives `z ^ n • w = p • c`, then `p • (y - z • c) = 0`;
    -- now use `hp`, and `ih` for `c`.
    rw [pow_succ', mul_smul] at h_eq
    obtain ⟨c, hc⟩ : ∃ c : M, z ^ n • w = p • c := hz _ _ h_eq
    have h_zero : p • (y - z • c) = 0 := by rw [smul_sub, ← h_eq, hc, smul_comm, sub_self]
    obtain h | h := hp _ h_zero
    · exact .inl h
    exact (ih c w hc).imp_right fun ⟨c', hc'⟩ ↦ ⟨c', by grind [sub_eq_zero, pow_succ', mul_smul]⟩

/-- A topological basis of `M` over `S` for the `I`-adic topology: vectors `b i` whose finite
combinations are dense, with linear forms `coord i` on `M` that read off the coefficients of a
finite combination. -/
structure Lift.AdicBasis.{u} (M : Type u) [AddCommGroup M] [Module S M] where
  /-- The index set of the basis. -/
  (Index : Type u)
  /-- The basis vectors in `M`. -/
  (b : Index → M)
  /-- The coordinate forms. -/
  (coord : Index → M →ₗ[S] S)
  /-- Finite combinations of the vectors `b i` are dense for the `I`-adic topology. -/
  dense : Surjective (mkQ (I • ⊤) ∘ₗ linearCombination S b)
  /-- The `i`-th coordinate form reads off the `i`-th coefficient of a finite combination. -/
  dual (i : Index) (f : Index →₀ S) : coord i (linearCombination S b f) = f i

/-- Let `S` be `I`-adically complete for a maximal ideal `I = (p, z)`. Suppose that `z` is regular
on `M / p M` and that `p` is zero or regular on `M`. Then every set `t ⊆ M` whose elements have
linearly independent images in the `S / I`-vector space `M / I M` lies in the range of an `I`-adic
basis `c` of `M`. Such a basis is a family `c.b` whose finite `S`-combinations are `I`-adically
dense in `M`, with linear forms `c.coord i` on `M` that read off the coefficients of any finite
combination. -/
lemma Lift.exists_adicBasis {I : Ideal S} {p z : S} (hI : I = Ideal.span {p, z}) [I.IsMaximal]
    [IsAdicComplete I S] (hz : ∀ a b : M, z • a = p • b → ∃ c : M, a = p • c) (t : Set M)
    (ht : LinearIndepOn (S ⧸ I) (I • ⊤ : Submodule S M).mkQ t)
    (hp : ∀ a : M, p • a = 0 → p = 0 ∨ a = 0) :
    ∃ c : AdicBasis I M, t ⊆ Set.range c.b := by
  -- Extend `t` to a set `s` that lifts a basis of `M / I M`. Finite combinations of `s` map onto
  -- `M / I M`, and a combination in `I ^ (n + n) M` has coefficients in `I ^ n`, so the coordinates
  -- extend.
  let : Field (S ⧸ I) := Quotient.field I
  obtain ⟨s, -, hts, h_span, h_indep⟩ := exists_linearIndepOn_extension ht le_top
  let β : (s →₀ S) →ₗ[S] M := linearCombination S (↑)
  have dense : Surjective (mkQ (I • ⊤) ∘ₗ β) := ind fun y ↦ by
    -- A span over `S ⧸ I` is the span over `S`, as `S → S ⧸ I` is onto.
    have h_mem : mkQ (I • ⊤) y ∈ span S ((I • ⊤ : Submodule S M).mkQ '' s) :=
      (restrictScalars_span S _ mk_surjective _).le
        (h_span (Set.mem_image_of_mem _ (Set.mem_univ y)))
    simpa [mem_span_iff_linearCombination] using! h_mem
  -- Coefficients of a combination in `(p, z) M`, then `(z ^ n, p) M`, then `(p ^ n, z ^ n) M`.
  have coef₁ : comap β (span {p, z} • ⊤) ≤ span {p, z} • ⊤ := by
    -- This is the linear independence of `s` modulo `I M`.
    rw [← hI]
    intro x hx
    have h_sum : ∑ i ∈ x.support, mkQ (I • ⊤ : Submodule S M) (x i • (i : M)) = 0 :=
      (map_sum (mkQ _) _ _).symm.trans (zero.2 hx)
    have h_coef : ∀ i : s, Ideal.Quotient.mk I (x i) = 0 :=
      linearIndependent_iff''.1 h_indep _ (x ·) (by simp_all) h_sum
    simpa [← submodule_top, ← submodule_smul, Quotient.eq_zero_iff_mem] using h_coef
  have coef₂ (n : ℕ) : comap β (span {z ^ n, p} • ⊤) ≤ span {z ^ n, p} • ⊤ :=
    comap_span_pow_smul_le β z coef₁ (by grind) n
  -- The hypothesis of `comap_span_pow_smul_le` for the pair `z ^ n`, `p`, from `hp` and `hz`.
  have regular (n : ℕ) : ∀ y w : M, z ^ n • w = p • y → p = 0 ∨ ∃ c : M, z ^ n • c = y :=
    eq_zero_or_exists_pow_smul_eq hz hp n
  have coef₃ (n : ℕ) : comap β (span {p ^ n, z ^ n} • ⊤) ≤ span {p ^ n, z ^ n} • ⊤ :=
    comap_span_pow_smul_le β p (coef₂ n) (regular n) n
  have cont (i : s) (n : ℕ) :
      comap β (I ^ (n + n) • ⊤) ≤ Submodule.comap (lapply i) (I ^ n • (⊤ : Submodule S S)) := by
    intro f hf
    have le₁ : I ^ (n + n) ≤ span {p ^ n, z ^ n} := by
      simp [hI, ← span_singleton_pow, sup_pow_add_le_pow_sup_pow, Ideal.span_insert]
    have le₂ : span {p ^ n, z ^ n} ≤ I ^ n := by
      simp [hI, ← span_singleton_pow, pow_right_mono, Ideal.span_insert]
    have hf_coef : f ∈ I ^ n • (⊤ : Submodule S (s →₀ S)) :=
      smul_mono_left le₂ (coef₃ n (smul_mono_left le₁ hf))
    exact smul_top_le_comap_smul_top _ _ hf_coef
  choose coord h_coord using fun i : s ↦ exists_adic_extension I β (lapply i) dense (cont i)
  exact ⟨⟨s, (↑), coord, dense, h_coord⟩, by simpa⟩

end AdicExtension

end New

/-! ## Finite freeness from a bound on the rank -/

/-- Let `S` be complete for the maximal ideal `I = (p, z)`, and let `M` be an `I`-adically separated
`S`-module of finite rank. Suppose that `p` is zero or acts injectively on `M` (`hp`), and that `z`
acts injectively on `M / p M` (`hz`). Then `M` is free and finitely generated. -/
lemma New.free_finite_of_rank_le {S M : Type} [CommRing S] [Nontrivial S] [AddCommGroup M]
    [Module S M] {I : Ideal S} {p z : S} (hI : I = Ideal.span {p, z}) [I.IsMaximal]
    [IsAdicComplete I S] (h_sep : IsHausdorff I M)
    (hz : ∀ x y : M, z • x = p • y → ∃ w : M, x = p • w) (d : ℕ) (h_rank : Module.rank S M ≤ d)
    (hp : ∀ x : M, p • x = 0 → p = 0 ∨ x = 0) :
    Module.Free S M ∧ Module.Finite S M := by
  -- `M` has a topological basis `c.b` with coordinate forms dual to it (`c.dual`). It is linearly
  -- independent, so finite by the bound on the rank; it spans `M` modulo `I` (`c.dense`), so it
  -- spans `M` (`S` is complete and `M` is separated).
  obtain ⟨c : Lift.AdicBasis I M, -⟩ := Lift.exists_adicBasis hI hz ∅ (by simp) hp
  have h_indep : LinearIndependent S c.b :=
    linearIndependent_iff.2 fun f hf ↦ f.ext fun i ↦ by simp [← c.dual i f, hf]
  have : Finite c.Index :=
    Cardinal.mk_lt_aleph0_iff.1 ((h_indep.cardinal_le_rank.trans h_rank).trans_lt (by simp))
  have e : (c.Index →₀ S) ≃ₗ[S] M :=
    .ofBijective _ ⟨h_indep, surjective_of_mkQ_comp_surjective c.dense⟩
  exact ⟨.of_equiv e, .equiv e⟩

/-!
## The subgroup nX of multiples and the p-adic filtration

`New.Period.nsmulRange n X` is the subgroup `n X` of an abelian group `X`.
-/

namespace New.Period

open Ideal Submodule

/-- The subgroup nX of an abelian group X, for a natural number n. -/
abbrev nsmulRange (n : ℕ) (X : Type*) [AddCommGroup X] : AddSubgroup X :=
  (nsmulAddMonoidHom (α := X) n).range

variable {X Y S : Type*} [AddCommGroup X] [AddCommGroup Y] [CommRing S] [Module S X] [Module S Y]
  {p : ℕ}

/-- A linear map carries the subgroup `n X` of multiples into `n Y`. -/
lemma nsmulRange.map_mem (f : X →ₗ[S] Y) {n : ℕ} {x : X} :
    x ∈ nsmulRange n X → f x ∈ nsmulRange n Y := by
  rintro ⟨a, rfl⟩
  exact ⟨f a, (map_nsmul f n a).symm⟩

/-- For a module X over a commutative ring S and natural numbers p and k, the submodule (p)^k · X is
the subgroup p^k X of multiples. -/
lemma nsmulRange.mem_span_pow_smul_top_iff {k : ℕ} {x : X} :
    x ∈ Ideal.span {(p : S)} ^ k • (⊤ : Submodule S X) ↔ x ∈ nsmulRange (p ^ k) X := by
  simp [span_singleton_pow, span_smul_eq, mem_singleton_set_smul, ← Nat.cast_smul_eq_nsmul S,
    eq_comm]

end New.Period

/-!
## Approximation and membership through the coordinates of a basis

* `New.Lift.AdicBasis.mem_of_coord`, `New.Lift.AdicBasis.eq_zero_of_coord`: a submodule
  containing `I ^ n A` contains `y` if it contains every `c.coord i y • c.b i`. If `A` is
  `I`-adically separated, an element with all coordinates zero is zero.
-/

namespace New.Lift.AdicBasis

open Finsupp Submodule AdicCompletion

variable {S A : Type*} [CommRing S] [AddCommGroup A] [Module S A] {I : Ideal S} (c : AdicBasis I A)

/-- For a topological basis `c` of `A` (vectors `c.b i` with coordinate forms `c.coord i`): if
`y - ∑ f_j • c.b j` lies in `I ^ n A` for a finitely supported `f`, then `c.coord i y - f i` lies
in `I ^ n` for every `i`. -/
lemma coord_sub_mem_pow {n : ℕ} {y : A} {f : c.Index →₀ S}
    (h : y - linearCombination S c.b f ∈ I ^ n • (⊤ : Submodule S A)) (i : c.Index) :
    c.coord i y - f i ∈ I ^ n := by
  simpa [dual] using smul_top_le_comap_smul_top _ (c.coord i) h

/-- For a topological basis `c` of `A`, every `y` in `A`, every `n`, and every large enough finite
set `F` of indices, `y - ∑_{i ∈ F} c.coord i y • c.b i` lies in `I ^ n A`. -/
lemma eventually_sub_sum_mem (y : A) (n : ℕ) :
    ∀ᶠ F : Finset c.Index in Filter.atTop,
      y - ∑ i ∈ F, c.coord i y • c.b i ∈ I ^ n • (⊤ : Submodule S A) := by
  -- Finite combinations of the `c.b i` span `A / I A`, so they are dense in the `I`-adic topology.
  obtain ⟨a, ha⟩ : ∃ a : AdicCauchySequence I (c.Index →₀ S),
      AdicCompletion.map I (linearCombination S c.b) (AdicCompletion.mk I _ a) = of I A y :=
    (map_surjective_of_mkQ_comp_surjective c.dense).comp (mk_surjective I _) (of I A y)
  -- the `n`-th term `a n` of such a sequence approximates `y`
  have hf : y - linearCombination S c.b (a n) ∈ I ^ n • (⊤ : Submodule S A) :=
    (Submodule.Quotient.eq _).1 (congrArg (fun z : AdicCompletion I A ↦ z.1 n) ha).symm
  set f : c.Index →₀ S := a n
  -- every `F` that contains the support of the approximation `f` will do
  refine Filter.mem_atTop_sets.2 ⟨f.support, fun F hF ↦ (sub_mem_iff_right _ hf).1 ?_⟩
  -- the two approximations differ by `∑ (c.coord i y - f i) • c.b i`, with coefficients in `I ^ n`
  have h_diff : (y - linearCombination S c.b f) - (y - ∑ i ∈ F, c.coord i y • c.b i) =
      ∑ i ∈ F, (c.coord i y - f i) • c.b i := by
    simp [linearCombination_apply_of_mem_supported _ hF, sub_smul]
  rw [h_diff]
  exact sum_mem fun i _ ↦ smul_mem_smul (c.coord_sub_mem_pow hf i) mem_top

/-- For a topological basis `c` of `A`, a submodule `P ⊇ I ^ n A` contains `y` if it contains every
`c.coord i y • c.b i`. -/
lemma mem_of_coord {P : Submodule S A} {n : ℕ} {y : A} (hP : I ^ n • ⊤ ≤ P)
    (h : ∀ i : c.Index, c.coord i y • c.b i ∈ P) :
    y ∈ P := by
  -- `y` differs from a finite sum of the `c.coord i y • c.b i` by an element of `I ^ n • ⊤ ≤ P`
  obtain ⟨F, hF⟩ := (c.eventually_sub_sum_mem y n).exists
  exact (sub_mem_iff_left P (sum_mem fun i _ ↦ h i)).1 (hP hF)

/-- If `A` is `I`-adically separated, an element whose coordinates in a topological basis `c` are
all zero is zero. -/
lemma eq_zero_of_coord [H : IsHausdorff I A] {y : A} (h : ∀ i : c.Index, c.coord i y = 0) :
    y = 0 :=
  H.haus y fun n ↦ SModEq.zero.2 (c.mem_of_coord le_rfl fun i ↦ by simp [h])

end New.Lift.AdicBasis

/-!
## Successive approximation in complete modules

* Two instances: `New.shiftDiff π` is injective on a `π`-adically separated module and surjective on
  a `π`-adically complete one.
* `New.exists_eq_pow_mul_of_not_forall_dvd`: an element that is not divisible by all powers of `π`
  is `π ^ n * c` with `c` not divisible by `π`.
-/

namespace New

open IsHausdorff AdicCompletion Submodule

variable {R R' N M : Type*} [CommRing R] [CommRing R'] [AddCommGroup N] [Module R N]
  [AddCommGroup M] [Module R' M] {π : R} {π' : R'}

/-- On a `π`-adically separated module, `(x_j) ↦ (x_j - π • x_{j+1})` is injective. -/
instance [IsHausdorff (Ideal.span {π}) N] : Fact (shiftDiff N π).Injective := by
  -- Iterating `step` puts `x m - y m` in `π ^ k N` for every `k`, and `N` is Hausdorff.
  refine ⟨fun x y h ↦ IsHausdorff.funext (.span {π}) fun k m ↦ (Submodule.Quotient.eq _).mpr ?_⟩
  have step (j : ℕ) : x j - y j = π • (x (j + 1) - y (j + 1)) := by
    simpa [shiftDiff, smul_sub, sub_eq_sub_iff_sub_eq_sub] using congrFun h j
  induction k generalizing m with
  | zero => simp
  | succ k ih =>
    rw [step m, pow_succ', mul_smul]
    exact smul_mem_smul (mem_span_singleton_self π) (ih (m + 1))

/-- On a `π`-adically complete module, `(x_j) ↦ (x_j - π • x_{j+1})` is surjective. -/
instance [IsAdicComplete (Ideal.span {π}) N] : Fact (shiftDiff N π).Surjective := by
  refine ⟨fun y ↦ ?_⟩
  -- `shiftDiff N π` is the linear map `f`, which is the identity modulo `π`; so `f` is onto after
  -- `π`-adic completion.
  let f : (ℕ → N) →ₗ[R] ℕ → N := 1 - π • .funLeft R N .succ
  have hf : Function.Surjective (AdicCompletion.map (Ideal.span {π}) f) :=
    map_surjective_of_mkQ_comp_surjective <|
      Quot.ind fun z ↦ ⟨z, SModEq.sub_mem.mpr (by simp [f, smul_mem_smul])⟩
  obtain ⟨w, hw⟩ := hf (of (Ideal.span {π}) (ℕ → N) y)
  -- `N` is complete, so each coordinate of the preimage `w` comes from an element of `N`.
  refine ⟨fun j ↦ (ofLinearEquiv (.span {π}) N).symm (pi _ _ w j), funext fun j ↦ ?_⟩
  obtain ⟨x, rfl⟩ := mk_surjective _ _ w
  apply of_injective (.span {π})
  -- This is the `j`-th coordinate of `hw`, read in the completion of `N`.
  -- `using!`: `pi` and `mk` are computed on representatives by definition
  simpa [shiftDiff, f] using! congrArg (fun z ↦ pi (Ideal.span {π}) (fun _ : ℕ ↦ N) z j) hw

/-- Successive approximation: let `New.shiftDiff`, the operator `(x_j) ↦ (x_j - π • x_{j+1})` on
sequences, be surjective for `π` on `N` and injective for `π'` on `M`. Let `f : N → M` be additive
with `f (π • n) = π' • f n`. If every `g x` has the form `f n + π' • g y`, then every `g x` lies in
the range of `f`. -/
lemma mem_range_of_approx [s : Fact (shiftDiff N π).Surjective]
    [i : Fact (shiftDiff M π').Injective] (f : N →+ M) (hf : ∀ n : N, f (π • n) = π' • f n)
    {X : Type*} (g : X → M) (h : ∀ x : X, ∃ (n : N) (y : X), g x = f n + π' • g y) (x : X) :
    ∃ n : N, f n = g x := by
  -- Iterating `h` along `x, y x, y (y x), …` gives terms `n (y^[j] x)`; surjectivity of
  -- `shiftDiff N π` sums them to a sequence `u`, and injectivity of `shiftDiff M π'` identifies
  -- `f (u j)` with `g (y^[j] x)`.
  choose n y hstep using h
  obtain ⟨u, hu⟩ : ∃ u : ℕ → N, shiftDiff N π u = fun j ↦ n (y^[j] x) := s.out _
  have key : shiftDiff M π' (f ∘ u) = shiftDiff M π' fun j ↦ g (y^[j] x) := by
    ext j
    calc
      shiftDiff M π' (f ∘ u) j = f (u j - π • u (j + 1)) := by simp [shiftDiff, hf]
      _ = f (n (y^[j] x)) := congrArg f (congrFun hu j)
      _ = g (y^[j] x) - π' • g (y^[j + 1] x) := by
        simp [Function.iterate_succ_apply', hstep (y^[j] x)]
  exact ⟨u 0, by simpa using congrFun (i.out key) 0⟩

/-- An element that is not divisible by every power of `π` is `π ^ n * c` for some `n` and some
`c` not divisible by `π`. -/
lemma exists_eq_pow_mul_of_not_forall_dvd (π x : R) (h : ¬∀ n : ℕ, π ^ n ∣ x) :
    ∃ (n : ℕ) (c : R), x = π ^ n * c ∧ ¬π ∣ c :=
  have h_fin : FiniteMultiplicity π x := FiniteMultiplicity.not_iff_forall.not_right.mpr h
  ⟨multiplicity π x, h_fin.exists_eq_pow_mul_and_not_dvd⟩

end New

end
