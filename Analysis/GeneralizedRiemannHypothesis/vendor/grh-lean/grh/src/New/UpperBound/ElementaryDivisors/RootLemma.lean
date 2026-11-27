import New.UpperBound.ElementaryDivisors.TwistingData

/-!
# Gauss filtrations, Stepanov's count and the root lemma

The group GL_k(W) acts on polynomials over R in variables x_{b,s} (b < k, s ∈ ℤ/N) through a
`New.FrobeniusCycle`: a power P of a prime p, ring maps ι_s : W → R with ι_{s+1} ≡ ι_s^P mod p,
and w in R with w² = p. The indices s ∈ ℤ/N are called letters and are alternately even and odd.
This file shows which monomials can carry the least w-adic order plus weight among all translates
of a polynomial.

* `New.stepanov_count`: Stepanov's count of zeros at the residue classes of a local ring.
* `New.IsRealFiltration`, `New.adicFiltration`, `New.gaussFiltration`: multiplicative filtrations
  indexed by ℝ, the w-adic one, and the Gauss filtration on polynomials with weighted variables.
* `New.FrobeniusCycle.RootAt`: a root and a letter, with the variables X_s, Y_s, the substitution
  that defines the auxiliary polynomial, and its expansions at the rational points.
* `New.FrobeniusCycle.defect_nonpos_of_extreme_term`: for weights that rise by an amount in [1/2, 1]
  from X_s to Y_s, a term of least order plus weight among all translates by SL₂(W) has defect at
  most 0 (see `New.FrobeniusCycle.defectWeight`).

The proof compares the degree of an auxiliary binary form with its zeros at the q + 1 rational
points of the projective line, in the affine coordinate t. For an extreme term it writes the defect
in the two variables X_s, Y_s of each letter, substitutes polynomials in t for them, and expands one
coefficient at infinity (which gives its degree) and at the q finite points.

Notions from other files:
* `New.FrobeniusCycle.polyAction`: the action of GL_k(W) on polynomials in the variables x_{b,s}; g
  sends x_{b,s} to ∑_c (g_s)_{cb} x_{c,s}, where g_s is ι_s(g) for even letters s and ι_s of the
  inverse transpose of g for odd s.
* `New.levi`: the Levi subgroup of a labelling τ of the indices, the matrices in GL_k(W) whose (i,j)
  entry vanishes whenever τ(i) ≠ τ(j).
* `New.FrobeniusCycle.rootVar`: for indices a, a' and a letter s, the variable (a',s) if s is even
  and (a,s) if s is odd.
* `New.FrobeniusCycle.defectWeight`: at a letter i along a root (a, a'), the weight of x_{b,s} is a
  signed multiple of P^((s - i) mod N) / (q - 1) at the variables X_s, Y_s and 0 elsewhere, plus 1
  at Y_i; the sum of these weights over a monomial is its defect.

## Notation

After the substitution the variable Y_s, s ≠ i, is kept by `mainSubst` as the variable
`X (D.varY s)` of the letter s. The functions `RootAt.sign` and `RootAt.moveSign` carry the signs.

## Relation to the literature

The group SL₂(W), placed in two rows and columns of GL_k(W), acts on polynomials in a circle of
variable sets, alternately by Frobenius twists and by inverse transposes, and a term that is least
for valuation plus a suitable weight among all translates has exponents obeying linear inequalities.
Other files use them to bound the elementary divisors of the Hecke operator. Twisted Dickson forms
on Frobenius twists of symmetric powers, weight inequalities via the Lang map, and the count of
zeros against degree are known in the literature. Related work: Ghate–Jana, Modular representations
of GL2(F_q) using calculus, 2025; Imai–Koskivirta, Automorphic vector bundles on the stack of
G-zips, 2021; Bombieri, Counting points on curves over finite fields, Sém. Bourbaki 430, 1973.
-/

namespace New

open Polynomial IsLocalRing Function in
/-- Stepanov's count. Let `W` be a local ring with `q` residue classes and `ι : W → R` a ring map.
If a non-zero polynomial `Φ` over `R` is divisible by `(X - ι x) ^ E` for every `x` in `W` (that
is, `X ^ E` divides `Φ(X + ι x)`), then `E * q ≤ deg Φ`. -/
lemma stepanov_count {R W : Type} [CommRing R] [CommRing W] [IsLocalRing W] (ι : W →+* R)
    {Φ : R[X]} (E : ℕ) (hΦ : Φ ≠ 0) (h_zero : ∀ x : W, X ^ E ∣ taylor (ι x) Φ) :
    E * Nat.card (ResidueField W) ≤ Φ.natDegree := by
  -- Lift the residue classes to points `a x` of `R` with unit differences. The coprime polynomials
  -- `(X - a x) ^ E` all divide `Φ`, hence so does their product, monic of degree `E q`.
  cases fintypeOrInfinite (ResidueField W) with
  | inr _ => simp [Nat.card_eq_zero_of_infinite (α := ResidueField W)]
  | inl _ =>
  have : Nontrivial R := Nontrivial.of_polynomial_ne hΦ
  let a (x : ResidueField W) : R := ι (surjInv residue_surjective x)
  have h_unit (x y : ResidueField W) (hxy : x ≠ y) : IsUnit (a x - a y) := by
    rw [← map_sub]
    exact .map ι (by simpa [sub_eq_zero, ← residue_ne_zero_iff_isUnit, surjInv_eq] using hxy)
  have h_dvd : ∏ x : ResidueField W, (X - C (a x)) ^ E ∣ Φ := Fintype.prod_dvd_of_coprime
    (fun x y hxy ↦ (isCoprime_X_sub_C_of_isUnit_sub (h_unit x y hxy)).pow)
    fun x ↦ X_sub_C_pow_dvd_iff.2 (h_zero _)
  have h_monic : (∏ x : ResidueField W, (X - C (a x))).Monic := monic_prod_X_sub_C a _
  by_contra! h_lt
  exact (h_monic.pow E).not_dvd_of_natDegree_lt hΦ (by simpa [h_monic.natDegree_pow] using h_lt)
    (by rwa [← Finset.prod_pow])

/-! ### Filtrations and Gauss weights -/

/-- A decreasing multiplicative filtration of a commutative ring by additive subgroups F_t, t
real: 1 ∈ F_0, F_s·F_t ⊆ F_{s+t}, and F_t ⊆ F_s for s ≤ t. -/
class IsRealFiltration {R : Type} [CommRing R] (F : ℝ → AddSubgroup R) extends
    SetLike.GradedMonoid F where
  /-- The filtration is decreasing: `F t ≤ F s` for `s ≤ t`. -/
  antitone : Antitone F

open MvPolynomial Matrix Finsupp SetLike Nat Ideal.Quotient IsRealFiltration AddSubgroup

section Filtration

variable {σ : Type*} {R A : Type} [CommRing R] [CommRing A] [Algebra R A]

/-- For a ring element `w` and real `t`, the additive subgroup of elements divisible by `w` to the
power `max(⌈t⌉, 0)`. -/
@[simp] def adicFiltration (w : R) (t : ℝ) : AddSubgroup R where
  carrier := {x : R | w ^ ⌈t⌉₊ ∣ x}
  add_mem' := Dvd.dvd.add
  zero_mem' := by simp
  neg_mem' := by simp

lemma mem_adicFiltration_iff {w : R} {t : ℝ} {x : R} : x ∈ adicFiltration w t ↔ w ^ ⌈t⌉₊ ∣ x :=
  Iff.rfl

instance (w : R) : IsRealFiltration (adicFiltration w) where
  one_mem := by simp
  mul_mem s t x y hx hy :=
    calc w ^ ⌈s + t⌉₊ ∣ w ^ (⌈s⌉₊ + ⌈t⌉₊) := pow_dvd_pow w (ceil_add_le s t)
      _ ∣ x • y := by simpa [pow_add] using mul_dvd_mul hx hy
  antitone s t hst x hx := (pow_dvd_pow w (ceil_mono hst)).trans hx

/-- The Gauss filtration: for subgroups `F t` of `R` and weights `c` of the variables, the additive
group of polynomials whose coefficient at each `x ^ α` lies in `F (t - c · α)`. -/
def gaussFiltration (F : ℝ → AddSubgroup R) (c : σ → ℝ) (t : ℝ) :
    AddSubgroup (MvPolynomial σ R) where
  carrier := {f : MvPolynomial σ R | ∀ α : σ →₀ ℕ, f.coeff α ∈ F (t - weight c α)}
  add_mem' hf hg α := by simpa using add_mem (hf α) (hg α)
  zero_mem' := by simp
  neg_mem' := by simp

variable {F : ℝ → AddSubgroup R} {c : σ → ℝ} {w : R} {t : ℝ}

lemma mem_gaussFiltration_iff {f : MvPolynomial σ R} :
    f ∈ gaussFiltration F c t ↔ ∀ α : σ →₀ ℕ, f.coeff α ∈ F (t - weight c α) := Iff.rfl

lemma mem_adicFiltration_of_nonpos {x : R} (h_nonpos : x ≠ 0 → t ≤ 0) :
    x ∈ adicFiltration w t := by
  by_cases hx : x = 0 <;> simp_all [ceil_eq_zero.2]

/-- The term `x * X ^ α` lies in the level `t` of the Gauss filtration if `x` lies in
`F (t - c · α)`. -/
lemma monomial_mem_gaussFiltration {α : σ →₀ ℕ} {x : R} (hx : x ∈ F (t - weight c α)) :
    monomial α x ∈ gaussFiltration F c t := by
  classical grind [mem_gaussFiltration_iff, coeff_monomial, zero_mem]

lemma C_mem_gaussFiltration {x : R} (hx : x ∈ F t) :
    (C x : MvPolynomial σ R) ∈ gaussFiltration F c t := monomial_mem_gaussFiltration (by simpa)

open scoped Classical in
instance {σ R : Type} [CommRing R] {F : ℝ → AddSubgroup R} {c : σ → ℝ} [IsRealFiltration F] :
    IsRealFiltration (gaussFiltration F c) where
  one_mem := monomial_mem_gaussFiltration (by simp [one_mem_graded])
  mul_mem s t f g hf hg α := by
    -- The coefficient at `α` is a sum of products of coefficients at `β`, `γ` with `β + γ = α`.
    rw [coeff_mul]
    refine sum_mem fun (β, γ) hβγ ↦ ?_
    obtain rfl : β + γ = α := by simpa using hβγ
    simpa [add_sub_add_comm] using mul_mem_graded (hf β) (hg γ)
  antitone s t hst f hf α := antitone (sub_le_sub_right hst _) (hf α)

/-- Substitution respects weights. Let `G` be a filtration of the `R`-algebra `A` such that the
algebra map sends `F t` into `G t`, and let `f` lie in the level `t` of the Gauss filtration for
`F` and the weights `c` of the variables. Let `χ`, `ψ` be substitutions with `χ X_i` in `G (c i)`
and `ψ X_i - χ X_i` in `G (c i + 1 / 20)`. Then `ψ f` lies in `G t` and `ψ f - χ f` in
`G (t + 1 / 20)`. -/
lemma algHom_sub_mem_of_mem_gaussFiltration (χ : MvPolynomial σ R →ₐ[R] A) (G : ℝ → AddSubgroup A)
    [IsRealFiltration G] {f : MvPolynomial σ R} (hf : f ∈ gaussFiltration F c t)
    (hχ : ∀ i : σ, χ (X i) ∈ G (c i)) (ψ : MvPolynomial σ R →ₐ[R] A)
    (hψ : ∀ i : σ, ψ (X i) - χ (X i) ∈ G (c i + 20⁻¹))
    (hF : ∀ {s : ℝ} {x : R}, x ∈ F s → algebraMap R A x ∈ G s) :
    ψ f ∈ G t ∧ ψ f - χ f ∈ G (t + 20⁻¹) := by
  classical
  -- Induction on `f`: degrees in the filtration add in products, so a gain of `20⁻¹` on one
  -- factor is a gain of `20⁻¹` on the product.
  induction f using induction_on'' generalizing t with
  | C x => simpa using hF (hf 0)
  | monomial_add α x f hα _ ih_f ih_monomial =>
    -- both summands lie in `gaussFiltration F c t`, since `α` is not in the support of `f`
    have h_monomial : monomial α x ∈ gaussFiltration F c t :=
      monomial_mem_gaussFiltration (by simpa [f.notMem_support_iff.1 hα] using hf α)
    have h_rest : f ∈ gaussFiltration F c t := (add_mem_cancel_left h_monomial).1 hf
    simpa [add_sub_add_comm, add_mem (ih_monomial h_monomial).1 (ih_f h_rest).1] using
      add_mem (ih_monomial h_monomial).2 (ih_f h_rest).2
  | mul_X p i ih =>
    have hp : p ∈ gaussFiltration F c (t - c i) := fun α ↦ by
      have h_level : t - c i - weight c α = t - weight c (α + .single i 1) := by
        simp [weight_single, sub_add_eq_sub_sub_swap]
      rw [h_level, ← coeff_mul_X α i p]
      exact hf _
    obtain ⟨hψp, h_diff⟩ : ψ p ∈ G (t - c i) ∧ ψ p - χ p ∈ G (t - c i + 20⁻¹) := ih hp
    have hψX : ψ (X i) ∈ G (c i) := by simpa using add_mem (hχ i) (antitone (by simp) (hψ i))
    refine ⟨by simpa using mul_mem_graded hψp hψX, ?_⟩
    rw [show ψ (p * X i) - χ (p * X i) =
      (ψ p - χ p) * χ (X i) + ψ p * (ψ (X i) - χ (X i)) by simp [sub_mul, mul_sub]]
    exact add_mem (by simpa [add_right_comm] using mul_mem_graded h_diff (hχ i))
      (by simpa [← add_assoc] using mul_mem_graded hψp (hψ i))

end Filtration

/-! ### One root and one letter -/

section Root

variable {R : Type} {N k : ℕ} {W : Type} [CommRing R] [CommRing W] [IsLocalRing W]
  (T : FrobeniusCycle N W R) {a a' : Fin k}

/-- The group `SL₂(W)` placed in the rows and columns `a`, `a'` of `GL_k(W)`: the matrices of
determinant `1` that agree with the identity matrix at `(i, j)` unless both `i` and `j` are among
`a`, `a'`. It is trivial for `a = a'`. -/
def rootSL (W : Type) [CommRing W] (a a' : Fin k) : Subgroup (GL (Fin k) W) :=
  agreeWithOneOn (fun i j : Fin k ↦ (i ≠ a ∧ i ≠ a') ∨ (j ≠ a ∧ j ≠ a')) W
    (fun _ _ _ hij ↦ hij.imp .inl .inr) ⊓ GeneralLinearGroup.det.ker

omit [IsLocalRing W] in
lemma rootSL_le_levi {τ : Fin k → ℕ} (hτ : τ a = τ a') : rootSL W a a' ≤ levi W τ :=
  fun _ hg i j hij ↦ (hg.1 i j (by grind)).trans (one_apply_ne (ne_of_apply_ne τ hij))

/-- A root `(a, a')` of `GL_k` and a letter `i`, the data at which a defect is measured. -/
structure FrobeniusCycle.RootAt (T : FrobeniusCycle N W R) (k : ℕ) where
  /-- The letter `i`. -/
  letter : ZMod N
  /-- The index `a`. -/
  fst : Fin k
  /-- The index `a'`. -/
  snd : Fin k
  /-- The two indices differ. -/
  ne : fst ≠ snd

namespace FrobeniusCycle.RootAt

variable {T} (D : T.RootAt k) {s : ZMod N} {z : Fin k × ZMod N}

/-- The variable `X_s`: index `a` at even and `a'` at odd letters `s`. -/
def varX (s : ZMod N) : Fin k × ZMod N := T.rootVar D.snd D.fst s

/-- The variable `Y_s`: index `a'` at even and `a` at odd letters `s`. -/
def varY (s : ZMod N) : Fin k × ZMod N := T.rootVar D.fst D.snd s

/-- The variables whose index is neither `a` nor `a'`. -/
def IsFixed (z : Fin k × ZMod N) : Prop := z.1 ≠ D.fst ∧ z.1 ≠ D.snd

/-- The permutation of the variables that swaps `X_s` and `Y_s` in each letter. -/
def swapVar (z : Fin k × ZMod N) : Fin k × ZMod N := (Equiv.swap D.fst D.snd z.1, z.2)

/-- The map of variables that sends `Y_i` to `X_i` and fixes the others. -/
def merge (z : Fin k × ZMod N) : Fin k × ZMod N :=
  if z = D.varY D.letter then D.varX D.letter else z

/-- The sign at `Y_s`: `-1` if `s` has the parity of `i = D.letter` and `1` otherwise. It is `0` at
the other variables. The parity of a letter is its mark `T.isEven` in the twisting data, which
alternates from `s` to `s + 1`. -/
def sign (z : Fin k × ZMod N) : ℤ :=
  if z = D.varY z.2 then if T.isEven z.2 = T.isEven D.letter then -1 else 1 else 0

/-- The number `q = P ^ N` of residue classes of `W`, as a constant whose casts `simp` keeps. -/
def card (_ : T.RootAt k) : ℕ := T.q

/-- The power `P_s = P ^ (s - i)`, with `s - i` read in `[0, N)`. -/
def frobPower (s : ZMod N) : ℕ := T.P ^ (s - D.letter).val

/-- The weights `q P_s` at `X_s` and `0` at the other variables, where `q = D.card` and
`P_s = D.frobPower s`. Under the hypotheses of `HasBoundedIncrements.weight_zeroOrder_mul_card_le`,
the weight of the exponent `α` bounds the degree in `t` of the auxiliary polynomial: the coefficient
`D.mergedCoeff α` after the substitution `D.mainSubst - D.crossSubst`, modulo `w ^ (l + 1)`. -/
def poleOrder (z : Fin k × ZMod N) : ℕ := if z = D.varX z.2 then D.card * D.frobPower z.2 else 0

/-- The weights `q = D.card` at `Y_i`, `P_s = D.frobPower s` at `Y_s` for `s ≠ i`, and `0` at the
other variables, where `i = D.letter`. Under the hypotheses of
`HasBoundedIncrements.weight_zeroOrder_mul_card_le`, the weight of the exponent `α` bounds from
below the order of vanishing of the auxiliary polynomial (see `poleOrder`) at the points
`t = ι_i(r)`, `r ∈ W`. -/
def zeroOrder (z : Fin k × ZMod N) : ℕ :=
  if z = D.varY z.2 then if z.2 = D.letter then D.card else D.frobPower z.2 else 0

/-- The sign of `Y_s` at both `X_s` and `Y_s` for `s ≠ i`, and `0` at the other variables. -/
def crossSign (z : Fin k × ZMod N) : R :=
  if z.2 = D.letter then 0 else D.sign z + D.sign (D.swapVar z)

lemma cast_card_pos [NeZero N] : (0 : ℝ) < D.card := by simpa [card] using one_pos.trans T.one_lt_q

@[simp] lemma varX_snd : (D.varX s).2 = s := rfl

@[simp] lemma varY_snd : (D.varY s).2 = s := rfl

@[simp] lemma varX_ne_varY (s t : ZMod N) : D.varX s ≠ D.varY t := by
  grind [varX, varY, rootVar, D.ne]

@[simp] lemma varY_ne_varX (s t : ZMod N) : D.varY s ≠ D.varX t := (D.varX_ne_varY t s).symm

@[simp] lemma varY_inj {t : ZMod N} : D.varY s = D.varY t ↔ s = t :=
  ⟨congrArg Prod.snd, congrArg D.varY⟩

@[simp] lemma swapVar_snd : (D.swapVar z).2 = z.2 := rfl

@[simp] lemma swapVar_varX : D.swapVar (D.varX s) = D.varY s := by
  grind [swapVar, varX, varY, rootVar]

@[simp] lemma swapVar_varY : D.swapVar (D.varY s) = D.varX s := by
  grind [swapVar, varX, varY, rootVar]

/-- Every variable is `Y_i`, `X_i`, some `Y_s` or `X_s` with `s ≠ i`, or lies off the root. -/
lemma var_cases (z : Fin k × ZMod N) : z = D.varY D.letter ∨ z = D.varX D.letter ∨
    (∃ s : ZMod N, s ≠ D.letter ∧ (z = D.varY s ∨ z = D.varX s)) ∨ D.IsFixed z := by
  have h_letter : z = D.varY z.2 ∨ z = D.varX z.2 ∨ D.IsFixed z := by
    grind [varX, varY, rootVar, IsFixed]
  grind

@[simp] lemma sign_varX : D.sign (D.varX s) = 0 := by simp [sign]

@[simp] lemma sign_varY_letter : D.sign (D.varY D.letter) = -1 := by simp [sign]

lemma sign_varY_eq_one_or_neg_one (s : ZMod N) :
    D.sign (D.varY s) = 1 ∨ D.sign (D.varY s) = -1 := by
  grind [sign, varY_snd]

@[simp] lemma frobPower_letter : D.frobPower D.letter = 1 := by simp [frobPower]

@[simp] lemma merge_varX : D.merge (D.varX s) = D.varX s := by simp [merge]

@[simp] lemma merge_varY :
    D.merge (D.varY s) = if s = D.letter then D.varX D.letter else D.varY s := by simp [merge]

@[simp] lemma poleOrder_varX : D.poleOrder (D.varX s) = D.card * D.frobPower s := by
  simp [poleOrder]

@[simp] lemma poleOrder_varY : D.poleOrder (D.varY s) = 0 := by simp [poleOrder]

@[simp] lemma zeroOrder_varX : D.zeroOrder (D.varX s) = 0 := by simp [zeroOrder]

@[simp] lemma zeroOrder_varY :
    D.zeroOrder (D.varY s) = if s = D.letter then D.card else D.frobPower s := ite_eq_left rfl

@[simp] lemma crossSign_varX : D.crossSign (D.varX s) =
    if s = D.letter then 0 else (D.sign (D.varY s) : R) := by simp [crossSign]

@[simp] lemma crossSign_varY : D.crossSign (D.varY s) =
    if s = D.letter then 0 else (D.sign (D.varY s) : R) := by simp [crossSign]

namespace IsFixed

variable {D}

lemma ne_varX (hz : D.IsFixed z) (s : ZMod N) : z ≠ D.varX s := by grind [varX, rootVar, IsFixed]

lemma ne_varY (hz : D.IsFixed z) (s : ZMod N) : z ≠ D.varY s := by grind [varY, rootVar, IsFixed]

lemma swapVar_eq (hz : D.IsFixed z) : D.swapVar z = z := by grind [swapVar, IsFixed]

lemma merge_eq (hz : D.IsFixed z) : D.merge z = z := ite_eq_right (hz.ne_varY D.letter)

lemma sign_eq_zero (hz : D.IsFixed z) : D.sign z = 0 := ite_eq_right (hz.ne_varY z.2)

lemma poleOrder_eq_zero (hz : D.IsFixed z) : D.poleOrder z = 0 := ite_eq_right (hz.ne_varX z.2)

lemma zeroOrder_eq_zero (hz : D.IsFixed z) : D.zeroOrder z = 0 := ite_eq_right (hz.ne_varY z.2)

lemma crossSign_eq_zero (hz : D.IsFixed z) : D.crossSign z = 0 := by
  simp [crossSign, hz.swapVar_eq, hz.sign_eq_zero]

end IsFixed

end FrobeniusCycle.RootAt

end Root

namespace FrobeniusCycle.RootAt

variable {R : Type} {N k : ℕ} {W : Type} [CommRing R] [CommRing W] [IsLocalRing W]

/-- Let `D` consist of two distinct indices `D.fst`, `D.snd` in `Fin k` and a letter. Let the
variable `z = (b, s)` lie off the root. Then the maps of variables `D.swapVar` and `D.merge` fix
`z`, and the signs `D.sign`, `D.crossSign` and the weights `D.poleOrder`, `D.zeroOrder` vanish at
`z`. -/
lemma IsFixed.swapVar_merge_eq_self_and_weights_eq_zero {T : FrobeniusCycle N W R}
    {D : T.RootAt k} {z : Fin k × ZMod N} (hz : D.IsFixed z) :
    D.swapVar z = z ∧
    D.merge z = z ∧
    D.sign z = 0 ∧
    D.poleOrder z = 0 ∧
    D.zeroOrder z = 0 ∧
    D.crossSign z = 0 :=
  ⟨hz.swapVar_eq, hz.merge_eq, hz.sign_eq_zero, hz.poleOrder_eq_zero, hz.zeroOrder_eq_zero,
    hz.crossSign_eq_zero⟩

/-- The defect weight `T.defectWeight D.letter D.fst D.snd z` of a variable `z` equals
`(D.zeroOrder z - D.poleOrder z / q) / (q - 1)` with `q = D.card`. Summing, the defect of an
exponent is `(ν - ν') / (q - 1)`, where `ν` is its weight for `D.zeroOrder` and `q ν'` its weight
for `D.poleOrder`. -/
lemma defectWeight_eq [NeZero N] {T : FrobeniusCycle N W R} (D : T.RootAt k) (z : Fin k × ZMod N) :
    T.defectWeight D.letter D.fst D.snd z =
      (D.zeroOrder z - D.poleOrder z / D.card) / (D.card - 1) := by
  change ((if z = D.varY z.2 then (T.P : ℝ) ^ (1 + (z.2 - 1 - D.letter).val) else 0) -
    if z = D.varX z.2 then (T.P : ℝ) ^ (z.2 - D.letter).val else 0) / (D.card - 1) = _
  rw [one_add_val_sub_one_sub, zeroOrder, poleOrder]
  congr 1
  split_ifs <;> simp [card, frobPower, T.prime.ne_zero]

/-- The matrix `!![0, 1; -1, x]` in the rows and columns `a`, `a'`, with `x = -r` if `i` is even and
`x = r` otherwise, written as a transposition times a transvection times the diagonal matrix with
`-1` at `a`. It relates the point at infinity of the projective line to the finite point with the
affine coordinate `ι_i(r)`. -/
def swapTransvection {T : FrobeniusCycle N W R} (D : T.RootAt k) (r : W) : GL (Fin k) W :=
  .swap W D.fst D.snd * transvectionGL D.ne (if T.isEven D.letter then -r else r) *
    diagGL (Function.update 1 D.fst (-1))

/-- The sign `-1` at the variables with index `a`, and `1` at the other variables. -/
def moveSign {T : FrobeniusCycle N W R} (D : T.RootAt k) (z : Fin k × ZMod N) : ℤ :=
  if z.1 = D.fst then -1 else 1

/-- Let `T : FrobeniusCycle N W R` give each letter `s ∈ ℤ/N` a parity `T.isEven s`, and let
`D : T.RootAt k` consist of two distinct indices `a = D.fst`, `a' = D.snd` below `k` and a letter
`i = D.letter`. The matrix `D.swapTransvection r`, which is `!![0, 1; -1, x]` in the rows and
columns `a`, `a'` with `x = -r` for even `i` and `x = r` for odd `i`, lies in `SL₂(W)` placed there
(`rootSL`): its three factors, the transposition of `a` and `a'`, the transvection by `x` and the
diagonal matrix with `-1` at `a`, agree with the identity elsewhere and have determinants
`-1`, `1`, `-1`. -/
lemma swapTransvection_mem_rootSL {T : FrobeniusCycle N W R} (D : T.RootAt k) (r : W) :
    D.swapTransvection r ∈ rootSL W D.fst D.snd := by
  refine ⟨mul_mem (mul_mem (fun i j hij ↦ ?_) fun i j hij ↦ ?_) fun i j hij ↦ ?_, Units.ext ?_⟩
  · have h_swap : Equiv.swap D.fst D.snd i = j ↔ i = j := by grind
    simp [swap, one_apply, h_swap]
  · have h_off : ¬(D.fst = i ∧ D.snd = j) := by grind
    simp [transvection, one_apply, Matrix.single, h_off]
  · obtain rfl | h_ne := eq_or_ne i j
    · simp [show i ≠ D.fst by tauto]
    · simp [h_ne]
  · change (D.swapTransvection r).val.det = 1
    have h_diag : (diagGL (Function.update 1 D.fst (-1)) : GL (Fin k) W).val.det = -1 := by
      simp [← Units.coe_prod, Finset.prod_update_of_mem]
    rw [swapTransvection, Units.val_mul, det_mul, h_diag]
    simp [swap, det_permutation, Equiv.Perm.sign_swap D.ne, transvectionGL,
      det_transvection_of_ne _ _ D.ne]

/-- The action of the matrix `D.swapTransvection r` on the variable `z = (b, s)` with index
`b : Fin k` and letter `s : ZMod N`. Let `a = D.fst` and `a' = D.snd`. The variable
`X_s = D.varX s` is `(a, s)` for even and `(a', s)` for odd `s`, and `Y_s = D.varY s` is the other
of the two; `D.swapVar` swaps them and fixes all other variables. Up to the sign `D.moveSign z`,
which is `-1` if `b = a` and `1` otherwise, the matrix sends `X_s` to `Y_s`, sends `Y_s` to
`X_s + ε_s ι_s(r) Y_s` and fixes the other variables. Here `ι_s = T.embedding s : W → R`, and
`ε_s = D.sign Y_s` is `-1` if `s` has the parity of the letter `D.letter` and `1` otherwise;
`D.sign` is `0` at the variables other than the `Y_s`. -/
lemma polyAction_swapTransvection_X [NeZero N] {T : FrobeniusCycle N W R} (D : T.RootAt k) (r : W)
    (z : Fin k × ZMod N) :
    T.polyAction (D.swapTransvection r) (X z) =
      D.moveSign z • (X (D.swapVar z) + C (D.sign z * T.embedding z.2 r) * X (D.varY z.2)) := by
  set x : W := if T.isEven D.letter then -r else r with hx
  -- The diagonal factor is its own inverse transpose, so it gives the same sign at all letters.
  let d : GL (Fin k) W := diagGL (Function.update 1 D.fst (-1))
  have h_diag : T.polyAction d (X z) = D.moveSign z • X z := by
    rw [polyAction_X, letterMatrix_apply, ← map_inv, ← Function.update_inv, inv_one, inv_neg_one]
    simp [d, moveSign, diagonal_apply, Function.update_apply, apply_ite Units.val,
      apply_ite (T.embedding _), apply_ite C]
  -- Read the column of `z` in the matrix of the letter, for both parities of `z.2` and of
  -- `D.letter`.
  let M : Matrix (Fin k) (Fin k) W :=
    if T.isEven z.2 then transvection D.fst D.snd x else (transvection D.fst D.snd (-x))ᵀ
  have h_column : T.polyAction (.swap W D.fst D.snd * transvectionGL D.ne x) (X z) =
      ∑ b : Fin k, C (T.embedding z.2 (M b z.1)) * X (Equiv.swap D.fst D.snd b, z.2) := by
    simp [M, polyAction_X, letterMatrix_apply, transvectionGL, swap,
      GeneralLinearGroup.swap, Equiv.swap_apply_eq_iff]
  -- Off the diagonal, the column of `z` has only the entry `D.sign z * r`, in the row of `X_s`.
  have h_entry (b : Fin k) : M b z.1 =
      (if b = z.1 then 1 else 0) + if (b, z.2) = D.varX z.2 then D.sign z * r else 0 := by
    cases h_letter : T.isEven D.letter <;> cases h_z : T.isEven z.2 <;>
      simp [M, hx, h_letter, h_z, sign, varX, varY, rootVar, transvection, one_apply,
        Matrix.single, Prod.ext_iff, ← ite_and, and_comm, eq_comm]
  rw [swapTransvection, map_mul, AlgHom.mul_apply, h_diag, map_zsmul, h_column, ← swapVar_varX,
    swapVar,
    swapVar]
  simp [h_entry, Prod.ext_iff, add_mul, apply_ite (T.embedding _), apply_ite C,
    Finset.sum_add_distrib]

/-- The weights `c` of the variables rise from `X_s` to `Y_s` by an amount in `[1 / 2, 1]`. -/
def HasBoundedIncrements {T : FrobeniusCycle N W R} (D : T.RootAt k) (c : Fin k × ZMod N → ℝ) :
    Prop :=
  ∀ s : ZMod N, c (D.varY s) - c (D.varX s) ∈ Set.Icc 2⁻¹ 1

/-- The slope `ρ = (c Y_i - c X_i) / q` of weights `c` of the variables, where `i = D.letter` and
`q = D.card`. The variable `t` of the auxiliary polynomial weighs `-ρ` in the expansion at infinity
and `ρ` in the expansion at a finite point, after the shift `t ↦ t + ι_i(r)`. -/
noncomputable def slope {T : FrobeniusCycle N W R} (D : T.RootAt k) (c : Fin k × ZMod N → ℝ) : ℝ :=
  (c (D.varY D.letter) - c (D.varX D.letter)) / D.card

lemma card_mul_slope [NeZero N]
    {T : FrobeniusCycle N W R} {D : T.RootAt k} {c : Fin k × ZMod N → ℝ} :
    D.card * D.slope c = c (D.varY D.letter) - c (D.varX D.letter) :=
  mul_div_cancel₀ _ D.cast_card_pos.ne'

lemma HasBoundedIncrements.slope_pos [NeZero N] {T : FrobeniusCycle N W R} {D : T.RootAt k}
    {c : Fin k × ZMod N → ℝ} (hc : D.HasBoundedIncrements c) : 0 < D.slope c :=
  div_pos (by linarith [(hc D.letter).1]) D.cast_card_pos

/-- If the steps of `c` lie in `[1 / 2, 1]`, then `P_s` times the slope is at most `1 / 5`, because
`5 P_s ≤ q`. -/
lemma HasBoundedIncrements.frobPower_mul_slope_le [NeZero N]
    {T : FrobeniusCycle N W R} {D : T.RootAt k}
    {c : Fin k × ZMod N → ℝ} (hc : D.HasBoundedIncrements c) (s : ZMod N) :
    D.frobPower s * D.slope c ≤ 1 / 5 := by
  have h_power : (5 * D.frobPower s : ℝ) ≤ D.card := mod_cast T.five_mul_P_pow_le_q (s - D.letter)
  have h_step : D.card * D.slope c ≤ 1 := card_mul_slope.trans_le (hc D.letter).2
  nlinarith [hc.slope_pos]

/-- If the steps of `c` lie in `[1 / 2, 1]` and `s ≠ D.letter`, then `q P_s` times the slope is at
least `2`, because `P_s ≥ 5`. -/
lemma HasBoundedIncrements.two_le_card_mul_frobPower_mul_slope [NeZero N] {T : FrobeniusCycle N W R}
    {D : T.RootAt k} {s : ZMod N} {c : Fin k × ZMod N → ℝ} (hc : D.HasBoundedIncrements c)
    (hs : s ≠ D.letter) :
    2 ≤ D.card * D.frobPower s * D.slope c := by
  have h_power : (5 : ℝ) ≤ D.frobPower s :=
    mod_cast T.five_le_P.trans (le_self_pow (by simpa [sub_eq_zero]) _)
  have h_step : (2⁻¹ : ℝ) ≤ D.card * D.slope c := (hc D.letter).1.trans_eq card_mul_slope.symm
  nlinarith

/-! ### The auxiliary polynomial -/

/-- The main part of the substitution, with a new variable `t = X ()`: `Y_i ↦ X_i`,
`X_s ↦ t ^ (q P_s) X_s`, and the other variables are fixed. -/
noncomputable def mainSubst {T : FrobeniusCycle N W R} (D : T.RootAt k) (z : Fin k × ZMod N) :
    MvPolynomial (Fin k × ZMod N) (MvPolynomial Unit R) :=
  C (monomial (single () (D.poleOrder z)) 1) * X (D.merge z)

/-- The cross terms: for `s ≠ i`, `Y_s ↦ ε_s X_s` and `X_s ↦ ε_s t ^ P_s Y_s`, where `ε_s` is the
sign `D.sign` at `Y_s`; the other variables go to `0`. The substitution that defines the auxiliary
polynomial is `D.mainSubst - D.crossSubst`. For `ε_s = -1` it sends `(X_s, Y_s)` to
`Y_s (t ^ P_s, 1) + X_s (t ^ (q P_s), 1)`, and for `ε_s = 1` to the same with `-Y_s` for `Y_s` on
both sides. -/
noncomputable def crossSubst {T : FrobeniusCycle N W R} (D : T.RootAt k) (z : Fin k × ZMod N) :
    MvPolynomial (Fin k × ZMod N) (MvPolynomial Unit R) :=
  C (monomial (single () (D.zeroOrder (D.swapVar z))) (D.crossSign z)) * X (D.swapVar z)

/-- The Gauss filtration on polynomials over `R[t]` in which `w` weighs `1`, `t` weighs `ρ` and
each variable `z` weighs `c z - v z * ρ`. -/
noncomputable abbrev _root_.New.FrobeniusCycle.iteratedGaussFiltration (T : FrobeniusCycle N W R)
    (c : Fin k × ZMod N → ℝ) (ρ : ℝ) (v : Fin k × ZMod N → ℕ) :
    ℝ → AddSubgroup (MvPolynomial (Fin k × ZMod N) (MvPolynomial Unit R)) :=
  gaussFiltration (gaussFiltration (adicFiltration T.sqrtPrime) fun _ : Unit ↦ ρ)
    fun z : Fin k × ZMod N ↦ c z - v z * ρ

lemma algebraMap_mem_iteratedGaussFiltration {T : FrobeniusCycle N W R} {c : Fin k × ZMod N → ℝ}
    {ρ b : ℝ} {v : Fin k × ZMod N → ℕ} {r : R}
    (hr : r ∈ adicFiltration T.sqrtPrime b) :
    algebraMap R (MvPolynomial (Fin k × ZMod N) (MvPolynomial Unit R)) r ∈
      T.iteratedGaussFiltration c ρ v b :=
  C_mem_gaussFiltration (C_mem_gaussFiltration hr)

/-- The term `C (monomial (single () n) r) * X z`, that is `r t ^ n` times the variable `X z`, lies
in `T.iteratedGaussFiltration c ρ v b` if `r = 0` or `b ≤ c z - v z * ρ + n * ρ`. That bound is the
weight of `t ^ n * X z`. -/
lemma C_monomial_mul_X_mem_iteratedGaussFiltration {T : FrobeniusCycle N W R} {z : Fin k × ZMod N}
    {c : Fin k × ZMod N → ℝ} {ρ b : ℝ} {v : Fin k × ZMod N → ℕ} {n : ℕ} {r : R}
    (hb : r ≠ 0 → b ≤ c z - v z * ρ + n * ρ) :
    C (monomial (single () n) r) * X z ∈ T.iteratedGaussFiltration c ρ v b := by
  rw [C_mul_X_eq_monomial]
  refine monomial_mem_gaussFiltration (monomial_mem_gaussFiltration ?_)
  exact mem_adicFiltration_of_nonpos (by simpa [weight_single, add_comm] using hb)

/-- Expansion at infinity. Let `w = T.sqrtPrime`, a square root of the prime `T.p` in `R`, let
`i = D.letter` and let `q = D.card = P ^ N` with `P = T.P`. In each letter `s`, `X_s = D.varX s` and
`Y_s = D.varY s` are the variables with index `D.fst`, `D.snd` if `s` is even, in reverse order if
it is odd. Let the weights `c` rise from `X_s` to `Y_s` by amounts in `[1 / 2, 1]`, let each term of
`f` have `w`-adic order plus `c`-weight at least `b`, and put
`P_s = D.frobPower s = P ^ (s - i).val` and `ρ = D.slope c = (c Y_i - c X_i) / q`.

In the filtration on polynomials in the variables `z` over `R[t]`, `w` weighs `1`, `t` weighs `-ρ`,
`X_s` weighs `c X_s + q P_s ρ` and any other variable `z` weighs `c z`. The main part `D.mainSubst`
minus the cross terms `D.crossSubst` sends `f` to level `b`, and the cross terms change the image of
`f` only in level `b + 1 / 20`. -/
lemma HasBoundedIncrements.aeval_mem_and_sub_mem_iteratedGaussFiltration [NeZero N]
    {T : FrobeniusCycle N W R}
    {D : T.RootAt k} {c : Fin k × ZMod N → ℝ} (hc : D.HasBoundedIncrements c) {b : ℝ}
    {f : MvPolynomial (Fin k × ZMod N) R}
    (hf : f ∈ gaussFiltration (adicFiltration T.sqrtPrime) c b) :
    aeval (D.mainSubst - D.crossSubst) f ∈ T.iteratedGaussFiltration c (-D.slope c) D.poleOrder b ∧
      aeval (D.mainSubst - D.crossSubst) f - aeval D.mainSubst f ∈
        T.iteratedGaussFiltration c (-D.slope c) D.poleOrder (b + 20⁻¹) := by
  have h_main (z : Fin k × ZMod N) :
      D.mainSubst z ∈ T.iteratedGaussFiltration c (-D.slope c) D.poleOrder (c z) := by
    refine C_monomial_mul_X_mem_iteratedGaussFiltration fun _ ↦ ?_
    by_cases hz : z = D.varY D.letter
    · simp [hz, card_mul_slope]
    · simp [merge, hz]
  have h_cross (z : Fin k × ZMod N) :
      D.crossSubst z ∈ T.iteratedGaussFiltration c (-D.slope c) D.poleOrder (c z + 20⁻¹) := by
    refine C_monomial_mul_X_mem_iteratedGaussFiltration fun h_sign ↦ ?_
    rcases D.var_cases z with rfl | rfl | ⟨s, hs, rfl | rfl⟩ | hz
    · simp at h_sign
    · simp at h_sign
    · -- `X_s` weighs `c X_s + q P_s * D.slope c ≥ c X_s + 2 ≥ c Y_s + 1`
      suffices c (D.varY s) + 20⁻¹ ≤ c (D.varX s) + D.card * D.frobPower s * D.slope c by simpa
      linarith [(hc s).2, hc.two_le_card_mul_frobPower_mul_slope hs]
    · -- `t ^ P_s Y_s` weighs `c Y_s - P_s * D.slope c ≥ c X_s + 1 / 2 - 1 / 5`
      suffices c (D.varX s) + 20⁻¹ ≤ c (D.varY s) + -(D.frobPower s * D.slope c) by simpa [hs]
      linarith [(hc s).1, hc.frobPower_mul_slope_le s]
    · exact absurd hz.crossSign_eq_zero h_sign
  exact algHom_sub_mem_of_mem_gaussFiltration (aeval D.mainSubst) _ hf (by simpa using h_main) _
    (by simpa using h_cross) algebraMap_mem_iteratedGaussFiltration

/-- The error in the rule `(t + ι_i(r)) ^ P ^ n = t ^ P ^ n + ι_{i + n}(r)`. -/
noncomputable def _root_.New.FrobeniusCycle.frobeniusError (T : FrobeniusCycle N W R) (i : ZMod N)
    (r : W) (n : ℕ) : MvPolynomial Unit R :=
  (X () + C (T.embedding i r)) ^ T.P ^ n - X () ^ T.P ^ n - C (T.embedding (i + n) r)

/-- For a letter `i`, `r` in `W` and natural `n`, take the polynomial in `t` `T.frobeniusError i r
n = (t + ι_i(r)) ^ P ^ n - t ^ P ^ n - ι_{i + n}(r)`. In `T.iteratedGaussFiltration c ρ v`, `w`
weighs `1`, `t` weighs `ρ` and a variable `z` weighs `c z - v z * ρ`. So for `ρ ≥ 0` the product of
this polynomial with `z` has level `2` more than the weight of `z`. -/
lemma frobeniusError_mul_X_mem {T : FrobeniusCycle N W R} {c : Fin k × ZMod N → ℝ} {ρ : ℝ}
    (hρ : 0 ≤ ρ) (v : Fin k × ZMod N → ℕ) (z : Fin k × ZMod N) (i : ZMod N) (r : W) (n : ℕ) :
    C (T.frobeniusError i r n) * X z ∈ T.iteratedGaussFiltration c ρ v (c z - v z * ρ + 2) := by
  have h_add : (T.p : MvPolynomial Unit R) ∣
      (X () + C (T.embedding i r)) ^ T.P ^ n - X () ^ T.P ^ n - C (T.embedding i r) ^ T.P ^ n := by
    simp [← pow_mul, add_pow_prime_pow_eq' T.prime, add_assoc]
  have h_shift : (T.p : MvPolynomial Unit R) ∣ C (T.embedding (i + n) r) - C (T.embedding i r) ^ T.P
    ^ n := by
    simpa using map_dvd C (T.frobenius_pow_congr n i r)
  have h_dvd : C (T.sqrtPrime ^ 2) ∣ T.frobeniusError i r n := by
    simpa [frobeniusError, sqrtPrime_sq] using dvd_sub h_add h_shift
  rw [C_mul_X_eq_monomial]
  refine monomial_mem_gaussFiltration fun β ↦
    (pow_dvd_pow T.sqrtPrime ?_).trans ((C_dvd_iff_dvd_coeff _ _).1 h_dvd β)
  -- The order asked for is `2` minus the weight `β () * ρ ≥ 0` of the monomial `β` in `t`.
  simpa [weight_single, β.weight_eq_sum _] using mul_nonneg (β ()).cast_nonneg hρ

/-- The substitution `t ↦ t + x` in the coefficients. -/
noncomputable def _root_.New.shiftCoeff (σ : Type*) (x : R) :
    MvPolynomial σ (MvPolynomial Unit R) →ₐ[R] MvPolynomial σ (MvPolynomial Unit R) :=
  mapAlgHom (((uniqueAlgEquiv R Unit).arrowCongr (uniqueAlgEquiv R Unit)).symm
    (Polynomial.taylorAlgHom x))

/-- The shift of `t` undoes the transvection in `D.swapTransvection r` up to Frobenius errors. For
`a = D.fst`, `a' = D.snd` and a letter `s ∈ ℤ/N`, `X_s = D.varX s` is `(a, s)` for even and
`(a', s)` for odd `s`, and `Y_s = D.varY s` is the other of the two. Let `i = D.letter`,
`q = P ^ N`, `P_s = P ^ (s - i).val` with `P = T.P`, and `ι_s = T.embedding s : W → R`.

Act on the variable `z` by `D.swapTransvection r` through `T.polyAction`, the action of `GL_k(W)` on
polynomials in the variables `(b, s)`. Then substitute `D.mainSubst - D.crossSubst`, with values in
the polynomials over `R[t]`, and replace `t` by `t + ι_i(r)` (`shiftCoeff`). Here `ε_s = D.sign Y_s`
is `-1` if `s` has the parity of `i` and `1` otherwise.

Up to the sign `D.moveSign z`, which is `-1` if `z` has index `a` and `1` otherwise, the result is
the polynomial substituted for `D.swapVar z` plus errors `T.frobeniusError i r n = (t + ι_i(r)) ^ P
^ n - t ^ P ^ n - ι_{i + n}(r)`. They occur only for `z = Y_s`: with `d = (s - i).val`, the error
for `n = N + d` multiplies `X_s`, and `-ε_s` times the error for `n = d` multiplies `Y_s`. -/
lemma shiftCoeff_aeval_swapTransvection_X [NeZero N]
    {T : FrobeniusCycle N W R} {D : T.RootAt k} (r : W) (z : Fin k × ZMod N) :
    shiftCoeff (Fin k × ZMod N) (T.embedding D.letter r)
        (aeval (D.mainSubst - D.crossSubst) (T.polyAction (D.swapTransvection r) (X z))) -
      D.moveSign z • (D.mainSubst - D.crossSubst) (D.swapVar z) =
    D.moveSign z •
      (C (T.frobeniusError D.letter (|D.sign z| * r) (N + (z.2 - D.letter).val)) *
          X (D.swapVar z) -
        D.sign z • (C (T.frobeniusError D.letter r (z.2 - D.letter).val) * X z)) := by
  rw [polyAction_swapTransvection_X, map_zsmul, map_zsmul, ← smul_sub]
  unfold shiftCoeff mainSubst crossSubst frobeniusError
  congr 1
  rcases D.var_cases z with rfl | rfl | ⟨s, hs, rfl | rfl⟩ | hz
  · -- `z = Y_i`
    simp [monomial_eq, card, ZMod.natCast_self]
    ring
  · -- `z = X_i`
    simp [monomial_eq]
  · -- `z = Y_s` with `s ≠ i`, the same computation for both signs
    rcases D.sign_varY_eq_one_or_neg_one s with h_sign | h_sign
    all_goals
      simp [monomial_eq, card, frobPower, pow_add, ZMod.natCast_self, hs, h_sign]
      ring
  · -- `z = X_s` with `s ≠ i`
    simp [monomial_eq, hs]
  · -- `z` lies off the root
    simp [monomial_eq, hz.swapVar_eq, hz.sign_eq_zero, hz.poleOrder_eq_zero, hz.crossSign_eq_zero]

/-- In each letter `s`, `X_s = D.varX s` and `Y_s = D.varY s` are the variables with the two indices
of the root, and `D.swapVar` swaps them and fixes the others. Let the weights `c` rise from `X_s` to
`Y_s` by amounts in `[1 / 2, 1]`, and put `i = D.letter`, `q = D.card = P ^ N`,
`P_s = P ^ (s - i).val` with `P = T.P` and `ρ = D.slope c = (c Y_i - c X_i) / q`. Filter polynomials
over `R[t]` so that `w = T.sqrtPrime` weighs `1`, `t` weighs `ρ` and a variable `y` weighs
`c y - D.zeroOrder y * ρ`.

Then the substitution `D.mainSubst - D.crossSubst` (`Y_i ↦ X_i`,
`X_s ↦ t ^ (q P_s) X_s - ε_s t ^ P_s Y_s`, `Y_s ↦ Y_s - ε_s X_s` for `s ≠ i`, where
`ε_s = D.sign Y_s` is `± 1`) sends `D.swapVar z` to level `c z`. -/
lemma HasBoundedIncrements.subst_swapVar_mem_iteratedGaussFiltration [NeZero N]
    {T : FrobeniusCycle N W R}
    {D : T.RootAt k} {c : Fin k × ZMod N → ℝ} (hc : D.HasBoundedIncrements c) (z : Fin k × ZMod N) :
    (D.mainSubst - D.crossSubst) (D.swapVar z) ∈
      T.iteratedGaussFiltration c (D.slope c) D.zeroOrder (c z) := by
  refine sub_mem (C_monomial_mul_X_mem_iteratedGaussFiltration fun _ ↦ ?_)
    (C_monomial_mul_X_mem_iteratedGaussFiltration (by simp [swapVar]))
  rcases D.var_cases z with rfl | rfl | ⟨s, hs, rfl | rfl⟩ | hz
  · simp [card_mul_slope]
  · simp
  · suffices c (D.varY s) ≤ c (D.varX s) + D.card * D.frobPower s * D.slope c by simpa
    linarith [(hc s).2, hc.two_le_card_mul_frobPower_mul_slope hs]
  · suffices c (D.varX s) + D.frobPower s * D.slope c ≤ c (D.varY s) by
      simpa [hs, le_sub_iff_add_le]
    linarith [(hc s).1, hc.frobPower_mul_slope_le s]
  · simp [hz.swapVar_merge_eq_self_and_weights_eq_zero]

/-- Let `i = D.letter`, and let `X_s = D.varX s`, `Y_s = D.varY s` be the two variables of the root
in the letter `s`. At a finite point a variable `y` weighs `c y - D.zeroOrder y * D.slope c`. If `c`
rises from `X_s` to `Y_s` by amounts in `[1 / 2, 1]`, then `c z + 1 / 20` is at most `2` plus the
weight of `y`, both for `y = z` and for `y = D.swapVar z`, the image of `z` when `X_s` and `Y_s` are
exchanged. -/
lemma HasBoundedIncrements.add_le_sub_zeroOrder_mul_slope_add_two [NeZero N]
    {T : FrobeniusCycle N W R}
    {D : T.RootAt k} {c : Fin k × ZMod N → ℝ} (hc : D.HasBoundedIncrements c) (z : Fin k × ZMod N) :
    c z + 20⁻¹ ≤ c (D.swapVar z) - D.zeroOrder (D.swapVar z) * D.slope c + 2 ∧
      c z + 20⁻¹ ≤ c z - D.zeroOrder z * D.slope c + 2 := by
  rcases D.var_cases z with rfl | rfl | ⟨s, hs, rfl | rfl⟩ | hz
  · suffices c (D.varY D.letter) + 20⁻¹ ≤ c (D.varX D.letter) + 2 by simpa [card_mul_slope]
    linarith [(hc D.letter).2]
  · norm_num [card_mul_slope]
  · suffices c (D.varY s) + 20⁻¹ ≤ c (D.varX s) + 2 ∧
        c (D.varY s) + 20⁻¹ ≤ c (D.varY s) - D.frobPower s * D.slope c + 2 by simpa [hs]
    constructor <;> linarith [(hc s).2, hc.frobPower_mul_slope_le s]
  · suffices c (D.varX s) + 20⁻¹ ≤ c (D.varY s) - D.frobPower s * D.slope c + 2 ∧
        (20⁻¹ : ℝ) ≤ 2 by simpa [hs]
    constructor <;> linarith [(hc s).1, hc.frobPower_mul_slope_le s]
  · norm_num [hz.swapVar_merge_eq_self_and_weights_eq_zero]

/-- Expansion at the finite point `ι_i(r)`, where `i = D.letter` and `ι_i = T.embedding i : W → R`.
In each letter `s`, `X_s = D.varX s` and `Y_s = D.varY s` are the variables with the indices
`a = D.fst`, `a' = D.snd` if `s` is even and in reverse order if it is odd. The matrix
`D.swapTransvection r` is `!![0, 1; -1, ± r]` in the rows and columns `a`, `a'` and acts on
polynomials by `T.polyAction`. Let the weights `c` rise from `X_s` to `Y_s` by amounts in
`[1 / 2, 1]`, and let each term of the translate of `f` by `(D.swapTransvection r)⁻¹` have order for
`w = T.sqrtPrime` plus `c`-weight at least `b`.

In `f`, substitute `D.mainSubst - D.crossSubst` (`Y_i ↦ X_i`,
`X_s ↦ t ^ (q P_s) X_s - ε_s t ^ P_s Y_s`, `Y_s ↦ Y_s - ε_s X_s` for `s ≠ i`, with `q = D.card`,
`P_s = D.frobPower s = T.P ^ (s - i).val` and `ε_s = D.sign Y_s`, which is `-1` if `s` has the
parity of `i` and `1` otherwise), then replace `t` by `t + ι_i(r)`. The result has level `b` when
`w` weighs `1`, `t` weighs `ρ = D.slope c = (c Y_i - c X_i) / q` and a variable `z` weighs
`c z - D.zeroOrder z * ρ`. -/
lemma HasBoundedIncrements.shiftCoeff_aeval_mem [NeZero N]
    {T : FrobeniusCycle N W R} {D : T.RootAt k}
    {c : Fin k × ZMod N → ℝ} (hc : D.HasBoundedIncrements c) (r : W) {b : ℝ}
    {f : MvPolynomial (Fin k × ZMod N) R}
    (hf : T.polyAction (D.swapTransvection r)⁻¹ f ∈
      gaussFiltration (adicFiltration T.sqrtPrime) c b) :
    shiftCoeff (Fin k × ZMod N) (T.embedding D.letter r) (aeval (D.mainSubst - D.crossSubst) f) ∈
      T.iteratedGaussFiltration c (D.slope c) D.zeroOrder b := by
  -- `ψ` (act, substitute, shift) is `θ` (signed swap, substitute) up to terms of more weight.
  let E := MvPolynomial (Fin k × ZMod N) R →ₐ[R] MvPolynomial (Fin k × ZMod N) (MvPolynomial Unit R)
  let ψ : E := (shiftCoeff _ (T.embedding D.letter r)).comp
    (.comp (aeval (D.mainSubst - D.crossSubst)) (T.polyAction (D.swapTransvection r)))
  let θ : E := aeval fun z ↦ D.moveSign z • (D.mainSubst - D.crossSubst) (D.swapVar z)
  have h_main (z : Fin k × ZMod N) :
      θ (X z) ∈ T.iteratedGaussFiltration c (D.slope c) D.zeroOrder (c z) := by
    rw [aeval_X]
    exact zsmul_mem (hc.subst_swapVar_mem_iteratedGaussFiltration z) _
  have h_error (z : Fin k × ZMod N) :
      ψ (X z) - θ (X z) ∈ T.iteratedGaussFiltration c (D.slope c) D.zeroOrder (c z + 20⁻¹) := by
    obtain ⟨h_exchange, h_self⟩ :
        c z + 20⁻¹ ≤ c (D.swapVar z) - D.zeroOrder (D.swapVar z) * D.slope c + 2 ∧
          c z + 20⁻¹ ≤ c z - D.zeroOrder z * D.slope c + 2 :=
      hc.add_le_sub_zeroOrder_mul_slope_add_two z
    rw [aeval_X, AlgHom.comp_apply, AlgHom.comp_apply, shiftCoeff_aeval_swapTransvection_X]
    refine zsmul_mem (sub_mem (antitone h_exchange ?_) (zsmul_mem (antitone h_self ?_) _)) _
    all_goals apply frobeniusError_mul_X_mem hc.slope_pos.le
  have h_level : ψ (T.polyAction (D.swapTransvection r)⁻¹ f) ∈ T.iteratedGaussFiltration c
    (D.slope c) D.zeroOrder b :=
    (algHom_sub_mem_of_mem_gaussFiltration θ _ hf h_main ψ h_error
      algebraMap_mem_iteratedGaussFiltration).left
  have h_cancel : T.polyAction (D.swapTransvection r) (T.polyAction (D.swapTransvection r)⁻¹ f) =
    f := by
    simp [← AlgHom.mul_apply, ← map_mul]
  rwa [AlgHom.comp_apply, AlgHom.comp_apply, h_cancel] at h_level

/-- The coefficient, a polynomial in `t`, of the monomial obtained from `x ^ α` by writing `X_i`
for `Y_i`. -/
noncomputable def mergedCoeff {T : FrobeniusCycle N W R} (D : T.RootAt k)
    (α : Fin k × ZMod N →₀ ℕ) (p : MvPolynomial (Fin k × ZMod N) (MvPolynomial Unit R)) :
    Polynomial R :=
  uniqueAlgEquiv R Unit (p.coeff (mapDomain D.merge α))

lemma mergedCoeff_add {T : FrobeniusCycle N W R} {D : T.RootAt k} (α : Fin k × ZMod N →₀ ℕ)
    (p p' : MvPolynomial (Fin k × ZMod N) (MvPolynomial Unit R)) :
    D.mergedCoeff α (p + p') = D.mergedCoeff α p + D.mergedCoeff α p' := by simp [mergedCoeff]

lemma mergedCoeff_sub {T : FrobeniusCycle N W R} {D : T.RootAt k} (α : Fin k × ZMod N →₀ ℕ)
    (p p' : MvPolynomial (Fin k × ZMod N) (MvPolynomial Unit R)) :
    D.mergedCoeff α (p - p') = D.mergedCoeff α p - D.mergedCoeff α p' := by simp [mergedCoeff]

/-- Shifting `t` by `x` in the coefficients of `p` shifts the polynomial `D.mergedCoeff α p` by
`x`. -/
lemma mergedCoeff_shiftCoeff {T : FrobeniusCycle N W R} {D : T.RootAt k} (α : Fin k × ZMod N →₀ ℕ)
    (x : R) (p : MvPolynomial (Fin k × ZMod N) (MvPolynomial Unit R)) :
    D.mergedCoeff α (shiftCoeff (Fin k × ZMod N) x p) = (D.mergedCoeff α p).taylor x := by
  simpa [mergedCoeff, shiftCoeff, coeff_map] using
    (uniqueAlgEquiv R Unit).apply_symm_apply ((D.mergedCoeff α p).taylor x)

/-- In `T.iteratedGaussFiltration c ρ v`, `w = T.sqrtPrime` weighs `1`, `t` weighs `ρ` and a
variable `z` weighs `c z - v z * ρ`. Let the polynomial `p` over `R[t]` have level `b` there, and
let `X_i = D.varX i` and `Y_i = D.varY i` have the same weight, where `i = D.letter` is the letter
of the root `D`. The univariate polynomial `D.mergedCoeff α p` in `t` is the coefficient in `p` of
the monomial obtained from `x ^ α` by writing `X_i` for `Y_i`. Its coefficient of `t ^ j` is
divisible by `w ^ (l + 1)` once `b` less the weight of `t ^ j x ^ α` exceeds `l`. -/
lemma pow_dvd_coeff_mergedCoeff {T : FrobeniusCycle N W R} {D : T.RootAt k} {c : Fin k × ZMod N → ℝ}
    {ρ b : ℝ} {v : Fin k × ZMod N → ℕ} {α : Fin k × ZMod N →₀ ℕ}
    {p : MvPolynomial (Fin k × ZMod N) (MvPolynomial Unit R)} {l : ℕ} (j : ℕ)
    (hp : p ∈ T.iteratedGaussFiltration c ρ v b)
    (h_merge_weight : c (D.varX D.letter) - v (D.varX D.letter) * ρ =
      c (D.varY D.letter) - v (D.varY D.letter) * ρ)
    (hj : l < b - (weight c α - weight v α * ρ) - j * ρ) :
    T.sqrtPrime ^ (l + 1) ∣ (D.mergedCoeff α p).coeff j := by
  have h_var (z : Fin k × ZMod N) : c (D.merge z) - v (D.merge z) * ρ = c z - v z * ρ := by
    grind [merge]
  have h_weight : weight (fun z ↦ c z - v z * ρ) (mapDomain D.merge α) =
      weight c α - weight v α * ρ := by
    rw [weight_apply, sum_mapDomain_index (by simp) (by simp [add_mul])]
    simp [h_var, weight_apply, mul_sub, Finsupp.sum_mul, mul_assoc]
  have h_coeff : T.sqrtPrime ^ ⌈b - (weight c α - weight v α * ρ) - j * ρ⌉₊ ∣
    (D.mergedCoeff α p).coeff j := by
    rw [mergedCoeff, coeff_uniqueAlgEquiv]
    simpa [h_weight, weight_single] using hp (mapDomain D.merge α) (single () j)
  exact (pow_dvd_pow T.sqrtPrime (lt_ceil.2 hj)).trans h_coeff

/-- Let `i = D.letter`. The map of variables `D.merge` sends `Y_i = D.varY i` to `X_i = D.varX i`
and fixes the others, and the weights `D.poleOrder` are `D.card * D.frobPower s` at `X_s` and `0`
at the other variables, in particular non-zero at `X_i` and `0` at `Y_i`. An exponent is determined
by its image under `D.merge` and its weight for `D.poleOrder`: the first forgets only how the degree
splits between `X_i` and `Y_i`, and the second recovers it. -/
lemma eq_of_mapDomain_merge_eq {T : FrobeniusCycle N W R} {D : T.RootAt k}
    {α β : Fin k × ZMod N →₀ ℕ} (h_merge : mapDomain D.merge β = mapDomain D.merge α)
    (h_weight : weight D.poleOrder β = weight D.poleOrder α) : β = α := by
  have h_merge_add (γ : Fin k × ZMod N →₀ ℕ) :
      mapDomain D.merge γ + single (D.varY D.letter) (γ (D.varY D.letter)) =
        γ + single (D.varX D.letter) (γ (D.varY D.letter)) := by
    induction γ using induction_linear with
    | zero => simp
    | add γ γ' hγ hγ' => grind [mapDomain_add, Finsupp.add_apply, Finsupp.single_add]
    | single z n => by_cases hz : z = D.varY D.letter <;> simp [merge, hz, Ne.symm, add_comm]
  have h_pole_merge (γ : Fin k × ZMod N →₀ ℕ) : weight D.poleOrder (mapDomain D.merge γ) =
      weight D.poleOrder γ + γ (D.varY D.letter) * D.card := by
    simpa [weight_single] using congrArg (weight D.poleOrder) (h_merge_add γ)
  have h_sum : weight D.poleOrder α + β (D.varY D.letter) * D.card =
      weight D.poleOrder α + α (D.varY D.letter) * D.card := by
    rw [← h_pole_merge, ← h_merge, h_pole_merge, h_weight]
  have h_exponent : β (D.varY D.letter) = α (D.varY D.letter) := by
    simpa [card, T.prime.ne_zero] using h_sum
  refine add_right_cancel (b := single (D.varX D.letter) (α (D.varY D.letter))) ?_
  rw [← h_merge_add α, ← h_merge, ← h_exponent, h_merge_add β]

/-- Put `i = D.letter`. In each letter `s`, `X_s = D.varX s` and `Y_s = D.varY s` are the two
variables of the root. The weights `D.poleOrder` are `q P_s` at `X_s` and `0` at the other
variables, where `q = D.card = P ^ N` and `P_s = D.frobPower s = P ^ (s - i).val` for `P = T.P`. In
`f` substitute `D.mainSubst`, which sends `Y_i` to `X_i` and any other variable `z` to
`t ^ D.poleOrder z * z`. Take the coefficient, a polynomial in `t`, of the monomial obtained from
`x ^ α` by writing `X_i` for `Y_i` (`D.mergedCoeff α`). Its coefficient of `t ^ d`, with `d` the
weight of `α` for `D.poleOrder`, is the coefficient of `x ^ α` in `f`: no other monomial of `f`
contributes to it. -/
lemma coeff_mergedCoeff_aeval_mainSubst {T : FrobeniusCycle N W R} {D : T.RootAt k}
    (α : Fin k × ZMod N →₀ ℕ) (f : MvPolynomial (Fin k × ZMod N) R) :
    (D.mergedCoeff α (aeval D.mainSubst f)).coeff (weight D.poleOrder α) = f.coeff α := by
  induction f using MvPolynomial.induction_on' with
  | monomial β r =>
    have h_image : aeval D.mainSubst (monomial β r) =
        monomial (mapDomain D.merge β) (monomial (single () (weight D.poleOrder β)) r) := by
      simp [mainSubst, aeval_monomial, X, C_mul_monomial, monomial_pow, Finsupp.prod,
        ← monomial_sum_prod, mapDomain, weight_apply, Finsupp.sum, single_finsetSum]
    have h_iff : mapDomain D.merge β = mapDomain D.merge α ∧
        weight D.poleOrder β = weight D.poleOrder α ↔ β = α :=
      ⟨fun h ↦ eq_of_mapDomain_merge_eq h.left h.right, fun h ↦ by simp [h]⟩
    rw [h_image, mergedCoeff, coeff_uniqueAlgEquiv, coeff_monomial, coeff_monomial]
    split_ifs <;> simp_all [coeff_monomial]
  | add p p' hp hp' => simp [mergedCoeff_add, hp, hp']

/-- Zeros against degree. Let `w = T.sqrtPrime`, a square root of the prime `T.p` in `R`, let
`i = D.letter` and let `q = D.card = P ^ N` be the number of residue classes of `W`. In each letter
`s`, `X_s = D.varX s` and `Y_s = D.varY s` are the variables with the indices `a = D.fst`,
`a' = D.snd` if `s` is even and in reverse order if it is odd. Let the weights `c` rise from `X_s`
to `Y_s` by amounts in `[1 / 2, 1]`. Suppose that in all translates of `f` by `SL₂(W)`, placed in
the rows and columns `a`, `a'` (`rootSL`), each term has `w`-adic order plus `c`-weight at least
`l + c · α`, and that `w ^ (l + 1)` does not divide the coefficient of `x ^ α` in `f`.

Let `ν` be the weight of `α` for `D.zeroOrder`, which is `q` at `Y_i` and `P_s = P ^ (s - i).val` at
`Y_s` for `s ≠ i`, and `q ν'` its weight for `D.poleOrder`, which is `q P_s` at `X_s`; both weights
vanish at all other variables. Then `ν q ≤ q ν'`. -/
lemma HasBoundedIncrements.weight_zeroOrder_mul_card_le [NeZero N]
    {T : FrobeniusCycle N W R} {D : T.RootAt k}
    {c : Fin k × ZMod N → ℝ} (hc : D.HasBoundedIncrements c)
    {f : MvPolynomial (Fin k × ZMod N) R} {α : Fin k × ZMod N →₀ ℕ} {l : ℕ}
    (h_least : ∀ g ∈ rootSL W D.fst D.snd,
      T.polyAction g f ∈ gaussFiltration (adicFiltration T.sqrtPrime) c (l + weight c α))
    (h_not_dvd : ¬T.sqrtPrime ^ (l + 1) ∣ f.coeff α) :
    weight D.zeroOrder α * D.card ≤ weight D.poleOrder α := by
  -- `Φ` is the auxiliary binary form of degree `ν + q ν'` in the affine coordinate `t`, modulo
  -- `w ^ (l + 1)`. It vanishes to order exactly `ν` at infinity, that is, it has the degree
  -- `q ν'`, and to order at least `ν` at the other `q` rational points.
  let p : MvPolynomial (Fin k × ZMod N) (MvPolynomial Unit R) :=
    aeval (D.mainSubst - D.crossSubst) f
  let Φ : Polynomial (R ⧸ Ideal.span {T.sqrtPrime ^ (l + 1)}) :=
    (D.mergedCoeff α p).map (Ideal.Quotient.mk _)
  have h_slope : 0 < D.slope c := hc.slope_pos
  obtain ⟨h_infinity, h_cross⟩ :
      p ∈ T.iteratedGaussFiltration c (-D.slope c) D.poleOrder (l + weight c α) ∧ p - aeval
        D.mainSubst f ∈
        T.iteratedGaussFiltration c (-D.slope c) D.poleOrder (l + weight c α + 20⁻¹) :=
    hc.aeval_mem_and_sub_mem_iteratedGaussFiltration (by simpa using h_least 1 (one_mem _))
  have h_merge_weight : c (D.varX D.letter) - D.poleOrder (D.varX D.letter) * -D.slope c =
      c (D.varY D.letter) - D.poleOrder (D.varY D.letter) * -D.slope c := by simp [card_mul_slope]
  -- Modulo `w ^ (l + 1)` the coefficient of `t ^ (q ν')` is the coefficient of `x ^ α` in `f`.
  have h_top : T.sqrtPrime ^ (l + 1) ∣ (D.mergedCoeff α p).coeff (weight D.poleOrder α) - f.coeff
    α := by
    rw [← coeff_mergedCoeff_aeval_mainSubst (D := D), ← Polynomial.coeff_sub, ← mergedCoeff_sub]
    exact pow_dvd_coeff_mergedCoeff _ h_cross h_merge_weight (by linarith)
  have Φ_ne : Φ ≠ 0 := by
    refine fun hΦ ↦ h_not_dvd ((dvd_sub_right ?_).1 h_top)
    simpa [Φ, eq_zero_iff_dvd] using Polynomial.ext_iff.1 hΦ (weight D.poleOrder α)
  have Φ_deg : Φ.natDegree ≤ weight D.poleOrder α := by
    refine Polynomial.natDegree_le_iff_coeff_eq_zero.2 fun j hj ↦ ?_
    have h_gap : weight D.poleOrder α * D.slope c < j * D.slope c := by gcongr
    rw [Polynomial.coeff_map, eq_zero_iff_dvd]
    exact pow_dvd_coeff_mergedCoeff j h_infinity h_merge_weight (by linarith)
  have Φ_zero (r : W) : Polynomial.X ^ weight D.zeroOrder α ∣
      Φ.taylor (((Ideal.Quotient.mk _).comp (T.embedding D.letter)) r) := by
    refine Polynomial.X_pow_dvd_iff.2 fun j hj ↦ ?_
    have h_gap : j * D.slope c < weight D.zeroOrder α * D.slope c := by gcongr
    have h_shift : shiftCoeff _ (T.embedding D.letter r) p ∈
        T.iteratedGaussFiltration c (D.slope c) D.zeroOrder (l + weight c α) :=
      hc.shiftCoeff_aeval_mem r (h_least _ (inv_mem (D.swapTransvection_mem_rootSL r)))
    rw [RingHom.comp_apply, ← Polynomial.map_taylor, ← mergedCoeff_shiftCoeff, Polynomial.coeff_map,
      eq_zero_iff_dvd]
    exact pow_dvd_coeff_mergedCoeff j h_shift (by simp [card_mul_slope]) (by linarith)
  calc weight D.zeroOrder α * D.card
      = weight D.zeroOrder α * Nat.card (IsLocalRing.ResidueField W) := by
        rw [T.card_residueField, card]
    _ ≤ Φ.natDegree := stepanov_count _ _ Φ_ne Φ_zero
    _ ≤ weight D.poleOrder α := Φ_deg

end FrobeniusCycle.RootAt

variable {R : Type} {N k : ℕ} {W : Type} [CommRing R] [NeZero N] [CommRing W] [IsLocalRing W]

/-- The root lemma. Let `T` be a Frobenius cycle: ring maps `ι_s : W → R` for the letters `s ∈ ℤ/N`,
alternately even and odd, with `ι_{s+1} ≡ ι_s ^ P` modulo a prime `p`, where `P = T.P` is a power of
`p` and `W` has `q = P ^ N` residue classes, and a square root `w = T.sqrtPrime` of `p` in `R`.

Let `a ≠ a'`. In the letter `s` let `Y_s = T.rootVar a a' s` be the variable `(a', s)` for even and
`(a, s)` for odd `s`, and let `X_s = T.rootVar a' a s` be the other of the two. Let the weights `c`
of the variables rise from `X_s` to `Y_s` by amounts in `[1 / 2, 1]`. Suppose that in all translates
of `f` by `SL₂(W)` in the rows and columns `a`, `a'` each term has `w`-adic order plus weight at
least `l + c · α`, and that `w ^ (l + 1)` does not divide the coefficient of `x ^ α` in `f`. Then
the defect of `α` at the letter `i` is at most `0`.

These bounds along the roots are Pieri's inequalities for the exponent of a term that is least among
all translates. -/
theorem FrobeniusCycle.defect_nonpos_of_extreme_term (T : FrobeniusCycle N W R) {a a' : Fin k}
    (i : ZMod N) (ha : a ≠ a') {c : Fin k × ZMod N → ℝ}
    (hc : ∀ s : ZMod N, c (T.rootVar a a' s) - c (T.rootVar a' a s) ∈ Set.Icc 2⁻¹ 1)
    {f : MvPolynomial (Fin k × ZMod N) R} {α : Fin k × ZMod N →₀ ℕ} {l : ℕ}
    (h_least : ∀ g ∈ rootSL W a a',
      T.polyAction g f ∈ gaussFiltration (adicFiltration T.sqrtPrime) c (l + weight c α))
    (h_not_dvd : ¬T.sqrtPrime ^ (l + 1) ∣ f.coeff α) : weight (T.defectWeight i a a') α ≤ 0 := by
  let D : T.RootAt k := ⟨i, a, a', ha⟩
  -- Stepanov's count gives `ν q ≤ q ν'`, and the defect is `(ν - ν') / (q - 1)`.
  have h_count : weight D.zeroOrder α * D.card ≤ weight D.poleOrder α :=
    RootAt.HasBoundedIncrements.weight_zeroOrder_mul_card_le (D := D) hc h_least h_not_dvd
  have h_card : (1 : ℝ) < D.card := by simpa [RootAt.card] using T.one_lt_q
  have h_defect : weight (T.defectWeight D.letter D.fst D.snd) α =
      (weight D.zeroOrder α - weight D.poleOrder α / D.card) / (D.card - 1) := by
    simp [weight_eq_sum, D.defectWeight_eq, mul_sub, mul_div, ← Finset.sum_div]
  refine h_defect.trans_le (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 ?_) (by linarith))
  exact (le_div_iff₀ D.cast_card_pos).2 (mod_cast h_count)

/-! ### Consequences -/

/-- The translate of a polynomial `f` by `g` in `GL_k(W)` has total degree at most that of `f`. -/
lemma FrobeniusCycle.totalDegree_polyAction_le (T : FrobeniusCycle N W R) (g : GL (Fin k) W)
    (f : MvPolynomial (Fin k × ZMod N) R) : (T.polyAction g f).totalDegree ≤ f.totalDegree := by
  have h_linear (x : Fin k × ZMod N) : (T.polyAction g (X x)).IsHomogeneous 1 := by
    rw [polyAction_X]
    exact .sum _ _ 1 fun b _ ↦ isHomogeneous_C_mul_X _ (b, x.2)
  have h_term (α : Fin k × ZMod N →₀ ℕ) :
      (T.polyAction g (monomial α (f.coeff α))).IsHomogeneous (1 * α.degree) := by
    rw [aeval_unique (T.polyAction g)]
    exact (isHomogeneous_monomial _ rfl).aeval _ h_linear
  conv_lhs => rw [f.as_sum, map_sum]
  exact totalDegree_finsetSum_le fun α hα ↦
    (h_term α).totalDegree_le.trans ((one_mul _).trans_le (le_totalDegree hα))

/-- For the variable weights `fun x ↦ depth x - T.defectWeight i a a' x / 3`, the weight of `α` is
`weight depth α` minus a third of `weight (T.defectWeight i a a') α`. -/
lemma FrobeniusCycle.weight_sub_defectWeight_div_three (T : FrobeniusCycle N W R) {a a' : Fin k}
    (i : ZMod N) (depth : Fin k × ZMod N → ℝ) (α : Fin k × ZMod N →₀ ℕ) :
    weight (fun x : Fin k × ZMod N ↦ depth x - T.defectWeight i a a' x / 3) α =
      weight depth α - weight (T.defectWeight i a a') α / 3 := by
  simp [weight_eq_sum, mul_sub, mul_div, ← Finset.sum_div]

/-- A large defect forces a divisible coefficient. Let `a ≠ a'`, and in each letter `s ∈ ℤ/N` let
`Y_s = T.rootVar a a' s` be the variable `(a', s)` for even and `(a, s)` for odd `s`, and
`X_s = T.rootVar a' a s` the other of the two. Let `depth` be weights of the variables that rise by
`1` from `X_s` to `Y_s` in each letter. If in all translates of `f` by `SL₂(W)` in the rows and
columns `a`, `a'` each term has order for `w = T.sqrtPrime` plus depth at least `v₀`, then each term
of `f` has order plus depth at least `v₀` plus a third of its defect at the letter `i` along the
root `(a, a')`. -/
theorem FrobeniusCycle.mem_gaussFiltration_sub_defect_div_three (T : FrobeniusCycle N W R)
    {a a' : Fin k} (i : ZMod N) (ha : a ≠ a') {depth : Fin k × ZMod N → ℝ}
    (h_step : ∀ s : ZMod N, depth (T.rootVar a a' s) - depth (T.rootVar a' a s) = 1)
    {v₀ : ℝ} {f : MvPolynomial (Fin k × ZMod N) R}
    (hf : ∀ g ∈ rootSL W a a', T.polyAction g f ∈ gaussFiltration (adicFiltration T.sqrtPrime) depth
      v₀) :
    f ∈ gaussFiltration (adicFiltration T.sqrtPrime)
      (fun x : Fin k × ZMod N ↦ depth x - T.defectWeight i a a' x / 3) v₀ := by
  -- Let `ω` be the depth minus a third of the defect weight. Suppose that some translate has a
  -- term whose order plus `ω`-weight is below `v₀`, and take a least such term. By
  -- `defect_nonpos_of_extreme_term` its defect is at most `0`, so its order plus depth is below
  -- `v₀` as well, against the hypothesis.
  set ω : Fin k × ZMod N → ℝ := fun x ↦ depth x - T.defectWeight i a a' x / 3
  have ω_step (s : ZMod N) : ω (T.rootVar a a' s) - ω (T.rootVar a' a s) ∈ Set.Icc 2⁻¹ 1 := by
    have h_rise : T.defectWeight i a a' (T.rootVar a a' s) -
        T.defectWeight i a a' (T.rootVar a' a s) ∈ Set.Icc 0 (3 / 2) :=
      T.defectWeight_sub_mem_Icc s (i := i) ha
    have h_diff : ω (T.rootVar a a' s) - ω (T.rootVar a' a s) =
        1 - (T.defectWeight i a a' (T.rootVar a a' s) -
          T.defectWeight i a a' (T.rootVar a' a s)) / 3 := by
      simp only [ω]
      linarith [h_step s]
    rw [h_diff]
    exact ⟨by linarith [h_rise.2], by linarith [h_rise.1]⟩
  -- `(α, l) ∈ low`: in some translate the term at `α` has order at most `l`, and `l + ω · α < v₀`.
  let low : Set ((Fin k × ZMod N →₀ ℕ) × ℕ) := {x | x.2 + weight ω x.1 < v₀ ∧
    ∃ g ∈ rootSL W a a', ¬T.sqrtPrime ^ (x.2 + 1) ∣ (T.polyAction g f).coeff x.1}
  -- A lower bound `t ≤ v₀` for `l + ω · α` on `low` is a level of all translates.
  have mem_of_forall {t : ℝ} (ht : t ≤ v₀) (h_low : ∀ x ∈ low, t ≤ x.2 + weight ω x.1)
      {g : GL (Fin k) W} (hg : g ∈ rootSL W a a') :
      T.polyAction g f ∈ gaussFiltration (adicFiltration T.sqrtPrime) ω t := by
    intro α
    by_contra h_not
    obtain ⟨l, hl⟩ : ∃ l : ℕ, ⌈t - weight ω α⌉₊ = l + 1 :=
      exists_eq_succ_of_ne_zero fun h_zero ↦ h_not (by simp [h_zero])
    have h_lt : l < t - weight ω α := lt_ceil.1 (by lia)
    linarith [h_low (α, l) ⟨by linarith, g, hg, by simpa [hl] using h_not⟩]
  suffices h_empty : ¬low.Nonempty by
    simpa using mem_of_forall le_rfl (fun x hx ↦ absurd ⟨x, hx⟩ h_empty) (one_mem _)
  intro h_ne
  -- The degree of `f` bounds `α`, and `v₀` bounds `l`.
  have h_finite : low.Finite := by
    refine ((finite_of_degree_le f.totalDegree).biUnion fun α _ ↦
      (Set.finite_singleton α).prod (Set.finite_Iio ⌈v₀ - weight ω α⌉₊)).subset ?_
    rintro ⟨α, l⟩ ⟨h_lt, g, -, h_not⟩
    have h_degree : α.degree ≤ f.totalDegree :=
      (le_totalDegree (MvPolynomial.mem_support_iff.2 fun h_zero ↦ h_not (by simp [h_zero]))).trans
        (T.totalDegree_polyAction_le g f)
    exact Set.mem_biUnion h_degree ⟨rfl, lt_ceil.2 (by linarith)⟩
  obtain ⟨⟨α, l⟩, ⟨h_lt, g₀, hg₀, h_not⟩, h_min⟩ :
      ∃ x ∈ low, ∀ y ∈ low, x.2 + weight ω x.1 ≤ y.2 + weight ω y.1 :=
    Set.exists_min_image low _ h_finite h_ne
  have h_defect : weight (T.defectWeight i a a') α ≤ 0 :=
    T.defect_nonpos_of_extreme_term i ha ω_step
      (fun g hg ↦ by simpa using mem_of_forall h_lt.le h_min (mul_mem hg hg₀)) h_not
  have h_weight : weight ω α = weight depth α - weight (T.defectWeight i a a') α / 3 :=
    T.weight_sub_defectWeight_div_three i depth α
  have h_depth : l < v₀ - weight depth α := by linarith
  exact h_not ((pow_dvd_pow _ (lt_ceil.2 h_depth)).trans (hf g₀ hg₀ α))

/-- The root lemma for weights that rise by `1`, over a field of characteristic `T.p`. Let `a ≠ a'`,
and let `height` be weights of the variables that rise by `1` from `X_s = T.rootVar a' a s` to
`Y_s = T.rootVar a a' s` in each letter `s ∈ ℤ/N`; these are the variables with index `a`, `a'` for
even `s` and in reverse order for odd `s`. A term of `f` whose height is least among the terms of
all translates of `f` by `SL₂(W)` in the rows and columns `a`, `a'` has defect at most `0`. -/
lemma FrobeniusCycle.weight_defectWeight_nonpos_of_least {a a' : Fin k} {K : Type} [Field K]
    (T : FrobeniusCycle N W K) [CharP K T.p] (i : ZMod N) (ha : a ≠ a')
    {height : Fin k × ZMod N → ℝ}
    (h_step : ∀ s : ZMod N, height (T.rootVar a a' s) - height (T.rootVar a' a s) = 1)
    {f : MvPolynomial (Fin k × ZMod N) K} {α : Fin k × ZMod N →₀ ℕ}
    (h_least : ∀ g ∈ rootSL W a a',
      T.polyAction g f ∈ gaussFiltration (adicFiltration T.sqrtPrime) height (weight height α))
    (hα : f.coeff α ≠ 0) : weight (T.defectWeight i a a') α ≤ 0 := by
  have w_zero : T.sqrtPrime = 0 := (pow_eq_zero_iff two_ne_zero).1
    (T.sqrtPrime_sq.trans (CharP.cast_eq_zero K _))
  exact T.defect_nonpos_of_extreme_term i ha (c := height) (l := 0) (fun s ↦ by norm_num [h_step])
    (by simpa using h_least) (by simpa [w_zero] using hα)

end New
