import Lib.Adelic.Unitary.Defs

/-!
# Characters of finite groups: averages, virtual characters and central projections

This file sets up the character theory of a finite group `G` that is used for the characters of
`GL n` over a finite field. From Wedderburn's theorem it derives criteria for irreducibility.

## Main definitions and results

* `New.IsIrreducibleChar`: characters of norm one that satisfy the convolution identity with every
  class function.
* `New.virtualChars S G`: the `S`-span of the characters, a subalgebra of `G → ℂ`; for `S = ℤ` these
  are the virtual characters, for `S = ℕ` the characters (`New.isChar_of_mem_virtualChars`).
* `New.IsCentralProj`: central idempotents e of the group algebra ℂ[H] of any group H. Their
  coefficients are class functions; 1 − e, the image of e under a ring endomorphism of ℂ and tensor
  products are again central idempotents.
* `New.IsClassFunction.isIrreducibleChar_of_classInner_eq_intCast`,
  `New.IsClassFunction.mem_virtualChars`, `New.IsClassFunction.exists_eq_mul_groupAlgElem_mul`:
  criteria for a class function `f` to be an irreducible character, for `f` to be a combination of
  characters with coefficients in a given semiring, and for an element of `ℂ[G]` to be recovered
  from its product with `New.groupAlgElem f`. They are collected in
  `New.isIrreducibleChar_and_mem_virtualChars_and_exists_mul`.
* `New.IsCentralProj.isChar_card_mul_coeff`: for a central idempotent `e` of `ℂ[G]`, the function
  `g ↦ |G| · e(g)` is a character. Its pairing with any character is the rank of an idempotent, so a
  natural number. It is the character of a representation of dimension at most `|G|`
  (`New.IsCentralProj.exists_character_eq_and_finrank_le_card`), so the coefficients of `e` have
  norm at most `1` (`New.IsCentralProj.norm_coeff_le_one`).
* `New.IsCentralProj.self_adjoint`, `New.IsCentralProj.sum_norm_sq_conv_le`: a central idempotent of
  `ℂ[G]` acts self-adjointly for every `G`-invariant form that is sesquilinear for `σ⁻¹ ∘ conj ∘ σ`,
  complex conjugation transported along an automorphism `σ` of `ℂ`. So it acts as an orthogonal
  projection in every unitary representation. Hence convolution with it does not increase `ℓ²`
  norms.
-/

noncomputable section

/-!
## Averages, inner products, characters and group algebra elements

The basic definitions: `New.finMean`, `New.classInner`, `New.groupAlgElem` (a function `f` as the
element `∑ g, f g • g` of the group algebra), `New.IsChar`, `New.IsClassFunction` and
`New.IsIrreducibleChar`.
-/

namespace New

variable {G : Type*} [Group G] [Finite G] (f h : G → ℂ)

/-- The average of a complex function f on a finite type G: the sum of its values divided by the
cardinality of G. -/
def finMean : ℂ := finsum f / Nat.card G

/-- The inner product ⟨f, h⟩ of complex functions on a finite set: the average over g of conj
f(g) · h(g). -/
def classInner : ℂ := finMean fun g ↦ starRingEnd ℂ (f g) * h g

/-- For a complex function f on a finite group G, the element Σ f(g)·g of the group algebra
ℂ[G]. -/
@[simps]
def groupAlgElem : MonoidAlgebra ℂ G := ⟨Finsupp.equivFunOnFinite.symm f⟩

/-- The function f : G → ℂ is the character of a finite-dimensional complex representation
of G. -/
def IsChar : Prop := ∃ V : FDRep ℂ G, V.character = f

/-- The function f : G → ℂ is a class function: f(xgx⁻¹) = f(g) for all g, x in G. -/
@[simp]
abbrev IsClassFunction : Prop := ∀ g x : G, f (x * g * x⁻¹) = f g

/-- The function `f` is an irreducible character, in the following form: (a) `f` is a character,
(b) its norm `New.classInner f f` is `1`, and (c) for every class function `h` and every `y`,
`f 1 * finMean (t ↦ conj (f t) * h (t * y)) = classInner f h * f y`. Clause (c) says that `h`
acts by a scalar in the representation. The lemma
`New.IsClassFunction.isIrreducibleChar_of_classInner_eq_intCast` gives a criterion for all three
clauses. -/
def IsIrreducibleChar : Prop :=
  IsChar f ∧ classInner f f = 1 ∧
  ∀ h : G → ℂ, IsClassFunction h → ∀ y : G,
    f 1 * finMean (fun t ↦ starRingEnd ℂ (f t) * h (t * y)) = classInner f h * f y

variable {f h}

section

omit [Finite G]

lemma IsIrreducibleChar.isChar (hf : IsIrreducibleChar f) : IsChar f := hf.left

lemma IsIrreducibleChar.classInner_self (hf : IsIrreducibleChar f) : classInner f f = 1 :=
  hf.right.left

/-- For an irreducible character `f`, a class function `h` and `y : G`, the inner product of `f`
with the translate `t ↦ h (t * y)`, times `f 1`, is `classInner f h * f y`. -/
lemma IsIrreducibleChar.mul_classInner_translate (hf : IsIrreducibleChar f) (hh : IsClassFunction h)
    (y : G) :
    f 1 * classInner f (fun t : G ↦ h (t * y)) = classInner f h * f y :=
  hf.right.right h hh y

end

end New

namespace New

/-!
## Averages of complex functions on finite sets

`New.finMean f` is the mean of a complex function on a finite type.
-/

section Average

open ComplexConjugate Finset Fintype

attribute [local instance low] Fintype.ofFinite

variable {α β : Type*} {ι : Type*} [Finite α] [Finite β] {f : α → ℂ} {g : β → ℂ}

omit [Finite α] in
lemma finMean_eq [Fintype α] : finMean f = (∑ x : α, f x) / Fintype.card α := by
  rw [finMean, finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card]

@[simp]
lemma finMean_const_mul (c : ℂ) : finMean (fun x : α ↦ c * f x) = c * finMean f := by
  simp [finMean_eq, mul_div, mul_sum]

lemma finMean_sum (s : Finset ι) (f : ι → α → ℂ) :
    finMean (fun x : α ↦ ∑ i ∈ s, f i x) = ∑ i ∈ s, finMean (f i) := by
  simp [finMean_eq, s.sum_comm, sum_div]

@[simp]
lemma finMean_const [Nonempty α] (c : ℂ) : finMean (fun _ : α ↦ c) = c := by
  simp [finMean_eq]

lemma finMean_conj : finMean (fun x : α ↦ conj (f x)) = conj (finMean f) := by
  simp [finMean_eq]

lemma finMean_equiv (e : β ≃ α) (hfg : ∀ x : β, f (e x) = g x) : finMean f = finMean g := by
  simp [finMean_eq, ← hfg, card_congr e, Equiv.sum_comp]

/-- Fubini: the average over a product is the iterated average. -/
lemma finMean_prod (f : α × β → ℂ) :
    finMean f = finMean fun x : α ↦ finMean fun y : β ↦ f (x, y) := by
  simp only [finMean_eq, sum_prod_type, card_prod, Nat.cast_mul, ← sum_div, div_div, mul_comm]

/-- Let `p : α →+ β` be a surjective homomorphism of finite additive groups. Then the mean of
`f ∘ p` over `α` equals the mean of `f` over `β`. -/
lemma finMean_comp_surjective [AddGroup α] [AddGroup β] (p : α →+ β) (hp : Function.Surjective p)
    (f : β → ℂ) : finMean (fun x : α ↦ f (p x)) = finMean f := by
  -- `α` is in bijection with `β × ker p`, and `p` becomes the first projection
  let e : α ≃ β × p.ker :=
    (Equiv.sigmaFiberEquiv p).symm.trans (.sigmaEquivProdOfEquiv (p.fiberEquivKerOfSurjective hp))
  calc
    _ = finMean fun x : β × p.ker ↦ f x.1 := (finMean_equiv e fun _ ↦ rfl).symm
    _ = finMean f := by simp_rw [finMean_prod, finMean_const]

end Average

/-!
## Characters and the algebra of virtual characters

* `New.IsChar.exists_sum_addChar_zpowers`: on a cyclic subgroup a character is a sum of linear
  characters; hence `New.IsChar.apply_inv`, `New.IsChar.isIntegral`, `New.IsChar.norm_apply_le` and
  `New.IsChar.star`.
-/

section VirtualCharacters

open ComplexConjugate Submodule AddChar LinearMap IsMulCommutative Finset Subgroup

attribute [local instance low] Fintype.ofFinite

variable {S : Type*} [CommSemiring S] [Algebra S ℂ]
  {G : Type*} [Group G] {χ ψ f : G → ℂ}

/-! ### The algebra spanned by the characters -/

/-- The product of two characters is a character, that of the tensor product. -/
lemma IsChar.mul (hχ : IsChar χ) (hψ : IsChar ψ) : IsChar (χ * ψ) := by
  obtain ⟨V, rfl⟩ := hχ
  obtain ⟨W, rfl⟩ := hψ
  exact ⟨CategoryTheory.MonoidalCategory.tensorObj V W, FDRep.char_tensor V W⟩

lemma isChar_monoidHom (l : G →* ℂ) : IsChar l :=
  -- the one-dimensional representation in which `g` acts as multiplication by `l g`
  ⟨.of (.comp MonoidHom.smulOneHom l), funext fun g ↦ Algebra.trace_self_apply (l g)⟩

variable (S G) in
/-- For a group G and a commutative semiring S with ℂ an S-algebra, the S-subalgebra of functions
G → ℂ spanned over S by the characters of G. -/
def virtualChars : Subalgebra S (G → ℂ) :=
  (span S {f : G → ℂ | IsChar f}).toSubalgebra
    -- the constant `1` is the trivial character
    (subset_span (isChar_monoidHom 1))
    -- a product of characters is a character, and multiplication is bilinear
    (BilinMap.apply_apply_mem_of_mem_span (span S {f : G → ℂ | IsChar f}) {f : G → ℂ | IsChar f}
      {f : G → ℂ | IsChar f} (LinearMap.mul S (G → ℂ)) fun _ hχ _ hψ ↦ subset_span (hχ.mul hψ))

/-- The zero function is a character, that of the zero representation. -/
lemma isChar_zero : IsChar (0 : G → ℂ) :=
  ⟨.of (Representation.trivial ℂ G PUnit), funext fun _ ↦ (trace ℂ PUnit).map_zero⟩

/-- The sum of two characters is a character, that of the direct sum. -/
lemma IsChar.add (hχ : IsChar χ) (hψ : IsChar ψ) : IsChar (χ + ψ) := by
  obtain ⟨V, rfl⟩ := hχ
  obtain ⟨W, rfl⟩ := hψ
  exact ⟨.of (.prod V.ρ W.ρ), funext fun g ↦ trace_prodMap' (V.ρ g) (W.ρ g)⟩

lemma isChar_of_mem_virtualChars (hf : f ∈ virtualChars ℕ G) : IsChar f := by
  -- The characters form an additive submonoid, which is therefore its own `ℕ`-span.
  let M : AddSubmonoid (G → ℂ) := ⟨⟨{χ : G → ℂ | IsChar χ}, IsChar.add⟩, isChar_zero⟩
  have h_span : f ∈ (span ℕ (M : Set (G → ℂ))).toAddSubmonoid := hf
  rwa [span_nat_eq] at h_span

/-! ### Properties of a character -/

lemma IsChar.comp (hχ : IsChar χ) {H : Type*} [Group H] (p : H →* G) : IsChar (χ ∘ p) := by
  obtain ⟨V, rfl⟩ := hχ
  exact ⟨.of (V.ρ.comp p), rfl⟩

lemma IsChar.mem_virtualChars (hχ : IsChar χ) : χ ∈ virtualChars S G := subset_span hχ

lemma IsChar.isClassFunction (hχ : IsChar χ) : IsClassFunction χ := by
  obtain ⟨V, rfl⟩ := hχ
  exact V.char_conj

variable [Finite G]

lemma IsChar.exists_finMean_eq_natCast (hχ : IsChar χ) : ∃ m : ℕ, finMean χ = m := by
  -- the average of a character is the dimension of the invariants
  obtain ⟨V, rfl⟩ := hχ
  use Module.finrank ℂ (Representation.invariants V.ρ)
  simp [finMean_eq, ← V.average_char_eq_finrank_invariants, div_eq_inv_mul]

/-- Fourier inversion on a finite abelian group `A`: a function `φ : A → ℂ` is the sum of the
characters `l` of `A`, weighted by the averages of `x ↦ φ x * l (-x)`. -/
lemma sum_finMean_mul_addChar {A : Type*} [AddCommGroup A] [Finite A] (φ : A → ℂ) (a : A) :
    ∑ l : AddChar A ℂ, finMean (fun x : A ↦ φ x * l (-x)) * l a = φ a := by
  classical
  calc ∑ l : AddChar A ℂ, finMean (fun x : A ↦ φ x * l (-x)) * l a
      = (Fintype.card A : ℂ)⁻¹ * ∑ x : A, φ x * ∑ l : AddChar A ℂ, l (-x + a) := by
        simp only [finMean_eq, div_eq_inv_mul, map_add_eq_mul, mul_sum, sum_mul, mul_assoc]
        exact sum_comm
    -- orthogonality: `∑ l, l y` is the order of `A` if `y = 0`, and `0` otherwise
    _ = φ a := by simp [field, sum_apply_eq_ite, neg_add_eq_zero]

/-- On the cyclic subgroup `zpowers g` generated by `g`, a character `χ` of `G` is the sum of the
linear characters `l` of that subgroup (written additively) with multiplicities `m l : ℕ`. -/
lemma IsChar.exists_sum_addChar_zpowers (hχ : IsChar χ) (g : G) :
    ∃ m : AddChar (Additive (zpowers g)) ℂ → ℕ, ∀ (u : G) (hu : u ∈ zpowers g),
      ∑ l : AddChar (Additive (zpowers g)) ℂ, m l • l (Additive.ofMul ⟨u, hu⟩) = χ u := by
  -- The Fourier coefficient of `l` in the restriction of `χ` to `zpowers g` is the average of the
  -- character `χ * l⁻¹` of that group, a natural number.
  have h_nat (l : AddChar (Additive (zpowers g)) ℂ) :
      ∃ m : ℕ, finMean (fun x : Additive (zpowers g) ↦ χ x.toMul * l (-x)) = m := by
    have h_res : IsChar fun x : zpowers g ↦ χ x := hχ.comp (zpowers g).subtype
    have h_inv : IsChar fun x : zpowers g ↦ l (-Additive.ofMul x) :=
      isChar_monoidHom
        { toFun x := l (-Additive.ofMul x)
          map_one' := by simp
          map_mul' x y := by simp [map_add_eq_mul, mul_comm] }
    obtain ⟨m, hm⟩ := (h_res.mul h_inv).exists_finMean_eq_natCast
    exact ⟨m, (finMean_equiv Additive.ofMul fun _ ↦ rfl).trans hm⟩
  choose m hm using h_nat
  refine ⟨m, fun u hu ↦ ?_⟩
  calc
    _ = ∑ l : AddChar (Additive (zpowers g)) ℂ,
        finMean (fun x ↦ χ x.toMul * l (-x)) * l (.ofMul ⟨u, hu⟩) := by simp [hm]
    _ = χ u := sum_finMean_mul_addChar (fun x : Additive (zpowers g) ↦ χ x.toMul) (.ofMul ⟨u, hu⟩)

lemma IsChar.apply_inv (hχ : IsChar χ) (g : G) : χ g⁻¹ = conj (χ g) := by
  -- on `zpowers g` the character is a sum of linear characters `l`, and `l (-x) = conj (l x)`
  obtain ⟨m, hm⟩ := hχ.exists_sum_addChar_zpowers g
  calc χ g⁻¹ = ∑ l : AddChar (Additive (zpowers g)) ℂ, m l • l (-.ofMul ⟨g, mem_zpowers g⟩) :=
        (hm g⁻¹ (inv_mem (mem_zpowers g))).symm
    _ = conj (χ g) := by simp [← hm g (mem_zpowers g), map_neg_eq_conj]

/-- The values of a character of a finite group are algebraic integers. -/
lemma IsChar.isIntegral (hχ : IsChar χ) (g : G) : IsIntegral ℤ (χ g) := by
  -- `χ g` is a sum of values of linear characters, which are roots of unity
  have h_root (l : AddChar (Additive (zpowers g)) ℂ) (x : Additive (zpowers g)) :
      IsIntegral ℤ (l x) := by
    have h_pow : l x ^ orderOf l = 1 := by rw [← pow_apply, pow_orderOf_eq_one, one_apply]
    exact .of_pow (orderOf_pos l) (by simp [h_pow, isIntegral_one])
  obtain ⟨m, hm⟩ := hχ.exists_sum_addChar_zpowers g
  rw [← hm g (mem_zpowers g)]
  exact IsIntegral.sum _ fun l _ ↦ (h_root l _).nsmul (m l)

/-- The norm of a character of a finite group is largest at the identity. -/
lemma IsChar.norm_apply_le (hχ : IsChar χ) (g : G) : ‖χ g‖ ≤ ‖χ 1‖ := by
  -- `χ g` is a sum of `∑ l, m l` roots of unity, and `χ 1` is their number
  obtain ⟨m, hm⟩ := hχ.exists_sum_addChar_zpowers g
  have h_one : χ 1 = (∑ l : AddChar (Additive (zpowers g)) ℂ, m l : ℕ) := by
    simp [← hm 1 (one_mem _), show (⟨1, one_mem _⟩ : zpowers g) = 1 from rfl]
  rw [h_one, Complex.norm_natCast, ← hm g (mem_zpowers g), Nat.cast_sum]
  exact norm_sum_le_of_le _ fun l _ ↦ by simp [AddChar.norm_apply]

/-- The complex conjugate of a character is a character, that of the dual representation. -/
lemma IsChar.star (hχ : IsChar χ) : IsChar fun g : G ↦ conj (χ g) := by
  simp only [← hχ.apply_inv]
  obtain ⟨V, rfl⟩ := hχ
  exact ⟨.of (.dual V.ρ), funext fun g ↦ by simp⟩

/-- The inner product `classInner χ f` (the average of `conj (χ g) * f g`) of a character `χ` with
an `S`-linear combination `f` of characters lies in the image of `S` in `ℂ`. -/
lemma IsChar.exists_classInner_eq (hχ : IsChar χ) (hf : f ∈ virtualChars S G) :
    ∃ m : S, classInner χ f = algebraMap S ℂ m := by
  -- Write `f = ∑ j, a j • ψ j` with characters `ψ j`. Each `classInner χ (ψ j)` is the average of
  -- the character `conj χ * ψ j`, a natural number `m j`.
  obtain ⟨n, a, ψ, rfl⟩ := mem_span_set'.1 hf
  choose m hm using fun j : Fin n ↦
    show ∃ m : ℕ, classInner χ (ψ j) = m from
      (hχ.star.mul (ψ j).property).exists_finMean_eq_natCast
  use ∑ j : Fin n, a j * m j
  calc classInner χ (∑ j : Fin n, a j • (ψ j : G → ℂ))
      = ∑ j : Fin n, algebraMap S ℂ (a j) * classInner χ (ψ j) := by
        simp [classInner, mul_sum, finMean_sum, Algebra.smul_def, mul_left_comm]
    _ = algebraMap S ℂ (∑ j : Fin n, a j * m j) := by simp [hm]

omit [Finite G] in
/-- The pull-back along a homomorphism from a finite group of an `S`-linear combination of
characters is an `S`-linear combination of characters. -/
lemma comp_mem_virtualChars (hf : f ∈ virtualChars S G) {H : Type*} [Group H] [Finite H]
    (p : H →* G) : f ∘ p ∈ virtualChars S H :=
  -- precomposition with `p` is linear and maps characters to characters
  mapsTo_span (f := funLeft S ℂ p) (fun _ hχ ↦ hχ.comp p) hf

omit [Finite G] in
lemma isClassFunction_of_mem_virtualChars (hf : f ∈ virtualChars S G) : IsClassFunction f := by
  induction hf using span_induction with
  | mem χ hχ => exact IsChar.isClassFunction hχ
  | zero => simp
  | add χ ψ _ _ hχ hψ => exact fun g x ↦ by simp [hχ g x, hψ g x]
  | smul a χ _ hχ => exact fun g x ↦ by simp [hχ g x]

end VirtualCharacters

/-!
## Central projections of group algebras and their tensor products

* `New.piTensorElem`: the tensor product ⊗ x_i in ℂ[∏ G_i] of elements x_i of ℂ[G_i], for a finite
  index type ι. If every x_i is a central idempotent, so is ⊗ x_i
  (`New.IsCentralProj.piTensorElem`).
* `New.piTensorElem_apply_eq_zero`, `New.piTensorElem_mul_eq_zero`: a tensor product kills a vector,
  or another tensor product, as soon as one factor does.
-/

section CentralProjections

open MonoidAlgebra Finset Finsupp Representation Function

attribute [local instance low] Fintype.ofFinite

variable {ι : Type _} [Fintype ι] [DecidableEq ι]
  {G : ι → Type _} [∀ i : ι, Group (G i)] [∀ i : ι, Finite (G i)] {H : Type*} [Group H]
  {x : ∀ i : ι, ℂ[G i]} {V : Type*} [AddCommGroup V] [Module ℂ V]
  (σ : Representation ℂ H V) {e : ℂ[H]} {ρ : Representation ℂ (∀ i : ι, G i) V}

lemma IsClassFunction.commute (he : IsClassFunction e.coeff) (x : ℂ[H]) : Commute x e := by
  have h_swap (t g : H) : e.coeff (g * t⁻¹) = e.coeff (t⁻¹ * g) := by
    simpa [mul_assoc] using he (t⁻¹ * g) t
  ext g
  simp only [coeff_mul_apply_left x e, coeff_mul_apply_right e x, h_swap, mul_comm]

/-- An element `e` of the group algebra of a finite group `H` acts in the representation `σ` as
the sum of the operators `σ s` weighted by the coefficients of `e`. -/
lemma asAlgebraHom_eq_sum [Fintype H] : σ.asAlgebraHom e = ∑ s : H, e.coeff s • σ s := by
  simp [asAlgebraHom_def, MonoidAlgebra.lift_apply, sum_fintype]

/-- `e` is a central idempotent of the complex group algebra `ℂ[H]` of a group `H`: it is
idempotent and its coefficients form a class function. -/
def IsCentralProj (e : ℂ[H]) : Prop := IsIdempotentElem e ∧ IsClassFunction e.coeff

lemma IsCentralProj.isIdempotentElem (h : IsCentralProj e) : IsIdempotentElem e := h.left

lemma IsCentralProj.isClassFunction (h : IsCentralProj e) : IsClassFunction e.coeff := h.right

open scoped Classical in
/-- The multiplicative map sending a family `x i ∈ ℂ[G i]` to its tensor product in the group
algebra of the product of the `G i`: the coefficient at `s` is the product over `i` of the
coefficients of `x i` at `s i`. -/
@[simps!]
noncomputable def piTensorElem : (∀ i : ι, ℂ[G i]) →* ℂ[∀ i : ι, G i] where
  toFun x := groupAlgElem fun s : ∀ i : ι, G i ↦ ∏ i : ι, (x i).coeff (s i)
  map_one' := by aesop (add simp [one_def, single_apply, prod_boole])
  map_mul' := by
    -- the convolution at `s` factors over `ι`, as a product of sums is a sum over families
    aesop (add simp [coeff_mul_apply_left, sum_fintype, prod_univ_sum, prod_mul_distrib])

/-- The tensor `1 ⊗ ⋯ ⊗ x ⊗ ⋯ ⊗ 1`, with `x` in place `i`, acts in a representation `ρ` of the
product of the groups `G j` as `x` does in the restriction of `ρ` to the factor `G i`. -/
lemma asAlgebraHom_piTensorElem_mulSingle (i : ι) (x : ℂ[G i]) :
    ρ.asAlgebraHom (piTensorElem (Pi.mulSingle i x)) =
      asAlgebraHom (ρ.comp (MonoidHom.mulSingle G i)) x := by
  classical
  -- Both sides are sums over a group; compare them along the inclusion of `G i` in the product.
  -- Every factor other than the one at `i` is a coefficient of `1`, so it is `1` or `0`.
  have h_coeff (s : ∀ j : ι, G j) : (piTensorElem (Pi.mulSingle i x)).coeff s =
      x.coeff (s i) * if ∀ j : ι, j ≠ i → s j = 1 then 1 else 0 := by
    simp +contextual [prod_congr rfl, Fintype.prod_eq_mul_prod_compl i, Pi.mulSingle, one_def,
      single_apply, prod_boole, eq_comm]
  rw [asAlgebraHom_eq_sum, asAlgebraHom_eq_sum,
    Fintype.sum_of_injective _ (Pi.mulSingle_injective i)]
  · -- an element outside the image is nontrivial at some index other than `i`
    intro s hs
    have h_ne : ¬ ∀ j : ι, j ≠ i → s j = 1 := fun h_one ↦
      hs ⟨s i, update_eq_iff.2 ⟨rfl, fun j hj ↦ (h_one j hj).symm⟩⟩
    simp [h_coeff, h_ne]
  · simp +contextual [h_coeff]

/-- If the factor `x i` kills the vector `v` in the restriction of `ρ` to `G i`, then the tensor
product of the `x j` kills `v` in `ρ`. -/
lemma piTensorElem_apply_eq_zero {v : V} (i : ι)
    (hv : asAlgebraHom (ρ.comp (MonoidHom.mulSingle G i)) (x i) v = 0) :
    ρ.asAlgebraHom (piTensorElem x) v = 0 := by
  -- split off the i-th component of x, which acts first and kills v
  have h_split : x = update x i 1 * Pi.mulSingle i (x i) := by
    rw [Pi.mulSingle, ← update_mul, one_mul, mul_one, update_eq_self]
  rw [h_split]
  simp [asAlgebraHom_piTensorElem_mulSingle, hv]

/-- Two tensor products multiply to zero as soon as their factors in one place `i` do. -/
lemma piTensorElem_mul_eq_zero {y : (i : ι) → ℂ[G i]} (i : ι) (h_mul : x i * y i = 0) :
    piTensorElem x * piTensorElem y = 0 := by
  ext s
  simpa [← map_mul] using
    prod_eq_zero (f := fun j ↦ (x j * y j).coeff (s j)) (mem_univ i) (by simp [h_mul])

namespace IsCentralProj

open scoped Classical in
lemma one_sub (h : IsCentralProj e) : IsCentralProj (1 - e) :=
  ⟨h.isIdempotentElem.one_sub, fun g x ↦ by
    simp [h.isClassFunction g x, eq_comm, one_def, single_apply]⟩

/-- Applying a ring endomorphism `σ` of `ℂ` to the coefficients of a central idempotent `e` of
`ℂ[H]` (`H` any group) gives a central idempotent. -/
lemma map (h : IsCentralProj e) (σ : ℂ →+* ℂ) : IsCentralProj (mapRingHom H σ e) :=
  ⟨h.isIdempotentElem.map (mapRingHom H σ), fun g x ↦ by simp [h.isClassFunction g x]⟩

lemma piTensorElem (h : ∀ i : ι, IsCentralProj (x i)) : IsCentralProj (New.piTensorElem x) := by
  have h_idem : IsIdempotentElem x := funext fun i ↦ (h i).isIdempotentElem
  exact ⟨h_idem.map New.piTensorElem, fun g s ↦ by simp [(h _).isClassFunction _ _]⟩

end IsCentralProj

end CentralProjections

/-!
## Irreducibility criteria and expansion of class functions

* `New.sum_mul_trace_block_eq_card_mul`, `New.classInner_eq_sum_of_eq_sum`: the trace computation
  behind the expansion of a class function in the block characters, and Parseval's identity.
* `New.IsChar.asAlgebraHom_groupAlgElem_eq_zero_iff`: `∑ g, conj (χ g) • g` acts as zero in `ρ` iff
  `χ` is orthogonal to the character of `ρ`. `New.IsChar.asAlgebraHom_groupAlgElem_eq_zero` is a
  sufficient condition for `∑ g, χ (i g * s) • g` to act as zero, `i` a group homomorphism.
-/

section IrreducibleCharacters

open MonoidAlgebra Finset LinearMap ComplexConjugate Matrix Algebra Representation

attribute [local instance low] Fintype.ofFinite

variable {G H V : Type*} [Group G] [Finite G] [Group H] {χ f : G → ℂ}
  [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V] {ρ : Representation ℂ G V}
  (Z : Type*) [CommSemiring Z] [Algebra Z ℂ]

section Blocks

variable {n : ℕ} {d : Fin n → ℕ} (e : ℂ[G] ≃ₐ[ℂ] ∀ i : Fin n, Matrix (Fin (d i)) (Fin (d i)) ℂ)

/-- If `e` identifies `ℂ[G]` with a product of matrix algebras, `G` acts on column vectors through
the `i`-th block. -/
def blockRepresentation (i : Fin n) : Representation ℂ G (Fin (d i) → ℂ) :=
  (lift ℂ _ G).symm (toLinAlgEquiv'.toAlgHom.comp ((Pi.evalAlgHom ℂ _ i).comp e.toAlgHom))

omit [Finite G] in
/-- Let `e` identify `ℂ[G]` with a product of matrix algebras of sizes `d i`. There is a character
`χ` of degree `d i`, that of the dual of the `i`-th block, such that the `i`-th block of each
`y : G` has trace `χ y⁻¹`. -/
lemma exists_isChar_trace_block (i : Fin n) :
    ∃ χ : G → ℂ, IsChar χ ∧ χ 1 = d i ∧ ∀ y : G, (e (single y 1) i).trace = χ y⁻¹ := by
  let V : FDRep ℂ G := .of (dual (blockRepresentation e i))
  have hρ (y : G) : blockRepresentation e i y = toLin' (e (single y 1) i) := rfl
  refine ⟨V.character, ⟨V, rfl⟩, by simp [V], fun y ↦ ?_⟩
  simp [← trace_toLin'_eq, ← hρ, V, FDRep.character]

/-- Let `e` identify `ℂ[G]` with a product of matrix algebras. For a class function `φ` the element
`∑ g, φ g • g` is central, so each of its blocks under `e` is a scalar matrix. -/
lemma IsClassFunction.exists_block_eq_algebraMap {φ : G → ℂ} (hφ : IsClassFunction φ) (i : Fin n) :
    ∃ c : ℂ, e (groupAlgElem φ) i = algebraMap ℂ (Matrix (Fin (d i)) (Fin (d i)) ℂ) c := by
  have h_comm (A : ∀ j, Matrix (Fin (d j)) (Fin (d j)) ℂ) : Commute A (e (groupAlgElem φ)) := by
    simpa using (IsClassFunction.commute (e := groupAlgElem φ) hφ (e.symm A)).map e
  have h_center : e (groupAlgElem φ) i ∈ Subalgebra.center ℂ (Matrix (Fin (d i)) (Fin (d i)) ℂ) :=
    Subalgebra.mem_center_iff.2 fun A ↦ by simpa using congrFun (h_comm (Pi.single i A)).eq i
  exact (IsCentral.mem_center_iff ℂ).1 h_center

/-- Let `e` identify `ℂ[G]` with a product of matrix algebras (the blocks). If the `i`-th block of
`∑ g, φ g • g` is the scalar `c` and `χ` is a character such that the `i`-th block of each `y` has
trace `χ y⁻¹`, then `∑ x, conj (χ x) * φ (x * y) = c * χ y`. -/
lemma IsChar.sum_conj_mul_eq_of_block {φ : G → ℂ} {i : Fin n} {c : ℂ} (hχ : IsChar χ)
    (h_trace : ∀ y : G, (e (single y 1) i).trace = χ y⁻¹)
    (hc : e (groupAlgElem φ) i = algebraMap ℂ (Matrix (Fin (d i)) (Fin (d i)) ℂ) c) (y : G) :
    ∑ x : G, conj (χ x) * φ (x * y) = c * χ y := by
  classical
  have h_repr : ∑ x : G, φ (x * y) • single x (1 : ℂ) = groupAlgElem φ * single y⁻¹ 1 := by
    ext x
    simp [Finsupp.single_apply]
  calc
    _ = (e (∑ x : G, φ (x * y) • single x (1 : ℂ)) i).trace := by
      simp [-MonoidAlgebra.smul_single, h_trace, hχ.apply_inv, mul_comm (φ _)]
    _ = c * χ y := by simp [h_repr, -MonoidAlgebra.smul_single, hc, h_trace, algebraMap_eq_smul_one]

/-- Let `e` identify `ℂ[G]` with a product of matrix algebras (the blocks) of sizes `d i`. If the
`i`-th block of `∑ g, φ g • g` is the scalar `c i` for each `i`, then `|G| * φ g` is the sum over
`i` of `c i * d i` times the trace of the `i`-th block of `g⁻¹`. -/
lemma sum_mul_trace_block_eq_card_mul {φ : G → ℂ} {c : Fin n → ℂ}
    (hc : ∀ i : Fin n,
      e (groupAlgElem φ) i = algebraMap ℂ (Matrix (Fin (d i)) (Fin (d i)) ℂ) (c i)) (g : G) :
    ∑ i : Fin n, c i * (d i * (e (single g⁻¹ 1) i).trace) = Nat.card G * φ g := by
  classical
  -- Both sides are the trace of the left multiplication `L`, computed in the basis `b` of matrix
  -- units and in the group basis.
  let L : ℂ[G] →ₗ[ℂ] ℂ[G] := mulLeft ℂ (groupAlgElem φ * single g⁻¹ 1)
  let b : Module.Basis (Σ i : Fin n, Fin (d i) × Fin (d i)) ℂ ℂ[G] :=
    (Pi.basis fun i ↦ stdBasis ℂ (Fin (d i)) (Fin (d i))).map e.symm.toLinearEquiv
  calc ∑ i : Fin n, c i * (d i * (e (single g⁻¹ 1) i).trace)
      = traceAux ℂ b L := by
        simp [L, b, hc, traceAux, Matrix.trace, stdBasis, toMatrix_apply, ← mul_sum,
          Fintype.sum_prod_type, Fintype.sum_sigma, ← single_eq_of_single_single,
          algebraMap_eq_smul_one]
    _ = traceAux ℂ (basis G ℂ) L := by rw [traceAux_eq ℂ b (basis G ℂ)]
    _ = Nat.card G * φ g := by simp [L, traceAux, Matrix.trace, toMatrix_apply, basis]

end Blocks

omit [Group G] in
/-- Parseval's identity: if `φ = ∑ i, ⟨χ i, φ⟩ • χ i` for the inner product `New.classInner`, then
`⟨φ, f⟩ = ∑ i, conj ⟨χ i, φ⟩ * ⟨χ i, f⟩`. -/
lemma classInner_eq_sum_of_eq_sum {ι : Type*} [Fintype ι] {χ : ι → G → ℂ} {φ : G → ℂ}
    (hφ : φ = ∑ i : ι, classInner (χ i) φ • χ i) (f : G → ℂ) :
    classInner φ f = ∑ i : ι, conj (classInner (χ i) φ) * classInner (χ i) f := by
  conv_lhs => rw [hφ, classInner]
  simp [sum_mul, finMean_sum, mul_assoc, finMean_const_mul, ← classInner.eq_1]

/-- Suppose `f = ∑ j, ⟨χ j, f⟩ • χ j` has norm `⟨f, f⟩ = 1` and `0 ≤ re (f 1)`. If the coefficient
`⟨χ i, f⟩` is a nonzero integer and `0 < re (χ i 1)`, then `f = χ i`. -/
lemma eq_of_eq_sum_of_classInner_eq_intCast {ι : Type*} [Fintype ι] {χ : ι → G → ℂ} {i : ι}
    {m : ℤ} (hf : f = ∑ j : ι, classInner (χ j) f • χ j) (h_norm : classInner f f = 1)
    (hf_one : 0 ≤ (f 1).re) (hχ_one : 0 < (χ i 1).re) (hm : classInner (χ i) f = m)
    (hm_ne : m ≠ 0) : f = χ i := by
  -- The squared norms of the coefficients add up to `1`, so all others vanish and `m = ±1`.
  have hm_sq : (1 : ℝ) ≤ ‖classInner (χ i) f‖ ^ 2 := by
    simpa [hm] using mod_cast Int.one_le_abs hm_ne
  have h_sum : ∑ j : ι, ‖classInner (χ j) f‖ ^ 2 = 1 := by
    apply Complex.ofReal_injective
    simpa [classInner_eq_sum_of_eq_sum hf f, Complex.conj_mul'] using h_norm
  have h_other (j : ι) (hj : j ≠ i) : classInner (χ j) f = 0 := by
    by_contra h_ne
    have h_lt : ‖classInner (χ i) f‖ ^ 2 < ∑ k : ι, ‖classInner (χ k) f‖ ^ 2 :=
      single_lt_sum (f := fun k ↦ ‖classInner (χ k) f‖ ^ 2) hj (mem_univ i) (mem_univ j)
        (by positivity) (by simp)
    linarith
  have hf_eq : f = (m : ℂ) • χ i := by
    simpa +contextual [sum_eq_single i, h_other, hm] using hf
  obtain rfl | hm_neg : m = 1 ∨ (m : ℝ) = -1 := by
    simpa +contextual [sum_eq_single i, h_other, hm] using h_sum
  · simpa using hf_eq
  · have h_re : (f 1).re = -(χ i 1).re := by simp [hf_eq, hm_neg]
    linarith

/-- A finite family `χ i` of characters of a finite group `G` in which every class function expands.
The brackets `⟨ , ⟩` denote the inner product `New.classInner`. -/
structure IsExpansionFamily {ι : Type*} [Fintype ι] (χ : ι → G → ℂ) : Prop where
  /-- Each `χ i` is a character. -/
  isChar (i : ι) : IsChar (χ i)
  /-- Each `χ i` has positive degree. -/
  re_apply_one_pos (i : ι) : 0 < (χ i 1).re
  /-- For a class function `φ`, `χ i 1 * ⟨χ i, φ (· * y)⟩ = ⟨χ i, φ⟩ * χ i y` for all `y`. -/
  mul_classInner_translate {φ : G → ℂ} (hφ : IsClassFunction φ) (i : ι) (y : G) :
    χ i 1 * classInner (χ i) (fun x : G ↦ φ (x * y)) = classInner (χ i) φ * χ i y
  /-- A class function `φ` is the sum of the `⟨χ i, φ⟩ • χ i`. -/
  eq_sum {φ : G → ℂ} (hφ : IsClassFunction φ) : φ = ∑ i : ι, classInner (χ i) φ • χ i

variable (G) in
/-- A finite group has a finite family of characters in which every class function expands. -/
lemma exists_isExpansionFamily : ∃ (n : ℕ) (χ : Fin n → G → ℂ), IsExpansionFamily χ := by
  classical
  -- Wedderburn: `e` identifies `ℂ[G]` with a product of matrix algebras; `χ i` is the character of
  -- the dual of the `i`-th block, of degree `d i`, and that block of `y` has trace `χ i y⁻¹`.
  -- A class function `φ` acts by a scalar `c φ i` on the `i`-th block.
  obtain ⟨n, d, hd, ⟨e⟩⟩ := IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed ℂ ℂ[G]
  choose χ hχ hχ_one hχ_trace using exists_isChar_trace_block e
  choose! c hc using fun φ (hφ : IsClassFunction φ) ↦ hφ.exists_block_eq_algebraMap e
  have h_translate (φ : G → ℂ) (hφ : IsClassFunction φ) (i : Fin n) (y : G) :
      classInner (χ i) (fun x ↦ φ (x * y)) = (Nat.card G : ℂ)⁻¹ * (c φ i * χ i y) := by
    rw [← (hχ i).sum_conj_mul_eq_of_block e (hχ_trace i) (hc φ hφ i) y, classInner, finMean,
      finsum_eq_sum_of_fintype, div_eq_inv_mul]
  have h_inner (φ : G → ℂ) (hφ : IsClassFunction φ) (i : Fin n) :
      classInner (χ i) φ = (Nat.card G : ℂ)⁻¹ * (c φ i * d i) := by
    simpa only [mul_one, hχ_one] using h_translate φ hφ i 1
  refine ⟨n, χ, hχ, fun i ↦ by simp [hχ_one, NeZero.pos], fun {φ} hφ i y ↦ ?_,
    fun {φ} hφ ↦ funext fun g ↦ ?_⟩
  · rw [h_translate φ hφ, h_inner φ hφ, hχ_one]
    ring
  · have h_trace : ∑ i : Fin n, c φ i * (d i * χ i g) = Nat.card G * φ g := by
      simpa only [hχ_trace, inv_inv] using sum_mul_trace_block_eq_card_mul e (hc φ hφ) g
    simp [h_inner φ hφ, mul_assoc, ← mul_sum, h_trace]

/-- Let `f` and `I` be class functions on a finite group `G` with `⟨I, f⟩ ≠ 0`, `⟨f, f⟩ = 1` and
`0 ≤ re (f 1)`, where `⟨ , ⟩` is the inner product `New.classInner`. Suppose `⟨χ, f⟩` is an integer
for every character `χ` with `⟨χ, I⟩ ≠ 0` and `χ 1 * ⟨χ, I (· * y)⟩ = ⟨χ, I⟩ * χ y` for all `y`.
Then `f` is an irreducible character. -/
lemma IsClassFunction.isIrreducibleChar_of_classInner_eq_intCast {I : G → ℂ}
    (hf : IsClassFunction f) (hI : IsClassFunction I) (h_inner_ne : classInner I f ≠ 0)
    (h_norm : classInner f f = 1) (h_re : 0 ≤ (f 1).re)
    (h_int : ∀ χ : G → ℂ, IsChar χ → classInner χ I ≠ 0 →
      (∀ y : G, χ 1 * classInner χ (fun x : G ↦ I (x * y)) = classInner χ I * χ y) →
      ∃ m : ℤ, classInner χ f = m) :
    IsIrreducibleChar f := by
  -- Expand in characters `χ i`. Some `χ i` is orthogonal to neither `I` nor `f`; its coefficient in
  -- `f` is a nonzero integer `m`, which forces `f = χ i`.
  obtain ⟨n, χ, hχ⟩ := exists_isExpansionFamily G
  rw [classInner_eq_sum_of_eq_sum (hχ.eq_sum hI)] at h_inner_ne
  obtain ⟨i, -, hi⟩ := exists_ne_zero_of_sum_ne_zero h_inner_ne
  obtain ⟨hI_ne, hf_ne⟩ : classInner (χ i) I ≠ 0 ∧ classInner (χ i) f ≠ 0 := by simpa using hi
  obtain ⟨m, hm⟩ := h_int (χ i) (hχ.isChar i) hI_ne (hχ.mul_classInner_translate hI i)
  obtain rfl : f = χ i := eq_of_eq_sum_of_classInner_eq_intCast (hχ.eq_sum hf) h_norm h_re
    (hχ.re_apply_one_pos i) hm (by simpa [hm] using hf_ne)
  exact ⟨hχ.isChar i, h_norm, fun φ hφ ↦ hχ.mul_classInner_translate hφ i⟩

variable {Z} in
/-- Let `f` be a class function on a finite group `G`. If the inner product of every character with
`f` comes from the semiring `Z`, then `f` is a `Z`-combination of characters. -/
lemma IsClassFunction.mem_virtualChars (hf : IsClassFunction f)
    (h_coeff : ∀ χ : G → ℂ, IsChar χ → ∃ m : Z, classInner χ f = algebraMap Z ℂ m) :
    f ∈ virtualChars Z G := by
  -- Every coefficient of the expansion of `f` in characters comes from `Z`.
  obtain ⟨n, χ, hχ⟩ := exists_isExpansionFamily G
  rw [hχ.eq_sum hf]
  refine sum_mem fun i _ ↦ ?_
  obtain ⟨m, hm⟩ := h_coeff (χ i) (hχ.isChar i)
  simpa [hm] using Subalgebra.smul_mem _ (hχ.isChar i).mem_virtualChars m

/-- Let `f` be a class function on a finite group `G`. Suppose `a ∈ ℂ[G]` acts as zero in every
finite-dimensional representation in which `New.groupAlgElem f = ∑ g, f g • g` acts as zero. Then
`a = u * New.groupAlgElem f * a` for some `u ∈ ℂ[G]`. -/
lemma IsClassFunction.exists_eq_mul_groupAlgElem_mul (hf : IsClassFunction f) (a : ℂ[G])
    (ha : ∀ V : FDRep ℂ G, asAlgebraHom V.ρ (groupAlgElem f) = 0 → asAlgebraHom V.ρ a = 0) :
    ∃ u : ℂ[G], a = u * groupAlgElem f * a := by
  -- Wedderburn: `e` identifies `ℂ[G]` with a product of matrix algebras, and the `i`-th block of
  -- `groupAlgElem f` is a scalar `c i`. Take for `u` the blockwise scalar `(c i)⁻¹`.
  obtain ⟨n, d, -, ⟨e⟩⟩ := IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed ℂ ℂ[G]
  choose c hc using hf.exists_block_eq_algebraMap e
  refine ⟨e.symm (c⁻¹ • 1), e.injective (funext fun i ↦ ?_)⟩
  by_cases hi : c i = 0
  · -- `groupAlgElem f` acts as zero on the `i`-th block, so `a` does too
    have ha_zero : e a i = 0 := by
      simpa [hc, hi, blockRepresentation, asAlgebraHom] using ha (.of (blockRepresentation e i))
    simp [ha_zero]
  · simp [hc, hi, algebraMap_eq_smul_one]

/-- Three criteria for a class function `f` on a finite group `G`, collected in one statement:
(a) `New.IsClassFunction.isIrreducibleChar_of_classInner_eq_intCast`, for `f` to be an irreducible
character; (b) `New.IsClassFunction.mem_virtualChars`, for `f` to be a `Z`-combination of
characters, `Z` a commutative semiring with `ℂ` a `Z`-algebra;
(c) `New.IsClassFunction.exists_eq_mul_groupAlgElem_mul`, for a left multiple of
`New.groupAlgElem f` to fix an element `a` of `ℂ[G]`. -/
lemma isIrreducibleChar_and_mem_virtualChars_and_exists_mul (hf_class : IsClassFunction f) :
    (∀ I : G → ℂ, IsClassFunction I → classInner I f ≠ 0 → classInner f f = 1 → 0 ≤ (f 1).re →
      (∀ χ : G → ℂ, IsChar χ → classInner χ I ≠ 0 →
        (∀ y : G, χ 1 * classInner χ (fun x : G ↦ I (x * y)) = classInner χ I * χ y) →
        ∃ m : ℤ, classInner χ f = m) →
      IsIrreducibleChar f) ∧
    ((∀ χ : G → ℂ, IsChar χ → ∃ m : Z, classInner χ f = algebraMap Z ℂ m) → f ∈ virtualChars Z G) ∧
    ∀ a : ℂ[G],
      (∀ V : FDRep ℂ G, asAlgebraHom V.ρ (groupAlgElem f) = 0 → asAlgebraHom V.ρ a = 0) →
      ∃ u : ℂ[G], a = u * groupAlgElem f * a :=
  ⟨fun _ ↦ hf_class.isIrreducibleChar_of_classInner_eq_intCast, hf_class.mem_virtualChars,
    hf_class.exists_eq_mul_groupAlgElem_mul⟩

/-- Let `i : G →* H` be a group homomorphism with `G` finite, `χ` a character of `H` and `s ∈ H`.
If the product of `χ ∘ i` with the character of a finite-dimensional representation `ρ` of `G` has
average zero, then `∑ g, χ (i g * s) • g` acts as zero in `ρ`. -/
lemma IsChar.asAlgebraHom_groupAlgElem_eq_zero {χ : H → ℂ} (hχ : IsChar χ) (i : G →* H) (s : H)
    (h_mean : finMean (χ ∘ i * ρ.character) = 0) :
    ρ.asAlgebraHom (groupAlgElem fun x : G ↦ χ (i x * s)) = 0 := by
  -- Let `τ` have character `χ`. The averaging projection of `(τ ∘ i) ⊗ ρ` has trace `0` by
  -- `h_mean`, so it vanishes.
  obtain ⟨τ, rfl⟩ := hχ
  have h_trace : trace ℂ (TensorProduct ℂ τ V) (tprod (τ.ρ.comp i) ρ).averageMap = 0 := by
    simpa [GroupAlgebra.average, trace_tensorProduct', FDRep.character, character, finMean,
      finsum_eq_sum_of_fintype] using h_mean
  have h_avg : (tprod (τ.ρ.comp i) ρ).averageMap = 0 :=
    (isProj_averageMap _).isIdempotentElem.eq_zero_of_trace_eq_zero h_trace
  -- Read this in `End τ ⊗ End V`, then apply `T : A ⊗ B ↦ trace (A * τ s) • B`.
  have h_tensor : ∑ u : G, τ.ρ (i u) ⊗ₜ[ℂ] ρ u = 0 := by
    apply (homTensorHomEquiv ℂ τ V τ V).injective
    simpa [GroupAlgebra.average] using h_avg
  let T : TensorProduct ℂ (τ →ₗ[ℂ] τ) (V →ₗ[ℂ] V) →ₗ[ℂ] V →ₗ[ℂ] V :=
    TensorProduct.lift (lsmul ℂ (V →ₗ[ℂ] V) ∘ₗ trace ℂ τ ∘ₗ mulRight ℂ (τ.ρ s))
  calc ρ.asAlgebraHom (groupAlgElem fun x : G ↦ τ.character (i x * s))
      = T (∑ u : G, τ.ρ (i u) ⊗ₜ[ℂ] ρ u) := by simp [T, FDRep.character, asAlgebraHom_eq_sum]
    _ = 0 := by rw [h_tensor, map_zero]

/-- For a character `χ` and finite-dimensional `ρ`, the element `∑ g, conj (χ g) • g` acts as zero
in `ρ` iff `χ` is orthogonal to the character of `ρ` for the inner product `New.classInner`. -/
lemma IsChar.asAlgebraHom_groupAlgElem_eq_zero_iff (h : IsChar χ) :
    ρ.asAlgebraHom (groupAlgElem (conj ∘ χ)) = 0 ↔ classInner χ ρ.character = 0 := by
  refine ⟨fun h_zero ↦ ?_, fun h_zero ↦ ?_⟩
  · simpa [classInner, finMean, finsum_eq_sum_of_fintype, character, asAlgebraHom_eq_sum]
      using congrArg (trace ℂ V) h_zero
  · -- `IsChar.asAlgebraHom_groupAlgElem_eq_zero` for the character `conj χ`, with `i` the identity
    -- and `s = 1`
    simpa [asAlgebraHom_eq_sum] using h.star.asAlgebraHom_groupAlgElem_eq_zero (i := .id G) (s := 1)
      h_zero

end IrreducibleCharacters

end New

/-! ## Integrality of central projections -/

section ProjectionCharacter

open MonoidAlgebra LinearMap Representation Finset

attribute [local instance low] Fintype.ofFinite

variable {G : Type*} [Group G] [Finite G] {e : ℂ[G]}

/-- If `e` is a central idempotent of the complex group algebra of a finite group `G`, then
`g ↦ |G| · e(g)`, with `e(g)` the coefficient of `g`, is the character of a finite-dimensional
representation of `G`. -/
lemma New.IsCentralProj.isChar_card_mul_coeff (h : IsCentralProj e) :
    IsChar fun g : G ↦ Nat.card G * e.coeff g := by
  -- The pairing of |G|·e with a character χ is the trace of e on a representation with character
  -- conj χ. As e acts there by an idempotent, this trace is a natural number, the rank.
  have h_class : IsClassFunction fun g ↦ Nat.card G * e.coeff g := by simp [h.isClassFunction _ _]
  -- A class function whose pairing with every character is in `ℕ` is an `ℕ`-combination of
  -- characters, hence a character.
  suffices h_nat : ∀ χ : G → ℂ, IsChar χ →
      ∃ m : ℕ, classInner χ (fun g ↦ Nat.card G * e.coeff g) = algebraMap ℕ ℂ m from
    isChar_of_mem_virtualChars (h_class.mem_virtualChars h_nat)
  intro χ hχ
  obtain ⟨ρ, hρ⟩ : ∃ ρ : FDRep ℂ G, ρ.character = fun g ↦ starRingEnd ℂ (χ g) := hχ.star
  have h_trace :
      classInner χ (fun g ↦ Nat.card G * e.coeff g) = trace ℂ ρ (asAlgebraHom ρ.ρ e) := by
    simp [classInner, finMean, finsum_eq_sum_of_fintype, ← congrFun hρ, asAlgebraHom_eq_sum,
      FDRep.character, sum_div, mul_rotate']
  use Module.finrank ℂ (range (asAlgebraHom ρ.ρ e))
  rw [h_trace, (h.isIdempotentElem.map _).isProj_range.trace, eq_natCast]

/-- If `e` is a central idempotent of the complex group algebra of a finite group `G`, then
`g ↦ |G| · e(g)`, with `e(g)` the coefficient of `g`, is the character of a representation of `G` of
dimension at most `|G|`. -/
lemma New.IsCentralProj.exists_character_eq_and_finrank_le_card (h : IsCentralProj e) :
    ∃ V : FDRep ℂ G,
      V.character = (fun g : G ↦ Nat.card G * e.coeff g) ∧
      Module.finrank ℂ V ≤ Nat.card G := by
  -- As `1 - e` is again a central idempotent, it gives a second representation. The two
  -- dimensions, the values of the characters at the identity, add up to `|G|`.
  obtain ⟨V, hV⟩ : IsChar fun g : G ↦ Nat.card G * e.coeff g := h.isChar_card_mul_coeff
  obtain ⟨W, hW⟩ : IsChar fun g : G ↦ Nat.card G * (1 - e).coeff g :=
    h.one_sub.isChar_card_mul_coeff
  have h_sum : (Module.finrank ℂ V + Module.finrank ℂ W : ℂ) = Nat.card G :=
    calc
      _ = V.character 1 + W.character 1 := by rw [FDRep.char_one, FDRep.char_one]
      _ = Nat.card G * (e.coeff 1 + (1 - e).coeff 1) := by rw [hV, hW, mul_add]
      _ = Nat.card G := by simp
  exact ⟨V, hV, Nat.le.intro (mod_cast h_sum)⟩

/-- The coefficients of a central idempotent of `ℂ[G]` have norm at most `1`. -/
lemma New.IsCentralProj.norm_coeff_le_one (h : IsCentralProj e) (g : G) : ‖e.coeff g‖ ≤ 1 := by
  obtain ⟨V, hV, h_dim⟩ := h.exists_character_eq_and_finrank_le_card
  refine le_of_mul_le_mul_left (a := (Nat.card G : ℝ)) ?_ (Nat.cast_pos.2 Nat.card_pos)
  calc (Nat.card G : ℝ) * ‖e.coeff g‖ = ‖V.character g‖ := by simp [hV]
    _ ≤ ‖V.character 1‖ := IsChar.norm_apply_le ⟨V, rfl⟩ g
    _ ≤ Nat.card G * 1 := by simpa [FDRep.char_one] using h_dim

end ProjectionCharacter

/-! ## Central projections as orthogonal projections -/

section CentralConvolution

open LinearMap LinearIsometryEquiv

namespace New.IsCentralProj

variable {G : Type*} [Group G] [Fintype G] {e : MonoidAlgebra ℂ G}

/-- Let `ρ` be a representation of a finite group `G` on a complex vector space `V` and `σ` a field
automorphism of `ℂ`. Let `B` be a `G`-invariant form on `V`, linear in the second argument and
semilinear for `σ⁻¹ ∘ conj ∘ σ` in the first. Then a central idempotent `e` of `ℂ[G]` is
self-adjoint for `B`: `B (e x) y = B x (e y)`. -/
lemma self_adjoint {V : Type*} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (he : IsCentralProj e) (σ : ℂ ≃+* ℂ)
    (B : V →ₛₗ[(↑σ⁻¹ : ℂ →+* ℂ).comp ((starRingEnd ℂ).comp (σ : ℂ →+* ℂ))] V →ₗ[ℂ] ℂ)
    (hB : ∀ (s : G) (x y : V), B (ρ s x) (ρ s y) = B x y) (x y : V) :
    B (ρ.asAlgebraHom e x) y = B x (ρ.asAlgebraHom e y) := by
  -- The coefficients of `σ e` are a character divided by `|G|`, so inversion conjugates them.
  -- Expand both sides over `G` and match the term of `s` with the term of `s⁻¹`.
  have h_coeff (s : G) : σ (e.coeff s⁻¹) = starRingEnd ℂ (σ (e.coeff s)) := by
    simpa using (he.map σ).isChar_card_mul_coeff.apply_inv s
  have h_adj (s : G) : B (ρ s x) y = B x (ρ s⁻¹ y) := by simp [← hB s x]
  have h_term (s : G) : B ((e.coeff s • ρ s) x) y = B x ((e.coeff s⁻¹ • ρ s⁻¹) y) := by
    simp [h_adj, ← h_coeff]
  simp only [asAlgebraHom_eq_sum, LinearMap.sum_apply, map_sum]
  exact Fintype.sum_equiv (.inv G) _ _ h_term

/-- Convolution with a central idempotent e of ℂ[G], along a homomorphism φ : G → H of finite
groups, is a contraction of ℓ²(H, V): ∑_s ‖∑_t e(t) f(φ(t)⁻¹ s)‖² ≤ ∑_s ‖f(s)‖². -/
lemma sum_norm_sq_conv_le {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (he : IsCentralProj e) {H : Type*} [Group H] [Fintype H] (φ : G →* H) (f : H → V) :
    ∑ s : H, ‖∑ t : G, e.coeff t • f ((φ t)⁻¹ * s)‖ ^ 2 ≤ ∑ s : H, ‖f s‖ ^ 2 := by
  -- `G` acts on `ℓ²(H, V)` by left translation through `φ`, unitarily; so `e` acts as an orthogonal
  -- projection, which does not increase the norm.
  let L (t : G) : PiLp 2 (fun _ : H ↦ V) ≃ₗᵢ[ℂ] PiLp 2 fun _ : H ↦ V :=
    piLpCongrLeft 2 ℂ V (.mulLeft (φ t))
  let ρ : Representation ℂ G (PiLp 2 fun _ : H ↦ V) :=
    { toFun t := (L t).toLinearEquiv.toLinearMap
      map_one' := by
        ext f s
        change f ((φ 1)⁻¹ * s) = f s
        simp
      map_mul' t u := by
        ext f s
        change f ((φ (t * u))⁻¹ * s) = f ((φ u)⁻¹ * ((φ t)⁻¹ * s))
        simp [mul_assoc] }
  -- for `σ = 1` the map `σ⁻¹ ∘ conj ∘ σ` of `self_adjoint` is `conj` by definition
  have h_symm : (ρ.asAlgebraHom e).IsSymmetric :=
    he.self_adjoint ρ 1 (innerₛₗ ℂ) fun t ↦ (L t).inner_map_map
  obtain ⟨K, _, hK : ρ.asAlgebraHom e = K.starProjection⟩ :=
    isSymmetricProjection_iff_eq_coe_starProjection.1 ⟨he.isIdempotentElem.map _, h_symm⟩
  have h_norm : ‖ρ.asAlgebraHom e (.toLp 2 f)‖ ≤ ‖WithLp.toLp 2 f‖ := by
    simpa [hK] using K.norm_starProjection_apply_le _
  -- write both norms in coordinates and square
  simpa (disch := positivity) [ρ, L, PiLp.norm_eq_of_L2, asAlgebraHom_eq_sum] using h_norm

end New.IsCentralProj

end CentralConvolution

end
