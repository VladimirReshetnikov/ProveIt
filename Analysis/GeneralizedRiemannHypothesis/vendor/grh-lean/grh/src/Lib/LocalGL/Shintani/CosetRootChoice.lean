import Lib.GaloisRep.Hilbert90.TameActions
import Lib.LocalGL.Green.HallAlgebra

/-!
# Root choices in a coset, induction, and extension of invariant characters

This file treats descent of class functions along a coset, as in Shintani descent. Given
`π : E →* Γ`, `σ ∈ Γ` and `j : G → E`, it defines root choices over `σ`. It defines the induction
`New.induceClassFn` of class functions and proves Frobenius reciprocity for it. It proves that
descent keeps inner products and commutes with induction. It also proves the following for a
`Γ`-invariant irreducible character `Y` of `G` and a virtual character `Φ` of `G ⋊ Γ` with
|Γ|⟨Φ,Φ⟩ = ⟨Φ|G,Φ|G⟩+|Γ|−1 and ⟨Y,Φ|G⟩ = 1+|Γ|m for some m ∈ ℤ. Under these conditions, the
function equal to `Y` on `G` and to `Φ` off `G` is an irreducible character of `G ⋊ Γ`
(`New.IsIrreducibleChar.extend_semidirect`). Here `New.classInner` is the mean of `conj f * h`,
and `New.virtualChars` is the span of the characters.

## Main definitions and results

* `New.DescendsOnCoset`: the function `h` on `E` descends to `f` on `G` over the coset of `σ`:
  `h s = f γ` for every `s : E` with `π s = σ` and every `γ : G` with `s ^ orderOf σ = j γ`.
* `New.IsRootChoice`, `New.exists_isRootChoice`: a conjugation-equivariant choice, for each `γ`, of
  a root `r γ` over `σ` with `r γ ^ orderOf σ = j γ`, and its existence for the units of an algebra
  over a finite field with a semilinear Galois action.
* `New.IsRootChoice.exists_conj_eq_of_map_eq`, `New.IsRootChoice.index_mul_finMean_eq_classInner`:
  the roots meet every class over `σ`, and descent keeps inner products.
* `New.IsRootChoice.descendsOnCoset_comp`: a function `g` invariant under the kernel of `π` descends
  to `g ∘ r`.
* `New.classInner_induceClassFn_of_surjective`: Frobenius reciprocity for `New.induceClassFn` when
  `π ∘ ρ` is onto.
* `New.DescendsOnCoset.induce`: descent commutes with induction.

Notions from other files:
* `New.IsIrreducibleChar`: `f` is an irreducible character, stated as three conditions: (a) `f` is a
  character, (b) `New.classInner f f = 1`, and (c) for every class function `h` and every `y`, `f 1
  * New.classInner f (h (· * y)) = New.classInner f h * f y`.

## Relation to the literature

Known; see `Lib.LocalGL.Shintani.LiftingGreenCharacters` and `Lib.LocalGL.Green.CuspidalFunctions`
for sources.
-/

namespace New

section CosetRoots

open Finset Function Subgroup ComplexConjugate SemidirectProduct AddMonoidAlgebra
  ZMod

attribute [local instance low] Fintype.ofFinite

variable {E E' Γ G G' : Type*} [Group E] [Group E'] [Group Γ] [Group G] [Group G'] [Finite E]
  [Finite E'] [Finite G] [Finite G'] (π : E →* Γ) (σ : Γ)

/-- The function `h` on `E` descends to `f` on `G` over the coset of `σ`: `h s = f γ` for every
`s : E` with `π s = σ` and every `γ : G` with `s ^ orderOf σ = j γ`. -/
def DescendsOnCoset (j : G → E) (h : E → ℂ) (f : G → ℂ) : Prop :=
  ∀ (s : E) (γ : G), π s = σ → s ^ orderOf σ = j γ → h s = f γ

open scoped Classical in
/-- The number of x in the kernel of π with xtx⁻¹ = s, as a complex number. -/
noncomputable def conjCount (s t : E) : ℂ :=
  ∑ x : E, if π x = 1 ∧ x * t * x⁻¹ = s then (1 : ℂ) else 0

/-- Induction of f along ρ over Γ: at s, the index of ker(π∘ρ) times the mean over t ∈ E' of
f(t)·#{x ∈ ker π : xρ(t)x⁻¹ = s}. -/
noncomputable def induceClassFn (ρ : E' →* E) (f : E' → ℂ) (s : E) : ℂ :=
  (π.comp ρ).ker.index * classInner (conjCount π s ∘ ρ) f

/-- j is injective and r(γ) is a conjugation-equivariant (ord σ)-th root of j(γ) over σ, such
that any x ∈ ker π conjugating one r(δ) to an r(γ) lies in j(G). -/
@[local grind]
structure IsRootChoice (j : G →* E) (r : G → E) where
  /-- The homomorphism `j` is injective. -/
  injective : Injective j
  /-- `r γ` lies over `σ`. -/
  map_apply (γ : G) : π (r γ) = σ
  /-- The power of `r γ` by the order of `σ` is `j γ`. -/
  pow_orderOf (γ : G) : r γ ^ orderOf σ = j γ
  /-- The choice of roots is equivariant for conjugation by `G`. -/
  map_conj (v γ : G) : r (v * γ * v⁻¹) = j v * r γ * (j v)⁻¹
  /-- An element of the kernel of `π` that conjugates a chosen root to a chosen root lies in the
  image of `j`. -/
  mem_range_of_conj (x : E) (γ δ : G) : π x = 1 → x * r δ * x⁻¹ = r γ → x ∈ j.range

variable {π σ} {j : G →* E} {r : G → E} {ρ : E' →* E} {h : E' → ℂ} {g : E → ℂ} {α : Γ →* MulAut G}
  {Y : G → ℂ}

/-! ### Induction of class functions -/

/-- Conjugating `s` by `y` and `t` by `u`, where `u` and `y` have the same image under `π`, does not
change the number of elements of the kernel of `π` that conjugate `t` to `s`. -/
lemma conjCount_conj {u y : E} (h_eq : π u = π y) (s t : E) :
    conjCount π (y * s * y⁻¹) (u * t * u⁻¹) = conjCount π s t := by
  classical
  -- The substitution `x ↦ y * x * u⁻¹` preserves the kernel of `π` and matches the conjugators.
  refine (sum_equiv (.mulLeft y * .mulRight u⁻¹) (by simp) fun x _ ↦ ?_).symm
  have h_ker : π (y * (x * u⁻¹)) = 1 ↔ π x = 1 := by simp [h_eq, ← mul_assoc]
  -- both sides are the same conjugation equation, moved by `y`
  have h_conj : y * (x * u⁻¹) * (u * t * u⁻¹) * (y * (x * u⁻¹))⁻¹ = y * s * y⁻¹ ↔
      x * t * x⁻¹ = s := by
    rw [show y * (x * u⁻¹) * (u * t * u⁻¹) * (y * (x * u⁻¹))⁻¹ = y * (x * t * x⁻¹) * y⁻¹ by group]
    simp
  simp only [Equiv.Perm.coe_mul, comp_apply, Equiv.coe_mulLeft, Equiv.coe_mulRight, h_ker, h_conj]

/-- Frobenius reciprocity for `induceClassFn`: let `ρ : E' →* E` with `π ∘ ρ` onto `Γ`, `h` a
function on `E'`, and `χ` a class function on `E`. Then the inner product of `χ` with the induction
of `h` equals the inner product of `χ ∘ ρ` with `h`. Here `induceClassFn π ρ h` at `s` is the index
of ker(π∘ρ) times the mean over t ∈ E' of h(t)·#{x ∈ ker π : xρ(t)x⁻¹ = s}. -/
lemma classInner_induceClassFn_of_surjective [Finite Γ] (h_surj : Surjective (π.comp ρ)) {χ : E → ℂ}
    (hχ : IsClassFunction χ) : classInner χ (induceClassFn π ρ h) = classInner (χ ∘ ρ) h := by
  classical
  -- The sum over `s` of `conj (χ s) * conjCount π s t` is `#π.ker * conj (χ t)`, and both `π.ker`
  -- and `(π.comp ρ).ker` have index `#Γ`, so the factors `#Γ * #π.ker = #E` cancel.
  have h_index : (π.comp ρ).ker.index = π.ker.index := by
    rw [index_ker, index_ker, MonoidHom.range_eq_top.mpr h_surj,
      MonoidHom.range_eq_top.mpr (h_surj.of_comp (f := π))]
  have h_count_sum (t : E) :
      ∑ s : E, conj (χ s) * conjCount π s t = Nat.card π.ker * conj (χ t) := by
    -- exchange the sums; the conjugate `x * t * x⁻¹` has the same value of `χ` as `t`
    simp only [conjCount, mul_sum, mul_ite, mul_one, mul_zero]
    rw [sum_comm]
    simp [ite_and, hχ, ← sum_filter, Fintype.card_subtype]
  have h_conj_count (s t : E) : conj (conjCount π s t) = conjCount π s t := by
    simp [conjCount]
  simp only [classInner, finMean, induceClassFn, h_index, h_conj_count, comp_apply,
    finsum_eq_sum_of_fintype, mul_sum, sum_div]
  rw [sum_comm]
  refine sum_congr rfl fun t _ ↦ ?_
  calc ∑ s : E, conj (χ s) * ((π.ker.index : ℂ) * (conjCount π s (ρ t) * h t / Nat.card E')) /
        Nat.card E
      = (∑ s : E, conj (χ s) * conjCount π s (ρ t)) *
          ((π.ker.index : ℂ) * h t / (Nat.card E' * Nat.card E)) := by
        rw [sum_mul]
        exact sum_congr rfl fun s _ ↦ by ring
    _ = conj (χ (ρ t)) * h t / Nat.card E' := by
        rw [h_count_sum, ← π.ker.index_mul_card, Nat.cast_mul]
        have h_ker_ne : (Nat.card π.ker : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
        field_simp [index_ne_zero_of_finite]

/-- Let `π ∘ ρ` be onto. If `h` is a `Z`-linear combination of characters of `E'`, then so is its
induction `induceClassFn π ρ h` to `E`. -/
lemma induceClassFn_mem_virtualChars [Finite Γ] {Z : Type*} [CommSemiring Z] [Algebra Z ℂ]
    (h_surj : Surjective (π.comp ρ)) (h_virtual : h ∈ virtualChars Z E') :
    induceClassFn π ρ h ∈ virtualChars Z E := by
  classical
  -- `induceClassFn π ρ h` is a class function: conjugation by `y` is matched by conjugation by an
  -- element `u` of `E'` with the same image in `Γ`.
  have h_class (s y : E) : induceClassFn π ρ h (y * s * y⁻¹) = induceClassFn π ρ h s := by
    obtain ⟨u, hu⟩ : ∃ u : E', π (ρ u) = π y := h_surj (π y)
    have h_term (t : E') :
        conj (conjCount π (y * s * y⁻¹) (ρ (MulAut.conj u t))) * h (MulAut.conj u t) =
          conj (conjCount π s (ρ t)) * h t := by
      simp [conjCount_conj hu, isClassFunction_of_mem_virtualChars h_virtual]
    unfold induceClassFn classInner
    congr 1
    exact finMean_equiv (MulAut.conj u) h_term
  -- a class function whose pairings with all characters come from `Z` is a `Z`-combination of them
  obtain ⟨-, h_mem_of_pairings, -⟩ := isIrreducibleChar_and_mem_virtualChars_and_exists_mul Z
    h_class
  refine h_mem_of_pairings fun (χ : E → ℂ) (hχ : IsChar χ) ↦ ?_
  -- Frobenius reciprocity moves the pairing to `E'`, where `h` is a `Z`-combination of characters
  rw [classInner_induceClassFn_of_surjective h_surj hχ.isClassFunction]
  exact (hχ.comp ρ).exists_classInner_eq h_virtual

/-! ### Semidirect products: existence of roots, extension of characters -/

/-- Let `S` be an algebra over the finite field `k'`, let `σ ∈ Gal(k'/k)` act on `Sˣ` through a
`σ`-semilinear ring endomorphism `τ`, and let `j` embed the finite group `G` onto the units fixed by
`σ`. Then there is `r : G → Sˣ ⋊ Gal(k'/k)` such that (a) `r` is a root choice: each `r γ` lies over
`σ`, is an `(ord σ)`-th root of `j γ` and is compatible with conjugation, and any unit conjugating
some `r δ` to some `r γ` lies in `j(G)`; and (b) the unit part of `r γ` lies in every
`k'`-subalgebra that contains `j γ`. -/
theorem exists_isRootChoice {k k' S : Type*} [Field k] [Field k'] [Algebra k k'] [Ring S]
    [Finite k'] [Algebra k' S] {β : Gal(k'/k) →* MulAut Sˣ} {σ : Gal(k'/k)} (τ : S →+* S)
    (hβ : ∀ u : Sˣ, β σ u = τ u) (hτ : Semiconj (algebraMap k' S) σ τ) {j : G →* Sˣ}
    (hj : Injective j) (h_range : ∀ u : Sˣ, u ∈ j.range ↔ β σ u = u) :
    ∃ r : G → Sˣ ⋊[β] Gal(k'/k),
      -- (a)
      IsRootChoice rightHom σ (inl.comp j) r ∧
      -- (b)
      ∀ (B : Subalgebra k' S) (γ : G), ↑(j γ) ∈ B → ↑(r γ).left ∈ B := by
  -- Let R = k'[C], with C cyclic of order |G| and σ acting on the coefficients. A generator of C
  -- is the norm of a unit z of R. Evaluate the generator at j γ and put r γ = (z(γ), σ).
  let C : Type := ZMod (Nat.card G)
  let s : k'[C] →+* k'[C] := (mapAlgAut k C σ).toRingHom
  -- the evaluation map R → S that sends the generator to j γ; it turns σ on R into τ on S
  let ev (γ : G) : k'[C] →ₐ[k'] S := lift k' S C
    ⟨⟨fun c : Multiplicative C ↦ j (γ ^ c.toAdd.val), by simp⟩, by simp [C, val_add, pow_add]⟩
  have h_fix (γ : G) : β σ (j γ) = j γ := (h_range (j γ)).mp ⟨γ, rfl⟩
  have h_ev (γ : G) (z : k'[C]) : τ (ev γ z) = ev γ (s z) := by
    induction z using induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | single c x => simp [ev, s, Algebra.smul_def, ← hβ, h_fix, hτ.eq]
  have h_tame : IsTameAtLevel s (orderOf σ) (algebraMap k' k'[C] 1) := by
    refine (isTameAtLevel_gal σ).of_semiconj (algebraMap k' k'[C]) (by simp [s, Semiconj]) ?_
    -- `mapAlgAut_apply` is left out: it turns `s` into `mapAlgEquiv k C σ`, whose power simp
    -- does not evaluate
    ext <;> simp [s, ← AlgEquiv.coe_pow, ← map_pow, -mapAlgAut_apply]
  -- `IsTameAtLevel.exists_prod_range_pow_apply_eq`: a σ-fixed unit of the finite ring R is the norm
  -- of a unit
  obtain ⟨z, -, -, hz_norm⟩ := h_tame.exists_prod_range_pow_apply_eq
    (.inl (Module.finite_of_finite k'))
    ((of k' C).toHomUnits (.ofAdd 1)).isUnit (by simp [s]) (one_dvd _)
  -- (u, σ)^m = (u σ(u) ⋯ σ^(m-1)(u), σ^m); for m the order of σ the product is the norm
  have h_pow (γ : G) (m : ℕ) : (⟨z.map ↑(ev γ), σ⟩ : Sˣ ⋊[β] Gal(k'/k)) ^ m =
      ⟨.map (ev γ) (∏ i ∈ range m, z.map (s ^ i).toMonoidHom), σ ^ m⟩ := by
    induction m with
    | zero => ext <;> simp
    | succ m ih =>
      rw [pow_succ', ih]
      ext
      · simp [pow_succ', prod_range_succ', mul_comm, hβ, h_ev, -map_pow, left_inr]
      · simp [pow_succ', -map_pow, right_inr, AlgEquiv.coe_pow]
  have h_root (γ : G) : (⟨z.map ↑(ev γ), σ⟩ : Sˣ ⋊[β] Gal(k'/k)) ^ orderOf σ = inl (j γ) := by
    rw [h_pow]
    -- `map_pow` is left out: the power must stay inside `j` for `γ ^ (1 % |G|) = γ` to reduce
    ext <;> simp_all [ev, val_one_eq_one_mod, -map_pow]
  -- z(γ) is a polynomial in j γ, so it follows conjugation
  have h_conj {γ : G} (δ : G) (u : Sˣ) (h_eq : j γ = u * j δ * u⁻¹) :
      z.map ↑(ev γ) = u * z.map ↑(ev δ) * u⁻¹ := by
    simp [Units.ext_iff, ev, lift_apply, Finsupp.sum, h_eq, u.conj_pow, mul_sum, sum_mul]
  refine ⟨fun γ ↦ ⟨z.map ↑(ev γ), σ⟩,
    ⟨inl_injective.comp hj, fun γ ↦ rfl, h_root, fun v γ ↦ ?_, ?_⟩, fun B γ hγ ↦ ?_⟩
  · ext <;> simp [(h_range _).1, h_conj γ (j v)]
  · -- if u conjugates r δ to r γ, it conjugates j δ to j γ (take powers) and so z(δ) to z(γ);
    -- comparing with u z(δ) σ(u)⁻¹ = z(γ) gives σ(u) = u
    rintro ⟨u, _⟩ γ δ rfl h_conj_root
    have h_j : j γ = u * j δ * u⁻¹ := by
      -- `mk_eq_inl_mul_inr` is left out: it splits `r γ` into `inl _ * inr σ`, and the power of
      -- that product is not reduced
      simpa [h_root, -mk_eq_inl_mul_inr] using
        congrArg (fun x ↦ (x ^ orderOf σ).left) h_conj_root.symm
    have h_fixed : β σ u = u := by
      simpa [h_conj δ u h_j] using congrArg SemidirectProduct.left h_conj_root
    obtain ⟨a, ha⟩ : ∃ a : G, j a = u := (h_range u).mpr h_fixed
    exact ⟨a, congrArg inl ha⟩
  · simp [ev, lift_apply, Finsupp.sum, sum_mem, B.smul_mem, pow_mem hγ]

variable [Finite Γ] in
/-- A semidirect product of finite groups is finite. -/
instance : Finite (G ⋊[α] Γ) := .of_equiv _ equivProd.symm

omit [Finite G] in
private lemma equivProd_symm_mk_one (g : G) : (equivProd.symm (g, 1) : G ⋊[α] Γ) = inl g := rfl

open scoped Classical in
/-- On a semidirect product `G ⋊ Γ`, take the function equal to `u` on `G` and to `w` off `G`. Its
mean is the mean of `w` plus the difference of the means of `u` and `w` over `G`, divided by
`|Γ|`. -/
@[simp]
lemma finMean_ite [Finite Γ] (u w : G ⋊[α] Γ → ℂ) :
    finMean (fun x : G ⋊[α] Γ ↦ if x.right = 1 then u x else w x) =
      finMean w +
        (finMean (fun g : G ↦ u (inl g)) - finMean (fun g : G ↦ w (inl g))) / Nat.card Γ := by
  -- The difference of the two sums is carried by the copy of G, and |G ⋊ Γ| = |G| |Γ|. The mean
  -- over `G ⋊ Γ` is moved to `G × Γ` (`↓`) before `finMean` is unfolded.
  simp [↓finMean_equiv equivProd.symm, finMean, ite_sub, ← sub_eq_iff_eq_add', ← sum_sub_distrib,
    field, finsum_eq_sum_of_fintype, Fintype.sum_prod_type, equivProd_symm_mk_one]

open scoped Classical in
/-- Let Y be a Γ-invariant irreducible character of G, Φ a virtual character of G⋊Γ with
|Γ|⟨Φ,Φ⟩ = ⟨Φ|G,Φ|G⟩+|Γ|−1 and ⟨Y,Φ|G⟩ = 1+|Γ|m, m ∈ ℤ. Then the function equal to Y on G
and Φ off G is an irreducible character of G⋊Γ. -/
lemma IsIrreducibleChar.extend_semidirect [Finite Γ] (hY : IsIrreducibleChar Y)
    (h_stable : ∀ (σ : Γ) (g : G), Y (α σ g) = Y g)
    {Φ : G ⋊[α] Γ → ℂ} (hΦ : Φ ∈ virtualChars ℤ (G ⋊[α] Γ))
    (h_self : Nat.card Γ * classInner Φ Φ = classInner (Φ ∘ inl) (Φ ∘ inl) + (Nat.card Γ - 1))
    (m : ℤ) (h_pair : classInner Y (Φ ∘ inl) = 1 + Nat.card Γ * m) :
    IsIrreducibleChar fun x : G ⋊[α] Γ ↦ if x.right = 1 then Y x.left else Φ x := by
  -- Apply the first part of `isIrreducibleChar_and_mem_virtualChars_and_exists_mul` to the function
  -- f of the statement, with the test function I equal to Y on G and to 0 off G. It asks that f and
  -- I be class functions, ⟨I, f⟩ ≠ 0, ⟨f, f⟩ = 1, 0 ≤ re f(1), and ⟨χ, f⟩ ∈ ℤ for every character χ
  -- with ⟨χ, I⟩ ≠ 0 and χ(1) ⟨χ, I(· y)⟩ = ⟨χ, I⟩ χ(y). Means over G ⋊ Γ are split by the simp
  -- lemma `finMean_ite`.
  obtain ⟨hY_char, hY_norm, hY_conv⟩ := hY
  have hf_class : IsClassFunction fun x : G ⋊[α] Γ ↦ if x.right = 1 then Y x.left else Φ x := by
    simp +contextual [hY_char.isClassFunction, isClassFunction_of_mem_virtualChars hΦ, h_stable]
  have hI_class : IsClassFunction fun x : G ⋊[α] Γ ↦ if x.right = 1 then Y x.left else 0 := by
    simp +contextual [hY_char.isClassFunction, h_stable]
  obtain ⟨h_irr_of_test, -, -⟩ := isIrreducibleChar_and_mem_virtualChars_and_exists_mul ℤ hf_class
  have h_card_ne : (Nat.card Γ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  refine h_irr_of_test _ hI_class ?_ ?_ ?_ fun χ hχ h_ne h_conv ↦ ?_
  · -- the pairing with I is ⟨Y, Y⟩ / |Γ|
    simp_all +contextual [classInner]
  · -- norm one: by `finMean_ite`, ⟨f, f⟩ = ⟨Φ, Φ⟩ + (⟨Y, Y⟩ - ⟨Φ|G, Φ|G⟩) / |Γ|; then `h_self`
    have h_split : classInner (fun x : G ⋊[α] Γ ↦ if x.right = 1 then Y x.left else Φ x)
          (fun x : G ⋊[α] Γ ↦ if x.right = 1 then Y x.left else Φ x) =
        classInner Φ Φ + (classInner Y Y - classInner (Φ ∘ inl) (Φ ∘ inl)) / Nat.card Γ := by
      simp +contextual [classInner]
    rw [h_split, hY_norm]
    field_simp
    linear_combination h_self
  · -- the value at 1 is `Y 1`, the dimension of a representation
    obtain ⟨V, hV⟩ := hY_char
    simp [← hV]
  -- χ meets I, so its restriction to G is a multiple of Y: compare the two convolution identities
  have h_res (g : G) : χ (inl g) = χ 1 / Y 1 * Y g := by
    -- the identity `hY_conv` for χ|G at g⁻¹, translated by g and conjugated
    have h_convY : conj (Y 1 * finMean fun t ↦ conj (Y (t * g)) * χ (inl (t * g * g⁻¹))) =
        conj (classInner Y (χ ∘ inl) * Y g⁻¹) := by
      rw [← hY_conv _ (hχ.comp inl).isClassFunction]
      congr 2
      exact (finMean_equiv (.mulRight g) (by simp)).symm
    have h_conv_g : χ 1 * (finMean fun t : G ↦ conj (χ (inl t)) * Y (t * g)) =
        (finMean fun t : G ↦ conj (χ (inl t)) * Y t) * χ (inl g) := by
      simpa [← finMean_conj, ← hY_char.apply_inv, field, classInner] using h_conv (inl g)
    have h_convY_g : Y 1 * (finMean fun t : G ↦ conj (χ (inl t)) * Y (t * g)) =
        (finMean fun t : G ↦ conj (χ (inl t)) * Y t) * Y g := by
      simp only [mul_comm (conj (χ _))]
      simpa [← finMean_conj, ← hY_char.apply_inv, field, classInner] using h_convY
    have h_pair_ne : (finMean fun t : G ↦ conj (χ (inl t)) * Y t) ≠ 0 := by
      simpa [← finMean_conj, ← hY_char.apply_inv, field, classInner] using h_ne
    have hY_one_ne : Y 1 ≠ 0 := fun h_zero ↦ by
      -- otherwise `hY_conv` for `Y` itself gives `Y = 0`, against `⟨Y, Y⟩ = 1`
      have hY_zero (t : G) : Y t = 0 := by
        simpa [h_zero, hY_norm] using (hY_conv Y hY_char.isClassFunction t).symm
      simp [classInner, hY_zero, finMean_eq] at hY_norm
    -- the two identities share the left mean: eliminate it and cancel the pairing
    field_simp
    refine mul_left_cancel₀ h_pair_ne ?_
    linear_combination χ 1 * h_convY_g - Y 1 * h_conv_g
  -- with N = ⟨χ|G, Y⟩ and M = ⟨χ, Φ⟩, the pairing is M + N (1 - ⟨Y, Φ|G⟩) / |Γ| = M - N m
  obtain ⟨N, hN⟩ : ∃ N : ℤ, classInner (χ ∘ inl) Y = algebraMap ℤ ℂ N :=
    (hχ.comp inl).exists_classInner_eq hY_char.mem_virtualChars
  obtain ⟨M, hM⟩ : ∃ M : ℤ, classInner χ Φ = algebraMap ℤ ℂ M := hχ.exists_classInner_eq hΦ
  refine ⟨M - N * m, ?_⟩
  -- by `finMean_ite`, ⟨χ, f⟩ = ⟨χ, Φ⟩ + (⟨χ|G, Y⟩ - ⟨χ|G, Φ|G⟩) / |Γ|
  have h_split : classInner χ (fun x : G ⋊[α] Γ ↦ if x.right = 1 then Y x.left else Φ x) =
      classInner χ Φ + (classInner (χ ∘ inl) Y - classInner (χ ∘ inl) (Φ ∘ inl)) / Nat.card Γ := by
    simp +contextual [classInner]
  -- on `G`, `χ` is `χ 1 / Y 1` times `Y`, so pairings with `χ|G` are `conj (χ 1 / Y 1)` times those
  -- with `Y`
  have h_scale (ψ : G → ℂ) : classInner (χ ∘ inl) ψ = conj (χ 1 / Y 1) * classInner Y ψ := by
    simp only [classInner, comp_apply, h_res, map_mul, mul_assoc, finMean_const_mul]
  have hN_eq : conj (χ 1 / Y 1) = N := by simpa [h_scale, hY_norm] using hN
  rw [h_split, hM, h_scale, h_scale, hY_norm, h_pair, hN_eq, eq_intCast]
  field_simp
  push_cast
  ring

omit [Finite E] [Finite G] in
lemma IsRootChoice.apply_emb_eq_one (R : IsRootChoice π σ j r) (γ : G) : π (j γ) = 1 := by
  rw [← R.pow_orderOf γ, map_pow, R.map_apply, pow_orderOf_eq_one]

/-- For a choice of roots `r`, the image of `j` in the kernel of `π`. -/
private abbrev IsRootChoice.rangeInKer (R : IsRootChoice π σ j r) : Subgroup π.ker :=
  (j.codRestrict π.ker R.apply_emb_eq_one).range

/-- For a choice of roots `r`, the map `(x, γ) ↦ x r(γ) x⁻¹` from `(ker π ⧸ j(G)) × G` to the coset
of `σ`, with `x` the chosen representative of its class. -/
private noncomputable def IsRootChoice.conjRoot (R : IsRootChoice π σ j r)
    (z : (π.ker ⧸ R.rangeInKer) × G) : π ⁻¹' {σ} :=
  ⟨(z.fst.out : E) * r z.snd * (z.fst.out : E)⁻¹, by
    simp [π.mem_ker.mp z.fst.out.property, R.map_apply]⟩

omit [Finite E] [Finite G] in
/-- For a choice of roots, the coset of `σ` has as many elements as the kernel of `π`. -/
private lemma IsRootChoice.card_preimage_eq (R : IsRootChoice π σ j r) :
    Nat.card (π ⁻¹' {σ}) = Nat.card π.ker := by
  rw [← R.map_apply 1]
  exact Nat.card_congr (π.fiberEquivKer _)

/-- For a choice of roots, `IsRootChoice.conjRoot` is a bijection onto the coset of `σ`: it is
injective by `IsRootChoice.mem_range_of_conj`, and both sides have `|ker π|` elements. -/
private lemma IsRootChoice.bijective_conjRoot (R : IsRootChoice π σ j r) :
    Bijective R.conjRoot := by
  have h_ker (x : π.ker) : π x = 1 := π.mem_ker.mp x.property
  have h_inj : Injective R.conjRoot := by
    rintro ⟨y, δ⟩ ⟨x, γ⟩ hc
    have h_val : (R.conjRoot (x, γ) : E) = R.conjRoot (y, δ) := congrArg Subtype.val hc.symm
    have h_conj : (y.out⁻¹ * x.out : π.ker) * r γ * ((y.out⁻¹ * x.out : π.ker) : E)⁻¹ = r δ := by
      simpa [IsRootChoice.conjRoot, mul_assoc] using
        congrArg (fun t : E ↦ (y.out : E)⁻¹ * t * y.out) h_val
    obtain ⟨a, ha⟩ : ∃ a : G, j a = (y.out⁻¹ * x.out : π.ker) :=
      R.mem_range_of_conj (y.out⁻¹ * x.out : π.ker) δ γ (h_ker _) h_conj
    have h_coset : y.out⁻¹ * x.out ∈ R.rangeInKer := ⟨a, Subtype.ext ha⟩
    obtain rfl : y = x := y.out_equiv_out.mp (QuotientGroup.leftRel_apply.mpr h_coset)
    -- equal roots have equal powers `j δ = j γ`, and `j` is injective
    have h_root : r δ = r γ := by simpa [IsRootChoice.conjRoot] using hc
    have h_j_eq : j δ = j γ := by rw [← R.pow_orderOf δ, ← R.pow_orderOf γ, h_root]
    rw [R.injective h_j_eq]
  have h_card_le : Nat.card (π ⁻¹' {σ}) ≤ Nat.card ((π.ker ⧸ R.rangeInKer) × G) := by
    rw [R.card_preimage_eq, ← R.rangeInKer.index_mul_card, Nat.card_prod]
    exact mul_le_mul_right (Finite.card_range_le _) _
  exact h_inj.bijective_of_nat_card_le h_card_le

/-- For a choice of roots `r`, every element `s` of `E` over `σ` is conjugate to some `r γ` by an
element of the kernel of `π`. -/
lemma IsRootChoice.exists_conj_eq_of_map_eq (R : IsRootChoice π σ j r) {s : E}
    (hs : π s = σ) : ∃ (x : E) (γ : G), π x = 1 ∧ x * r γ * x⁻¹ = s := by
  obtain ⟨⟨x, γ⟩, hc⟩ := R.bijective_conjRoot.surjective ⟨s, hs⟩
  exact ⟨x.out, γ, π.mem_ker.mp x.out.property, congrArg Subtype.val hc⟩

open scoped Classical in
/-- For a choice of roots `r`, let `h` and `g` descend on the coset of `σ` to `f` and `f'` and be
invariant under conjugation by the kernel of `π`. Then the index of the kernel times the mean of
`conj h * g` over `E`, taken as zero off the coset of `σ`, is the inner product of `f` and `f'`. -/
lemma IsRootChoice.index_mul_finMean_eq_classInner [Finite Γ]
    (R : IsRootChoice π σ j r) {h g : E → ℂ}
    {f f' : G → ℂ} (hh : DescendsOnCoset π σ j h f) (hg : DescendsOnCoset π σ j g f')
    (hh_conj : ∀ s x : E, π x = 1 → h (x * s * x⁻¹) = h s)
    (hg_conj : ∀ s x : E, π x = 1 → g (x * s * x⁻¹) = g s) :
    π.ker.index * finMean (fun s : E ↦ if π s = σ then conj (h s) * g s else 0) =
      classInner f f' := by
  -- Reindex the sum over the coset by `IsRootChoice.conjRoot`; the terms do not depend on `x`.
  have h_ker (x : π.ker) : π x = 1 := π.mem_ker.mp x.property
  -- `erw`: the sum over the coset carries another `Fintype` instance than `Bijective.sum_comp`
  erw [classInner, finMean, finMean_eq, finsum_eq_sum_of_fintype, ← sum_filter,
    sum_subtype _ mem_filter_univ, ← R.bijective_conjRoot.sum_comp, ← π.ker.index_mul_card,
    ← R.card_preimage_eq, ← Nat.card_eq_of_bijective _ R.bijective_conjRoot]
  have h_index : (π.ker.index : ℂ) ≠ 0 := mod_cast index_ne_zero_of_finite
  simp [IsRootChoice.conjRoot, h_ker, hh_conj, hg_conj, field, Fintype.sum_prod_type, mul_sum]
  -- the values at r(γ) are those of f and f'
  grind [DescendsOnCoset]

omit [Finite E] [Finite G] in
/-- A choice of roots restricts to a subgroup `H` of `E` and its preimage `H₀` in `G`, if the
roots of the elements of `H₀` lie in `H`. -/
lemma IsRootChoice.restrict_subgroup (R : IsRootChoice π σ j r) (H : Subgroup E) {H₀ : Subgroup G}
    (h_comap : comap j H = H₀) (h_mem : ∀ γ ∈ H₀, r γ ∈ H) :
    IsRootChoice (G := H₀) (π.comp H.subtype) σ (j.restrict h_comap.ge)
      fun γ : H₀ ↦ ⟨r γ, h_mem γ γ.property⟩ := by
  refine ⟨?_, fun γ ↦ R.map_apply γ, fun γ ↦ Subtype.ext (R.pow_orderOf γ),
    fun v γ ↦ Subtype.ext (R.map_conj v γ), fun u γ δ hu h_conj ↦ ?_⟩
  · exact fun a b h_eq ↦ Subtype.ext (R.injective (congrArg Subtype.val h_eq))
  -- An element `u` of `H ⊓ π.ker` that conjugates two roots is `j a`, and `a ∈ H₀` as `j a ∈ H`.
  obtain ⟨a, ha⟩ : ∃ a : G, j a = u := R.mem_range_of_conj u γ δ hu (congrArg Subtype.val h_conj)
  exact ⟨⟨a, h_comap.le (by simp [mem_comap, ha])⟩, Subtype.ext ha⟩

/-- Given a choice of roots `r`, a function `g` on `E` that is invariant under conjugation by the
kernel of `π` descends on the coset over `σ` to `g ∘ r`. -/
lemma IsRootChoice.descendsOnCoset_comp (R : IsRootChoice π σ j r)
    (h_inv : ∀ s x : E, π x = 1 → g (x * s * x⁻¹) = g s) :
    DescendsOnCoset π σ j g (g ∘ r) := by
  intro s γ hs h_pow
  -- Restrict the roots to the centraliser of `j γ`, which holds `s` as `s ^ orderOf σ = j γ`.
  have h_root : ∀ δ ∈ (centralizer {j γ}).comap j, r δ ∈ centralizer {j γ} := by
    simp_all [← map_mul, R.injective.eq_iff, ← R.map_conj, ← mul_inv_eq_iff_eq_mul,
      mem_centralizer_iff]
  have h_mem : s ∈ centralizer {j γ} := by simp [← h_pow, pow_mul_comm', mem_centralizer_iff]
  -- There `s` is conjugate to a root `r δ` by some `x` in the kernel of `π`. The power `orderOf σ`
  -- gives `x * j δ * x⁻¹ = j γ`, and `x` commutes with `j γ`, so `δ = γ`.
  obtain ⟨⟨x, hx⟩, δ, h_ker, h_s⟩ :=
    (R.restrict_subgroup (centralizer {j γ}) rfl h_root).exists_conj_eq_of_map_eq
      (s := ⟨s, h_mem⟩) hs
  have h_s_eq : x * r δ * x⁻¹ = s := congrArg Subtype.val h_s
  have h_conj_pow : x * j δ * x⁻¹ = j γ := by
    calc x * j δ * x⁻¹ = (x * r δ * x⁻¹) ^ orderOf σ := by rw [conj_pow, R.pow_orderOf δ]
      _ = j γ := by rw [h_s_eq, h_pow]
  have h_comm : j γ * x = x * j γ := mem_centralizer_iff.mp hx (j γ) rfl
  have h_j_eq : j δ = j γ := mul_left_cancel <| by rwa [← h_comm, ← mul_inv_eq_iff_eq_mul]
  show g s = g (r γ)
  rw [← h_s_eq, h_inv (r δ) x h_ker, R.injective h_j_eq]

omit [Finite G] in
/-- For a choice of roots `r`, the number of elements of the kernel of `π` that conjugate `r δ` to
`r γ` is the number of `v : G` with `δ = v⁻¹ * γ * v`. -/
private lemma IsRootChoice.conjCount_root (R : IsRootChoice π σ j r) [Fintype G] [DecidableEq G]
    (γ δ : G) :
    conjCount π (r γ) (r δ) = ∑ v : G, if δ = (MulAut.conj v)⁻¹ • γ then 1 else 0 := by
  classical
  have h_r_inj : Injective r :=
    fun a b h_eq ↦ R.injective (by rw [← R.pow_orderOf a, ← R.pow_orderOf b, h_eq])
  -- only the elements of `j G` contribute, by `IsRootChoice.mem_range_of_conj`
  refine (Fintype.sum_of_injective j R.injective _ _ ?_ ?_).symm
  · grind [j.mem_range]
  · -- `↓`: `eq_inv_smul_iff` must act before the action is unfolded to `v⁻¹ * γ * v`
    simp [R.apply_emb_eq_one, ← R.map_conj, ↓eq_inv_smul_iff, h_r_inj.eq_iff]

/-- Descent commutes with induction. Let `ρ₀ : G' → G` be compatible with `ρ : E' →* E`, with
choices of roots on both sides. If the class function `h` descends to `f`, and the class function
`F` is induced from `f` along `ρ₀` in the sense of Frobenius reciprocity (`hF`), then
`induceClassFn π ρ h` (the index of ker(π∘ρ) times the mean over t of h(t)·#{x ∈ ker π :
xρ(t)x⁻¹ = s}) descends to `F`. -/
lemma DescendsOnCoset.induce [Finite Γ]
    (R : IsRootChoice π σ j r) (h_class : IsClassFunction h) (ρ₀ : G' → G)
    {j' : G' →* E'} (h_comm : ∀ γ : G', ρ (j' γ) = j (ρ₀ γ)) {f : G' → ℂ} {r' : G' → E'}
    (R' : IsRootChoice (π.comp ρ) σ j' r') (h_lift : DescendsOnCoset (π.comp ρ) σ j' h f)
    {F : G → ℂ} (hF_class : IsClassFunction F)
    (hF : ∀ χ : G → ℂ, IsClassFunction χ → classInner F χ = classInner f (χ ∘ ρ₀)) :
    DescendsOnCoset π σ j (induceClassFn π ρ h) F := by
  classical
  -- By `IsRootChoice.index_mul_finMean_eq_classInner` for the roots r', the value of the induced
  -- function at s is the pairing on G' of the count `δ ↦ conjCount π s (r δ)`, pulled back by ρ₀,
  -- with f. By `hF` this is the conjugate of the pairing of F with that count on G, which is F γ.
  intro s γ hs hγ
  have h_conj_snd (t x : E) (hx : π x = 1) :
      conjCount π s (x * t * x⁻¹) = conjCount π s t := by
    simpa using conjCount_conj (hx.trans π.map_one.symm) s t
  have h_conj_fst (t t' x : E) (hx : π x = 1) :
      conjCount π (x * t' * x⁻¹) t = conjCount π t' t := by
    simpa using conjCount_conj (hx.trans π.map_one.symm).symm t' t
  -- the count vanishes off the coset of σ
  have h_coset : (fun t ↦ conj (conjCount π s (ρ t)) * h t) =
      fun t ↦ if π.comp ρ t = σ then conj (conjCount π s (ρ t)) * h t else 0 := by
    simp +contextual [funext_iff, conjCount, ne_of_apply_ne π, hs]
  have h_lifts :
      DescendsOnCoset (π.comp ρ) σ j' (conjCount π s ∘ ρ) ((conjCount π s ∘ r) ∘ ρ₀) := by
    intro t δ ht hδ
    have h_pow_eq : ρ t ^ orderOf σ = j (ρ₀ δ) := by rw [← map_pow, hδ, h_comm]
    exact R.descendsOnCoset_comp h_conj_snd (ρ t) (ρ₀ δ) ht h_pow_eq
  have h_induce : induceClassFn π ρ h s = classInner ((conjCount π s ∘ r) ∘ ρ₀) f := by
    change ((π.comp ρ).ker.index : ℂ) * finMean (fun t ↦ conj (conjCount π s (ρ t)) * h t) = _
    rw [h_coset]
    exact R'.index_mul_finMean_eq_classInner h_lifts h_lift
      (fun t x hx ↦ by simpa using h_conj_snd (ρ t) (ρ x) hx) fun t x _ ↦ h_class t x
  have h_count (δ : G) :
      conjCount π s (r δ) = ∑ v : G, if δ = (MulAut.conj v)⁻¹ • γ then 1 else 0 := by
    -- `s` may be replaced by the root `r γ`
    have h_at_root : conjCount π s (r δ) = conjCount π (r γ) (r δ) :=
      R.descendsOnCoset_comp (g := fun t ↦ conjCount π t (r δ)) (h_conj_fst _) s γ hs hγ
    rw [h_at_root, R.conjCount_root γ δ]
  have h_count_class : IsClassFunction (conjCount π s ∘ r) := by grind [R.apply_emb_eq_one]
  -- the count is real, so swapping the two sides of a pairing with it conjugates the pairing
  have h_count_real (t : E) : conj (conjCount π s t) = conjCount π s t := by
    simp [conjCount]
  -- `F` is a class function, so the mean over `δ` of the count at `r δ` times `F δ` is `F γ`
  have h_mean_count : classInner (conjCount π s ∘ r) F = F γ := by
    -- each `v` contributes `F (v⁻¹ * γ * v) = F γ`
    have h_sum : ∑ δ : G, conj (conjCount π s (r δ)) * F δ = Nat.card G * F γ := by
      -- `sum_boole` is left out so that the count stays a sum over `v` and the sums can be swapped;
      -- `inv_inv` is left out so that `hF_class` matches `v⁻¹ * γ * v⁻¹⁻¹`
      simp [h_count, apply_ite conj, -sum_boole, sum_comm (γ := G), ← map_inv,
        hF_class, -inv_inv, sum_mul]
    simp [classInner, finMean_eq, h_sum, ← Nat.card_eq_fintype_card, Nat.card_pos.ne']
  calc induceClassFn π ρ h s
      = classInner ((conjCount π s ∘ r) ∘ ρ₀) f := h_induce
    _ = conj (classInner f ((conjCount π s ∘ r) ∘ ρ₀)) := by
        simp [classInner, ← finMean_conj, h_count_real, mul_comm]
    _ = conj (classInner F (conjCount π s ∘ r)) := by rw [hF _ h_count_class]
    _ = classInner (conjCount π s ∘ r) F := by
        simp [classInner, ← finMean_conj, h_count_real, mul_comm]
    _ = F γ := h_mean_count

end CosetRoots

end New
