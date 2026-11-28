import Lib.Cyclotomic.OddSha
import Lib.GaloisRep.TaylorWiles
import New.Congruences.FirstOrder.KummerMaps

/-!
# Taylor–Wiles places in a triangle for the even classes, with prescribed Frobenii

Auxiliary (Taylor–Wiles) places that cut down the even classes of the Tate twists, with Frobenius
data in a prescribed set.

The places are indexed by an exponent e > 0 and a test point, and are chosen one after another. Step
1 finds a new Kummer map (`New.Selmer.IsKummerMap`) and an element that the earlier maps kill and at
which the value of the new map is a given product. Step 2 gets from Chebotarev's theorem a place
whose Frobenius element has twice these values under the maps, and at which even classes take twice
their value at the test point. Step 3 applies the reciprocity law of each Kummer map at its own
place and the later ones.

Throughout, ℓ is a prime, Ω is the algebraic closure of ℚ, and E is a CM field embedded in Ω that
contains a primitive 5040-th root of unity (`New.CMFieldWithRoot5040`); F is its maximal real
subfield, and `New.Selmer.primeBelowPlus` w is the prime of F below a prime w of E.
`New.cyclotomicChar` (written cyc) is the ℓ-adic cyclotomic character; G_ν is the kernel of its
reduction `New.cyclotomicCharMod` modulo ℓ^ν, and `New.conjGal` is the conjugation of Galois
elements by complex conjugation. The letter γ denotes a Galois element that separates the exponents;
in `New.Selmer.exists_isPrimeTriangle` it generates the Galois group modulo the kernel of cyc, and
the triangle is stated for γ⁻¹.

* `New.Selmer.exists_isPrimeTriangle`: for each ν > 0 there are Taylor–Wiles places of level ℓ^ν,
  indexed by one finite ordered set, that satisfy `New.Selmer.IsPrimeTriangle` and have their
  Frobenius data in a prescribed set.

Notions from other files:
* `New.CoeffRing`: The coefficient rings: rings of integers of the finite Galois extensions of ℚ_ℓ
  inside its algebraic closure.
* `New.Selmer.evenClasses`: The even classes: cocycles c in (O/ℓ^ν)(−e), O a coefficient ring,
  unramified off ℓ and a given set of places with their conjugates, with c(`conjGal` g) = c(g), that
  vanish on the elements of trivial cyc in the decomposition groups above ℓ.
* `New.Selmer.IsNuSplitPlace`: A condition on Frobenius data (w, A, σ), which consist of w of prime
  norm, A a place of Ω above w and σ a geometric Frobenius at A: w is not above ℓ, σ fixes μ_{ℓ^ν}.
* `New.Selmer.HasKummerType`: A continuous map to ℤ/ℓ^ν, an odd homomorphism on G_ν, that
  conjugation by a multiplies by cyc(a)^(e + 1); Kummer maps of exponent e have it.
* `New.Selmer.IsKummerMap`: A Kummer map of exponent e for a finite family x of split places, off a
  finite set T of primes of F: the restriction to Gal(Ω/E) of a relation over F. It has the Kummer
  type of exponent e and is unramified off T. For a finite family w of split places above distinct
  primes of F outside T it satisfies a reciprocity law: a linear relation among the values of a
  cocycle over F at the tame generators of w, with the values of the map at the Frobenius elements
  of w as coefficients. The cocycle must satisfy local conditions at the primes above ℓ and below
  the places of x.
* `New.Selmer.IsPrimeTriangle`: Ordered places whose tame generators and Frobenius elements cut down
  the even classes one after another, up to given powers of ℓ.
* `New.mostFrobenii`: The filter of most Frobenii. A set X of data (w, A, σ) belongs to it if each
  nonempty open set of Galois elements has a nonempty open part U such that, for almost all w, X
  contains every datum with σ ∈ U.
* `New.mostFrobeniiAt`: The filter of most Frobenii near g: the same filter, refined by the
  condition that σ lies near g.

## Relation to the literature

Taylor–Wiles primes, equally many at every ℓ-power level, are chosen in triangular form by means of
a count over the real subfield, which gives reciprocity laws for even classes in Tate twists. Each
new Frobenius kills the earlier Kummer maps but not the new one, and their reciprocity laws remove
the even classes. No bound for the even classes is needed; for small ℓ congruences between the
twists cost a power of ℓ for each prime. Tame ramification governed by Frobenius in the Kummer field
of units and the inductive choice of primes at every level are known. Related work: Gras–Munnier,
Extensions cycliques T-totalement ramifiées, 1998; Hajir–Maire–Ramakrishna, Tame Z/pZ-extensions
with prescribed ramification, 2022; Taylor–Wiles, Ring-theoretic properties of certain Hecke
algebras, 1995; Darmon–Diamond–Taylor, Fermat's Last Theorem (2.19), 1995; Dotto–Thorne, Residually
reducible representations of rank 2, 2026.
-/

open New Patching Function Finset Fintype Filter PadicInt WellFoundedLT OddPart

/-- Let `u` be a unit of `ℤ_ℓ` such that every `u ^ a - 1` with `0 < a < t` divides `ℓ ^ h`, and
let `t + 2 ≤ y`. If `n` divides `ℓ ^ (3 * h)`, then `n` times the product of the `u ^ a - u ^ k`
over the `k < t` other than a given `a < t` divides `ℓ ^ (y * h)`. -/
lemma New.Selmer.mul_prod_pow_sub_pow_dvd {ℓ : ℕ} [ThePrime ℓ] {t y h : ℕ} {u : ℤ_[ℓ]ˣ}
    (hy : t + 2 ≤ y) (hu : ∀ a ∈ Set.Ioo 0 t, (u ^ a).val - 1 ∣ ℓ ^ h) (a : Fin t) {n : ℤ_[ℓ]}
    (hn : n ∣ ℓ ^ (3 * h)) :
    n * ∏ k ∈ {a}ᶜ, ((u ^ a.val).val - (u ^ k.val).val) ∣ ℓ ^ (y * h) := by
  have h_lt (b k : Fin t) (hkb : k < b) : (u ^ b.val).val - (u ^ k.val).val ∣ ℓ ^ h := by
    have h_eq : (u ^ b.val).val - (u ^ k.val).val =
        ((u ^ (b.val - k.val)).val - 1) * (u ^ k.val).val := by
      rw [sub_one_mul, ← Units.val_mul, ← pow_add, Nat.sub_add_cancel hkb.le]
    rw [h_eq, Units.mul_right_dvd]
    exact hu _ ⟨Nat.sub_pos_of_lt hkb, by omega⟩
  have h_ne (k : Fin t) (hk : k ∈ ({a}ᶜ : Finset (Fin t))) :
      (u ^ a.val).val - (u ^ k.val).val ∣ ℓ ^ h := by
    rcases (show k ≠ a by simpa using hk).lt_or_gt with hlt | hgt
    · exact h_lt a k hlt
    · simpa using (h_lt k a hgt).neg_left
  calc
    n * ∏ k ∈ {a}ᶜ, ((u ^ a.val).val - (u ^ k.val).val) ∣
      ℓ ^ (3 * h) * ∏ _k ∈ ({a}ᶜ : Finset (Fin t)), (ℓ ^ h : ℤ_[ℓ]) :=
      mul_dvd_mul hn (prod_dvd_prod_of_dvd _ _ h_ne)
    _ = ℓ ^ ((3 + (t - 1)) * h) := by simp [card_compl, pow_add, add_mul, pow_mul']
    _ ∣ ℓ ^ (y * h) := pow_dvd_pow _ (Nat.mul_le_mul_right h (by grind [a.isLt]))

/-- A family of vectors, none of which lies in the span of the earlier ones, is linearly
independent. -/
lemma New.Selmer.linearIndependent_of_notMem_span_Iio {F V J : Type} [Field F] [AddCommGroup V]
    [Module F V] [LinearOrder J] {v : J → V}
    (hv : ∀ j : J, v j ∉ Submodule.span F (v '' Set.Iio j)) : LinearIndependent F v := by
  refine linearIndependent_iff_finset_linearIndependent.2 fun s ↦ (?_ : LinearIndepOn F v s)
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert j s h_lt ih =>
    rw [coe_insert]
    exact ih.insert fun h ↦ hv j (Submodule.span_mono (Set.image_mono h_lt) h)

/-- Let `ν > 0`, and let the maps `ψ i` from a group to `ℤ/ℓ^ν` send products to sums. If their
reductions modulo `ℓ` are linearly independent, then together they take every family of values (by
Nakayama's lemma). -/
lemma New.Selmer.surjective_of_linearIndependent_cast {ℓ ν : ℕ} [Fact ℓ.Prime] (hν : 0 < ν)
    {A ι : Type} [Group A] [Fintype ι] {ψ : ι → A → ZMod (ℓ ^ ν)}
    (h_mul : ∀ (i : ι) (a b : A), ψ i (a * b) = ψ i a + ψ i b)
    (h_indep : LinearIndependent (ZMod ℓ) fun (i : ι) (a : A) ↦ ((ψ i a).cast : ZMod ℓ)) :
    Surjective fun (a : A) (i : ι) ↦ ψ i a := by
  -- The image spans modulo `ℓ`, so by Nakayama's lemma it is everything.
  let red : ZMod (ℓ ^ ν) →+* ZMod ℓ := ZMod.castHom (dvd_pow_self ℓ hν.ne') (ZMod ℓ)
  let Ψ : Additive A →+ ι → ZMod (ℓ ^ ν) :=
    .mk' (fun a i ↦ ψ i a.toMul) fun a b ↦ funext fun i ↦ h_mul i _ _
  let Ψ₁ : Additive A →+ ι → ZMod ℓ := (red.toAddMonoidHom.compLeft ι).comp Ψ
  have h_span : (⊤ : Submodule (ZMod ℓ) (ι → ZMod ℓ)) ≤ Ψ₁.range.toZModSubmodule ℓ := by
    rw [← span_flip_eq_top_iff_linearIndependent.2 h_indep, Submodule.span_le]
    exact fun _ ⟨a, ha⟩ ↦ ⟨.ofMul a, ha⟩
  -- So the image and the multiples of `ℓ` generate everything.
  let N : Submodule (ZMod (ℓ ^ ν)) (ι → ZMod (ℓ ^ ν)) := Ψ.range.toZModSubmodule (ℓ ^ ν)
  let 𝔪 : Ideal (ZMod (ℓ ^ ν)) := .span {(ℓ : ZMod (ℓ ^ ν))}
  have h_sup : ⊤ ≤ N ⊔ 𝔪 • ⊤ := fun v _ ↦ by
    obtain ⟨a, ha⟩ : ∃ a, Ψ₁ a = fun i ↦ red (v i) := h_span Submodule.mem_top
    have h_dvd (i : ι) : (ℓ : ZMod (ℓ ^ ν)) ∣ v i - Ψ a i := by
      simpa using map_dvd (Int.castRingHom (ZMod (ℓ ^ ν)))
        ((ZMod.natCast_eq_natCast_iff (Ψ a i).val (v i).val ℓ).1
          (by simpa [Ψ₁, red] using congrFun ha i)).dvd
    choose t ht using h_dvd
    rw [show v = Ψ a + (ℓ : ZMod (ℓ ^ ν)) • t from funext fun i ↦ by simp [← ht i]]
    exact Submodule.add_mem_sup ⟨a, rfl⟩
      (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top)
  have h_jacobson : 𝔪 ≤ Ideal.jacobson ⊥ :=
    (Ideal.span_singleton_le_iff_mem _).2
      (Ideal.radical_le_jacobson ⟨ν, (Nat.cast_pow ℓ ν).symm.trans (ZMod.natCast_self _)⟩)
  intro v
  obtain ⟨a, ha⟩ : v ∈ N := Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top
    h_jacobson h_sup Submodule.mem_top
  exact ⟨a.toMul, ha⟩

/-- Let `ℓ` be a prime, `Ω` the algebraic closure of `ℚ`, and `E ⊆ Ω` a CM field with a primitive
`5040`-th root of unity and at least four infinite places. Let `ν > 0`, and let `G_ν ≤ Gal(Ω/E)` be
the subgroup that fixes the `ℓ ^ ν`-th roots of unity. Let `x` be a finite family of split places
above distinct primes of the real subfield `F`, and let `v i : G_ν → ℤ/ℓ` be any maps with the same
indices. Then for some finite set `T` of primes of `F` that contains `familyPrimes ℓ x` (the primes
above `ℓ` or below the `x i`), some Kummer map `ψ` of exponent `e` for `x` off `T` has its reduction
`G_ν → ℤ/ℓ` outside the span of the `v i`. -/
lemma New.Selmer.exists_isKummerMap_notMem_span {ℓ : ℕ} {E : Type} [ThePrime ℓ] [Field E]
    [CMFieldWithRoot5040 E] {ν : ℕ} (hν : 0 < ν) (e : ℕ) (h_inf_places : 4 ≤ Core.numInfPlaces E)
    {I : Type} [Fintype I] {x : I → FrobeniusDatum E} (hx : ∀ i : I, IsNuSplitPlace ν (x i))
    (primeBelow_inj : Injective fun i : I ↦ primeBelowPlus (x i).place)
    (v : I → (cyclotomicCharMod (Γ := Gal(Ω/E)) Ω (ℓ ^ ν)).ker → ZMod ℓ) :
    ∃ (T : Finset (FinPlace (NumberField.maximalRealSubfield E))) (ψ : Gal(Ω/E) → ZMod (ℓ ^ ν)),
      familyPrimes ℓ x ⊆ T ∧ IsKummerMap e hx T ψ ∧
        reductionModL ψ ∉ Submodule.span (ZMod ℓ) (Set.range v) := by
  obtain ⟨T, hT, h_dim⟩ : ∃ T, familyPrimes ℓ x ⊆ T ∧
      Fintype.card I < Module.finrank (ZMod ℓ) (kummerReductions e hx T) :=
    exists_card_lt_finrank_kummerReductions hν e h_inf_places hx primeBelow_inj
  by_contra! h_mem
  -- Otherwise the Kummer reductions would span at most as many dimensions as there are maps `v`.
  have h_le : kummerReductions e hx T ≤ Submodule.span (ZMod ℓ) (Set.range v) :=
    Submodule.span_le.2 <| Set.image_subset_iff.2 fun ψ hψ ↦ h_mem T ψ hT hψ
  have : Module.Finite (ZMod ℓ) (Submodule.span (ZMod ℓ) (Set.range v)) :=
    .span_of_finite _ (Set.finite_range v)
  exact h_dim.not_ge ((Submodule.finrank_mono h_le).trans (finrank_range_le_card v))

/-- Conjugation separates the exponents. Let `cyc` be `cyclotomicCharMod Ω (ℓ ^ ν)`, with `Ω` the
algebraic closure of `ℚ`, and let `G_ν` be its kernel. For a finite set `s` of exponents below `t`
and `g ∈ G_ν` there is `g' ∈ G_ν` at which every map `ψ` of exponent `d` takes the value
`∏_{a ∈ s} (cyc γ ^ d - cyc γ ^ a) · ψ g`. -/
lemma New.Selmer.exists_apply_eq_prod_mul {ℓ : ℕ} {E : Type} [ThePrime ℓ] [Field E]
    [CMFieldWithRoot5040 E] {ν t : ℕ} (γ : Gal(Ω/E)) {g : Gal(Ω/E)}
    (hg : cyclotomicCharMod Ω (ℓ ^ ν) g = 1) (s : Finset (Fin t)) :
    ∃ g' : Gal(Ω/E), cyclotomicCharMod Ω (ℓ ^ ν) g' = 1 ∧
      ∀ {d : ℕ} {ψ : Gal(Ω/E) → ZMod (ℓ ^ ν)}, HasKummerType ν d ψ → ψ g' =
        (∏ a ∈ s, ((cyclotomicCharMod Ω (ℓ ^ ν) γ).val ^ d -
          (cyclotomicCharMod Ω (ℓ ^ ν) γ).val ^ a.val)) * ψ g := by
  set c : (ZMod (ℓ ^ ν))ˣ := cyclotomicCharMod Ω (ℓ ^ ν) γ with hc
  induction s using Finset.induction with
  | empty => exact ⟨g, hg, by simp⟩
  | insert a s ha ih =>
    -- Conjugation by `γ` followed by the power `c⁻¹` multiplies a map of exponent `d` by `c ^ d`.
    obtain ⟨b, hb, hbψ⟩ := ih
    refine ⟨(γ * b * γ⁻¹) ^ (c⁻¹).val.val * b ^ (-c.val ^ a.val).val, by simp [hb],
      fun {d ψ} hψ ↦ ?_⟩
    calc ψ ((γ * b * γ⁻¹) ^ (c⁻¹).val.val * b ^ (-c.val ^ a.val).val)
        = (c⁻¹).val * (c.val ^ (d + 1) * ψ b) + -c.val ^ a.val * ψ b := by
          rw [hψ.map_mul (by simp [hb]) (by simp [hb]), hψ.map_pow (by simp [hb]), hψ.map_pow hb,
            hψ.map_conj γ hb, ← hc, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
      _ = (c.val ^ d - c.val ^ a.val) * ψ b := by
          linear_combination (c.val ^ d * ψ b) * c.inv_mul
      _ = (∏ a' ∈ insert a s, (c.val ^ d - c.val ^ a'.val)) * ψ g := by
          rw [hbψ hψ, prod_insert ha, mul_assoc]

/-- The separating element for the auxiliary places. Let `ν > 0`, let `ψ i` be maps of exponent
`ty i` and `ψ₀` a map of exponent `e`. Suppose the reductions modulo `ℓ` (`reductionModL`) of the
`ψ i` with `ty i = e` are linearly independent, and the reduction of `ψ₀` is not in their span. Then
some `u` with `cyclotomicCharMod Ω (ℓ ^ ν) u = 1` has `ψ i u = 0` for all `i` and
`ψ₀ u = ∏_{k ≠ e} (cyc γ ^ e - cyc γ ^ k)` over the `k < t`. Here `cyc` is
`cyclotomicCharMod Ω (ℓ ^ ν)` and `Ω` is the algebraic closure of `ℚ`. -/
lemma New.Selmer.exists_separating_element {ℓ : ℕ} {E : Type} [ThePrime ℓ] [Field E]
    [CMFieldWithRoot5040 E] {ν t : ℕ} (hν : 0 < ν) (γ : Gal(Ω/E)) (e : Fin t) {I : Type} [Fintype I]
    (ty : I → Fin t) {ψ : I → Gal(Ω/E) → ZMod (ℓ ^ ν)}
    (hψ : ∀ i : I, HasKummerType ν (ty i) (ψ i))
    (h_indep : LinearIndependent (ZMod ℓ) fun i : {i : I | ty i = e} ↦ reductionModL (ψ i))
    {ψ₀ : Gal(Ω/E) → ZMod (ℓ ^ ν)} (hψ₀ : HasKummerType ν e ψ₀)
    (h_notMem : reductionModL ψ₀ ∉
      Submodule.span (ZMod ℓ) (Set.range fun i : {i : I | ty i = e} ↦ reductionModL (ψ i))) :
    ∃ u : Gal(Ω/E), cyclotomicCharMod Ω (ℓ ^ ν) u = 1 ∧ (∀ i : I, ψ i u = 0) ∧
      ψ₀ u = ∏ k ∈ {e}ᶜ, ((cyclotomicCharMod Ω (ℓ ^ ν) γ).val ^ e.val -
        (cyclotomicCharMod Ω (ℓ ^ ν) γ).val ^ k.val) := by
  -- `ψ₀` and the maps of exponent `e` together are onto; let `g` go to `1` under `ψ₀` and to `0`
  -- under the others.
  let Ψ (o : Option {i : I | ty i = e}) (g : (cyclotomicCharMod (Γ := Gal(Ω/E)) Ω (ℓ ^ ν)).ker) :
      ZMod (ℓ ^ ν) := o.elim (ψ₀ g) fun i ↦ ψ i g
  have h_onto : Surjective fun g o ↦ Ψ o g := by
    refine surjective_of_linearIndependent_cast hν ?_ ?_
    · rintro (_ | i) a b
      exacts [hψ₀.map_mul a.2 b.2, (hψ i).map_mul a.2 b.2]
    · have h_eq : (fun o g ↦ ((Ψ o g).cast : ZMod ℓ)) =
          fun o ↦ o.casesOn' (reductionModL ψ₀) fun i ↦ reductionModL (ψ i) := by
        funext o
        cases o <;> rfl
      simpa only [h_eq] using h_indep.option h_notMem
  obtain ⟨g, hg⟩ := h_onto fun o ↦ o.elim 1 fun _ ↦ 0
  have hg₀ : ψ₀ g = 1 := congrFun hg none
  have hg_zero (i : I) (hi : ty i = e) : ψ i g = 0 := congrFun hg (some ⟨i, hi⟩)
  -- Remove the other exponents by conjugation.
  obtain ⟨u, hu, huψ⟩ := exists_apply_eq_prod_mul γ g.2 {e}ᶜ
  refine ⟨u, hu, fun i ↦ ?_, ?_⟩
  · rw [huψ (hψ i)]
    by_cases hi : ty i = e
    · exact mul_eq_zero_of_right _ (hg_zero i hi)
    · exact mul_eq_zero_of_left (prod_eq_zero (i := ty i) (by simpa using hi) (sub_self _)) _
  · rw [huψ hψ₀, hg₀, mul_one]

/-- Let `δ, g` have trivial cyclotomic character, let `u` fix `μ_{ℓ^ν}`, and let `f`, with values in
`ℤ/ℓ^ν`, satisfy `f (a * b) = f a + f b` whenever `a` has trivial cyclotomic character and `b` fixes
`μ_{ℓ^ν}`. In its value at `δ ^ ℓ ^ ν * (g * conjGal g * (u / conjGal u))` the first factor
contributes `ℓ ^ ν • f δ = 0`, which leaves a signed sum of the values at
`g, conjGal g, u, conjGal u`. -/
lemma New.Selmer.additive_apply_pow_mul_conj {ℓ : ℕ} {E : Type} [ThePrime ℓ] [Field E]
    [CMFieldWithRoot5040 E] {ν : ℕ} {δ g u : Gal(Ω/E)} (hδ : cyclotomicChar Ω ℓ δ = 1)
    (hg : cyclotomicChar Ω ℓ g = 1) (hu : cyclotomicCharMod Ω (ℓ ^ ν) u = 1)
    {f : Gal(Ω/E) → ZMod (ℓ ^ ν)}
    (hf : ∀ a b : Gal(Ω/E), cyclotomicChar Ω ℓ a = 1 →
      cyclotomicCharMod Ω (ℓ ^ ν) b = 1 → f (a * b) = f a + f b) :
    f (δ ^ ℓ ^ ν * (g * conjGal g * (u / conjGal u))) =
      f g + f (conjGal g) + (f u - f (conjGal u)) := by
  have h_div : f u = f (u / conjGal u) + f (conjGal u) := by
    -- `conjGal` preserves the cyclotomic character.
    simpa using hf (u / conjGal u) (conjGal u) (by simp)
      (by simpa [cyclotomicCharMod_prime_pow_eq] using hu)
  have h_pow (n : ℕ) :
      f (δ ^ n * (g * conjGal g * (u / conjGal u))) =
        n • f δ + (f g + f (conjGal g) + f (u / conjGal u)) := by
    induction n with
    | zero => simp [hf, hg, cyclotomicCharMod_prime_pow_eq]
    | succ n ih =>
      rw [pow_succ', mul_assoc, hf δ _ hδ (by simp [cyclotomicCharMod_prime_pow_eq, hδ, hg]), ih,
        succ_nsmul]
      ring
  simp [h_pow, h_div, CharP.cast_eq_zero]

/-- Let `Ω` be the algebraic closure of `ℚ`, let `δ, g : Gal(Ω/E)` have trivial `ℓ`-adic cyclotomic
character `cyc`, and let `u` lie in the group `G_ν` that fixes `μ_{ℓ^ν}`. Near
`δ ^ ℓ ^ ν * (g * conjGal g * (u / conjGal u))`, where `conjGal` is conjugation by complex
conjugation, a map `ψ` of exponent `e` takes the value `2 * ψ u`. -/
lemma New.Selmer.HasKummerType.eventually_eq_two_mul {ℓ : ℕ} {E : Type} [ThePrime ℓ] [Field E]
    [CMFieldWithRoot5040 E] {ν e : ℕ} {ψ : Gal(Ω/E) → ZMod (ℓ ^ ν)} (hψ : HasKummerType ν e ψ)
    {δ g u : Gal(Ω/E)} (hδ : cyclotomicChar Ω ℓ δ = 1) (hg : cyclotomicChar Ω ℓ g = 1)
    (hu : cyclotomicCharMod Ω (ℓ ^ ν) u = 1) :
    ∀ᶠ s in nhds (δ ^ ℓ ^ ν * (g * conjGal g * (u / conjGal u))), ψ s = 2 * ψ u := by
  have h_val : ψ (δ ^ ℓ ^ ν * (g * conjGal g * (u / conjGal u))) = 2 * ψ u := by
    rw [additive_apply_pow_mul_conj hδ hg hu fun a b ha hb ↦
        hψ.map_mul (by simp [cyclotomicCharMod_prime_pow_eq, ha]) hb,
      hψ.map_conjGal hu, hψ.map_conjGal (a := g) (by simp [cyclotomicCharMod_prime_pow_eq, hg])]
    ring
  rw [← h_val]
  exact hψ.isLocallyConstant.eventually_eq _

/-- Let `Ω` be the algebraic closure of `ℚ`, let `δ, g : Gal(Ω/E)` have trivial cyclotomic character
and let `u` fix `μ_{ℓ^ν}`; let `conjGal` be conjugation by complex conjugation. Near
`δ ^ ℓ ^ ν * (g * conjGal g * (u / conjGal u))` all even classes `c` of exponent `e` unramified off
`ℓ`, for all coefficient rings `O`, take the value `2 • c g`. -/
lemma New.Selmer.evenClasses_eventually_eq_two_nsmul {ℓ : ℕ} {E : Type} [ThePrime ℓ] [Field E]
    [CMFieldWithRoot5040 E] {ν : ℕ} (e : ℕ) {δ g u : Gal(Ω/E)} (hδ : cyclotomicChar Ω ℓ δ = 1)
    (hg : cyclotomicChar Ω ℓ g = 1) (hu : cyclotomicCharMod Ω (ℓ ^ ν) u = 1) :
    ∀ᶠ s in nhds (δ ^ ℓ ^ ν * (g * conjGal g * (u / conjGal u))),
      ∀ O : CoeffRing ℓ, ∀ c ∈ evenClasses O ∅ ν e, c s = 2 • c g := by
  set σ : Gal(Ω/E) := δ ^ ℓ ^ ν * (g * conjGal g * (u / conjGal u))
  -- There are finitely many cocycles in `ℤ/ℓ^ν(-e)` unramified off `ℓ`; all are constant near `σ`.
  let χ : Gal(Ω/E) →* (ZMod (ℓ ^ ν))ˣ := cyclotomicCharMod Ω (ℓ ^ ν)
  let V : DiscreteModule (ZMod (ℓ ^ ν)) Gal(Ω/E) :=
    .of (charRep (ZMod (ℓ ^ ν)) (χ ^ e)⁻¹)
      ((((Continuous.of_isOpen_ker χ Fact.out).pow e).inv).fst'.smul continuous_snd)
  have h_const : ∀ᶠ s in nhds σ,
      ∀ c ∈ Z1 V.ρ ⊓ .pi (inertiaAbove (placesDividing E ℓ)ᶜ) ⊥, c s = c σ :=
    (selmerZ1.finite_unramified_cocycles V (placesDividing E ℓ).toFinite).eventually_all.mpr
      fun c ⟨⟨hc_cont, _⟩, _⟩ ↦ (continuous_discrete_rng.mp hc_cont (c σ)).mem_nhds rfl
  filter_upwards [h_const] with s hs O c hc
  -- It is enough to test against the additive maps `φ` to `ℤ/ℓ^ν` that make `φ ∘ c` a continuous
  -- cocycle for `V`.
  have ⟨hc_sel, hc_even, _⟩ := hc
  obtain ⟨hc_coc, hc_unr, -, -⟩ := mem_selmerModule_iff.mp hc_sel
  refine sub_eq_zero.mp (eq_zero_of_forall_mem_Z1_of_mem_evenClasses hc fun φ hφ ↦ ?_)
  have h_mem :
      (fun a : Gal(Ω/E) ↦ φ (c a)) ∈ Z1 V.ρ ⊓ .pi (inertiaAbove (placesDividing E ℓ)ᶜ) ⊥ :=
    ⟨hφ, by simp +contextual [hc_unr]⟩
  have h_add (a b : Gal(Ω/E)) (ha : cyclotomicChar Ω ℓ a = 1)
    (_ : cyclotomicCharMod Ω (ℓ ^ ν) b = 1) :
      φ (c (a * b)) = φ (c a) + φ (c b) := by simp [hc_coc, tateTwist, cyclotomicInv, ha]
  have h_val : φ (c s) = φ (c g) + φ (c (conjGal g)) + (φ (c u) - φ (c (conjGal u))) :=
    (hs _ h_mem).trans (additive_apply_pow_mul_conj (f := fun a ↦ φ (c a)) hδ hg hu h_add)
  -- As `c` is even, the values at `g, conjGal g` add up and those at `u, conjGal u` cancel.
  have h_two : φ (c s) = φ (c g) + φ (c g) := by simpa [hc_even] using h_val
  rw [map_sub, h_two, map_nsmul, two_nsmul, sub_self]

/-- Choice along a well-founded order: if, for every `f` whose values before `j` satisfy `P` with
their predecessors, some value satisfies `P j` with the values of `f` before `j`, then some function
satisfies `P` at every index with its values at the earlier ones. -/
lemma New.Selmer.exists_forall_of_wellFoundedLT {J X : Type} [Preorder J] [WellFoundedLT J]
    [Nonempty X] {P : ∀ j : J, (Set.Iio j → X) → X → Prop}
    (h_step : ∀ (f : J → X) (j : J),
      (∀ i : J, i < j → P i (fun k : Set.Iio i ↦ f k) (f i)) →
        ∃ x : X, P j (fun k : Set.Iio j ↦ f k) x) :
    ∃ f : J → X, ∀ j : J, P j (fun i : Set.Iio j ↦ f i) (f j) := by
  let f : J → X := fix fun j g ↦ Classical.epsilon (P j fun i ↦ g i i.prop)
  refine ⟨f, fun j ↦ ?_⟩
  induction j using WellFoundedLT.induction with
  | ind j ih =>
    rw [show f j = Classical.epsilon (P j fun i : Set.Iio j ↦ f i) from fix_eq _ j]
    exact Classical.epsilon_spec (h_step f j ih)

/-- What is chosen at one index of the triangle: a split place of `E`, a map from `Gal(Ω/E)` to
`ℤ/ℓ^ν` (`Ω` is the algebraic closure of `ℚ`), and a finite set of primes of the real subfield that
this place and the later ones have to avoid. -/
structure New.Selmer.TriangleEntry (ℓ : ℕ) (E : Type) [ThePrime ℓ] [Field E] [CMFieldWithRoot5040 E]
    (ν : ℕ) where
  /-- The place with its Frobenius element. -/
  frobeniusDatum : FrobeniusDatum E
  /-- The place is not above `ℓ` and its Frobenius element fixes the `ℓ^ν`-th roots of unity. -/
  isNuSplitPlace : IsNuSplitPlace (ℓ := ℓ) ν frobeniusDatum
  /-- The primes to avoid. -/
  avoidedPrimes : Finset (FinPlace (NumberField.maximalRealSubfield E))
  /-- The map, a Kummer map once the entry follows earlier ones. -/
  kummerCandidate : Gal(Ω/E) → ZMod (ℓ ^ ν)

/-- The entry `q` of exponent `e` may follow the entries `f i` of exponents `ty i`: its map is a
Kummer map for the earlier places of exponent `e` and new modulo `ℓ`, and its place is a new one in
`W`, at whose Frobenius element the earlier maps vanish, twice the value of the new map divides the
loss `n`, and the even classes of exponent `e` unramified off `ℓ` take twice their value at the test
element `g`. -/
structure New.Selmer.TriangleEntry.MayFollow {ℓ : ℕ} {E : Type} [ThePrime ℓ] [Field E]
    [CMFieldWithRoot5040 E] {ν t : ℕ} {K : Type} [Finite K] (ty : K → Fin t)
    (f : K → TriangleEntry ℓ E ν) (e : Fin t) (g : Gal(Ω/E)) (n : ℕ) (W : Set (FrobeniusDatum E))
    (q : TriangleEntry ℓ E ν) : Prop where
  /-- The new map is a Kummer map of exponent `e` off `q.avoidedPrimes`: the restriction of a
  relation over the real subfield that is unramified off `q.avoidedPrimes` and whose reciprocity law
  holds at split primes off `q.avoidedPrimes`, for cocycles with local conditions above `ℓ` and
  below the earlier places of exponent `e`. -/
  isKummerMap : IsKummerMap e (fun i : {i : K | ty i = e} ↦ (f i).isNuSplitPlace) q.avoidedPrimes
    q.kummerCandidate
  /-- The primes to avoid include the primes of the real subfield above `ℓ` or below an earlier
  place of exponent `e`. -/
  familyPrimes_subset : familyPrimes ℓ (fun i : {i : K | ty i = e} ↦ (f i).frobeniusDatum) ⊆
    q.avoidedPrimes
  /-- Modulo `ℓ` the new map is independent of the earlier maps of exponent `e`. -/
  notMem_span : reductionModL q.kummerCandidate ∉
    Submodule.span (ZMod ℓ) (Set.range fun i : {i : K | ty i = e} ↦
      reductionModL (f i).kummerCandidate)
  /-- At the new Frobenius element the new map is nearly a unit: twice its value divides `n`. -/
  two_mul_dvd : 2 * q.kummerCandidate q.frobeniusDatum.frob ∣ n
  /-- At the new Frobenius element the earlier maps vanish. -/
  apply_eq_zero (i : K) : (f i).kummerCandidate q.frobeniusDatum.frob = 0
  /-- At the new Frobenius element the even classes of exponent `e` unramified off `ℓ` take twice
  their value at `g`. -/
  even_apply (O : CoeffRing ℓ) : ∀ z ∈ evenClasses O ∅ ν e, z q.frobeniusDatum.frob = 2 • z g
  /-- The new place lies above a new prime of the real subfield. -/
  primeBelowPlus_ne (i : K) : primeBelowPlus (f i).frobeniusDatum.place ≠ primeBelowPlus
    q.frobeniusDatum.place
  /-- It avoids the primes excluded by the earlier maps. -/
  notMem_earlier (i : K) : primeBelowPlus q.frobeniusDatum.place ∉ (f i).avoidedPrimes
  /-- It avoids the primes excluded by the new map. -/
  notMem : primeBelowPlus q.frobeniusDatum.place ∉ q.avoidedPrimes
  /-- The new place, with its Frobenius element, is allowed. -/
  mem : q.frobeniusDatum ∈ W

/-- Almost all places of `E` lie neither above `ℓ` nor above a prime in a given finite set `T` of
primes of the real subfield. -/
lemma New.Selmer.eventually_primeBelowPlus_notMem {ℓ : ℕ} {E : Type} [ThePrime ℓ] [Field E]
    [CMFieldWithRoot5040 E] {T : Set (FinPlace (NumberField.maximalRealSubfield E))}
    (hT : T.Finite) :
    ∀ᶠ w : FinPlace E in cofinite, ↑ℓ ∉ w.asIdeal ∧ primeBelowPlus w ∉ T := by
  filter_upwards [GaloisRep.eventually_notMem_star_notMem ℓ ∅, tendsto_place_comap_cofinite
    (algebraMap (NumberField.maximalRealSubfield E) E) hT.compl_mem_cofinite]
    with w ⟨_, _, h_off⟩ h_avoid using ⟨h_off, h_avoid⟩

/-- Let `ℓ` be a prime and `E` a CM field with a primitive `5040`-th root of unity and at least four
infinite places. Let `ν > 0`, `t + 2 ≤ y` and `4 ∣ ℓ ^ (3 h)`, let `cyc γ ^ a - 1` divide `ℓ ^ h`
for `0 < a < t`, let `g` have trivial cyclotomic character `cyc`, and, for every `g'`, let `W`
contain most Frobenii near `δ ^ ℓ ^ ν * g'` for some `δ` with trivial cyclotomic character. Let
finitely many entries `f i` lie above distinct primes of `F`, let their maps have exponents `ty i`,
and let those of exponent `e` be independent as maps `G_ν → ℤ/ℓ` (`reductionModL`). Then some entry
`q` may follow them (`MayFollow`): its map is a Kummer map of exponent `e` for the earlier places of
exponent `e`, off a set `q.avoidedPrimes` that contains the primes above `ℓ` and below these places,
and is outside the span modulo `ℓ` of the earlier maps of exponent `e`; the prime of `F` below its
place is none of the earlier ones and lies in none of the sets of primes to avoid; its datum lies in
`W`; at its Frobenius element the earlier maps vanish, twice the value of the new map divides the
loss `ℓ ^ (y * h)`, and the even classes of exponent `e` unramified off `ℓ` take twice their value
at `g`. -/
lemma New.Selmer.TriangleEntry.exists_mayFollow {ℓ : ℕ} {E : Type} [ThePrime ℓ] [Field E]
    [CMFieldWithRoot5040 E] {ν t y h : ℕ} {γ g : Gal(Ω/E)} (hν : 0 < ν)
    (h_inf_places : 4 ≤ Core.numInfPlaces E) (hty : t + 2 ≤ y)
    (hγ_dvd : ∀ a ∈ Set.Ioo 0 t, (cyclotomicChar Ω ℓ γ ^ a).val - 1 ∣ ℓ ^ h) (e : Fin t)
    (h_four : (4 : ℤ_[ℓ]) ∣ ℓ ^ (3 * h)) (hg : cyclotomicChar Ω ℓ g = 1)
    {W : Set (FrobeniusDatum E)} (hW : ∀ g' : Gal(Ω/E),
      ∃ δ : Gal(Ω/E), cyclotomicChar Ω ℓ δ = 1 ∧ W ∈ mostFrobeniiAt E (δ ^ ℓ ^ ν * g'))
    {I : Type} [Fintype I] (ty : I → Fin t) {f : I → TriangleEntry ℓ E ν}
    (primeBelow_inj : Injective fun i : I ↦ primeBelowPlus (f i).frobeniusDatum.place)
    (h_type : ∀ i : I, HasKummerType ν (ty i) (f i).kummerCandidate)
    (h_indep : LinearIndependent (ZMod ℓ) fun i : {i : I | ty i = e} ↦
      reductionModL (f i).kummerCandidate) :
    ∃ q : TriangleEntry ℓ E ν, MayFollow ty f e g (ℓ ^ (y * h)) W q := by
  -- Take a new map `ψ₀`, a point `u` where the earlier maps vanish while `ψ₀ u` is
  -- `∏_{k ≠ e} (cyc γ ^ e - cyc γ ^ k)`, and a Frobenius element near a suitable `σ`.
  obtain ⟨T₀, ψ₀, hT₀, hψ₀, h_notMem⟩ := exists_isKummerMap_notMem_span hν e h_inf_places
    (fun i : {i : I | ty i = e} ↦ (f i).isNuSplitPlace) (primeBelow_inj.comp Subtype.val_injective)
    fun i ↦ reductionModL (f i).kummerCandidate
  obtain ⟨u, hu, hψu, hψ₀u⟩ :=
    exists_separating_element hν γ e ty h_type h_indep hψ₀.hasKummerType h_notMem
  obtain ⟨δ, hδ, hσW⟩ := hW (g * conjGal g * (u / conjGal u))
  set σ : Gal(Ω/E) := δ ^ ℓ ^ ν * (g * conjGal g * (u / conjGal u)) with hσ
  have hσ_cyc : σ ∈ (cyclotomicCharMod Ω (ℓ ^ ν)).ker := by
    simp [hσ, cyclotomicCharMod_prime_pow_eq, hδ, hg]
  have h_near : ∀ᶠ s in nhds σ, ψ₀ s = 2 * ψ₀ u ∧
    (∀ i, (f i).kummerCandidate s = 2 * (f i).kummerCandidate u) ∧
      (∀ O, ∀ z ∈ evenClasses O ∅ ν e, z s = 2 • z g) ∧ cyclotomicCharMod Ω (ℓ ^ ν) s = 1 :=
    (hψ₀.hasKummerType.eventually_eq_two_mul hδ hg hu).and <|
      (eventually_all.2 fun i ↦ (h_type i).eventually_eq_two_mul hδ hg hu).and <|
      (evenClasses_eventually_eq_two_nsmul e hδ hg hu).and
        (isOpen_ker_cyclotomicCharMod.1.mem_nhds hσ_cyc)
  let T' : Set (FinPlace (NumberField.maximalRealSubfield E)) :=
    T₀ ∪ ⋃ i, insert (primeBelowPlus (f i).frobeniusDatum.place) (f i).avoidedPrimes
  have h_most : ∀ᶠ x : FrobeniusDatum E in mostFrobenii E,
      ↑ℓ ∉ x.place.asIdeal ∧ primeBelowPlus x.place ∉ T' :=
    eventually_mostFrobenii (eventually_primeBelowPlus_notMem (Set.toFinite T')) fun _ ↦ id
  -- The filter `mostFrobeniiAt E σ` is proper (Chebotarev): some `x₀` has all this.
  obtain ⟨x₀, hW₀, ⟨h_off, hT'⟩, hψ₀x, hψx, h_even, h_cyc⟩ :=
    nonempty_of_mem (inter_mem hσW (inter_mem_inf h_most (preimage_mem_comap h_near)))
  have h_dvd : 2 * ψ₀ x₀.frob ∣ ↑(ℓ ^ (y * h)) := by
    have h_int : (4 : ℤ_[ℓ]) * ∏ k ∈ {e}ᶜ,
        ((cyclotomicChar Ω ℓ γ ^ e.val).val - (cyclotomicChar Ω ℓ γ ^ k.val).val) ∣ ℓ ^ (y * h) :=
      mul_prod_pow_sub_pow_dvd hty hγ_dvd e h_four
    rw [hψ₀x, hψ₀u, ← mul_assoc, show (2 * 2 : ZMod (ℓ ^ ν)) = 4 by norm_num]
    -- This is the divisibility `h_int` reduced modulo `ℓ ^ ν`.
    simpa [cyclotomicCharMod_prime_pow_eq, map_ofNat] using map_dvd (toZModPow ν) h_int
  obtain ⟨h_notMem₀, h_avoid⟩ : primeBelowPlus x₀.place ∉ T₀ ∧ ∀ i : I,
      primeBelowPlus (f i).frobeniusDatum.place ≠ primeBelowPlus x₀.place ∧
        primeBelowPlus x₀.place ∉ (f i).avoidedPrimes := by simpa [T', eq_comm] using hT'
  exact ⟨⟨x₀, ⟨h_off, h_cyc⟩, T₀, ψ₀⟩,
    { isKummerMap := hψ₀, familyPrimes_subset := hT₀, notMem_span := h_notMem
      two_mul_dvd := h_dvd
      apply_eq_zero := fun i ↦ by rw [hψx i, hψu i, mul_zero]
      even_apply := h_even
      primeBelowPlus_ne := fun i ↦ (h_avoid i).1, notMem_earlier := fun i ↦ (h_avoid i).2
      notMem := h_notMem₀, mem := hW₀ }⟩

/-- Some entry exists: at a split place, with the zero map and no primes to avoid. -/
instance New.Selmer.TriangleEntry.nonempty {ℓ : ℕ} {E : Type} [ThePrime ℓ] [Field E]
    [CMFieldWithRoot5040 E] {ν : ℕ} : Nonempty (TriangleEntry ℓ E ν) := by
  have h_near : ∀ᶠ s : Gal(Ω/E) in nhds 1, cyclotomicCharMod Ω (ℓ ^ ν) s = 1 :=
    isOpen_ker_cyclotomicCharMod.1.mem_nhds (map_one _)
  obtain ⟨x, ⟨h_off, -⟩, h_cyc⟩ := nonempty_of_mem (f := mostFrobeniiAt E 1) (inter_mem_inf
    (eventually_mostFrobenii (eventually_primeBelowPlus_notMem (ℓ := ℓ) Set.finite_empty)
      fun _ ↦ id) (preimage_mem_comap h_near))
  exact ⟨x, ⟨h_off, h_cyc⟩, ∅, 0⟩

/-- Let `ℓ` be a prime, `E` a CM field with a primitive `5040`-th root of unity and at least four
infinite places, inside the algebraic closure `Ω` of `ℚ`, and `cyc` the `ℓ`-adic cyclotomic
character. Along a finite linear order `J`, with exponents `ty j` and test elements `g j` of trivial
`cyc`, entries `f j` can be chosen so that each may follow the earlier ones (`MayFollow`): its map
is a Kummer map of exponent `ty j` for the earlier places of this exponent, off its set of primes to
avoid, and is independent of their maps modulo `ℓ` on the elements fixing `μ_{ℓ^ν}`; the prime of
`F` below its place is new and avoided by none of the maps up to it; its Frobenius datum is in `W`;
at its Frobenius element the earlier maps vanish, twice the value of its map divides the loss
`ℓ ^ (y * h)`, and the even classes of exponent `ty j` unramified off `ℓ` take twice their value at
`g j`. As in `New.Selmer.TriangleEntry.exists_mayFollow`, it is assumed that `ν > 0`, that
`t + 2 ≤ y`, that `cyc γ ^ a - 1` divides `ℓ ^ h` for `0 < a < t`, that `4 ∣ ℓ ^ (3 h)` unless `J`
is empty, and that for every `g'` there is a `δ` of trivial `cyc` such that `W` contains most
Frobenii near `δ ^ ℓ ^ ν * g'` (`mostFrobeniiAt`). -/
lemma New.Selmer.TriangleEntry.exists_forall_mayFollow {ℓ : ℕ} {E : Type} [ThePrime ℓ] [Field E]
    [CMFieldWithRoot5040 E] {ν t y h : ℕ} {γ : Gal(Ω/E)} (hν : 0 < ν)
    (h_inf_places : 4 ≤ Core.numInfPlaces E) (hty : t + 2 ≤ y)
    (hγ_dvd : ∀ a ∈ Set.Ioo 0 t, (cyclotomicChar Ω ℓ γ ^ a).val - 1 ∣ ℓ ^ h)
    {W : Set (FrobeniusDatum E)} (hW : ∀ g' : Gal(Ω/E),
      ∃ δ : Gal(Ω/E), cyclotomicChar Ω ℓ δ = 1 ∧ W ∈ mostFrobeniiAt E (δ ^ ℓ ^ ν * g'))
    {J : Type} [Fintype J] [LinearOrder J] (ty : J → Fin t) {g : J → Gal(Ω/E)}
    (hg : ∀ j : J, cyclotomicChar Ω ℓ (g j) = 1) (h_four : Nonempty J → (4 : ℤ_[ℓ]) ∣ ℓ ^ (3 * h)) :
    ∃ f : J → TriangleEntry ℓ E ν, ∀ j : J, MayFollow (fun i : Set.Iio j ↦ ty i)
      (fun i : Set.Iio j ↦ f i) (ty j) (g j) (ℓ ^ (y * h)) W (f j) := by
  refine exists_forall_of_wellFoundedLT (P := fun j f ↦
    MayFollow (fun i : Set.Iio j ↦ ty i) f (ty j) (g j) (ℓ ^ (y * h)) W) fun f j h_prev ↦ ?_
  have h_inj : Injective fun i : Set.Iio j ↦ primeBelowPlus (f i).frobeniusDatum.place :=
    .of_lt_imp_ne fun a b hab ↦ (h_prev b b.2).primeBelowPlus_ne ⟨a, hab⟩
  have h_type (i : Set.Iio j) : HasKummerType ν (ty i) (f i).kummerCandidate :=
    (h_prev i i.2).isKummerMap.hasKummerType
  -- By induction the earlier maps of the exponent of `j` are independent modulo `ℓ`.
  have h_indep : LinearIndependent (ZMod ℓ)
      fun i : {i : Set.Iio j | ty i = ty j} ↦ reductionModL (f i.1).kummerCandidate := by
    refine linearIndependent_of_notMem_span_Iio fun i h_mem ↦
      (h_prev i i.1.2).notMem_span (Submodule.span_mono ?_ h_mem)
    rintro _ ⟨k, hk, rfl⟩
    exact ⟨⟨⟨k, hk⟩, k.2.trans i.2.symm⟩, rfl⟩
  exact exists_mayFollow hν h_inf_places hty hγ_dvd (ty j) (h_four ⟨j⟩) (hg j) hW _ h_inj h_type
    h_indep

/-- If the entries `f j` are indexed by a finite linear order and each may follow the earlier ones
(`MayFollow`), then their places lie above distinct primes of the real subfield. -/
lemma New.Selmer.TriangleEntry.primeBelowPlus_injective_of_mayFollow {ℓ : ℕ} {E : Type} [ThePrime ℓ]
    [Field E] [CMFieldWithRoot5040 E] {ν t n : ℕ} {W : Set (FrobeniusDatum E)}
    {J : Type} [Fintype J] [LinearOrder J] {ty : J → Fin t}
    {g : J → Gal(Ω/E)} {f : J → TriangleEntry ℓ E ν} (hf : ∀ j : J,
      MayFollow (fun i : Set.Iio j ↦ ty i) (fun i : Set.Iio j ↦ f i) (ty j) (g j) n W (f j)) :
    Injective fun j : J ↦ primeBelowPlus (f j).frobeniusDatum.place :=
  .of_lt_imp_ne fun a b hab ↦ (hf b).primeBelowPlus_ne ⟨a, hab⟩

/-- The places of entries, with their tame generators and Frobenius elements, form a tame generator
family (`New.Selmer.IsTameGeneratorFamily`): they are not above `ℓ`, the Frobenius elements fix
`μ_{ℓ^ν}`, and the tame generators are the chosen ones at places of `Ω` above them. -/
lemma New.Selmer.TriangleEntry.isTameGeneratorFamily {ℓ : ℕ} {E : Type} [ThePrime ℓ] [Field E]
    [CMFieldWithRoot5040 E] {ν : ℕ} {J : Type} (f : J → TriangleEntry ℓ E ν) :
    IsTameGeneratorFamily ν (fun j : J ↦ (f j).frobeniusDatum.place)
      (fun j : J ↦ (f j).frobeniusDatum.isPlaceOver.tameGenerator)
      fun j : J ↦ (f j).frobeniusDatum.frob := fun j ↦
  ⟨(f j).isNuSplitPlace.1, (f j).isNuSplitPlace.2, _, (f j).frobeniusDatum.isPlaceOver, rfl⟩

/-- Let the entries `f j`, of exponents `ty j`, be indexed by a finite linear order `J`, and suppose
that each may follow the earlier ones with test element `g j`, loss `n` and Frobenius data in `W`.
Let `z` be an even class of exponent `ty j`: a cocycle on `Gal(Ω/E)` in `(O/ℓ^ν)(-ty j)`, written as
a function with values in `Unit → O/ℓ^ν`, invariant under complex conjugation and trivial on the
elements of trivial cyclotomic character in the decomposition groups above `ℓ`, here allowed to
ramify at `ℓ`, at the places of the entries and at their conjugates. Let it vanish at the tame
generators of the places before `j` and at the Frobenius elements of those among them of exponent
`ty j`. Then `n` kills the value of `z` at the tame generator of the `j`-th place. -/
lemma New.Selmer.TriangleEntry.nsmul_tameGenerator_eq_zero_of_mayFollow {ℓ : ℕ} {E : Type}
    [ThePrime ℓ] [Field E] [CMFieldWithRoot5040 E] {ν t n : ℕ} {W : Set (FrobeniusDatum E)}
    {J : Type} [Fintype J] [LinearOrder J] {ty : J → Fin t} {g : J → Gal(Ω/E)}
    {f : J → TriangleEntry ℓ E ν} (hf : ∀ j : J,
      MayFollow (fun i : Set.Iio j ↦ ty i) (fun i : Set.Iio j ↦ f i) (ty j) (g j) n W (f j))
    {O : CoeffRing ℓ} {j : J} {z : Gal(Ω/E) → Unit → QuotSpan (ℓ ^ ν : ↑O)}
    (hz : z ∈ evenClasses O (Set.range fun i : J ↦ (f i).frobeniusDatum.place) ν (ty j))
    (hz_tame : ∀ i : J, i < j → z (f i).frobeniusDatum.isPlaceOver.tameGenerator = 0)
    (hz_frob : ∀ i : J, i < j → ty i = ty j → z (f i).frobeniusDatum.frob = 0) :
    n • z (f j).frobeniusDatum.isPlaceOver.tameGenerator = 0 := by
  -- As `z` kills the earlier tame generators, it is unramified at the earlier places, so the
  -- reciprocity law of the `j`-th Kummer map applies at the places from `j` on.
  have h_range : (Set.range fun i : J ↦ (f i).frobeniusDatum.place) =
      (Set.range fun i : Set.Ici j ↦ (f i).frobeniusDatum.place) ∪ .range fun i : Set.Iio j ↦
        (f i).frobeniusDatum.place := by
    simp [← Set.image_eq_range fun i : J ↦ (f i).frobeniusDatum.place, ← Set.image_union,
      Set.union_comm (.Ici j)]
  have h_subset : placesDividing E ℓ ∪ Set.conjClosure
    (.range fun i : J ↦ (f i).frobeniusDatum.place) ⊆
      placesDividing E ℓ ∪ Set.conjClosure (.range fun i : Set.Ici j ↦ (f i).frobeniusDatum.place) ∪
        Set.conjClosure (.range fun i : Set.Iio j ↦ (f i).frobeniusDatum.place) := by
    simp only [h_range, Set.conjClosure, Set.preimage_union, Set.subset_def, Set.mem_union]
    tauto
  obtain ⟨hz_mem, hz_even⟩ := hz
  have h_tame : ∀ i : Set.Iio j × Bool,
      z (withConjInv (fun i : Set.Iio j ↦ (f i).frobeniusDatum.isPlaceOver.tameGenerator.val) i) =
        0 := by
    simp +contextual [idOrConjInv, cocycle_apply_inv (mem_selmerModule_iff.1 hz_mem).1,
      hz_even.1, hz_tame, -smul_eq_zero]
  have hz_later : z ∈ evenClasses O (.range fun i : Set.Ici j ↦ (f i).frobeniusDatum.place) ν
    (ty j) :=
    ⟨(isTameGeneratorFamily fun i : Set.Iio j ↦ f i).mem_selmerModule_of_tame_eq_zero hz_mem h_tame
      h_subset
      fun _ _ ↦ tateTwist_eq_one_of_cyclotomicChar_eq_one, hz_even⟩
  have h_allowed : ∀ i : Set.Ici j, primeBelowPlus (f i).frobeniusDatum.place ∉
    (f j).avoidedPrimes := fun ⟨i, hji⟩ ↦ by
    obtain rfl | hlt := eq_or_lt_of_le (α := J) hji
    · exact (hf j).notMem
    · exact (hf i).notMem_earlier ⟨j, hlt⟩
  -- The `j`-th map vanishes at the later Frobenius elements.
  have h_zero (i : Set.Ici j) (hi : i ≠ ⊥) : (f j).kummerCandidate (f i).frobeniusDatum.frob = 0 :=
    (hf i).apply_eq_zero ⟨j, hi.bot_lt⟩
  have h_inj : Injective fun i : Set.Ici j ↦ primeBelowPlus (f i).frobeniusDatum.place :=
    (primeBelowPlus_injective_of_mayFollow hf).injOn.injective
  have h_frob : ∀ i : {i : Set.Iio j | ty i = ty j}, z (f i).frobeniusDatum.frob = 0 :=
    fun ⟨⟨i, hi⟩, hty⟩ ↦ hz_frob i hi hty
  -- So the reciprocity law of the `j`-th map applies, with `j` as the least of the later indices.
  exact (hf j).isKummerMap.nsmul_apply_tameGenerator_eq_zero (hf j).familyPrimes_subset
    (w := fun i : Set.Ici j ↦ (f i).frobeniusDatum) (fun i ↦ (f i).isNuSplitPlace) h_inj h_allowed
      (j := ⊥)
    h_zero hz_later h_frob (hf j).two_mul_dvd

/-- If the datum `x` is `ν`-split (`IsNuSplitPlace`: its prime is not above `ℓ` and its Frobenius
element fixes `μ_{ℓ^ν}`), then `ℓ ^ ν` divides `x.place.q - 1`, i.e. the norm `q` of its place is
`1` modulo `ℓ ^ ν`. -/
lemma New.Selmer.IsNuSplitPlace.prime_pow_dvd_q_sub_one {ℓ : ℕ} {E : Type} [ThePrime ℓ] [Field E]
    [CMFieldWithRoot5040 E] {ν : ℕ} {x : FrobeniusDatum E} (hx : IsNuSplitPlace (ℓ := ℓ) ν x) :
    ℓ ^ ν ∣ x.place.q - 1 :=
  have h_modEq : x.place.q ≡ 1 [MOD ℓ ^ ν] := (x.isFrob_inv.mem_ker_cyclotomicCharMod_iff
    (by simp [x.isPlaceOver.valuation_natCast_eq_one_iff, hx.1])).1 (inv_mem hx.2)
  h_modEq.symm.dvd'

/-- Places of prime norm above distinct primes of the real subfield are distinct from each other and
from all their conjugates. -/
lemma New.Selmer.isConjApart_of_injective_primeBelowPlus {E : Type} [Field E]
    [CMFieldWithRoot5040 E] {J : Type} {x : J → FrobeniusDatum E}
    (hx : Injective fun j : J ↦ primeBelowPlus (x j).place) :
    IsConjApart fun j : J ↦ (x j).place := by
  refine ⟨.of_comp (f := primeBelowPlus) hx, fun i j hij ↦ ?_⟩
  obtain rfl : i = j := hx (by simp only [← hij, primeBelowPlus_star])
  -- A place of prime norm is not its own conjugate.
  exact isSplit_of_q_prime (x i).prime_q hij

/-- Let `ℓ` be a prime, `cyc` the `ℓ`-adic cyclotomic character, and `E` a CM field with a primitive
`5040`-th root of unity and at least four infinite places, inside the algebraic closure `Ω` of `ℚ`,
that lies in the cyclotomic field of level `N > 0`. Let `N + t < y`, let `γ` generate `Gal(Ω/E)`
topologically modulo the kernel of `cyc`, let `cyc γ ^ a - 1` divide `ℓ ^ h` for `0 < a < t`, let
`ℓ ≤ y ^ 2` or `h = 0`, and suppose that for all `ν` and `g` there is a `δ` of trivial `cyc` such
that `W` contains most Frobenii near `δ ^ ℓ ^ ν * g`. Then there is a finite linear order `J` with a
monotone map `ty` (the exponent) to the `e` with `0 < e < t` such that for each `ν > 0` some
Taylor–Wiles places `Q` of level `ℓ ^ ν` indexed by `J` have their Frobenius data in `W` and satisfy
`IsPrimeTriangle` for `γ⁻¹` with bounds `b = y * h` and `c = y ^ 22 * h`. This says, with `τ j` the
chosen generator of tame inertia and `φ j` the Frobenius element at the `j`-th place:
* the `φ j` fix `μ_{ℓ^ν}` and the places are not above `ℓ`;
* there is a finite set `s` of test points of trivial `cyc` with `(#J + #s + 1) * b ≤ c`, such that
  a cocycle unramified off `ℓ` that vanishes at `γ⁻¹` and on `s` is zero, and for each exponent `e`
  and each point of `s` some `φ j` of exponent `e` is where the even classes unramified off `ℓ` take
  twice their value at that point;
* if an even class of exponent `ty j`, allowed to ramify at the places and their conjugates,
  vanishes at the earlier `τ i` and at the earlier `φ i` of the same exponent, then `ℓ ^ b` kills
  its value at `τ j`;
* `∏_{k ≠ e} (cyc γ ^ e - cyc γ ^ k)` and, for `e > 0`, `4 (cyc γ ^ e - 1) ^ 2` divide `ℓ ^ b`. -/
lemma New.Selmer.exists_isPrimeTriangle {ℓ : ℕ} {E : Type} [ThePrime ℓ] [Field E]
    [CMFieldWithRoot5040 E] (t : ℕ) {N y h : ℕ} {γ : Gal(Ω/E)} [NeZero N]
    (hE : ∀ x : E, algebraMap E Ω x ∈ cycloField N) (hN : N + t < y)
    (hγ_gen : (cyclotomicChar Ω ℓ).IsGeneratorModKer γ)
    (hγ_dvd : ∀ a ∈ Set.Ioo 0 t, (cyclotomicChar Ω ℓ γ ^ a).val - 1 ∣ ℓ ^ h)
    (hy : ℓ ≤ y ^ 2 ∨ h = 0) (h_inf_places : 4 ≤ Core.numInfPlaces E) {W : Set (FrobeniusDatum E)}
    (hW : ∀ (ν : ℕ) (g : Gal(Ω/E)), ∃ δ : Gal(Ω/E),
      cyclotomicChar Ω ℓ δ = 1 ∧ W ∈ mostFrobeniiAt E (δ ^ ℓ ^ ν * g)) :
    ∃ (J : Type) (_ : Fintype J) (_ : LinearOrder J) (ty : J →o {e : Fin t // 0 < e.val}),
      ∀ ν > (0 : ℕ), ∃ Q : TaylorWilesPlaces E J (ℓ ^ ν),
        IsPrimeTriangle ν Q.place (fun j : J ↦ (Q.frobData j).isPlaceOver.tameGenerator)
          (fun j : J ↦ (Q.frobData j).frob) γ⁻¹ t ty (y * h) (y ^ 22 * h) ∧
        ∀ j : J, Q.frobData j ∈ W := by
  -- `J` has one place for each exponent `0 < e < t` and each test point `i ∈ testPoints`. In the
  -- order of `J` choose a Kummer map and then a place, with `i` as test element. The test points
  -- have trivial cyclotomic character, and with `γ⁻¹` they detect the cocycles unramified off `ℓ`.
  obtain ⟨testPoints, h_ker, h_card, h_detect⟩ :=
    exists_detecting_points_mem_ker hE ℓ hγ_gen.inv
  have hty : t + 2 ≤ y := by grind [NeZero.pos N]
  -- `4` divides `cyc γ ^ e - 1`, which divides `ℓ ^ h`; so `4 (cyc γ ^ e - 1) ^ 2` divides
  -- `ℓ ^ (3 h)`.
  have h_four (e : {e : Fin t // 0 < e.val}) :
      (4 * ((cyclotomicChar Ω ℓ γ ^ e.1.val).val - 1) ^ 2 : ℤ_[ℓ]) ∣ ℓ ^ (3 * h) := by
    have he : (cyclotomicChar Ω ℓ γ ^ e.1.val).val - 1 ∣ ℓ ^ h := hγ_dvd _ ⟨e.2, e.1.isLt⟩
    have h_dvd : (2 ^ 2 : ℤ_[ℓ]) ∣ ℓ ^ h :=
      (four_dvd_cyclotomicChar_sub_one (γ ^ e.1.val)).trans (by simpa using he)
    calc (4 * ((cyclotomicChar Ω ℓ γ ^ e.1.val).val - 1) ^ 2 : ℤ_[ℓ])
        = 2 ^ 2 * ((cyclotomicChar Ω ℓ γ ^ e.1.val).val - 1) ^ 2 := by norm_num
      _ ∣ ℓ ^ h * (ℓ ^ h) ^ 2 := mul_dvd_mul h_dvd (pow_dvd_pow_of_dvd he 2)
      _ = ℓ ^ (3 * h) := by ring
  -- Well-order the test points, and order `J` lexicographically, first by the exponent.
  obtain ⟨points_order, points_wf⟩ := exists_wellFoundedLT testPoints
  let J : Type := {e : Fin t // 0 < e.val} ×ₗ testPoints
  let ty : J →o {e : Fin t // 0 < e.val} := ⟨fun j ↦ (ofLex j).1, Prod.Lex.monotone_fst⟩
  refine ⟨J, inferInstance, inferInstance, ty, fun ν hν ↦ ?_⟩
  let ty' : J → Fin t := fun j ↦ ty j
  let g' : J → Gal(Ω/E) := fun j ↦ (ofLex j).2
  obtain ⟨f, hf⟩ := TriangleEntry.exists_forall_mayFollow hν h_inf_places hty hγ_dvd (hW ν) ty'
    (g := g') (fun j ↦ h_ker _ (coe_mem _)) fun ⟨j⟩ ↦ dvd_of_mul_right_dvd (h_four (ty j))
  have h_apart : IsConjApart fun j : J ↦ (f j).frobeniusDatum.place :=
    isConjApart_of_injective_primeBelowPlus (TriangleEntry.primeBelowPlus_injective_of_mayFollow hf)
  refine ⟨⟨fun j ↦ (f j).frobeniusDatum, h_apart, fun j ↦
    (f j).isNuSplitPlace.prime_pow_dvd_q_sub_one⟩,
    { isTameGeneratorFamily := TriangleEntry.isTameGeneratorFamily f
      exists_test_points := ⟨testPoints, h_ker, ?_, fun O e ↦ h_detect, fun e i hi ↦ ?_⟩
      prod_dvd := fun e ↦ ?_
      pow_smul_eq_zero := fun O j z hz h_earlier ↦
        TriangleEntry.nsmul_tameGenerator_eq_zero_of_mayFollow hf hz (fun i hi ↦ (h_earlier i hi).1)
          fun i hi h_eq ↦ (h_earlier i hi).2 (Subtype.ext h_eq)
      four_mul_sq_dvd := fun O e ↦ ?_ }, fun j ↦ (hf j).mem⟩
  · -- There are at most `(t + 2) * y ^ 20 ≤ y ^ 21` places and points, each of cost `y * h`.
    obtain hℓy | rfl := hy
    · have h_one : testPoints.card + 1 ≤ 2 * y ^ 20 := by
        grind [h_card y (by omega) hℓy, Nat.one_le_pow 20 y (by omega)]
      grw [h_one, card_lex, card_prod, card_subtype_le, card_coe, h_card y (by omega) hℓy,
        Fintype.card_fin, ← add_mul, hty]
      exact le_of_eq (by ring)
    · simp
  · -- At the place of index `(e, i)` the even classes take twice their value at `i`.
    exact ⟨toLex (e, ⟨i, hi⟩), rfl, (hf (toLex (e, ⟨i, hi⟩))).even_apply⟩
  · simpa using mul_prod_pow_sub_pow_dvd hty hγ_dvd e (one_dvd _)
  · have h_int : (4 * ((cyclotomicChar Ω ℓ γ ^ (e : ℕ)).val - 1) ^ 2 : ℤ_[ℓ]) ∣ ℓ ^ (y * h) :=
      dvd_of_mul_right_dvd (mul_prod_pow_sub_pow_dvd hty hγ_dvd e.1 (h_four e))
    simpa [cyclotomicInv, map_ofNat] using map_dvd (algebraMap _ O) h_int
