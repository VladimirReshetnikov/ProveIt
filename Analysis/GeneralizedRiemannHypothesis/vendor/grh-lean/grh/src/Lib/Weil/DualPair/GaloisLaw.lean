import Lib.Weil.DualPair.FiniteAction

/-!
# Semilinear maps intertwining the Weil action up to σΔ/Δ

This file gives an abstract form of the Galois law for the Weil representation. A map `L` on the
data `𝒮 V` that is semilinear along `σ : ℂ →+* ℂ` may keep the finite part and turn the finite
Heisenberg translation by `x` into that by `b x`, where `σ` takes `ψ z` to `ψ (b b̄ z)` for the
additive character `ψ = New.stdLattice.selfDualAddChar E` of the finite adeles. Such a map also
intertwines the Weil action, on the finite part and for finite points, up to the factor σ(Δ_f)/Δ_f,
with Δ_f the finite multiplier `New.finMultiplier`. Writing `b = u a` with `u` unitary and `a` a
unit of `Ô`, the laws are first proved for `ω(u)⁻¹ L`, which scales translations by `a`. Finite
vectors are read through `finVec x = (0, α x)`, with `α` the idele of the Weil data.

## Main definitions and results

* `New.Space.ScalesTranslations`: the property of a `σ`-semilinear map to keep the finite part and
  to turn the finite translation by `x` into that by `b x`, while `σ` takes `selfDualAddChar E z` to
  `selfDualAddChar E (b b̄ z)`; `New.Space.ScalesTranslations.map_omega` is its law for `ω`, and
  `New.Space.ScalesTranslations.exists_map_schrodingerOp` its law for the vacuum and for the vectors
  `V.schrodingerOp R Ψ V.vacElem` with `Ψ` Schwartz–Bruhat at a set `R` of finite places.
* `New.multiplierRatio`: The factor `σ (Δ g) / Δ g`, for the multiplier `Δ = New.finMultiplier` of a
  finite unitary point `g`.

Notions from other files:
* `New.Space.ϱ`, `New.Space.ω`, `New.Space.vacElem`: The Heisenberg operators, the Weil
  representation and the vacuum vector of the space of data `New.𝒮 V`.
* `New.scalarFin` (`Lib.Weil.DualPair.FiniteAction`): the scalar matrices, as a homomorphism from
  the finite adeles of norm one to `Gf E n`.

## Relation to the literature

Known result: Galois action on CM theta functions and on the finite Weil representation. Here it is
stated for semilinear maps on the finite part of the data that scale the Heisenberg translations,
with an explicit factor; such a map is built from Taylor series of theta functions in
`New.UpperBound.Kernels.JetConjugatesAndBounds`. Source: G. Shimura, Theta functions with complex
multiplication, Duke Math. J. 43 (1976) 673-696; for the rationality of the Weil representation, J.
Trias, On the rationality of the Weil representation and the local theta correspondence, arXiv
2601.16141.
-/

noncomputable section

namespace New

open Matrix ComplexConjugate WeilData stdLattice Submodule Unitary Complex Space

unseal finitePart

variable {E : Type} [Field E] [CMType E] [WeilData E] {n : Type} [Fintype n] [DecidableEq n]
  {s : n → ℤˣ} {V : Space E n s} (σ : ℂ →+* ℂ) (g : Gf E n)

/-! ### The factor σΔ/Δ -/

/-- The factor `σ (Δ g) / Δ g`, for the multiplier `Δ = New.finMultiplier` of a finite unitary point
`g`. -/
noncomputable def multiplierRatio : ℂ := σ (finMultiplier g) / finMultiplier g

/-- An embedding `σ` of `ℂ` into itself fixes the product of the finite multiplier `Δ g` and its
conjugate, which is a natural number. -/
lemma map_finMultiplier_mul_conj :
    σ (finMultiplier g) * σ (conj (finMultiplier g)) =
      finMultiplier g * conj (finMultiplier g) := by
  -- `finMultiplier g * conj (finMultiplier g) = ‖finMultiplier g‖ ^ 2` is a lattice index, so a
  -- natural number (`norm_finMultiplier_sq`).
  simp [← map_mul, mul_conj', ← ofReal_pow, norm_finMultiplier_sq]

/-- Let E be a CM field with Weil data, σ a ring endomorphism of ℂ, and g a point of the finite
adelic unitary group `Gf E n`. Then the square of `multiplierRatio σ g` = σ(Δ g)/Δ g, where
Δ = `New.finMultiplier` is the multiplier of g, equals υ(det g)/σ(υ(det g)). Here `detFin 1 g` is
the determinant of g as a norm-one adele (that of (1, g) in G, all signs being 1), and
υ = `upsilonU1` is the splitting character of the Weil data restricted to norm-one ideles. -/
lemma multiplierRatio_sq :
    multiplierRatio σ g ^ 2 = upsilonU1.val (detFin 1 g) / σ (upsilonU1.val (detFin 1 g)) := by
  -- `conj (Δ g) / Δ g` is `υ (det g)`, and `σ` fixes `Δ g * conj (Δ g)`.
  have h_det : Unitary.toUnits (detFin 1 g) = finIdeleIncl g.val.det := by
    refine Units.ext (Prod.ext ?_ (G.det_snd (1, g)))
    exact (det_fst (1, g)).trans (funext fun w ↦ by simp)
  have h_ratio : conj (finMultiplier g) = upsilonU1.val (detFin 1 g) * finMultiplier g := by
    rw [upsilonU1_apply, h_det, upsilon_mul_finMultiplier]
  have h_norm : σ (finMultiplier g) ^ 2 * σ (upsilonU1.val (detFin 1 g)) =
      upsilonU1.val (detFin 1 g) * finMultiplier g ^ 2 := by
    have h_fixed := map_finMultiplier_mul_conj σ g
    rw [h_ratio, map_mul] at h_fixed
    linear_combination h_fixed
  rwa [multiplierRatio, div_pow, div_eq_div_iff (pow_ne_zero 2 (finMultiplier_ne_zero g)) (by simp)]

/-- As `σ` fixes the natural number `‖Δ g‖ ^ 2`, it takes `Δ g / ‖Δ g‖ ^ 2`, the constant in the
expansion of `ω(g) vacElem` into translates, to `σ (Δ g) / Δ g` (`multiplierRatio`) times itself.
Here `Δ = finMultiplier` is the multiplier of the Weil action at finite points. -/
lemma map_finMultiplier_div_norm_sq :
    σ (finMultiplier g / ‖finMultiplier g‖ ^ 2) =
      multiplierRatio σ g * (finMultiplier g / ‖finMultiplier g‖ ^ 2) := by
  have h_index : σ ((‖finMultiplier g‖ : ℂ) ^ 2) = (‖finMultiplier g‖ : ℂ) ^ 2 := by
    rw [← ofReal_pow, norm_finMultiplier_sq, ofReal_natCast, map_natCast]
  rw [map_div₀, h_index, multiplierRatio, div_mul_div_cancel₀ (finMultiplier_ne_zero g)]

/-! ### The scale is a unitary adele times a unit -/

variable {σ}

/-- Let `selfDualAddChar` be the additive character of the finite adeles for which `Ô` is self-dual.
If a ring endomorphism `σ` of `ℂ` takes `selfDualAddChar z` to `selfDualAddChar (t z)` for all `z`,
then `t` is a unit at every finite place. -/
lemma v_eq_one_of_map_selfDualAddChar {t : 𝔸f E}
    (hψ : ∀ z : 𝔸f E, σ (selfDualAddChar E z) = selfDualAddChar E (t * z))
    (w : FinPlace E) : Valued.v (t w) = 1 := by
  -- As `Ô` is its own dual under `selfDualAddChar`, `t z` is integral exactly when `z` is.
  have h_dual (z : 𝔸f E) : t * z ∈ Ô E ↔ z ∈ Ô E := by
    rw [← forall_selfDualAddChar_mul_eq_one_iff, ← forall_selfDualAddChar_mul_eq_one_iff z]
    simp_rw [mul_assoc t, ← hψ, map_eq_one_iff σ σ.injective]
  have h_single (z : 𝔸f E) (x : LocField w) :
      z * singleAdele w x ∈ Ô E ↔ Valued.v (x * z w) ≤ 1 := by
    rw [mem_Ô, ← and_forall_ne w]
    -- `map_mul` would split `Valued.v (x * z w)`, so it is left out.
    simp +contextual [mul_comm x, -map_mul]
  have h_local (x : LocField w) : Valued.v (x * t w) ≤ 1 ↔ Valued.v x ≤ 1 := by
    rw [← h_single, h_dual, ← one_mul (singleAdele w x), h_single]
    simp
  -- Test this with `x = 1` and with the inverse of a uniformiser.
  refine LE.le.eq_of_not_lt (by simpa using (h_local 1).2 (by simp)) ?_
  rw [← v_uniformizer_inv_mul_le_one_iff, h_local, ← mul_one (uniformizer w).val⁻¹,
    v_uniformizer_inv_mul_le_one_iff]
  simp

/-- If `R ∩ R̄ = ∅` and `b b̄` is a unit at every finite place, then `b` is the product of an adele
of norm one and a unit `a` of the ring `Ô` of integral finite adeles that equals 1 at the places of
`R` (`idem R` is the idempotent adele that is 1 exactly at `R`). -/
lemma exists_unitary_mul_unit {b : 𝔸f E} {R : Set (FinPlace E)} (hR : R.IsConjDisjoint)
    (hb : ∀ w : FinPlace E, Valued.v ((b * star b) w) = 1) :
    ∃ (u : unitary (𝔸f E)) (a : (Ô E)ˣ), b = u.val * a.val ∧ idem R * a.val = idem R := by
  -- A unit `x` of `Ô` has the norm of `b`. It is changed to a unit `a` of the same norm that is
  -- `1` on `R`, and then `u = b / a`.
  obtain ⟨x, hx⟩ : ∃ x : (Ô E)ˣ, star x.val.val * x.val.val = b * star b :=
    exists_unit_star_mul_self_eq (star_mul_star b b) hb
  -- `cut y` is `1` on `R`, `y ȳ` on `R̄` and `y` elsewhere; it is multiplicative and has
  -- the same norm as `y`.
  let e : 𝔸f E := idem R
  have h_idem : e * e = e := idem_mul_self R
  have h_idem_star : star e * star e = star e := by rw [← star_mul', h_idem]
  have h_disj : e * star e = 0 := idem_mul_star hR
  let cut (y : 𝔸f E) : 𝔸f E := y + e * (1 - y) - star (e * (1 - y)) * y
  have h_mem {y : 𝔸f E} (hy : y ∈ Ô E) : cut y ∈ Ô E :=
    have h_part : e * (1 - y) ∈ Ô E := mul_mem (idem_mem_Ô R) (sub_mem (one_mem _) hy)
    sub_mem (add_mem hy h_part) (mul_mem (star_mem_Ô h_part) hy)
  have h_norm (y : 𝔸f E) : cut y * star (cut y) = y * star y := by
    simp only [cut, star_sub, star_add, star_mul', star_star, star_one]
    grind -- uses that `e` and `star e` are orthogonal idempotents
  have h_mul (y z : 𝔸f E) : cut y * cut z = cut (y * z) := by
    simp only [cut, star_sub, star_mul', star_one]
    grind
  have h_cut_on (y : 𝔸f E) : e * cut y = e := by
    simp only [cut, star_mul']
    grind
  have h_inv : cut x.val * cut x⁻¹.val = 1 := by
    simp only [h_mul, ← Subring.coe_mul, x.mul_inv, Subring.coe_one]
    simp [cut]
  let a : (Ô E)ˣ := .mkOfMulEqOne ⟨_, h_mem x.val.2⟩ ⟨_, h_mem x⁻¹.val.2⟩ (Subtype.ext h_inv)
  -- `a` has the norm of `x`, which is that of `b`, so `b / a` has norm `1`.
  have h_norm_x : cut x.val * star (cut x.val) = b * star b := by rw [h_norm, mul_comm, hx]
  have h_unitary : b * cut x⁻¹.val * star (b * cut x⁻¹.val) = 1 := by
    rw [star_mul', mul_mul_mul_comm, ← h_norm_x, mul_mul_mul_comm, ← star_mul', h_inv, star_one,
      one_mul]
  have h_eq : b = b * cut x⁻¹.val * cut x.val := by
    rw [mul_assoc, mul_comm (cut x⁻¹.val), h_inv, mul_one]
  exact ⟨⟨b * cut x⁻¹.val, (mul_comm _ _).trans h_unitary, h_unitary⟩, a, h_eq, h_cut_on _⟩

/-! ### Maps that scale finite translations -/

omit [WeilData E] in
lemma scalarFin_mulVec (u : unitary (𝔸f E)) (x : n → 𝔸f E) :
    (scalarFin n u).val.val *ᵥ x = u.val • x := by
  simp [scalarFin]

/-- Let `Λ = stdLattice E n`. A unit `a` of the ring `Ô` of integral finite adeles permutes the
cosets of `Λ ∩ g⁻¹ Λ` in `Λ`. Hence it does not change the sum of the translates of the vacuum by
`g q` (`finHeisenbergOp` is the normalised finite Heisenberg operator), `q` running over these
cosets; this sum is `ω(g) vacElem` up to a scalar (`New.Space.omega_vacElem_sum`). -/
lemma Space.finsum_finHeisenbergOp_unit_smul (a : (Ô E)ˣ) (g : Gf E n) :
    ∑ᶠ q : stdLattice E n ⧸
        ((stdLattice E n).comap g.val.val.mulVecLin).addSubgroupOf (stdLattice E n),
      V.finHeisenbergOp (a.val.val • g.val.val *ᵥ q.out.val) V.vacElem =
    ∑ᶠ q : stdLattice E n ⧸
        ((stdLattice E n).comap g.val.val.mulVecLin).addSubgroupOf (stdLattice E n),
      V.finHeisenbergOp (g.val.val *ᵥ q.out.val) V.vacElem := by
  let Λ : AddSubgroup (n → 𝔸f E) := stdLattice E n
  let Λ' : AddSubgroup Λ := (Λ.comap g.val.val.mulVecLin).addSubgroupOf Λ
  -- Multiplication by `a` is an automorphism `mulUnit` of `Λ` that preserves `Λ' = Λ ∩ g⁻¹ Λ`.
  let mulUnit : Λ ≃+ Λ :=
    { toFun x := ⟨a.val.val • x.val, smul_mem_stdLattice a.val.2 x.2⟩
      invFun x := ⟨a⁻¹.val.val • x.val, smul_mem_stdLattice a⁻¹.val.2 x.2⟩
      left_inv x := Subtype.ext (inv_smul_smul a x.val)
      right_inv x := Subtype.ext (smul_inv_smul a x.val)
      map_add' x y := Subtype.ext (smul_add a.val.val x.val y.val) }
  have h_map : Λ'.map mulUnit = Λ' := AddSubgroup.ext fun x ↦ by
    rw [AddSubgroup.map_equiv_eq_comap_symm]
    change g.val.val *ᵥ a⁻¹.val.val • x.val ∈ Λ ↔ g.val.val *ᵥ x.val ∈ Λ
    rw [mulVec_smul]
    exact ⟨fun h ↦ by simpa [smul_smul, ← Subring.coe_mul] using smul_mem_stdLattice a.val.2 h,
      smul_mem_stdLattice a⁻¹.val.2⟩
  -- The term at a coset times `a` is the term at the coset moved by `mulUnit`.
  let perm : Λ ⧸ Λ' ≃+ Λ ⧸ Λ' := QuotientAddGroup.congr Λ' Λ' mulUnit h_map
  have h_term (q : Λ ⧸ Λ') : V.finHeisenbergOp (a.val.val • g.val.val *ᵥ q.out.val) V.vacElem =
      V.finHeisenbergOp (g.val.val *ᵥ (perm q).out.val) V.vacElem := by
    have h_rep : QuotientAddGroup.mk (mulUnit q.out) = perm q := congrArg perm q.out_eq'
    rw [← mulVec_smul]
    exact (V.finHeisenbergOp_mulVec_out_vacElem h_rep).symm
  exact finsum_eq_of_bijective perm perm.bijective h_term

/-- The `σ`-semilinear map `L` on the data of `V` scales finite translations by the finite adele
`b`: it keeps the finite part, spanned by the translates of the vacuum, and turns the translation by
`x` into that by `b x` there, and `σ` acts on the additive character `selfDualAddChar` as
multiplication by `b b̄` does. -/
structure Space.ScalesTranslations (V : Space E n s) (σ : ℂ →+* ℂ) (b : 𝔸f E)
    (L : 𝒮 V →ₛₗ[σ] 𝒮 V) : Prop where
  /-- `σ` takes `selfDualAddChar z` to `selfDualAddChar (b b̄ z)`. -/
  map_selfDualAddChar (z : 𝔸f E) : σ (selfDualAddChar E z) = selfDualAddChar E (b * star b * z)
  /-- `L` maps the finite part to itself. -/
  map_mem {f : 𝒮 V} (hf : f ∈ V.finitePart) : L f ∈ V.finitePart
  /-- On the finite part, `L ϱ(x) = ϱ(b x) L` for the finite vectors `finVec x`. -/
  map_rho {f : 𝒮 V} (hf : f ∈ V.finitePart) (x : n → 𝔸f E) :
    L (V.ϱ (finVec x) f) = V.ϱ (finVec (b • x)) (L f)

namespace Space.ScalesTranslations

variable {V : Space E n s} {σ : ℂ →+* ℂ} {b : 𝔸f E} {L : 𝒮 V →ₛₗ[σ] 𝒮 V} {f : 𝒮 V}

/-- Suppose the `σ`-semilinear map `L` on 𝒮(V) scales finite translations by `b`: it keeps the
finite part (the span of the translates of the vacuum under the finite Heisenberg operators), turns
the translation by `x` into that by `b x` there, and `σ` acts on `selfDualAddChar` as multiplication
by `b b̄` does. Then for `f` in the finite part, `L (finHeisenbergOp x f) = finHeisenbergOp (b x) (L
f)`, because `σ` takes the phase `semichar x` to `semichar (b x)`. Here `finHeisenbergOp x` is
`semichar x • ϱ (finVec x)`, with the phase `semichar x` = ψ(c₀ x*x / 2), c₀ = `traceOneAdele`. -/
lemma map_finHeisenbergOp (hL : V.ScalesTranslations σ b L) (hf : f ∈ V.finitePart) (x : n → 𝔸f E) :
    L (V.finHeisenbergOp x f) = V.finHeisenbergOp (b • x) (L f) := by
  have h_phase : σ (semichar x) = semichar (b • x) := by
    simp only [semichar, hL.map_selfDualAddChar, star_smul, smul_dotProduct, dotProduct_smul,
      smul_eq_mul]
    ring_nf
  simp only [finHeisenbergOp, _root_.smul_apply, map_smulₛₗ, h_phase, hL.map_rho hf]

/-- Let `L` be a `σ`-semilinear map on `𝒮 V` that scales finite translations by `u a`, where `a` is
a finite adele and `u` a finite adele of norm one. This means L keeps the finite part spanned by the
translates of the vacuum, turns the translation by x there into the translation by `u a x`, and σ
acts on `selfDualAddChar` as multiplication by (ua)(ua)‾ does. Then `ω(1, u⁻¹) ∘ L` scales finite
translations by `a`, where `ω` is the Weil representation and `scalarFin n u` is the scalar matrix u
in `Gf E n`. -/
lemma omega_inv_comp {u : unitary (𝔸f E)} {a : 𝔸f E} (hL : V.ScalesTranslations σ (u * a) L) :
    V.ScalesTranslations σ a ((V.ω (1, (scalarFin n u)⁻¹)).toLinearMap ∘ₛₗ L) where
  map_selfDualAddChar z := by
    rw [hL.map_selfDualAddChar, star_mul', mul_mul_mul_comm, mul_star_self_of_mem u.2, one_mul]
  map_mem hf := omega_mem_finitePart _ (hL.map_mem hf)
  map_rho {f} hf x := by
    have h_scalar : (scalarFin n u)⁻¹.val.val *ᵥ (u.val * a) • x = a • x := by
      simp [mul_smul, ← scalarFin_mulVec u]
    change V.ω (1, (scalarFin n u)⁻¹) (L (V.ϱ (finVec x) f)) =
      V.ϱ (finVec (a • x)) (V.ω (1, (scalarFin n u)⁻¹) (L f))
    rw [hL.map_rho hf, omega_rho, mulVec_finVec, ← h_scalar]
    rfl

/-- If `L` scales finite translations by a unit of the ring `Ô` of integral finite adeles, it sends
the vacuum vector `vacElem` to a multiple of itself. -/
lemma exists_map_vacElem_of_unit {a : (Ô E)ˣ} (hL : V.ScalesTranslations σ a.val.val L) :
    ∃ c : ℂ, L V.vacElem = c • V.vacElem := by
  -- The translations by the lattice fix the vacuum, hence its image.
  have h_fix (y : n → 𝔸f E) (hy : y ∈ stdLattice E n) :
      V.finHeisenbergOp y (L V.vacElem) = L V.vacElem :=
    calc _ = V.finHeisenbergOp (a.val.val • a⁻¹.val.val • y) (L V.vacElem) := by
          simp [smul_smul, ← Subring.coe_mul]
      _ = L (V.finHeisenbergOp (a⁻¹.val.val • y) V.vacElem) :=
        (hL.map_finHeisenbergOp vacElem_mem_finitePart _).symm
      _ = L V.vacElem := by rw [finHeisenbergOp_vacElem (smul_mem_stdLattice a⁻¹.val.2 hy)]
  simpa [Prod.mk_one_one] using exists_eq_smul_omega_vacElem (g := 1)
    (hL.map_mem vacElem_mem_finitePart) (by simpa using h_fix)

/-- If `L` scales finite translations by a unit of `Ô`, then `L ω(g) = (σ (Δ g) / Δ g) ω(g) L` on
the finite part, the span of the translates of the vacuum. Here `Δ = finMultiplier` is the
multiplier of the Weil representation `ω`, and `multiplierRatio σ g` is this factor. -/
lemma map_omega_of_unit {a : (Ô E)ˣ} (hL : V.ScalesTranslations σ a.val.val L) (g : Gf E n)
    (hf : f ∈ V.finitePart) :
    L (V.ω (1, g) f) = multiplierRatio σ g • V.ω (1, g) (L f) := by
  obtain ⟨c, hc⟩ := hL.exists_map_vacElem_of_unit
  -- For the vacuum, expand `ω(g) vacElem` into translates over the finitely many cosets of `Λ'`;
  -- `L` multiplies their sum by `c`, as `a` permutes the cosets.
  let Λ : AddSubgroup (n → 𝔸f E) := stdLattice E n
  let Λ' : AddSubgroup Λ := (Λ.comap g.val.val.mulVecLin).addSubgroupOf Λ
  have h_finite : Finite (Λ ⧸ Λ') :=
    Nat.finite_of_card_ne_zero (isCompact_stdLattice.relIndex_ne_zero_add
      (isOpen_stdLattice.preimage (f := g.val.val.mulVec) (by fun_prop)))
  have h_term (y : n → 𝔸f E) :
      L (V.finHeisenbergOp y V.vacElem) = c • V.finHeisenbergOp (a.val.val • y) V.vacElem := by
    rw [hL.map_finHeisenbergOp vacElem_mem_finitePart, hc, map_smul]
  have h_sum : L (∑ᶠ q : Λ ⧸ Λ', V.finHeisenbergOp (g.val.val *ᵥ q.out.val) V.vacElem) =
      c • ∑ᶠ q : Λ ⧸ Λ', V.finHeisenbergOp (g.val.val *ᵥ q.out.val) V.vacElem := by
    simp only [map_finsum L (Set.toFinite _), h_term]
    rw [← smul_finsum, finsum_finHeisenbergOp_unit_smul]
  have h_vac : L (V.ω (1, g) V.vacElem) = multiplierRatio σ g • V.ω (1, g) (L V.vacElem) := by
    rw [hc, map_smul, omega_vacElem_sum, map_smulₛₗ, h_sum, map_finMultiplier_div_norm_sq, mul_smul,
      smul_comm c]
  -- Both sides turn the translation by `x` into that by `a g x`, and the translates span.
  induction hf using span_induction with
  | mem _ h_gen =>
    obtain ⟨x, rfl⟩ := h_gen
    rw [omega_finHeisenbergOp, hL.map_finHeisenbergOp
      (omega_mem_finitePart g vacElem_mem_finitePart), h_vac,
      hL.map_finHeisenbergOp vacElem_mem_finitePart, omega_finHeisenbergOp, map_smul, mulVec_smul]
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul r x _ hx => simp [hx, smul_comm (σ r)]

omit [DecidableEq n] in
/-- Let `σ` take `selfDualAddChar z` to `selfDualAddChar (a ā z)`, where `a` is `1` on the set `R`
of places. Then `σ` takes the translate by `y` of the box function above `R` to its translate by
`a y`. Here `schrodingerAct R y` is the translation in the Schrödinger model at `R`,
`boxIndicator n R` the indicator of the vectors integral at `R`, and `idem R` the adele that is `1`
exactly at `R`. -/
lemma _root_.New.map_schrodingerAct_boxIndicator {a : 𝔸f E} {R : Set (FinPlace E)}
    (hψ : ∀ z : 𝔸f E, σ (selfDualAddChar E z) = selfDualAddChar E (a * star a * z))
    (ha : idem R * a = idem R) (y : n → 𝔸f E) :
    σ ∘ schrodingerAct R y (boxIndicator n R) = schrodingerAct R (a • y) (boxIndicator n R) := by
  -- Above `R` the vectors `y` and `a y` agree, so only the character sees the change.
  ext x
  have h_cut (z : n → 𝔸f E) : idem R • (z + a • y) = idem R • (z + y) := by simp [smul_smul, ha]
  have h_box : σ (boxIndicator n R (x + y)) = boxIndicator n R (x + a • y) := by
    classical
    simp [integralBox, smul_smul, ha, apply_ite σ]
  have h_phase : a * star a * (half * star y ⬝ᵥ idem R • (x + (x + y))) =
      half * star (a • y) ⬝ᵥ idem R • (x + (x + a • y)) := by
    rw [← add_assoc, ← add_assoc, h_cut, star_smul, smul_dotProduct, dotProduct_smul]
    linear_combination (star a * half * star y ⬝ᵥ (x + x + y)) * ha
  simp only [schrodingerAct, Function.comp_apply, LinearMap.pi_apply, LinearMap.smul_apply,
    LinearMap.proj_apply, smul_eq_mul, map_mul, hψ, h_phase, h_box]

/-- Let `L` scale finite translations by an adele `a` that is `1` on a set `R` of places disjoint
from its conjugate, and let `L vacElem = c vacElem`, `vacElem` being the vacuum vector. Then
`L (Ψ ⊗ vacElem) = c ((σ ∘ Ψ) ⊗ vacElem)` for `Ψ` Schwartz–Bruhat at the places of `R`. Here
`Ψ ⊗` is `V.schrodingerOp R Ψ`, the operator on data with component `Ψ` at these places. -/
lemma map_schrodingerOp_of_map_vacElem {a : 𝔸f E} (hL : V.ScalesTranslations σ a L)
    {R : Set (FinPlace E)} (hR : R.IsConjDisjoint) (ha : idem R * a = idem R) {c : ℂ}
    (hc : L V.vacElem = c • V.vacElem) {Ψ : (n → 𝔸f E) → ℂ} (hΨ : IsSchwartzBruhat R Ψ) :
    L (V.schrodingerOp R Ψ V.vacElem) = c • V.schrodingerOp R (σ ∘ Ψ) V.vacElem := by
  -- `Ψ` is a combination of translates of the box function, which name the translates of the
  -- vacuum by `ϱ` (`schrodingerOp_schrodingerAct_boxIndicator`); `L` scales both by `a`.
  obtain ⟨d, rfl : ∑ y ∈ d.support, d y • schrodingerAct R y (boxIndicator n R) = Ψ⟩ :=
    mem_range_schrodingerCombination hR hΨ
  have h_term (y : n → 𝔸f E) :
      L (V.schrodingerOp R (schrodingerAct R y (boxIndicator n R)) V.vacElem) =
        c • V.schrodingerOp R (schrodingerAct R (a • y) (boxIndicator n R)) V.vacElem := by
    rw [schrodingerOp_schrodingerAct_boxIndicator hR, schrodingerOp_schrodingerAct_boxIndicator hR,
      projOn_vacElem, hL.map_rho vacElem_mem_finitePart, hc, map_smul, smul_comm a]
  have h_sum : σ ∘ ∑ y ∈ d.support, d y • schrodingerAct R y (boxIndicator n R) =
      ∑ y ∈ d.support, σ (d y) • schrodingerAct R (a • y) (boxIndicator n R) := by
    simp [funext_iff, ← map_schrodingerAct_boxIndicator hL.map_selfDualAddChar ha]
  simp [h_sum, h_term, Finset.smul_sum, smul_comm c]

/-- For `R` disjoint from its conjugate, the scale `b` is a unitary adele times a unit of `Ô` that
is `1` on `R`. -/
lemma exists_eq_unitary_mul_unit (hL : V.ScalesTranslations σ b L) {R : Set (FinPlace E)}
    (hR : R.IsConjDisjoint) :
    ∃ (u : unitary (𝔸f E)) (a : (Ô E)ˣ), b = u.val * a.val ∧ idem R * a.val = idem R :=
  exists_unitary_mul_unit hR (v_eq_one_of_map_selfDualAddChar hL.map_selfDualAddChar)

/-- Suppose the `σ`-semilinear map `L` on 𝒮(V) scales finite translations by the finite adele `b`:
it keeps the finite part spanned by the translates of the vacuum, turns the translation by `x` into
that by `b x` there, and `σ` acts on `selfDualAddChar` as multiplication by `b b̄` does. Then `b` is
a unit of the finite adeles. -/
lemma isUnit (hL : V.ScalesTranslations σ b L) : IsUnit b := by
  obtain ⟨u, a, rfl, -⟩ := hL.exists_eq_unitary_mul_unit (R := ∅) disjoint_bot_left
  exact isUnit_coe.mul (a.isUnit.map (Ô E).subtype)

/-- Let `L` be a `σ`-semilinear map on the data of `V` that scales finite translations by the finite
adele `b`: it preserves the finite part (spanned by the translates of the vacuum), turns translation
by `x` into translation by `b x` there, and `σ` acts on `selfDualAddChar` as multiplication by
`b b̄` does. Then for a finite point `g` and `f` in the finite part,
`L (ω(1, g) f) = (σ (Δ g) / Δ g) • ω(1, g) (L f)`, where `Δ = finMultiplier` is the multiplier of
the Weil representation. This is the Galois law for the finite Weil representation. -/
theorem map_omega (hL : V.ScalesTranslations σ b L) (g : Gf E n) (hf : f ∈ V.finitePart) :
    L (V.ω (1, g) f) = multiplierRatio σ g • V.ω (1, g) (L f) := by
  -- Write `b = u a`; the law holds for `ω(u)⁻¹ L`, and `u` is central.
  obtain ⟨u, a, rfl, -⟩ := hL.exists_eq_unitary_mul_unit (R := ∅) disjoint_bot_left
  have h_unit : V.ω (1, (scalarFin n u)⁻¹) (L (V.ω (1, g) f)) =
      multiplierRatio σ g • V.ω (1, g) (V.ω (1, (scalarFin n u)⁻¹) (L f)) :=
    hL.omega_inv_comp.map_omega_of_unit g hf
  simpa [rep_apply_apply, (Seesaw.commute_scalarFin g).left_comm, Prod.mk_one_one] using
    congrArg (V.ω (1, scalarFin n u)) h_unit

/-- Let `L` be `σ`-semilinear and scale finite translations, and let `R` be a set of places disjoint
from its conjugate. There are a number `c` and a unitary adele `u`, acting as a scalar matrix, with
`L vacElem = c ω(u) vacElem` and `L (Ψ ⊗ vacElem) = c ω(u) ((σ ∘ Ψ) ⊗ vacElem)` for all `Ψ`
Schwartz–Bruhat above `R`, where `Ψ ⊗` is `V.schrodingerOp R Ψ`. -/
theorem exists_map_schrodingerOp (hL : V.ScalesTranslations σ b L) {R : Set (FinPlace E)}
    (hR : R.IsConjDisjoint) :
    ∃ (c : ℂ) (u : unitary (𝔸f E)),
      L V.vacElem = c • V.ω (1, scalarFin n u) V.vacElem ∧
      ∀ Ψ : (n → 𝔸f E) → ℂ, IsSchwartzBruhat R Ψ →
        L (V.schrodingerOp R Ψ V.vacElem) = c • V.ω (1, scalarFin n u)
          (V.schrodingerOp R (σ ∘ Ψ) V.vacElem) := by
  -- Write `b = u a` with `a = 1` on `R`, and apply `ω(u)` to the laws for `ω(u)⁻¹ L`.
  obtain ⟨u, a, rfl, ha⟩ := hL.exists_eq_unitary_mul_unit hR
  obtain ⟨c, hc⟩ := hL.omega_inv_comp.exists_map_vacElem_of_unit
  have h_move {f f' : 𝒮 V} (h : V.ω (1, (scalarFin n u)⁻¹) (L f) = c • f') :
      L f = c • V.ω (1, scalarFin n u) f' := by
    simpa [rep_apply_apply, Prod.mk_one_one] using congrArg (V.ω (1, scalarFin n u)) h
  exact ⟨c, u, h_move hc, fun Ψ hΨ ↦ h_move
    (hL.omega_inv_comp.map_schrodingerOp_of_map_vacElem hR ha hc hΨ)⟩

end Space.ScalesTranslations

end New

end
