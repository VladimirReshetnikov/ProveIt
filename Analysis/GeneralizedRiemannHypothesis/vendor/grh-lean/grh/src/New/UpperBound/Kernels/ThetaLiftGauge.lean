import Lib.Weil.DualPair.KernelLaws
import New.Derivatives.Vacuum.Divisibility
import New.UpperBound.Kernels.JetConjugatesAndBounds

/-!
# p-adic gauge bounds for one theta lift and data from functions modulo an ideal

This file derives `p`-adic bounds for one theta lift between the definite spaces with index types
`n` and `n'` from bounds on jets. A function `Ψ` on `n' × n` matrices modulo a modulus `𝔪`, put at
the places dividing `𝔪` with the integral vacuum elsewhere, gives a datum. If the values of `Ψ` are
integral away from `q`, an integer multiple of this datum is a standard datum at the primes not
dividing `q`.

## Main definitions and results

* `New.Kernel.raises`: the additive monoid of data that multiply gauges by at most `max c 0`.
* `New.Parameters.omega_mem_raises_of_schurJet_le`: a standard datum translated by `(1, x * d * y)`,
  with `d` diagonal at the places above `p` that define the gauge and `x`, `y` integral above `p`,
  raises gauges by at most `max B 0` for any bound `B` on the weighted entries of the jet matrices.
* `New.Parameters.mem_raises_of_standardData`: an explicit bound for a standard datum itself.
* `New.Parameters.smul_mem_raises_of_dvd`: if a multiple of a datum is standard and the scale is
  `p`-integral, an explicit larger multiple of the datum does not increase the gauges.
* `New.Parameters.smul_vacuumDatum_mem_standardData`: if `q * N` lies in `𝔪` and the values of `Ψ`
  are integral away from `q`, an explicit integer multiple of the datum is a standard datum at every
  prime `l` prime to `q`.
* `New.Parameters.isVacuumCombination_vacuumDatum`: the datum is a combination of translates of the
  scaled vacuum by finite adelic vectors, with coefficients of controlled size.

Notions from other files:
* `New.Kernel`: an abstract theta kernel, that is, a representation `ω` of the finite points of the
  two unitary groups on data and an equivariant map `jetMap` from data to linear maps.
* `New.thetaKernel`: the theta kernel of the definite pair `stdSpace E n`, `stdSpace E n'`; its jet
  matrix is `schurJet κ (jetSeries _ c f)`, with derivatives scaled by `c`.
* `New.weylGauge`: the `p`-adic sup norm of `g⁻¹` applied to `ιₚ ∘ ξ`, where `ιₚ : ℂ →+* ℂ_[p]` is
  the chosen `p`-adic place.
* `New.Parameters.standardData`: the span, over the ring of the complex `z` with `‖ιₚ z‖ ≤ 1`, of
  the translates of the integral vacuum `intVacuum V = vacuumScale ^ card n • V.vacElem` by the
  vectors that `δ` makes integral above `p`.
* `New.Seesaw.IsAdmissibleCombination`: a finite linear combination with conditions on the support,
  the denominators and the size of the conjugates of its coefficients.

## Relation to the literature

See `New.UpperBound.Divisibility.LocalDivisibility` and
`New.UpperBound.Kernels.JetConjugatesAndBounds` for related work.
-/

/-! ## Standard data and the p-adic gauge of a theta kernel -/

section OneLift

open New G Matrix Function Kernel Fintype NeZero Parameters IsUltrametricDist

variable {P : Parameters} {s : ℕ}
  {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  {κ : NumberField.InfinitePlace (P.E s) → ℕ → ℕ} {e ea eb : NumberField.InfinitePlace (P.E s) → ℤ}

section Raises

variable {c : ℝ} {K : Subgroup (Gf (P.E s) n)} {p : ℕ} [Fact p.Prime] [PadicPlace p]
  {S : Type*} [AddCommGroup S] [Module ℂ S] (k : Kernel n n' κ e ea K S)

/-- The `p`-adic gauge `New.weylGauge` is ultrametric in the vector. -/
lemma New.weylGauge_add_le_max (g : Gf (P.E s) n) (ξ η : WeylIndex n κ → ℂ) :
    weylGauge κ e g (ξ + η) ≤ max (weylGauge κ e g ξ) (weylGauge κ e g η) := by
  have h_add : ιₚ ∘ (ξ + η) = ιₚ ∘ ξ + ιₚ ∘ η := funext fun i ↦ map_add ιₚ (ξ i) (η i)
  simpa only [weylGauge, h_add, mulVec_add] using norm_add_le_max _ _

/-- The data `Φ` whose kernel multiplies the `p`-adic gauge by at most `c`: for all `g`, `h` and
`ξ`, the gauge at `h * d'` of `jetMap (ω (g, h) Φ) ξ` is at most `max c 0` times the gauge at
`g * d` of `ξ`. The factor is `max c 0` so that `0` is a member for every real `c`; sums stay inside
because the gauge is ultrametric. -/
def New.Kernel.raises (d : Gf (E P s) n) (d' : Gf (E P s) n') (c : ℝ) : AddSubmonoid S where
  carrier :=
    {Φ : S | ∀ (g : Gf (P.E s) n) (h : Gf (P.E s) n') (ξ : WeylIndex n κ → ℂ),
      weylGauge κ ea (h * d') (k.jetMap (k.ω (g, h) Φ) ξ) ≤ max c 0 * weylGauge κ e (g * d) ξ}
  add_mem' hΦ hΨ g h ξ := by
    simp only [map_add, LinearMap.add_apply]
    exact (weylGauge_add_le_max _ _ _).trans (max_le (hΦ g h ξ) (hΨ g h ξ))
  zero_mem' := by simp [weylGauge, mul_nonneg]

/-- Let `k` be a theta kernel with data in `S`: the pairs of finite adelic points of rank `n`, `n'`
over the CM field `P.E s` act on `S` by `k.ω`, and `k.jetMap` sends a datum to a linear map from
vectors of weight `(κ, e)` in rank `n` to vectors of weight `(κ, ea)` in rank `n'`. Thus
`Φ ∈ k.raises d d' B` says that for all points `g`, `h` and vectors `ξ` the gauge at `h * d'` of
`jetMap (ω (g, h) Φ) ξ` is at most `max B 0` times the gauge at `g * d` of `ξ`. If this holds and
`‖ιₚ z‖ * B ≤ B'` for a complex number `z`, then it holds for `z • Φ` with `B'` in place of `B`. -/
lemma New.Kernel.smul_mem_raises {B : ℝ} {K : Subgroup (Gf (P.E s) n)}
    {p : ℕ} [Fact p.Prime] [PadicPlace p] {S : Type*} [AddCommGroup S] [Module ℂ S]
    (k : Kernel n n' κ e ea K S) {B' : ℝ} {Φ : S} {d : Gf (P.E s) n} {d' : Gf (P.E s) n'} {z : ℂ}
    (hΦ : Φ ∈ k.raises (p := p) d d' B) (hz : ‖(ιₚ z : ℂ_[p])‖ * B ≤ B') :
    z • Φ ∈ k.raises (p := p) d d' B' := by
  intro g g' ξ
  have h_nonneg : 0 ≤ weylGauge κ e (g * d) ξ := by simp [weylGauge]
  -- The kernel is linear in `Φ`, and `z` scales the gauge by `‖ιₚ z‖`.
  calc
    _ = ‖ιₚ z‖ * weylGauge κ ea (g' * d') (k.jetMap (k.ω (g, g') Φ) ξ) := by simp [weylGauge_smul]
    _ ≤ ‖ιₚ z‖ * (max B 0 * weylGauge κ e (g * d) ξ) := by grw [hΦ g g' ξ]
    _ = max (‖ιₚ z‖ * B) 0 * weylGauge κ e (g * d) ξ := by simp [← mul_assoc, mul_max_of_nonneg]
    _ ≤ _ := by grw [hz]

/-- Translating the datum by `(g₀, h₀)` amounts to translating the two base points: the translate
`k.ω (g₀, h₀) Φ` is in `k.raises (g₀ * d) (h₀ * d') B` exactly when `Φ` is in `k.raises d d' B`. -/
lemma New.Kernel.omega_mem_raises_iff {K : Subgroup (Gf (P.E s) n)}
    {p : ℕ} [Fact p.Prime] [PadicPlace p] {S : Type*} [AddCommGroup S] [Module ℂ S]
    (k : Kernel n n' κ e ea K S) {B : ℝ} {Φ : S} {d g₀ : Gf (P.E s) n} {d' h₀ : Gf (P.E s) n'} :
    k.ω (g₀, h₀) Φ ∈ k.raises (p := p) (g₀ * d) (h₀ * d') B ↔ Φ ∈ k.raises (p := p) d d' B := by
  -- `ω(g, h) ω(g₀, h₀) = ω(g g₀, h h₀)`, and `(g, h) ↦ (g g₀, h h₀)` is a bijection.
  refine ⟨fun hΦ g h ξ ↦ ?_, fun hΦ g h ξ ↦ ?_⟩
  · simpa only [k.omega_omega, Prod.mk_mul_mk, mul_assoc, inv_mul_cancel_left, inv_mul_cancel,
    mul_one]
      using hΦ (g * g₀⁻¹) (h * h₀⁻¹) ξ
  · simpa only [k.omega_omega, Prod.mk_mul_mk, mul_assoc] using hΦ (g * g₀) (h * h₀) ξ

end Raises

/-- The weight of the row `i` for diagonal matrices `u τ` over `ℂ_[p]` and exponents `e τ`: the
product over the places `τ` of `‖det (diagonal (u τ))‖ ^ e τ` and of the `‖u τ b‖` over the boxes of
the filling `i τ`, where `b` is the index in the box. -/
noncomputable def New.diagonalWeight {p : ℕ} [Fact p.Prime]
    (e : NumberField.InfinitePlace (P.E s) → ℤ)
    (u : NumberField.InfinitePlace (P.E s) → n → ℂ_[p]) (i : WeylIndex n κ) : ℝ :=
  ∏ τ : NumberField.InfinitePlace (P.E s),
    (∏ b : n, ‖u τ b‖) ^ e τ *
      ∏ h : Fin (card n), ∏ j : Fin (κ τ h), ∏ t : Fin h, ‖u τ ((i τ).val h j t)‖

lemma New.diagonalWeight_nonneg {p : ℕ} [Fact p.Prime]
    (e : NumberField.InfinitePlace (P.E s) → ℤ)
    (u : NumberField.InfinitePlace (P.E s) → n → ℂ_[p]) (i : WeylIndex n κ) :
    0 ≤ diagonalWeight e u i := by
  unfold diagonalWeight
  positivity

lemma New.diagonalWeight_one {p : ℕ} [Fact p.Prime]
    (e : NumberField.InfinitePlace (P.E s) → ℤ) (i : WeylIndex n κ) :
    diagonalWeight e (1 : NumberField.InfinitePlace (P.E s) → n → ℂ_[p]) i = 1 := by
  simp [diagonalWeight]

namespace New.Parameters

/-- Let `a`, `b` be automorphic characters of the CM field `E = P.E s` with exponents `ea`, `eb` at
the infinite places and tame parts `ψ`, `ψ'` at the finite ones (`AutChar.HasWeight`). The standard
data for `δ` on the space of maps between the standard definite hermitian spaces `stdSpace E n`,
`stdSpace E n'` are the combinations, with coefficients `z` such that `‖ιₚ z‖ ≤ 1`, of the
translates of the integral vacuum (`intVacuum`) by the vectors that `δ` makes integral above `p`.
The Weil action `New.pairWeil` of a pair `(g, h)` of finite adelic points integral above `p`
preserves these data. Here `(1, g)` is the adelic point with trivial infinite part and finite part
`g`. -/
lemma pairWeil_mem_standardData {a b : AutChar (E P s)}
    {ψ ψ' : (w : FinPlace (P.E s)) → MulChar (ResField w) ℂ} {p : ℕ} [Fact p.Prime] [PadicPlace p]
    {δ : NumberField.RingOfIntegers P.K}
    {f : 𝒮 ((stdSpace (P.E s) n).hom (stdSpace (P.E s) n'))} (ha : a.HasWeight ea ψ)
    (hb : b.HasWeight eb ψ')
    (hf : f ∈ standardData ((stdSpace (E P s) n).hom (stdSpace (E P s) n')) δ) {g : Gf (P.E s) n}
    {h : Gf (P.E s) n'} (hg : g ∈ integralAbove n p) (hh : h ∈ integralAbove n' p) :
    pairWeil (stdSpace (E P s) n) (stdSpace (E P s) n') a b ((1, g), 1, h) f ∈
      standardData ((stdSpace (E P s) n).hom (stdSpace (E P s) n')) δ := by
  -- `pairWeil` is `ω` at a point that is finite (`onHom_fin`) and integral above `p`, times values
  -- of the characters `a` and `b`, which are `p`-adic units.
  have h_char :
      ‖ιₚ (pairChar a b (((1, g), 1, h) : G (P.E s) (1 : n → ℤˣ) × G (P.E s) 1))‖ ≤ 1 := by
    simp [ha.norm_apply_detFin_eq_one hh, hb.norm_apply_detFin_eq_one hg]
  have h_int : (onHom (((1, g), 1, h) : G (P.E s) (1 : n → ℤˣ) × G (P.E s) (1 : n' → ℤˣ))).2 ∈
      integralAbove (n' × n) p := by
    simp_all [localLevel]
  change (⟨pairChar a b ((1, g), 1, h), h_char⟩ : embValRing) •
    ((stdSpace (P.E s) n).hom (stdSpace (P.E s) n')).ω (onHom ((1, g), 1, h)) f ∈ _
  refine Submodule.smul_mem _ _ ?_
  rw [onHom_fin g h]
  exact omega_mem_standardData h_int hf

/-- Let `E = P.E s` (a CM field) and `Gf` its finite adelic unitary group. Take the theta kernel
(`thetaKernel`) of scale `c` and level `K`, for the standard definite spaces of ranks `n`, `n'` over
`E`. Its characters `a`, `b` have exponents `ea`, `eb`, and its weight `(κ, e)` has `κ τ h` columns
of height `h` at `τ` and lifts from rank `n` to `n'` (`IsLiftWeight`). Let `Ψ`, in the span
`finitePart` of vacuum translates, be standard for `δ`: a `p`-integral combination of translates of
the integral vacuum by points that `δ` makes integral above `p`. Let `x`, `y` in `Gf` be integral
above `p`. Suppose that, for each infinite place `τ`, the embedding `z ↦ ιₚ (Φ_τ (conj z))` of `E`
(`weightEmbedding`), extended to finite adeles (`adeleExtension`) and applied entrywise, sends `d`
to the diagonal matrix `u τ`, and that for every standard `f` and entry `(i', i)` of its jet matrix,
`‖ιₚ entry‖` times `diagonalWeight ea u i'` is at most `B`.

Then the translate `ω (1, x * d * y) Ψ` lies in `raises 1 1 B`: for all finite points `g`, `h`,
applying it after translation by `(g, h)` to a vector `ξ` gives a vector of gauge at `h` at most
`max B 0` times the gauge of `ξ` at `g`. -/
lemma omega_mem_raises_of_schurJet_le {c : ℂ} {K : Subgroup (Gf (P.E s) n)}
    {a b : AutChar (E P s)} {ψ ψ' : (w : FinPlace (P.E s)) → MulChar (ResField w) ℂ}
    {ha : a.HasWeight ea ψ} {hb : b.HasWeight eb ψ'}
    {p : ℕ} [Fact p.Prime] [PadicPlace p] {hκ : IsLiftWeight n n' κ eb e}
    {Ψ : ↥((stdSpace (P.E s) n).hom (stdSpace (P.E s) n')).finitePart}
    {δ : NumberField.RingOfIntegers P.K}
    (hΨ : Ψ.val ∈ standardData ((stdSpace (E P s) n).hom (stdSpace (E P s) n')) δ)
    {x d y : Gf (P.E s) n'} (hx : x ∈ integralAbove n' p) (hy : y ∈ integralAbove n' p)
    {u : NumberField.InfinitePlace (E P s) → n' → ℂ_[p]}
    (hu : ∀ τ : NumberField.InfinitePlace (P.E s),
      (d : GL n' (𝔸f (P.E s))).val.map (adeleExtension (weightEmbedding ιₚ τ)) = diagonal (u τ))
    {B : ℝ}
    (h_bound : ∀ f ∈ standardData ((stdSpace (E P s) n).hom (stdSpace (E P s) n')) δ,
      ∀ (i' : WeylIndex n' κ) (i : WeylIndex n κ),
      diagonalWeight ea u i' *
        ‖ιₚ
          (schurJet κ (((stdSpace (E P s) n).hom (stdSpace (E P s) n')).jetSeries c f) i' i)‖ ≤ B) :
    (thetaKernel hκ c ha hb K).ω (1, x * d * y) Ψ ∈ (thetaKernel hκ c ha hb K).raises 1 1 B := by
  -- Gauges do not change under rational points acting on both the point and the vector, nor under
  -- points integral above `p` on the right. This moves the two gauges to `d⁻¹` and `1`, where the
  -- claim is an entrywise bound.
  let V : Space (P.E s) (n' × n) (homSigns 1 1) := (stdSpace (P.E s) n).hom (stdSpace (P.E s) n')
  let k : Kernel n n' κ e ea K V.finitePart := thetaKernel hκ c ha hb K
  intro g g' ξ
  -- Weak approximation: `g₀ = γ * g`, `g₁ = ε * (g' * x * d)` and `d * g₁ * d⁻¹` are integral
  -- above `p` for suitable rational `γ`, `ε`.
  obtain ⟨γ, hγ, -⟩ := exists_mul_mem_integralAbove p g 1
  obtain ⟨ε, hε, hεd⟩ := exists_mul_mem_integralAbove p (g' * x * d) d
  set g₀ : Gf (P.E s) n := (stdSpace (P.E s) n).embFin γ * g with hg₀
  set g₁ : Gf (P.E s) n' := (stdSpace (P.E s) n').embFin ε * (g' * x * d) with hg₁
  set Ψ' : V.finitePart := k.ω (g₀, g₁ * y) Ψ with hΨ'
  have h_std : Ψ'.val ∈ standardData V δ := pairWeil_mem_standardData ha hb hΨ hγ (mul_mem hε hy)
  set η : WeylIndex n κ → ℂ := (stdSpace (P.E s) n).weightRep κ e γ ξ
  -- At `weightEmbedding ιₚ τ` the point `d` acts by a diagonal matrix, so the operator from the
  -- gauge at `1` to the gauge at `d⁻¹` is the jet matrix with its rows scaled by the weights.
  let A : Matrix (WeylIndex n' κ) (WeylIndex n κ) ℂ_[p] :=
    (∏ τ : NumberField.InfinitePlace (P.E s), (∏ b : n', u τ b) ^ ea τ) •
      (diagonal (fun i' : WeylIndex n' κ ↦ ∏ τ, ∏ h, ∏ j, ∏ t, u τ ((i' τ).val h j t)) *
        (schurJet κ (V.jetSeries c Ψ'.val)).map ιₚ)
  have hA (i' : WeylIndex n' κ) (i : WeylIndex n κ) : ‖A i' i‖ ≤ max B 0 :=
    le_max_of_le_left <| by
      simpa [A, diagonalWeight, Finset.prod_mul_distrib, mul_assoc]
        using h_bound Ψ'.val h_std i' i
  calc weylGauge κ ea (g' * 1) (k.jetMap (k.ω (g, g') (k.ω (1, x * d * y) Ψ)) ξ)
    _ = weylGauge κ ea ((stdSpace (P.E s) n').embFin ε * g') (k.jetMap Ψ' η) := by
      rw [← weylGauge_embFin (γ := ε), ← k.equivariant γ ε]
      simp [hΨ', hg₀, hg₁, k.omega_omega, mul_assoc, η]
    _ = weylGauge κ ea d⁻¹ (k.jetMap Ψ' η) := by
      rw [← weylGauge_mul_of_mem_integralAbove (hk := div_mem hx hεd)]
      simp [hg₁, ← mul_assoc, div_eq_mul_inv]
    _ = ‖A *ᵥ ιₚ ∘ η‖ := by
      simp [A, V, k, thetaKernel, ιₚ.map_mulVec, weylGauge, comp_def, weylRep, hu, Units.smul_def,
        schur_diagonal_eq_prod]
    _ ≤ max B 0 * ‖ιₚ ∘ η‖ := norm_mulVec_le_of_nonneg (le_max_right B 0) hA _
    _ = max B 0 * weylGauge κ e 1 η := by simp [weylGauge, weylRep]
    _ = max B 0 * weylGauge κ e (g * 1) ξ := by
      rw [← weylGauge_embFin (g := g * 1) (γ := γ), ← weylGauge_mul_of_mem_integralAbove (hk := hγ),
        one_mul, mul_one]

/-- Take the theta kernel (`New.thetaKernel`) of scale `c`, at any level `K`, of the standard
definite spaces of ranks `n`, `n'` over the CM field `E = P.E s`, with characters `a`, `b` of
exponents `ea`, `eb`, and weight `(κ, e)` lifting from rank `n` to rank `n'` (`IsLiftWeight`). Let
`Ψ` be a standard datum for `δ`, and let `x`, `y` be finite points integral above `p`. Suppose that,
for each infinite place `τ`, the embedding `z ↦ ιₚ (Φ_τ (conj z))` of `E` (`weightEmbedding`) sends
`d` to the diagonal matrix `u τ`, and that for every standard `f`, every filling `i'` and all
`p`-integral `w τ col l`, the jet of the Taylor series `jetSeries c f` along the polynomial
`minorProd i' w` has norm at most `B` after multiplication by `diagonalWeight ea u i'`. This
polynomial is the product, over the places and the columns of height `h < card n'` of `κ`, of the
minors of the matrices `Z τ * w τ` on the rows listed in that column of `i'` and the columns
`l < h`. The weight is the product over `τ` of `‖det (u τ)‖ ^ ea τ` and of the `‖u τ b‖` over the
entries `b` of the filling.

Then the translate of `Ψ` by `(1, x * d * y)` multiplies the `p`-adic gauge `New.weylGauge` by at
most `max B 0`. -/
lemma omega_mem_raises_of_jet_minorProd_le {c : ℂ} {K : Subgroup (Gf (P.E s) n)}
    {a b : AutChar (E P s)} {ψ ψ' : (w : FinPlace (P.E s)) → MulChar (ResField w) ℂ}
    {ha : a.HasWeight ea ψ} {hb : b.HasWeight eb ψ'}
    {p : ℕ} [Fact p.Prime] [PadicPlace p] {hκ : IsLiftWeight n n' κ eb e}
    {Ψ : ↥((stdSpace (P.E s) n).hom (stdSpace (P.E s) n')).finitePart}
    {δ : NumberField.RingOfIntegers P.K}
    (hΨ : Ψ.val ∈ standardData ((stdSpace (E P s) n).hom (stdSpace (E P s) n')) δ)
    {x d y : Gf (P.E s) n'} (hx : x ∈ integralAbove n' p) (hy : y ∈ integralAbove n' p)
    {u : NumberField.InfinitePlace (E P s) → n' → ℂ_[p]}
    (hu : ∀ τ : NumberField.InfinitePlace (P.E s),
      (d : GL n' (𝔸f (P.E s))).val.map (adeleExtension (weightEmbedding ιₚ τ)) = diagonal (u τ))
    {B : ℝ}
    (h_bound : ∀ f ∈ standardData ((stdSpace (E P s) n).hom (stdSpace (E P s) n')) δ,
      ∀ (i' : WeylIndex n' κ) (w : P.Φ s → n → ℕ → valRingCp p),
      diagonalWeight ea u i' *
        ‖jet ℂ_[p] (minorProd i' fun (τ : P.Φ s) (col : n) (l : ℕ) ↦ (w τ col l : ℂ_[p]))
          ((((stdSpace (E P s) n).hom (stdSpace (E P s) n')).jetSeries c f).map ιₚ)‖ ≤ B) :
    (thetaKernel hκ c ha hb K).ω (1, x * d * y) Ψ ∈ (thetaKernel hκ c ha hb K).raises 1 1 B := by
  -- An entry of the jet matrix is bounded by the jet along a product of minors with the same rows.
  refine omega_mem_raises_of_schurJet_le hΨ hx hy hu fun f hf i' i ↦ ?_
  set F : MvPowerSeries (P.Φ s × n' × n) ℂ :=
    ((stdSpace (E P s) n).hom (stdSpace (E P s) n')).jetSeries c f
  obtain ⟨w, hw⟩ : ∃ w : P.Φ s → n → ℕ → valRingCp p, ‖schurJet κ (F.map ιₚ) i' i‖ ≤
      ‖jet ℂ_[p] (minorProd i' fun τ col l ↦ (w τ col l : ℂ_[p])) (F.map ιₚ)‖ :=
    exists_norm_schurJet_le_norm_jet_minorProd hκ.1 (F.map ιₚ) i' i
  rw [map_schurJet hκ]
  exact (mul_le_mul_of_nonneg_left hw (diagonalWeight_nonneg ea u i')).trans (h_bound f hf i' w)

/-- Take the theta kernel (`New.thetaKernel`) of scale `c * P.jetScale s`, at any level `K`, of the
standard definite spaces of ranks `n`, `n'` over the CM field `P.E s`, with characters `a`, `b` of
exponents `ea`, `eb` and weight `(κ, e)` (`IsLiftWeight`). Here `P.jetScale s` is the scale at
which Taylor series of theta functions are taken and `P.d` is the prime with `P.K = ℚ(√(-P.d))`.
For an integer `δ ≠ 0` of `P.K`, a standard datum `Φ` for `δ` is a combination, with coefficients
integral under `ιₚ`, of translates of the integral vacuum by the vectors that `δ` makes integral
above `p`. Such a `Φ` lies in `raises 1 1` of `(‖ιₚ c‖ / ‖ιₚ (star δ * P.d)‖) ^ L`, where
`L = boxes κ (card n')` counts the boxes in columns of height below `card n'`: for all finite points
`g`, `h`, its kernel translated by `(g, h)` multiplies the `p`-adic gauge (`New.weylGauge`) from
`g` to `h` by at most this factor. -/
lemma mem_raises_of_standardData {c : ℂ} {K : Subgroup (Gf (P.E s) n)}
    {a b : AutChar (E P s)} {ψ ψ' : (w : FinPlace (P.E s)) → MulChar (ResField w) ℂ}
    {ha : a.HasWeight ea ψ} {hb : b.HasWeight eb ψ'}
    {p : ℕ} [Fact p.Prime] [PadicPlace p] {hκ : IsLiftWeight n n' κ eb e}
    {Φ : ↥((stdSpace (P.E s) n).hom (stdSpace (P.E s) n')).finitePart}
    {δ : NumberField.RingOfIntegers P.K} (hδ : δ ≠ 0)
    (hΦ : Φ.val ∈ standardData ((stdSpace (E P s) n).hom (stdSpace (E P s) n')) δ) :
    Φ ∈ (thetaKernel hκ (c * P.jetScale s) ha hb K).raises 1 1
        ((‖ιₚ c‖ / ‖ιₚ (star (δ : ℂ) * P.d)‖) ^ boxes κ (card n')) := by
  -- Apply `omega_mem_raises_of_schurJet_le` with `x = d = y = 1`; the entrywise bound is
  -- `norm_jet_jetSeries_le_pow`.
  have h_one : (thetaKernel hκ (c * P.jetScale s) ha hb K).ω (1, 1 * 1 * 1) Φ = Φ := by
    simp [Prod.mk_one_one]
  rw [← h_one]
  refine omega_mem_raises_of_schurJet_le hΦ (one_mem _) (one_mem _) (u := 1) (by simp)
    fun f hf i' i ↦ ?_
  -- The entries of the Schur matrix are homogeneous polynomials with integral coefficients.
  let Q : MvPolynomial (P.Φ s × n' × n) embValRing :=
    schur κ (fun τ ↦ of fun (row : n') (col : n) ↦ MvPolynomial.X (τ, row, col)) i' i
  have h_map : Q.map embValRing.subtype =
      schur κ (fun τ ↦ of fun (row : n') (col : n) ↦ MvPolynomial.X (τ, row, col)) i' i := by
    simp [Q, map_schur hκ.1]
  have hQ : Q.IsHomogeneous (boxes κ (card n')) :=
    .of_map embValRing.subtype_injective (by simpa only [h_map] using isHomogeneous_schur hκ.1 i' i)
  have h_entry (F : MvPowerSeries (P.Φ s × n' × n) ℂ) :
      schurJet κ F i' i = jet ℂ (Q.map embValRing.subtype) F := by simp [h_map, schurJet]
  rw [h_entry, diagonalWeight_one, one_mul]
  simpa only [map_div₀, norm_div] using norm_jet_jetSeries_le_pow hδ hf c hQ

/-- One lift at a prime `p` that is not split in `P.K = ℚ(√(-P.d))`. Take the theta kernel
(`New.thetaKernel`) of weight `(κ, e)` and scale `c * P.jetScale s`, with `c` integral at `p`, at
any level `K`. A standard datum `Φ` for `δ = 1` multiplies the `p`-adic gauge by at most
`p ^ (-(D - f * N ^ 3 * (1 + log_p (max L 1))))`, in the sense of `New.Kernel.raises`. Here
`f = card (P.Φ s)` is the number of infinite places, `N = card n'` and `L` is the number of boxes of
`κ` in columns of height below `N`.

The term `D` is `New.predictedDivisibility`. -/
lemma mem_raises_predictedDivisibility {c : ℂ} {K : Subgroup (Gf (P.E s) n)}
    {a b : AutChar (E P s)} {ψ ψ' : (w : FinPlace (P.E s)) → MulChar (ResField w) ℂ}
    {ha : a.HasWeight ea ψ} {hb : b.HasWeight eb ψ'}
    {p : ℕ} [Fact p.Prime] [PadicPlace p] {hκ : IsLiftWeight n n' κ eb e}
    (hp : chiK P.d p ≠ 1) (hc : ‖ιₚ c‖ ≤ 1)
    {Φ : ↥((stdSpace (P.E s) n).hom (stdSpace (P.E s) n')).finitePart}
    (hΦ : Φ.val ∈ standardData ((stdSpace (E P s) n).hom (stdSpace (E P s) n')) 1) :
    let N : ℕ := card n'
    Φ ∈ (thetaKernel hκ (c * P.jetScale s) ha hb K).raises 1 1
      (p ^ (-(predictedDivisibility P.d p (P.partner s p) κ N -
        card (P.Φ s) * N ^ 3 * (1 + Real.logb p (max (boxes κ N) 1 : ℕ))) : ℝ)) := by
  -- Apply `omega_mem_raises_of_jet_minorProd_le` with `x = d = y = 1`: jets along products of
  -- minors have the predicted divisibility.
  intro N
  have h_one : (thetaKernel hκ (c * P.jetScale s) ha hb K).ω (1, 1 * 1 * 1) Φ = Φ := by
    simp [Prod.mk_one_one]
  rw [← h_one]
  refine omega_mem_raises_of_jet_minorProd_le hΦ (one_mem _) (one_mem _) (d := 1) (u := 1) (by simp)
    fun f hf i' w ↦ ?_
  simpa [N, diagonalWeight_one] using norm_jet_minorProd_jetSeries_le hp hf hc i' w

/-- Take the theta kernel (`New.thetaKernel`) of weight `(κ, e)`, with `κ` giving the column numbers
of the diagrams, and of scale `c * P.jetScale s`, where `P.jetScale s` is the scale of Taylor series
of theta functions and `‖ιₚ c‖ ≤ 1` for the chosen embedding `ιₚ : ℂ →+* ℂ_[p]`. Let `f` be a datum
such that `d • f` is standard for the natural number `N ≠ 0`. If `d * (N * P.d) ^ L` divides `M`,
where `L` is the number of boxes of `κ` in columns of height below `card n'`, then `M • f` does not
increase the `p`-adic gauge `New.weylGauge` (`New.Kernel.raises` with bound `1`). -/
lemma smul_mem_raises_of_dvd {c : ℂ} {K : Subgroup (Gf (P.E s) n)}
    {a b : AutChar (E P s)} {ψ ψ' : (w : FinPlace (P.E s)) → MulChar (ResField w) ℂ}
    {ha : a.HasWeight ea ψ} {hb : b.HasWeight eb ψ'}
    {p : ℕ} [Fact p.Prime] [PadicPlace p] {hκ : IsLiftWeight n n' κ eb e} {N d M : ℕ} [NeZero N]
    (f : ↥((stdSpace (P.E s) n).hom (stdSpace (P.E s) n')).finitePart)
    (hf : (d : ℂ) • f.val ∈
      standardData (p := p) ((stdSpace (E P s) n).hom (stdSpace (E P s) n')) N)
    (hc : ‖ιₚ c‖ ≤ 1) (hM_dvd : d * (N * P.d) ^ boxes κ (card n') ∣ M) :
    (M : ℂ) • f ∈ (thetaKernel hκ (c * P.jetScale s) ha hb K).raises (p := p) 1 1 1 := by
  -- Write `M = d * (N * P.d) ^ boxes * q`. The datum `d • f` is standard for `N`, so it raises
  -- gauges by at most `(‖ιₚ c‖ / ‖ιₚ (N * P.d)‖) ^ boxes`; `(N * P.d) ^ boxes` cancels the divisor.
  obtain ⟨q, rfl⟩ := hM_dvd
  rw [mul_rotate, Nat.cast_mul, mul_smul]
  refine smul_mem_raises _ (mem_raises_of_standardData NeZero.out hf) ?_
  -- After `‖ιₚ c‖ ≤ 1`, what remains is `‖ιₚ q‖ ≤ 1` for a natural number `q`.
  grw [hc]
  simpa [mul_pow, field, NeZero.ne] using norm_natCast_le_one ℂ_[p] q

end New.Parameters

end OneLift

/-! ## Functions modulo an ideal on the vacuum as combinations of translates -/

namespace New.Parameters

open NumberField Fintype Ideal Seesaw Function

variable {P : Parameters} {s : ℕ}
  {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  {𝔪 : Modulus (E P s)} {Ψ : Matrix n' n 𝔪.ResidueRing → ℂ}

/-- The absolute norm of the ideal of `𝓞 (P.E s)` generated by a natural number `k` is
`k ^ (2 * numInfPlaces)`, where `numInfPlaces` is the number of infinite places of the CM field
`P.E s`. -/
lemma absNorm_span_natCast_eq_pow_numInfPlaces (k : ℕ) :
    absNorm (span {(k : 𝓞 (P.E s))}) = k ^ (2 * Core.numInfPlaces (P.E s)) := by
  rw [absNorm_span_natCast, RingOfIntegers.rank, finrank_eq_two_mul_card_infinitePlace]

/-- If a positive integer `k` lies in the ideal of the modulus `𝔪`, then the residue ring
`𝔪.ResidueRing` has at most `k ^ (2 * Core.numInfPlaces (P.E s))` elements. Here
`Core.numInfPlaces (P.E s)` is the number of infinite places of the CM field `P.E s`. -/
lemma _root_.New.Modulus.card_residueRing_le {k : ℕ} (hk_mem : (k : 𝓞 (P.E s)) ∈ 𝔪.ideal)
    (hk : 0 < k) : Nat.card 𝔪.ResidueRing ≤ k ^ (2 * Core.numInfPlaces (P.E s)) := by
  -- The left side is the norm of `𝔪.ideal`, which divides the norm of the ideal `(k)`.
  have h_dvd : absNorm 𝔪.ideal ∣ absNorm (span {(k : 𝓞 (E P s))}) :=
    map_dvd absNorm (dvd_span_singleton.2 hk_mem)
  rw [absNorm_span_natCast_eq_pow_numInfPlaces] at h_dvd
  exact Nat.le_of_dvd (by positivity) h_dvd

/-- Let `V` be a hermitian space over the CM field `E = P.E s` with basis indexed by `n` and signs
`ε`, let `𝔪` be a modulus, that is, an ideal of `𝓞_E` prime to its conjugate, and let `N q ∈ 𝔪`.
Let `Ψ` be a function on `(𝓞_E/𝔪)ⁿ` with values in `integralAway q`, that is, integral in every
embedding into `ℂ_[l]` for `l` prime to `q`. Its lift `𝔪.liftFn Ψ` to finite adelic vectors reduces
the components at the places dividing `𝔪` modulo `𝔪` and is `0` where they are not integral. The
operator `V.schrodingerOp 𝔪.places` is the combination of Heisenberg operators at those places
which puts this function there; it is applied to the integral vacuum
`intVacuum V = vacuumScale ^ card n • V.vacElem`. Then, for a prime `l` not dividing `q`,
`N^(2f|n|)` times this datum is a standard datum for `N` at the chosen place above `l`: a
combination, with coefficients integral at that place, of translates of the integral vacuum by
vectors `y` with `N y` integral above `l`. Here `f` is the number of infinite places of `E`. -/
lemma smul_schrodingerOp_mem_standardData {n : Type} [Fintype n] [DecidableEq n] {ε : n → ℤˣ}
    (V : Space (E P s) n ε) {Ψ : (n → 𝔪.ResidueRing) → ℂ} {N q l : ℕ} [Fact l.Prime] [PadicPlace l]
    (hNq : ((N * q : ℕ) : 𝓞 (P.E s)) ∈ 𝔪.ideal) (hΨ : ∀ x : n → 𝔪.ResidueRing, Ψ x ∈ integralAway q)
    (hlq : ¬l ∣ q) :
    ((N ^ (2 * Core.numInfPlaces (P.E s) * card n) : ℕ) : ℂ) •
        V.schrodingerOp 𝔪.places (𝔪.liftFn Ψ) (intVacuum V) ∈ standardData (p := l) V N := by
  have hl : l.Coprime q := (Fact.out : l.Prime).coprime_iff_not_dvd.2 hlq
  -- The vectors `y` for which `N y` is integral at the places that do not divide `q`.
  let A : Set (n → 𝔸f (P.E s)) := translations n q (star (algebraMap (𝓞 (E P s)) (𝔸f (E P s)) N))
  -- Fourier inversion modulo `𝔪`: the datum combines translates of `intVacuum V` by vectors of `A`,
  -- with denominator the norm of `N` to the power `|n|`. No bound on the size is stated.
  have h_comb : IsAdmissibleCombination (fun y : n → 𝔸f (P.E s) ↦ V.finHeisenbergOp y (intVacuum V))
    A q
      (absNorm (span {(N : 𝓞 (P.E s))}) ^ card n) False 0
      (V.schrodingerOp 𝔪.places (𝔪.liftFn Ψ) (intVacuum V)) :=
    isAdmissibleCombination_schrodingerOp V 𝔪 (by simpa using hNq) hΨ nofun (by simp [intVacuum])
  -- A place above `l` does not divide `q`, so these translates are standard data for `N`.
  have h_translate : ∀ y ∈ A, V.finHeisenbergOp y (intVacuum V) ∈ standardData (p := l) V N := by
    refine fun y hy ↦ Submodule.subset_span ⟨y, ?_, rfl⟩
    simpa [integralAfter] using
      fun (i : n) (w : FinPlace (P.E s)) (hw : (l : 𝓞 (P.E s)) ∈ w.asIdeal) ↦
        hy i w (IsPrime.notMem_of_isCoprime_of_mem hl.cast hw)
  rw [pow_mul, ← absNorm_span_natCast_eq_pow_numInfPlaces]
  exact h_comb.smul_mem hl h_translate

/-- The vacuum datum of `Ψ`, scaled by `P.vacuumScale s ^ |n' × n|`, is the operator `schrodingerOp`
of the space of `n' × n` matrices, for the lift of `Ψ` at the places of `𝔪`, applied to
`intVacuum`. -/
lemma vacuumScale_pow_smul_vacuumDatum (Ψ : Matrix n' n 𝔪.ResidueRing → ℂ) :
    P.vacuumScale s ^ card (n' × n) •
        (vacuumDatum (stdSpace (E P s) n) (stdSpace (E P s) n') 𝔪 Ψ).val =
      ((stdSpace (E P s) n).hom (stdSpace (E P s) n')).schrodingerOp 𝔪.places
        (𝔪.liftFn fun x : n' × n → 𝔪.ResidueRing ↦ Ψ (vecToMatrix x))
        (intVacuum ((stdSpace (E P s) n).hom (stdSpace (E P s) n'))) := by
  simp [intVacuum, comp_def, vacuumDatum]

/-- Let `q N ∈ 𝔪`, let the values of `Ψ` on matrices modulo `𝔪` be integral away from `q`
(`integralAway`), and let `l` be a prime not dividing `q`. The vacuum datum of `Ψ`, scaled to be
integral and multiplied by `N^(2f|n'||n|)`, is then a standard datum for `N` at the chosen place
above `l`: an integral combination there of translates of the integral vacuum by vectors `y` with
`N y` integral above `l`. Here `f` is the number of infinite places of `P.E s`. -/
lemma smul_vacuumDatum_mem_standardData {N q l : ℕ} [Fact l.Prime] [PadicPlace l]
    (hqN : ((q * N : ℕ) : 𝓞 (P.E s)) ∈ 𝔪.ideal)
    (hΨ : ∀ x : Matrix n' n 𝔪.ResidueRing, Ψ x ∈ integralAway q) (hl : l.Coprime q) :
    ((N ^ (2 * Core.numInfPlaces (P.E s) * card (n' × n)) : ℕ) : ℂ) •
        P.vacuumScale s ^ card (n' × n) •
        (vacuumDatum (stdSpace (E P s) n) (stdSpace (E P s) n') 𝔪 Ψ).val ∈
      standardData (p := l) ((stdSpace (E P s) n).hom (stdSpace (E P s) n')) N := by
  rw [vacuumScale_pow_smul_vacuumDatum]
  exact smul_schrodingerOp_mem_standardData _ (by rwa [mul_comm]) (fun x ↦ hΨ (vecToMatrix x))
    ((Fact.out : l.Prime).coprime_iff_not_dvd.1 hl)

/-- Let `𝔪` be a modulus of the CM field `E = P.E s` and `Ψ` a complex function on the `n' × n`
matrices modulo `𝔪`, with `∑ x, ‖σ (Ψ x)‖ ≤ B` for all automorphisms `σ` of `ℂ`. The vacuum datum of
`Ψ` (`vacuumDatum`) is the datum on the maps between the standard spaces that is `Ψ` at the places
dividing `𝔪` and the vacuum elsewhere. Multiply it by `P.vacuumScale s ^ card (n' × n)`, the factor
that turns the vacuum into the integral vacuum `intVacuum`. The result is a finite combination
`∑ y, r y • (translate of intVacuum by y)` over finite adelic vectors `y` with `∑ y, ‖σ (r y)‖ ≤ B`
for all `σ`. -/
lemma isAdmissibleCombination_vacuumDatum_of_sum_le {B : ℝ}
    (hB : ∀ σ : ℂ ≃+* ℂ, ∑ x : n' × n → 𝔪.ResidueRing, ‖σ (Ψ (vecToMatrix x))‖ ≤ B) :
    IsAdmissibleCombination
      (fun y : n' × n → 𝔸f (P.E s) ↦
        ((stdSpace (E P s) n).hom (stdSpace (E P s) n')).finHeisenbergOp y
          (intVacuum ((stdSpace (P.E s) n).hom (stdSpace (P.E s) n'))))
      (A := Set.univ) (n := 0) (d := 0) (p := True) B
      (P.vacuumScale s ^ card (n' × n) •
        (vacuumDatum (stdSpace (E P s) n) (stdSpace (E P s) n') 𝔪 Ψ).val) := by
  -- Fourier inversion modulo `𝔪` (`isAdmissibleCombination_schrodingerOp`) with `q = 0`: no prime
  -- is coprime to `0`, so integrality asks for nothing.
  let V : Space (P.E s) (n' × n) (homSigns 1 1) := (stdSpace (P.E s) n).hom (stdSpace (P.E s) n')
  have h_int (x : n' × n → 𝔪.ResidueRing) : Ψ (vecToMatrix x) ∈ integralAway 0 :=
    fun l ⟨hl_prime⟩ hl_coprime ↦
      absurd (l.coprime_zero_right.1 hl_coprime) hl_prime.ne_one
  -- The integral vacuum is the vacuum at the places of `𝔪`.
  have h_proj : V.projOn 𝔪.places (intVacuum V) = intVacuum V := by simp [intVacuum]
  rw [vacuumScale_pow_smul_vacuumDatum]
  have h_comb : IsAdmissibleCombination (V.finHeisenbergOp · (intVacuum V))
      (translations (n' × n) 0 (star (algebraMap (𝓞 (E P s)) (𝔸f (E P s)) 0))) 0
      (absNorm (span {(0 : 𝓞 (P.E s))}) ^ card (n' × n)) True B
      (V.schrodingerOp 𝔪.places (𝔪.liftFn fun x : n' × n → 𝔪.ResidueRing ↦ Ψ (vecToMatrix x))
        (intVacuum V)) :=
    isAdmissibleCombination_schrodingerOp V 𝔪 (by simp) h_int (fun _ ↦ hB) h_proj
  -- Enlarge the translations to `univ`: each translate is a combination of itself of size `1`.
  exact h_comb.bind (d' := 1) (B' := 1) (fun y _ ↦ .single y (Set.mem_univ y)) (dvd_zero _)
    fun _ ↦ by simp

/-- Let `𝔪` be a modulus of the CM field `P.E s` and `Ψ` a complex function on the `n' × n` matrices
modulo `𝔪` with `‖σ (Ψ x)‖ ≤ M` for all automorphisms `σ` of `ℂ` and all `x`. Its vacuum datum,
scaled by `P.vacuumScale s ^ card (n' × n)`, is a combination of translates of the integral vacuum
`intVacuum` by finite adelic vectors (`finHeisenbergOp`). For each `σ` the conjugates of the
coefficients have total absolute value at most `M` times the number of matrices modulo `𝔪`. -/
lemma isAdmissibleCombination_vacuumDatum (M : ℝ)
    (hM : ∀ (σ : ℂ ≃+* ℂ) (x : Matrix n' n 𝔪.ResidueRing), ‖σ (Ψ x)‖ ≤ M) :
    IsAdmissibleCombination
      (fun y : n' × n → 𝔸f (P.E s) ↦
        ((stdSpace (E P s) n).hom (stdSpace (E P s) n')).finHeisenbergOp y
          (intVacuum ((stdSpace (P.E s) n).hom (stdSpace (P.E s) n'))))
      (A := Set.univ) (n := 0) (d := 0) (p := True) (card (n' × n → 𝔪.ResidueRing) * M)
      (P.vacuumScale s ^ card (n' × n) •
        (vacuumDatum (stdSpace (E P s) n) (stdSpace (E P s) n') 𝔪 Ψ).val) := by
  refine isAdmissibleCombination_vacuumDatum_of_sum_le fun σ ↦ ?_
  grw [hM]
  simp

/-- Let `Ψ` be a complex function on the `n' × n` matrices modulo the modulus `𝔪` of the CM field
`P.E s`, with `‖σ (Ψ x)‖ ≤ M` for all automorphisms `σ` of `ℂ` and all `x`. Then its vacuum datum,
scaled to be integral, is a finite combination of translates of the integral vacuum, and for every
`σ` the absolute values of the conjugates of its coefficients have sum at most `M` times the number
of matrices modulo `𝔪`. -/
lemma isVacuumCombination_vacuumDatum (M : ℝ)
    (hM : ∀ (σ : ℂ ≃+* ℂ) (x : Matrix n' n 𝔪.ResidueRing), ‖σ (Ψ x)‖ ≤ M) :
    P.IsVacuumCombination ((stdSpace (P.E s) n).hom (stdSpace (P.E s) n'))
      (card (n' × n → 𝔪.ResidueRing) * M)
      (P.vacuumScale s ^ card (n' × n) •
        (vacuumDatum (stdSpace (E P s) n) (stdSpace (E P s) n') 𝔪 Ψ).val) :=
  P.isVacuumCombination_of_isAdmissibleCombination (isAdmissibleCombination_vacuumDatum M hM)

/-- For a modulus `𝔪` of the CM field `P.E s`, let the datum be the indicator of one matrix `y₀`
modulo `𝔪` at the places dividing `𝔪` and the vacuum elsewhere (`vacuumDatum`), scaled by
`P.vacuumScale s ^ card (n' × n)`. It is a finite combination of translates of the integral vacuum
`intVacuum` by finite adelic vectors (`finHeisenbergOp`) whose coefficients `r` have `∑ ‖σ r‖ ≤ 1`
for every automorphism `σ` of `ℂ`. -/
lemma isAdmissibleCombination_vacuumDatum_indicator (y₀ : Matrix n' n 𝔪.ResidueRing) :
    IsAdmissibleCombination
      (fun y : n' × n → 𝔸f (P.E s) ↦
        ((stdSpace (E P s) n).hom (stdSpace (E P s) n')).finHeisenbergOp y
          (intVacuum ((stdSpace (P.E s) n).hom (stdSpace (P.E s) n'))))
      (A := Set.univ) (n := 0) (d := 0) (p := True) 1
      (P.vacuumScale s ^ card (n' × n) •
        (vacuumDatum (stdSpace (E P s) n) (stdSpace (E P s) n') 𝔪 (Pi.single y₀ 1)).val) := by
  refine isAdmissibleCombination_vacuumDatum_of_sum_le fun σ ↦ le_of_eq ?_
  -- Only the vector of the entries of `y₀` contributes to the sum.
  have h_other (x : n' × n → 𝔪.ResidueRing) (hx : x ≠ matrixToVec y₀) : vecToMatrix x ≠ y₀ := by
    rintro rfl
    exact hx (matrixToVec_vecToMatrix x).symm
  rw [sum_eq_single (matrixToVec y₀) fun x hx ↦ by simp [h_other x hx]]
  simp [vecToMatrix_matrixToVec]

end New.Parameters
