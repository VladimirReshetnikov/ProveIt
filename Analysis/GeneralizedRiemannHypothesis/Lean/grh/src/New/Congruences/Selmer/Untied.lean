import New.Congruences.Selmer.OneSystem

/-!
# The failure to be tied

At a prime of norm `≡ 1` modulo `ℓ ^ N`, a Frobenius element `φ` and an inertial element `γ` commute
up to wild inertia and `ℓ ^ N`-th powers of inertia. If these act trivially and a cocycle `z`
vanishes on them, then `z(γ φ) = z(φ γ)`, which is the relation `(φ - 1) z(γ) = (γ - 1) z(φ)`.

Let `𝔮₀` be the first auxiliary prime and `s_𝔮` the slopes at the others. At a point of the line
`X_{𝔮₀} = Y`, `X_𝔮 = s_𝔮 Y` the relation puts `tie_w(z) = z(γ_w) - s_𝔮 z(φ_w)`, for `w = 𝔮, 𝔮̄`, in
the kernel of `φ_w - 1` for the twisted action. At `Y = 0` it does the same for `z(γ_w)`,
`w = 𝔮₀, 𝔮̄₀`. The valuation of a determinant bounds the length of the kernel.

* `New.Selmer.sub_one_smul_eq_of_tame`: the relation.
* `New.Selmer.selmerOnLine`: the Selmer module of the twist at a point of the line.
* `New.Selmer.IsTiedPrimes.relLength_tied_le`: the failure to be tied at the primes other than the
  first is at most `v(P¹(y))`, where `P¹ = New.Selmer.tiePolynomial`.
* `New.Selmer.IsTiedPrimes.relLength_tieRelations_le_sum_addVal_det`: the cost of dropping the ties
  at the first prime and its conjugate, at the point `0`.

Letters: `J` is the set of all auxiliary primes, `P₀ ∈ J` is the first prime `𝔮₀`, and `d` attaches
to `v ∈ J` the elements `φ_v = (d v).1.frob` and `γ_v = (d v).1.tameGenerator`, the homomorphism
`λ_v = (d v).1.character` to `ℤ / ℓ ^ N` and, for each index `i : ι`, the slope `(d v).2 i`.
Coefficients are taken modulo `ℓ ^ M`.

Notions from other files:
* `New.Selmer.IsTiedPrimes`: an auxiliary set `J` of primes with places, Frobenius elements `φ`,
  tame generators `γ`, characters to `ℤ / ℓ ^ N` and slopes, and a first prime `P₀ ∈ J`.
* `New.Selmer.tieRelations`: the ties `z(γ) = s z(φ)` at the primes of a set and at their
  conjugates.
* `New.Selmer.universalChar`: the polynomial `ψ_X(g) = ∏ (1 + X_j) ^ (h_j g)`;
  `New.Selmer.selmerAtPoint` is the Selmer module `Sel(x)` of the twist by `ψ_x`.

## Relation to the literature

See `New.Congruences.Selmer.TwistingTheorem` for related work.
-/

noncomputable section

namespace New.Selmer

open Finset

open scoped Polynomial

variable {ℓ : ℕ}

section Affine

open Matrix.Module

variable {E O n B : Type} [Field E] [EmbeddedNumberField E] [CommRing O] [Fintype n] [DecidableEq n]
  [AddCommGroup B] [Module O B] {ρ : Gal(Ω/E) →* Matrix n n O} {c : Gal(Ω/E) → n → B}

lemma affineAction_apply (hc : ∀ g h : Gal(Ω/E), c (g * h) = c g + ρ g • c h) (g : Gal(Ω/E))
    (u : n → B) : affineAction hc g u = c g + ρ g • u := rfl

/-- If `g` acts through `ρ` by the scalar `α`, then the affine action `u ↦ c(g) + g u` of the
cocycle `c` has `k`-th iterate `u ↦ α ^ k u + ∑ i < k, α ^ i c(g)` at `g`. At `u = 0` this says
`c(g ^ k) = ∑ i < k, α ^ i c(g)`. -/
lemma affineAction_pow_apply (hc : ∀ g h : Gal(Ω/E), c (g * h) = c g + ρ g • c h)
    {g : Gal(Ω/E)} {α : O} (hg : ρ g = α • 1) (k : ℕ) (u : n → B) :
    (affineAction hc g ^ k) u = α ^ k • u + (∑ i ∈ range k, α ^ i) • c g := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih, affineAction_apply, hg, smul_assoc, one_smul,
      geom_sum_succ]
    module

/-- If `g` acts through `ρ` by the scalar `α` and `∑ i < k, α ^ i = 0`, then the affine action
`u ↦ c(g) + g u` of the cocycle `c` at `g` has `k`-th power `1`: the element `g ^ k` acts trivially
and `c` vanishes at it. -/
lemma affineAction_pow_eq_one (hc : ∀ g h : Gal(Ω/E), c (g * h) = c g + ρ g • c h)
    {g : Gal(Ω/E)} {α : O} (hg : ρ g = α • 1) {k : ℕ} (hα : ∑ i ∈ range k, α ^ i = 0) :
    affineAction hc g ^ k = 1 := by
  have h_pow : α ^ k = 1 := by rw [← sub_eq_zero, ← geom_sum_mul, hα, zero_mul]
  exact Equiv.ext fun u ↦ by simp [affineAction_pow_apply hc hg, hα, h_pow]

/-- Let `c` be a locally constant cocycle for `ρ`, let `A` be a place of `Ω` over the prime `v`, and
let `ρ` be trivial on the elements of inertia at `A` near `1`. Each `g` acts by the affine map
`u ↦ c(g) + ρ(g) u` (`affineAction`). Suppose that this map has `q`-th power `1` for every `g` in
inertia at `A`, with `q` prime to `A`. Then the affine maps of a Frobenius element `φ` at `A` of
norm `k ≡ 1` modulo `q` and of an element `γ` of inertia at `A` commute. -/
lemma commute_affineAction (hc : ∀ g h : Gal(Ω/E), c (g * h) = c g + ρ g • c h)
    {A : ClosurePlace} {v : FinPlace E} (hA : IsPlaceOver A v) (hc_lc : IsLocallyConstant c)
    (h_open : ∀ᶠ g : Gal(Ω/E) in nhds 1, g ∈ inertiaGroup Gal(Ω/E) A → ρ g = 1) {q k : ℕ}
    (hq : A.valuation (q : ℕ) = 1)
    (h_pow : ∀ g ∈ inertiaGroup Gal(Ω/E) A, affineAction hc g ^ q = 1) (hk : k ≡ 1 [MOD q])
    {φ γ : Gal(Ω/E)} (hφ : IsFrob A k φ) (hγ : γ ∈ inertiaGroup Gal(Ω/E) A) :
    Commute (affineAction hc φ) (affineAction hc γ) := by
  have h_one : c 1 = 0 := by simpa using hc 1 1
  have h_near : ∀ᶠ g : Gal(Ω/E) in nhds 1,
      g ∈ inertiaGroup Gal(Ω/E) A → affineAction hc g = 1 := by
    filter_upwards [hc_lc.eventually_eq 1, h_open] with g hcg hρg hg
    exact Equiv.ext fun u ↦ by simp [affineAction_apply, hcg, h_one, hρg hg]
  -- On inertia the action is tame, so conjugation by `φ` is the power `k ≡ 1` modulo `q`.
  have h_conj : affineAction hc (φ * γ * φ⁻¹) = affineAction hc γ := by
    rw [(hA.tame_inertia (affineAction hc) h_near hq h_pow ⟨γ, hγ⟩).right k φ hφ,
      pow_eq_pow_of_modEq hk (h_pow γ hγ), pow_one]
  rw [commute_iff_eq, ← map_mul, ← h_conj, ← map_mul, inv_mul_cancel_right]

/-- If the affine maps `u ↦ c(g) + g u` of the cocycle `c` at `g = φ` and `g = γ` commute, then
`c(γ φ) = c(φ γ)`, which is `(φ - 1) c(γ) = (γ - 1) c(φ)` by the cocycle rule. -/
lemma sub_one_smul_eq_of_commute (hc : ∀ g h : Gal(Ω/E), c (g * h) = c g + ρ g • c h)
    {φ γ : Gal(Ω/E)} (h_comm : Commute (affineAction hc φ) (affineAction hc γ)) :
    (ρ φ - 1) • c γ = (ρ γ - 1) • c φ := by
  have h_swap : c φ + ρ φ • c γ = c γ + ρ γ • c φ := by
    simpa [affineAction_apply] using DFunLike.congr_fun h_comm.eq 0
  rw [sub_smul, sub_smul, one_smul, one_smul]
  linear_combination (norm := abel) h_swap

/-- The relation `(φ - 1) c(γ) = (γ - 1) c(φ)` for a cocycle `c` passes from `φ` to `φ⁻¹` if `γ`
acts by a scalar: multiply it by `-φ⁻¹` and use `c(φ⁻¹) = -φ⁻¹ c(φ)`. -/
lemma inv_sub_one_smul_eq (hc : ∀ g h : Gal(Ω/E), c (g * h) = c g + ρ g • c h)
    {φ γ : Gal(Ω/E)} {α : O} (hγ : ρ γ = α • 1) (h_rel : (ρ φ - 1) • c γ = (ρ γ - 1) • c φ) :
    (ρ φ⁻¹ - 1) • c γ = (ρ γ - 1) • c φ⁻¹ := by
  have h_inv : ρ φ⁻¹ * ρ φ = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have h_comm : ρ φ⁻¹ * (ρ γ - 1) = (ρ γ - 1) * ρ φ⁻¹ := by simp [hγ, mul_sub, sub_mul]
  calc
    (ρ φ⁻¹ - 1) • c γ = -(ρ φ⁻¹ • (ρ φ - 1) • c γ) := by
      rw [← mul_smul, mul_sub, h_inv, mul_one, ← neg_smul, neg_sub]
    _ = -(ρ φ⁻¹ • (ρ γ - 1) • c φ) := by rw [h_rel]
    _ = (ρ γ - 1) • c φ⁻¹ := by
      rw [cocycle_apply_inv hc, smul_neg, ← mul_smul, h_comm, mul_smul]

/-- The relation from tame inertia. Let `q` be prime to the place `A`, let `ρ` be trivial on
inertia near `1`, and let each inertial element act by a scalar `α` with `∑ i < q, α ^ i = 0`. If
`φ` or `φ⁻¹` is a Frobenius element of norm `k ≡ 1` modulo `q` and `γ` is inertial, every locally
constant cocycle `c` has `(φ - 1) c(γ) = (γ - 1) c(φ)`. -/
lemma sub_one_smul_eq_of_tame (hc : ∀ g h : Gal(Ω/E), c (g * h) = c g + ρ g • c h)
    {A : ClosurePlace} {v : FinPlace E} (hA : IsPlaceOver A v) (hc_lc : IsLocallyConstant c)
    (h_open : ∀ᶠ g : Gal(Ω/E) in nhds 1, g ∈ inertiaGroup Gal(Ω/E) A → ρ g = 1) {q k : ℕ}
    (hq : A.valuation (q : ℕ) = 1)
    (h_scalar : ∀ g ∈ inertiaGroup Gal(Ω/E) A, ∃ α : O, ρ g = α • 1 ∧ ∑ i ∈ range q, α ^ i = 0)
    (hk : k ≡ 1 [MOD q]) {φ γ : Gal(Ω/E)} (hφ : IsFrob A k φ ∨ IsFrob A k φ⁻¹)
    (hγ : γ ∈ inertiaGroup Gal(Ω/E) A) : (ρ φ - 1) • c γ = (ρ γ - 1) • c φ := by
  have h_frob {φ' : Gal(Ω/E)} (hφ' : IsFrob A k φ') : (ρ φ' - 1) • c γ = (ρ γ - 1) • c φ' := by
    refine sub_one_smul_eq_of_commute hc
      (commute_affineAction hc hA hc_lc h_open hq (fun g hg ↦ ?_) hk hφ' hγ)
    obtain ⟨α, hα, h_sum⟩ := h_scalar g hg
    exact affineAction_pow_eq_one hc hα h_sum
  obtain hφ | hφ := hφ
  · exact h_frob hφ
  · obtain ⟨α, hα, -⟩ := h_scalar γ hγ
    simpa only [inv_inv] using inv_sub_one_smul_eq hc hα (h_frob hφ)

end Affine

section Line

open Matrix.Module Module IsDiscreteValuationRing Polynomial

variable {E ι O n : Type} [Field E] [EmbeddedNumberField E] [NumberField.IsCMField E]
  [CommRing O] [Fintype n] [DecidableEq n]
  {V : ι → Gal(Ω/E) → Prop} {W : Set Gal(Ω/E)} {S₀ J : Finset (FinPlace E)} {M N : ℕ}
  {P₀ : FinPlace E} {ρ : Gal(Ω/E) →* Matrix n n O}
  {d : FinPlace E → AuxPrimeData E (ℓ ^ N) × (ι → O)}

open scoped Classical in
/-- The direction of the line `X_{P₀} = Y`, `X_v = s_v Y` in the space with coordinates `X_v`,
`v ∈ J`: the entry at the prime `P₀` is `1`, and the entry at `v ≠ P₀` is the slope
`s_v = (d v).2 i` that `d` attaches to `v` and the index `i`. -/
def lineDirection {q : ℕ} (P₀ : FinPlace E) (J : Finset (FinPlace E))
    (d : FinPlace E → AuxPrimeData E q × (ι → O)) (i : ι) (v : J) : O :=
  if ↑v = P₀ then 1 else (d v).2 i

/-- The Selmer module at the point `Y = y` of the line with index `i`. The point `x` has coordinates
`x_{P₀} = y` and `x_v = e(s_v) y` for `v ≠ P₀` in `J`, where `s_v = (d v).2 i` (`lineDirection`).
The module is `Sel(x)` (`selmerAtPoint`) for the characters that `d` attaches to the primes of `J`:
the locally constant cocycles in `(O' / ℓ ^ M) ^ n` for the twist of `ρ` at `x` that are unramified
outside `S` and obey the linear relations `L`. -/
def selmerOnLine (ℓ M : ℕ) {q : ℕ} (ρ : Gal(Ω/E) →* Matrix n n O) (P₀ : FinPlace E)
    (J : Finset (FinPlace E)) (d : FinPlace E → AuxPrimeData E q × (ι → O)) (i : ι)
    {O' : Type} [CommRing O'] (e : O →+* O') (y : O') (S : Set (FinPlace E))
    (L : Set (Gal(Ω/E) →₀ Matrix n n O)) : Submodule O' (Gal(Ω/E) → n → QuotSpan (ℓ ^ M : O')) :=
  selmerAtPoint ℓ M (fun v : J ↦ (d v).1.character) ρ S L e fun v : J ↦
    e (lineDirection P₀ J d i v) * y

/-- The polynomial `det ((1 + Y) A - 1)`. -/
def shiftedDet (A : Matrix n n O) : O[X] := ((1 + X : O[X]) • A.map C - 1).det

/-- Evaluating `shiftedDet A` at `y`, with coefficients mapped by `e`, gives
`det ((1 + y) e(A) - 1)`. -/
lemma eval₂_shiftedDet {O' : Type} [CommRing O'] (e : O →+* O') (y : O') (A : Matrix n n O) :
    (shiftedDet A).eval₂ e y = ((1 + y) • A.map e - 1).det := by
  rw [shiftedDet, ← coe_eval₂RingHom, RingHom.map_det]
  congr 1
  ext i j
  simp [Matrix.one_apply, apply_ite (eval₂ e y)]

lemma coeff_shiftedDet_card (A : Matrix n n O) :
    (shiftedDet A).coeff (Fintype.card n) = A.det := by
  have h_split : (1 + X : O[X]) • A.map C - 1 = (X : O[X]) • A.map C + (A - 1).map C := by
    rw [add_smul, one_smul, Matrix.map_sub _ (map_sub C), Matrix.map_one _ C_0 C_1]
    abel
  rw [shiftedDet, h_split, coeff_det_X_add_C_card]

/-- The polynomial `P¹(Y) = ∏_w det ((1 + Y) ρ(φ_w) - 1)`, over the primes `w` of `I` and their
conjugates; here `φ_w` is the Frobenius element of the data `d` at `v ∈ I` for `w = v`, and its
conjugate inverse for the conjugate prime. -/
def tiePolynomial {q : ℕ} (ρ : Gal(Ω/E) →* Matrix n n O) (I : Finset (FinPlace E))
    (d : FinPlace E → AuxPrimeData E q × (ι → O)) : O[X] :=
  ∏ p : I × Bool, shiftedDet (ρ (idOrConjInv p.2 (d p.1).1.frob))

omit [NumberField.IsCMField E] in
/-- For a family `h` of characters to `ℤ / q`, the twist of `ρ` by the function
`ψ_x(g) = ∏ (1 + x_j) ^ (h_j g)` is trivial at `x = 0`. So the Selmer module at the point `0`, with
the places `S` of allowed ramification and the relations `L`, is the Selmer module of `ρ` with
values in `(O / ℓ ^ M) ^ n`. -/
lemma selmerAtPoint_zero {σ : Type} [Fintype σ] {q : ℕ}
    (h : σ → Gal(Ω/E) →* Multiplicative (ZMod q)) (S : Set (FinPlace E))
    (L : Set (Gal(Ω/E) →₀ Matrix n n O)) :
    selmerAtPoint ℓ M h ρ S L (RingHom.id O) (fun _ : σ ↦ 0) =
      selmerModule ρ S L (QuotSpan (ℓ ^ M : O)) := by
  have h_twist : pointTwist h (fun _ ↦ 0) (.id O) ρ = ρ := funext fun g ↦ by
    simp [pointTwist, universalChar]
  rw [selmerAtPoint, h_twist, show mapRel (.id O) '' L = L by simp [mapRel.eq_def]]

/-- For the line with index `i` (the points `x_{P₀} = Y` and `x_v = s_v Y` for `v ≠ P₀`, with
`s_v = (d v).2 i`), the point at `Y = 0` is `0`. So the Selmer module `selmerOnLine` at
`Y = 0` is the Selmer module of `ρ` with values in `(O / ℓ ^ M) ^ n`. -/
lemma selmerOnLine_zero {q : ℕ} (P₀ : FinPlace E) (J : Finset (FinPlace E))
    (d : FinPlace E → AuxPrimeData E q × (ι → O)) (i : ι) (S : Set (FinPlace E))
    (L : Set (Gal(Ω/E) →₀ Matrix n n O)) : selmerOnLine ℓ M ρ P₀ J d i (RingHom.id O) 0 S L =
      selmerModule ρ S L (QuotSpan (ℓ ^ M : O)) := by
  simp only [selmerOnLine, mul_zero, selmerAtPoint_zero]

omit [NumberField.IsCMField E] in
/-- If `ρ(g)` and `ρ(g')` agree modulo `ℓ ^ M`, then their images under `e : O →+* O'` act in the
same way on `(O' / ℓ ^ M) ^ n`. -/
lemma map_smul_eq_of_reduceModPow_eq {g g' : Gal(Ω/E)}
    (h_eq : reduceModPow ℓ M ρ g = reduceModPow ℓ M ρ g') {O' : Type} [CommRing O'] (e : O →+* O')
    (u : n → QuotSpan (ℓ ^ M : O')) : (ρ g).map e • u = (ρ g').map e • u := by
  let red : QuotSpan (ℓ ^ M : O) →+* QuotSpan (ℓ ^ M : O') := Ideal.quotientMap _ e (by simp)
  have h_red (g : Gal(Ω/E)) :
      ((ρ g).map e).map (Ideal.Quotient.mk _) = (reduceModPow ℓ M ρ g).map red := by
    ext i j
    simp [reduceModPow, red]
  rw [← map_mk_smul, ← map_mk_smul ((ρ g').map e), h_red, h_red, h_eq]

/-- If `y` divides all coordinates of the point `x`, then it divides `ψ_x(g) - 1`, where `ψ_x(g)` is
the value at `x` of the polynomial `universalChar h g = ∏ (1 + X_j) ^ (h_j g)`. -/
lemma dvd_eval_universalChar_sub_one {G σ O' : Type} [Monoid G] [Fintype σ] [CommRing O'] {q : ℕ}
    (h : σ → G →* Multiplicative (ZMod q)) {y : O'} {x : σ → O'} (hx_dvd : ∀ j : σ, y ∣ x j)
    (g : G) : y ∣ MvPolynomial.eval x (universalChar h g) - 1 := by
  rw [← Ideal.Quotient.eq_zero_iff_dvd]
  simp [eval_universalChar, (Ideal.Quotient.eq_zero_iff_dvd y _).2 (hx_dvd _)]

omit [NumberField.IsCMField E] in
/-- Let `h` be a finite family of characters `h_j` to `ℤ / q`, let `e : O →+* O'` be a change of
coefficients, and let `ψ_x(g) = ∏ (1 + x_j) ^ (h_j g)` be the value of `universalChar h g` at a
point `x` with coordinates in `O'`. If the `1 + x_j` are `q`-th roots of unity modulo `ℓ ^ M`, then
the twisted matrices `pointTwist h x e ρ g = ψ_x(g) e(ρ(g))` act on `(O' / ℓ ^ M) ^ n` through a
representation `R` over `O' / ℓ ^ M`, and `R(g)` is the scalar `ψ_x(g)` wherever `ρ(g) ≡ 1` modulo
`ℓ ^ M`. -/
lemma exists_monoidHom_smul_eq_pointTwist_smul {σ O' : Type} [Fintype σ] [CommRing O'] {q : ℕ}
    [NeZero q] (h : σ → Gal(Ω/E) →* Multiplicative (ZMod q)) (e : O →+* O') {x : σ → O'}
    (hx_pow : ∀ j : σ, algebraMap O' (QuotSpan (ℓ ^ M : O')) (1 + x j) ^ q = 1) :
    ∃ R : Gal(Ω/E) →* Matrix n n (QuotSpan (ℓ ^ M : O')),
      (∀ (g : Gal(Ω/E)) (u : n → QuotSpan (ℓ ^ M : O')), R g • u = pointTwist h x e ρ g • u) ∧
      ∀ g : Gal(Ω/E), reduceModPow ℓ M ρ g = 1 →
        R g = algebraMap O' (QuotSpan (ℓ ^ M : O')) (MvPolynomial.eval x (universalChar h g)) •
          1 := by
  -- Modulo `ℓ ^ M`, `ψ_x` is a character `χ`; take `R = χ • ρ`.
  let B : Type := QuotSpan (ℓ ^ M : O')
  let χ : Gal(Ω/E) →* B := pointChar h (fun j ↦ algebraMap O' B (1 + x j)) hx_pow
  have hχ (g : Gal(Ω/E)) : χ g = algebraMap O' B (MvPolynomial.eval x (universalChar h g)) := by
    simp [χ, eval_universalChar]
  let red : QuotSpan (ℓ ^ M : O) →+* B := Ideal.quotientMap _ e (by simp)
  let R : Gal(Ω/E) →* Matrix n n B := twistRep red χ (reduceModPow ℓ M ρ)
  have hR (g : Gal(Ω/E)) : R g = χ g • (reduceModPow ℓ M ρ g).map red := rfl
  refine ⟨R, fun g u ↦ ?_, fun g hg ↦ by simp [hR, hχ, hg, B]⟩
  rw [← map_mk_smul]
  congr 1
  ext j k
  simp [hR, hχ, pointTwist, reduceModPow, red, B]

/-- Let `v ∤ ℓ` be a prime of the CM field `E` of norm `≡ 1` modulo `ℓ ^ N`, and let `a` consist of
a place over `v`, a Frobenius element `φ`, the tame generator `γ` and a character
(`IsAuxPrimeDataAt`). Let `S` contain `v` and its complex conjugate `star v`, let `ρ` be trivial
on inertia above `S` near `1`, and let each element of inertia above `S` act by a scalar `α` with
`∑ j < ℓ ^ N, α ^ j = 0`. Then every locally constant cocycle `c` has
`(φ_b - 1) c(γ_b) = (γ_b - 1) c(φ_b)`. Here `g_b = idOrConjInv b g` is `g` for `b = true` and
`(τ g τ)⁻¹` for `b = false`, where `τ = cmConj` is the chosen complex conjugation of `Ω`. -/
lemma sub_one_smul_eq_of_isAuxPrimeDataAt {B : Type} [AddCommGroup B] [Module O B]
    {c : Gal(Ω/E) → n → B} (hc : ∀ g h : Gal(Ω/E), c (g * h) = c g + ρ g • c h)
    (hc_lc : IsLocallyConstant c) {S : Set (FinPlace E)}
    (h_open : ∀ᶠ g : Gal(Ω/E) in nhds 1, g ∈ inertiaAbove S → ρ g = 1)
    (h_scalar : ∀ g ∈ inertiaAbove S, ∃ α : O, ρ g = α • 1 ∧ ∑ j ∈ range (ℓ ^ N), α ^ j = 0)
    {v : FinPlace E} {a : AuxPrimeData E (ℓ ^ N)}
    (ha : IsAuxPrimeDataAt (placesDividing E ℓ) v a) (hv : v ∈ S) (hv_star : star v ∈ S)
    (b : Bool) :
    (ρ (idOrConjInv b a.frob) - 1) • c (idOrConjInv b a.tameGenerator) =
      (ρ (idOrConjInv b a.tameGenerator) - 1) • c (idOrConjInv b a.frob) := by
  have h_tame {w : FinPlace E} {A : ClosurePlace} (hA : IsPlaceOver A w) (hw : w ∈ S)
      (hℓ : w ∉ placesDividing E ℓ) {φ γ : Gal(Ω/E)} (hφ : IsFrob A v.q φ ∨ IsFrob A v.q φ⁻¹)
      (hγ : γ ∈ inertiaGroup Gal(Ω/E) A) : (ρ φ - 1) • c γ = (ρ γ - 1) • c φ :=
    sub_one_smul_eq_of_tame hc hA hc_lc (h_open.mono fun g hg hgA ↦ hg ⟨w, hw, A, hA, hgA⟩)
      (q := ℓ ^ N) (by simp [hA.valuation_natCast_eq_one_iff.2 hℓ])
      (fun g hgA ↦ h_scalar g ⟨w, hw, A, hA, hgA⟩) ha.norm_modEq hφ hγ
  cases b
  · -- At the conjugate prime, `φ_w` is the inverse of a Frobenius element.
    exact h_tame ha.isPlaceOver.conjPlace_star hv_star (by simpa using ha.notMem)
      (.inr (by simpa [idOrConjInv] using ha.isFrob.conjPlace_conjGal))
      (inv_mem (conjGal_mem_inertiaGroup_iff.2 ha.tame_gen.left))
  · exact h_tame ha.isPlaceOver hv ha.notMem (.inl ha.isFrob) ha.tame_gen.left

/-- Let `J` be a finite set of primes of the CM field `E` that lie, with their conjugates, outside
`S₀`, and let `d` attach to each `u ∈ J` a Frobenius element `φ_u`, a tame generator `γ_u` of
inertia and a character `λ_u` to `ℤ / ℓ ^ N`. This is the part of `hp` (`IsTiedPrimes`) that is
used; its conditions on the first prime `P₀`, the set `W`, the properties `V` and the slopes play no
role. Let `ρ` modulo `ℓ ^ M` (`reduceModPow`) be trivial on inertia outside `S₀`. Let `e : O →+* O'`
be a ring map, let `x` be a point over `O'` with coordinates divisible by `y`, and let
`∑ j < ℓ ^ N, α ^ j` vanish modulo `ℓ ^ M` whenever `α ≡ 1` modulo `y`. Let `g` act through the
twist `pointTwist`, the matrix `ψ_x(g) e(ρ(g))` with `ψ_x(g) = ∏_{u ∈ J} (1 + x_u) ^ (λ_u g)`, and
let `z` be a locally constant cocycle in `(O' / ℓ ^ M) ^ n` for this twist, unramified outside `S`
and obeying the linear relations `L` (`selmerAtPoint`). Then `(φ_w - 1) z(γ_w) = (γ_w - 1) z(φ_w)`
for `w` a prime `v` of `J` (`b = true`) or its conjugate (`b = false`), where `φ_w`, `γ_w` are
`φ_v`, `γ_v` or their conjugate inverses (`idOrConjInv`). -/
lemma IsTiedPrimes.frob_sub_one_smul_eq [ThePrime ℓ] (hp : IsTiedPrimes ℓ S₀ V W N P₀ J d)
    (h_unr : ∀ g ∈ inertiaAbove S₀ᶜ, reduceModPow ℓ M ρ g = 1) {O' : Type} [CommRing O']
    (e : O →+* O') {y : O'}
    (h_geom_sum : ∀ α : O', y ∣ α - 1 → (ℓ ^ M : O') ∣ ∑ j ∈ range (ℓ ^ N), α ^ j)
    {x : J → O'} (hx_dvd : ∀ w : J, y ∣ x w)
    {S : Set (FinPlace E)} {L : Set (Gal(Ω/E) →₀ Matrix n n O)}
    {z : Gal(Ω/E) → n → QuotSpan (ℓ ^ M : O')}
    (hz : z ∈ selmerAtPoint ℓ M (fun v : J ↦ (d v).1.character) ρ S L e x) (v : J) (b : Bool) :
    (pointTwist (fun u : J ↦ (d u).1.character) x e ρ (idOrConjInv b (d v).1.frob) - 1) •
        z (idOrConjInv b (d v).1.tameGenerator) =
      (pointTwist (fun u : J ↦ (d u).1.character) x e ρ (idOrConjInv b (d v).1.tameGenerator) - 1) •
        z (idOrConjInv b (d v).1.frob) := by
  -- Modulo `ℓ ^ M` the twist is a representation `R`. Inertia off `S₀` acts by scalars `≡ 1`
  -- modulo `y`, and trivially near the identity.
  let B : Type := QuotSpan (ℓ ^ M : O')
  let lam (w : J) : Gal(Ω/E) →* Multiplicative (ZMod (ℓ ^ N)) := (d w).1.character
  have h_sum {α : O'} (hα : y ∣ α - 1) : ∑ j ∈ range (ℓ ^ N), algebraMap O' B α ^ j = 0 := by
    simpa [B] using (Ideal.Quotient.eq_zero_iff_dvd _ _).2 (h_geom_sum α hα)
  have hx_pow (w : J) : algebraMap O' B (1 + x w) ^ ℓ ^ N = 1 := by
    rw [← sub_eq_zero, ← geom_sum_mul, h_sum (by simp [hx_dvd]), zero_mul]
  obtain ⟨R, hR_smul, hR_scalar⟩ : ∃ R : Gal(Ω/E) →* Matrix n n B,
      (∀ (g : Gal(Ω/E)) (u : n → B), R g • u = pointTwist lam x e ρ g • u) ∧
      ∀ g : Gal(Ω/E), reduceModPow ℓ M ρ g = 1 →
        R g = algebraMap O' B (MvPolynomial.eval x (universalChar lam g)) • 1 :=
    exists_monoidHom_smul_eq_pointTwist_smul lam e hx_pow
  obtain ⟨hz_cocycle, -, -, hz_lc⟩ := mem_selmerModule_iff.1 hz
  have hc (g g' : Gal(Ω/E)) : z (g * g') = z g + R g • z g' := by rw [hR_smul, hz_cocycle]
  have h_open : ∀ᶠ g : Gal(Ω/E) in nhds 1, g ∈ inertiaAbove S₀ᶜ → R g = 1 := by
    have h_near : ∀ᶠ g : Gal(Ω/E) in nhds 1, ∀ u : J, lam u g = lam u 1 :=
      Filter.eventually_all.2 fun u ↦ (hp.isAuxPrimeDataAt u u.2).isLocallyConstant.eventually_eq 1
    filter_upwards [h_near] with g hg hg_inertia
    simp [hR_scalar g (h_unr g hg_inertia), eval_universalChar, hg]
  have h_scalar (g : Gal(Ω/E)) (hg : g ∈ inertiaAbove S₀ᶜ) :
      ∃ α : B, R g = α • 1 ∧ ∑ j ∈ range (ℓ ^ N), α ^ j = 0 :=
    ⟨_, hR_scalar g (h_unr g hg), h_sum (dvd_eval_universalChar_sub_one lam hx_dvd g)⟩
  obtain ⟨hv_off, -, -, hv_star_off⟩ := hp.auxiliary v v.2
  -- Tame inertia at `v` or at its conjugate, both off `S₀`, gives the relation for `R`.
  simpa only [sub_smul, one_smul, hR_smul] using
    sub_one_smul_eq_of_isAuxPrimeDataAt hc hz_lc h_open h_scalar (hp.isAuxPrimeDataAt v v.2)
      hv_off hv_star_off b

/-- Let `J` be a finite set of primes of the CM field `E` that lie, with their conjugates, outside
`S₀`. Let `d` attach to each `v ∈ J` a Frobenius element `φ_v`, a tame generator `γ_v` of inertia, a
character `λ_v` to `ℤ / ℓ ^ N` and a slope `s_v = (d v).2 i` in `O` for the index `i : ι`. The
hypothesis `hp` (`IsTiedPrimes`) says this, and further that `P₀ ∈ J` is a first prime, that for
`v ≠ P₀` the value `λ_u(φ_v)` is `1` for `u = P₀` and `0` otherwise, and that the property `V i`
holds at `φ_v` and its conjugate inverse if `s_v ≠ 0`.

Let `ρ` modulo `ℓ ^ M` be trivial on inertia outside `S₀` and at the elements with the property
`V i`, and let `∑ j < ℓ ^ N, α ^ j` vanish modulo `ℓ ^ M` whenever `α ≡ 1` modulo `y`. Let `z` be a
locally constant cocycle for the twist of `ρ` at the point `x_{P₀} = y`, `x_v = e(s_v) y`,
unramified outside `S` and obeying the linear relations `L` (`selmerOnLine`). Then the matrix
`(1 + y) e(ρ(φ_w)) - 1` kills `z(γ_w) - e(s_v) z(φ_w)`. Here `w` is a prime `v` of `J` (`b = true`)
or its conjugate (`b = false`), where `φ_w`, `γ_w` are `φ_v`, `γ_v` or their conjugate inverses
(`idOrConjInv`), and `v` may be `P₀` only if `y = 0`. -/
lemma IsTiedPrimes.frob_sub_one_smul_tie_eq_zero_of_selmerOnLine [ThePrime ℓ]
    (hp : IsTiedPrimes ℓ S₀ V W N P₀ J d) (hN : N ≠ 0) (i : ι)
    (h_unr : ∀ g ∈ inertiaAbove S₀ᶜ, reduceModPow ℓ M ρ g = 1)
    (h_triv_of_V : ∀ g : Gal(Ω/E), V i g → reduceModPow ℓ M ρ g = 1) {O' : Type} [CommRing O']
    (e : O →+* O') {y : O'}
    (h_geom_sum : ∀ α : O', y ∣ α - 1 → (ℓ ^ M : O') ∣ ∑ j ∈ range (ℓ ^ N), α ^ j)
    {S : Set (FinPlace E)} {L : Set (Gal(Ω/E) →₀ Matrix n n O)}
    {z : Gal(Ω/E) → n → QuotSpan (ℓ ^ M : O')}
    (hz : z ∈ selmerOnLine ℓ M ρ P₀ J d i e y S L) (v : J)
    (hy_zero_of_eq_first : ↑v = P₀ → y = 0) (b : Bool) :
    ((1 + y) • (ρ (idOrConjInv b (d v).1.frob)).map e - 1) •
      (z (idOrConjInv b (d v).1.tameGenerator) - e ((d v).2 i) • z (idOrConjInv b (d v).1.frob)) =
        0 := by
  let x (w : J) : O' := e (lineDirection P₀ J d i w) * y
  let lam (w : J) : Gal(Ω/E) →* Multiplicative (ZMod (ℓ ^ N)) := (d w).1.character
  let φ : Gal(Ω/E) := idOrConjInv b (d v).1.frob
  let γ : Gal(Ω/E) := idOrConjInv b (d v).1.tameGenerator
  -- We have `ψ_x(γ) = 1 + s y` and `ψ_x(φ) = 1 + y`. At the first prime `y = 0`, and both values
  -- are `1`.
  have hψγ : MvPolynomial.eval x (universalChar lam γ) = 1 + e ((d v).2 i) * y := by
    by_cases hvP : ↑v = P₀
    · simp [universalChar, x, hy_zero_of_eq_first hvP]
    · simp [γ, lam, hp.universalChar_tame_gen hN v, x, lineDirection, hvP]
  have hψφ : MvPolynomial.eval x (universalChar lam φ) = 1 + y := by
    by_cases hvP : ↑v = P₀
    · simp [universalChar, x, hy_zero_of_eq_first hvP]
    · simp [φ, lam, hp.universalChar_frob hN v.2 hvP, x, lineDirection]
  have h_trivial {g : Gal(Ω/E)} (hg : reduceModPow ℓ M ρ g = 1) (u : n → QuotSpan (ℓ ^ M : O')) :
      (ρ g).map e • u = u := by
    simpa using map_smul_eq_of_reduceModPow_eq (hg.trans (map_one _).symm) e u
  obtain ⟨hv_off, -, -, hv_star_off⟩ := hp.auxiliary v v.2
  have hγ : reduceModPow ℓ M ρ γ = 1 :=
    have hd : IsAuxPrimeDataAt (placesDividing E ℓ) v (d v).1 := hp.isAuxPrimeDataAt v v.2
    h_unr γ (idOrConjInv_mem_inertiaAbove hd.isPlaceOver hd.tame_gen.left
      ⟨hv_off, hv_star_off⟩ b)
  let Φ : Matrix n n O' := (1 + y) • (ρ φ).map e
  have hγ_act (u : n → QuotSpan (ℓ ^ M : O')) :
      pointTwist lam x e ρ γ • u = (1 + e ((d v).2 i) * y) • u := by
    rw [pointTwist, hψγ, smul_assoc, h_trivial hγ]
  have hφ_twist : pointTwist lam x e ρ φ = Φ := by rw [pointTwist, hψφ]
  have h_commute : (Φ - 1) • z γ = (e ((d v).2 i) * y) • z φ := by
    have h_eq : (pointTwist lam x e ρ φ - 1) • z γ = (pointTwist lam x e ρ γ - 1) • z φ :=
      hp.frob_sub_one_smul_eq h_unr e h_geom_sum (fun w : J ↦ dvd_mul_left y _) hz v b
    simpa [hφ_twist, sub_smul, hγ_act, add_smul] using h_eq
  -- Moreover `s (φ - 1)` acts on `z φ` as `s y`, as `γ - 1` does: if `s ≠ 0` then `ρ(φ) ≡ 1`
  -- modulo `ℓ ^ M`.
  have h_slope : (e ((d v).2 i) * y) • z φ = e ((d v).2 i) • (Φ - 1) • z φ := by
    by_cases hs : (d v).2 i = 0
    · simp [hs]
    · simp [Φ, sub_smul, add_smul, mul_smul,
        h_trivial (h_triv_of_V φ (hp.apply_idOrConjInv_of_slope_ne_zero v.2 hs b))]
  show (Φ - 1) • (z γ - e ((d v).2 i) • z φ) = 0
  rw [smul_sub, h_commute, smul_comm, h_slope, sub_self]

/-- Let `J` be a finite set of primes of the CM field `E` that lie, with their conjugates, outside
`S₀`. Let `d` attach to each `v ∈ J` a Frobenius element `φ_v`, a tame generator `γ_v` of inertia, a
character to `ℤ / ℓ ^ N` and a slope `s_v = (d v).2 i` in `O` for the index `i : ι`. The hypothesis
`hp` (`IsTiedPrimes`) says this, singles out a first prime `P₀ ∈ J` with Frobenius element in `W`,
fixes the values of the characters at the `φ_v` with `v ≠ P₀`, and gives the property `V i` at `φ_v`
and its conjugate inverse if `s_v ≠ 0`.

Let `ρ` modulo `ℓ ^ M` be trivial on inertia outside `S₀` and at the elements with the property
`V i`, and let `∑ j < ℓ ^ N, α ^ j` vanish modulo `ℓ ^ M` whenever `α ≡ 1` modulo `y`. Consider the
locally constant cocycles `z` for the twist of `ρ` at the point `x_{P₀} = y`, `x_v = e(s_v) y`,
unramified outside `S` and obeying the linear relations `L` (`selmerOnLine`). Let `I ⊆ J` contain
`P₀` only if `y = 0`, and let `w` run over the primes `v` of `I` and their conjugates, where `φ_w`,
`γ_w` are `φ_v`, `γ_v` or conjugate inverses (`idOrConjInv`). The quotient by the cocycles with
`z(γ_w) = e(s_v) z(φ_w)` for all `w` (`tieRelations`) has length (`relLength`) at most the sum of
the lengths of the kernels of the `(1 + y) e(ρ(φ_w)) - 1` on `(O' / ℓ ^ M) ^ n`. -/
lemma IsTiedPrimes.relLength_tied_le_sum_ker [ThePrime ℓ]
    (hp : IsTiedPrimes ℓ S₀ V W N P₀ J d) (hN : N ≠ 0)
    (i : ι) (h_unr : ∀ g ∈ inertiaAbove S₀ᶜ, reduceModPow ℓ M ρ g = 1)
    (h_triv_of_V : ∀ g : Gal(Ω/E), V i g → reduceModPow ℓ M ρ g = 1) {O' : Type} [CommRing O']
    [DVR O'] (e : O →+* O') {y : O'}
    (h_geom_sum : ∀ α : O', y ∣ α - 1 → (ℓ ^ M : O') ∣ ∑ j ∈ range (ℓ ^ N), α ^ j)
    (S : Set (FinPlace E)) (L : Set (Gal(Ω/E) →₀ Matrix n n O))
    {I : Finset (FinPlace E)} (hI : I ⊆ J) (hy_zero_of_first_mem : P₀ ∈ I → y = 0) :
    relLength (selmerOnLine ℓ M ρ P₀ J d i e y S L)
        (selmerOnLine ℓ M ρ P₀ J d i e y S (L ∪ tieRelations I d i)) ≤
      ∑ v : I, ∑ b : Bool, length O' (LinearMap.ker
        (((1 + y) • (ρ (idOrConjInv b (d v).1.frob)).map e - 1) • 1 :
          End O' (n → QuotSpan (ℓ ^ M : O')))) := by
  let B : Type := QuotSpan (ℓ ^ M : O')
  let Sel (L' : Set (Gal(Ω/E) →₀ Matrix n n O)) : Submodule O' (Gal(Ω/E) → n → B) :=
    selmerOnLine ℓ M ρ P₀ J d i e y S L'
  let φ (p : I × Bool) : Gal(Ω/E) := idOrConjInv p.2 (d p.1).1.frob
  let γ (p : I × Bool) : Gal(Ω/E) := idOrConjInv p.2 (d p.1).1.tameGenerator
  let tie (p : I × Bool) : (Gal(Ω/E) → n → B) →ₗ[O'] n → B :=
    LinearMap.proj (γ p) - e ((d p.1).2 i) • LinearMap.proj (φ p)
  have h_tied : Sel L ⊓ ⨅ p, (tie p).ker ≤ Sel (L ∪ tieRelations I d i) := by
    rintro z ⟨hz, hz_tie⟩
    obtain ⟨h_cocycle, h_unram, hL, h_lc⟩ := mem_selmerModule_iff.1 hz
    refine mem_selmerModule_iff.2 ⟨h_cocycle, h_unram, mem_obeying.2 ?_, h_lc⟩
    rintro _ ⟨f, hf | ⟨p, rfl⟩, rfl⟩
    · exact mem_obeying.1 hL _ ⟨f, hf, rfl⟩
    · simpa [tie, mapRel, Finsupp.mapRange_sub', Matrix.map_smul'] using
        (Submodule.mem_iInf _).1 hz_tie p
  calc
    relLength (Sel L) (Sel (L ∪ tieRelations I d i)) ≤ relLength (Sel L) (⨅ p, (tie p).ker) :=
      relLength_le_of_mapsTo LinearMap.id (fun _ hz ↦ hz) fun z hz hz' ↦ h_tied ⟨hz, hz'⟩
    _ ≤ ∑ p : I × Bool, relLength (Sel L) (tie p).ker := relLength_iInf_le _ _
    _ = ∑ v : I, ∑ b : Bool, relLength (Sel L) (tie (v, b)).ker := Fintype.sum_prod_type _
    _ ≤ _ := sum_le_sum fun v _ ↦ sum_le_sum fun b _ ↦ by
      -- The image of `Sel L` under `tie (v, b)` lies in the kernel.
      have hy_zero_of_eq_first (h_first : ↑v = P₀) : y = 0 :=
        hy_zero_of_first_mem (by simp [← h_first])
      rw [relLength_ker]
      refine length_mono ?_
      rintro _ ⟨z, hz, rfl⟩
      exact hp.frob_sub_one_smul_tie_eq_zero_of_selmerOnLine hN i h_unr h_triv_of_V e h_geom_sum hz
        ⟨v, hI v.property⟩ hy_zero_of_eq_first b

open scoped Classical in
/-- Let `J` be a finite set of primes of the CM field `E` that lie, with their conjugates, outside
`S₀`. Let `d` attach to each `v ∈ J` a Frobenius element `φ_v`, a tame generator `γ_v` of inertia, a
character to `ℤ / ℓ ^ N` and a slope `s_v = (d v).2 i` in `O` for the index `i : ι`. The hypothesis
`hp` (`IsTiedPrimes`) says this, singles out a first prime `P₀ ∈ J` with Frobenius element in `W`,
fixes the values of the characters at the `φ_v` with `v ≠ P₀`, and gives the property `V i` at `φ_v`
and its conjugate inverse if `s_v ≠ 0`.

Let `ρ` modulo `ℓ ^ M` be trivial on inertia outside `S₀` and at the elements with the property
`V i`, and let `∑ j < ℓ ^ N, α ^ j` vanish modulo `ℓ ^ M` whenever `α ≡ 1` modulo `y`. Consider the
locally constant cocycles `z` for the twist of `ρ` at the point `x_{P₀} = y`, `x_v = e(s_v) y`,
unramified outside `S` and obeying the linear relations `L` (`selmerOnLine`). Adding the ties
`z(γ_w) = e(s_v) z(φ_w)` for `w` a prime `v ≠ P₀` of `J` or its conjugate (`tieRelations`) lowers
the length by at most the normalised valuation `addVal` of `tiePolynomial ρ (J.erase P₀) d`, with
coefficients mapped by `e`, evaluated at `y`. -/
lemma IsTiedPrimes.relLength_tied_le [ThePrime ℓ]
    (hp : IsTiedPrimes ℓ S₀ V W N P₀ J d) (hN : N ≠ 0) (i : ι)
    (h_unr : ∀ g ∈ inertiaAbove S₀ᶜ, reduceModPow ℓ M ρ g = 1)
    (h_triv_of_V : ∀ g : Gal(Ω/E), V i g → reduceModPow ℓ M ρ g = 1) {O' : Type} [CommRing O']
    [DVR O'] (e : O →+* O') {y : O'}
    (h_geom_sum : ∀ α : O', y ∣ α - 1 → (ℓ ^ M : O') ∣ ∑ j ∈ range (ℓ ^ N), α ^ j)
    (S : Set (FinPlace E)) (L : Set (Gal(Ω/E) →₀ Matrix n n O)) :
    relLength (selmerOnLine ℓ M ρ P₀ J d i e y S L)
        (selmerOnLine ℓ M ρ P₀ J d i e y S (L ∪ tieRelations (J.erase P₀) d i)) ≤
      addVal O' ((tiePolynomial ρ (J.erase P₀) d).eval₂ e y) := by
  let Φ (v : J.erase P₀) (b : Bool) : Matrix n n O' :=
    (1 + y) • (ρ (idOrConjInv b (d v).1.frob)).map e - 1
  calc
    _ ≤ ∑ v, ∑ b, length O' (LinearMap.ker (Φ v b • 1 : End O' (n → QuotSpan (ℓ ^ M : O')))) :=
      hp.relLength_tied_le_sum_ker hN i h_unr h_triv_of_V e h_geom_sum S L (J.erase_subset P₀)
        fun h ↦ absurd h (J.notMem_erase P₀)
    _ ≤ ∑ v, ∑ b, addVal O' (Φ v b).det :=
      sum_le_sum fun v _ ↦ sum_le_sum fun b _ ↦ length_ker_le_addVal_det (Φ v b) _
    _ = addVal O' ((tiePolynomial ρ (J.erase P₀) d).eval₂ e y) := by
      simp only [tiePolynomial, eval₂_finsetProd, eval₂_shiftedDet, addVal_prod,
        Fintype.sum_prod_type, Φ]

/-- Release of the first prime. Let `J` be a finite set of primes of the CM field `E` that lie, with
their conjugates, outside `S₀`. Let `d` attach to each `v ∈ J` a Frobenius element, a tame generator
of inertia, a character to `ℤ / ℓ ^ N` and a slope `(d v).2 i` in `O` for the index `i : ι`. The
hypothesis `hp` (`IsTiedPrimes`) says this, singles out a first prime `P₀ ∈ J` of slope `0` with
Frobenius element `φ₀` in `W`, and gives the property `V i` at the Frobenius elements of the primes
with nonzero slope.

Let `ρ` modulo `ℓ ^ M` be trivial on inertia outside `S₀` and at the elements with the property
`V i`, let `M ≤ N`, and let `φ₀` and its conjugate inverse `φ₀^{-c}` (`idOrConjInv`) act modulo
`ℓ ^ M` as `g₀` and `g₀^{-c}`. Consider the locally constant cocycles `z` for `ρ` in
`(O / ℓ ^ M) ^ n`, unramified outside `S` and obeying the linear relations `L` (`selmerModule`). The
relations `tieRelations {P₀} d i` say `z(γ₀) = 0 = z(γ₀^{-c})` for the tame generator `γ₀` at `P₀`.
Adding them lowers the length by at most `∑ v(det (ρ(g) - 1))`, over `g = g₀, g₀^{-c}` (`relLength`
is the length of the quotient, `v = addVal` the normalised valuation). -/
lemma IsTiedPrimes.relLength_tieRelations_le_sum_addVal_det [ThePrime ℓ] [DVR O]
    (hp : IsTiedPrimes ℓ S₀ V W N P₀ J d) (hN : N ≠ 0)
    (i : ι) (h_unr : ∀ g ∈ inertiaAbove S₀ᶜ, reduceModPow ℓ M ρ g = 1)
    (h_triv_of_V : ∀ g : Gal(Ω/E), V i g → reduceModPow ℓ M ρ g = 1) (hMN : M ≤ N) {g₀ : Gal(Ω/E)}
    (h_frob_first : ∀ b : Bool, reduceModPow ℓ M ρ (idOrConjInv b (d P₀).1.frob) =
      reduceModPow ℓ M ρ (idOrConjInv b g₀))
    (S : Set (FinPlace E)) (L : Set (Gal(Ω/E) →₀ Matrix n n O)) :
    relLength (selmerModule ρ S L (QuotSpan (ℓ ^ M : O)))
        (selmerModule ρ S (L ∪ tieRelations {P₀} d i) (QuotSpan (ℓ ^ M : O))) ≤
      ∑ b : Bool, addVal O (ρ (idOrConjInv b g₀) - 1).det := by
  have h_geom_sum (α : O) (hα : 0 ∣ α - 1) : (ℓ ^ M : O) ∣ ∑ j ∈ range (ℓ ^ N), α ^ j := by
    obtain rfl : α = 1 := sub_eq_zero.1 (zero_dvd_iff.1 hα)
    simpa using pow_dvd_pow (ℓ : O) hMN
  let K (A : Matrix n n O) : Submodule O (n → QuotSpan (ℓ ^ M : O)) :=
    LinearMap.ker ((A - 1) • 1 : End O (n → QuotSpan (ℓ ^ M : O)))
  let Φ (b : Bool) : Matrix n n O :=
    (1 + 0 : O) • (ρ (idOrConjInv b (d P₀).1.frob)).map (RingHom.id O)
  have h_ker (b : Bool) : K (Φ b) ≤ K (ρ (idOrConjInv b g₀)) := by
    intro u hu
    have h_eq : ρ (idOrConjInv b (d P₀).1.frob) • u = ρ (idOrConjInv b g₀) • u := by
      simpa using map_smul_eq_of_reduceModPow_eq (h_frob_first b) (RingHom.id O) u
    simpa [K, Φ, sub_smul, h_eq] using hu
  calc
    _ ≤ ∑ b : Bool, length O (K (Φ b)) := by
      -- At `y = 0`, where the point of the line is `0`, the two tie maps take their values in the
      -- kernels of `ρ(φ₀) - 1` and `ρ(φ₀^{-c}) - 1`.
      simpa [K, Φ, selmerOnLine_zero] using
        hp.relLength_tied_le_sum_ker hN i h_unr h_triv_of_V (RingHom.id O) h_geom_sum S L
          (singleton_subset_iff.2 hp.first_mem) fun _ ↦ rfl
    _ ≤ ∑ b : Bool, length O (K (ρ (idOrConjInv b g₀))) :=
      sum_le_sum fun b _ ↦ length_mono (h_ker b)
    _ ≤ _ := sum_le_sum fun b _ ↦ length_ker_le_addVal_det _ _

end Line

end New.Selmer

end
