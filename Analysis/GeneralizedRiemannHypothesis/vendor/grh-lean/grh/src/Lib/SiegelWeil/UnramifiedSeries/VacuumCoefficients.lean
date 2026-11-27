import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Lib.Adelic.AutomorphicForms.PAdicGauge
import Lib.ClassField.HeckeCharacter.TameModulus
import Lib.SiegelWeil.NeighbourLattices

/-!
# Vacuum coefficients, coset representatives and the weight of steps through neighbours

This file defines the coefficients of the vacuum `New.SiegelWeil.vacuumCoeff`, the representatives
`New.SiegelWeil.cosetRep` of the cosets of `localLevel n A` and the series
`New.SiegelWeil.rallisSeries`. It shows that the coefficients and the cosets are multiplicative over
two sets of places with disjoint supports. It bounds sums along a walk (`New.tsum_le_of_walk`) and
shows that every residue field has at least four elements if `E` contains a primitive root of unity
of order `5040` (`New.FinPlace.four_le_q`). It defines the weight `New.SiegelWeil.stepWeight` of the
steps at a place to a neighbouring lattice and bounds it for `2 * card n < M`. If these weights over
`A` and its conjugate add up to at most `1 / 3`, it bounds the sum of the moduli of the coefficients
(`New.SiegelWeil.tsum_ofReal_norm_vacuumCoeff_le`).

## Main definitions and results

* `New.SiegelWeil.vacuumCoeff`, `New.SiegelWeil.cosetRep`, `New.SiegelWeil.rallisSeries`: the
  coefficients, the representatives of the cosets and the series.
* `New.SiegelWeil.stepWeight`: the number `stepWeight n M w`, with the bounds
  `New.SiegelWeil.tsum_stepWeight_conjClosure_singleton_le` and
  `New.SiegelWeil.summable_stepWeight`.

Notions from other files:
* `localLevel n A`: the points of `Gf E n` integral at the places of `A`; `stdLevel E n`: the points
  integral at all finite places.
* `supportedOn n A`: the points with component `1` outside `A` and its conjugate, whose union is
  `A.conjClosure`; `trivialOn n A`: the points with component `1` at `A`.
* `finMultiplier`: the multiplier of a finite point; its squared modulus is the index
  `[L : L ∩ γ⁻¹ L] = [γ L : L ∩ γ L]` at the point `γ`.
* `AutChar E`: the characters `b` of the norm-one adeles of `E` trivial on the norm-one elements of
  `E`; `detFin 1 g`: the determinant of the finite point `g`, as such an adele with component `1` at
  the infinite places.
* `HasLevel y K`: right translation by each point of `K` fixes the function `y` on the adelic points
  `G E s`, the products of a point of `GInf E s` (the real points, the only part that depends on the
  signs `s : n → ℤˣ`) and a point of `Gf E n`.

## Relation to the literature

Known; see `Lib.SiegelWeil.UnramifiedSeries.RallisSeries` for sources.
-/

noncomputable section

namespace New.SiegelWeil

open Matrix MeasureTheory Fintype Space Gf G WeilData NumberField Rows

variable {E n m : Type} [Field E] [CMType E] [WeilData E] [Fintype n] [DecidableEq n] [Fintype m]
  {s : n → ℤˣ} {b : AutChar E} {A : Set (FinPlace E)} {y : G E s → ℂ}

/-! ### Vacuum coefficients and coset representatives -/

/-- For `g` in the finite adelic unitary group, the multiplier `finMultiplier g` is the
`glMultiplier` of its underlying matrix in GL_n(𝔸_f). It is unchanged by multiplying `g` on either
side by integral finite points: `finMultiplier (k * g * k') = finMultiplier g` for all `k, k'` in
`stdLevel E n` = G_f ∩ GL_n(Ô). -/
lemma finMultiplier_mul_mul_of_mem_stdLevel {k k' : Gf E n} (hk : k ∈ stdLevel E n)
    (hk' : k' ∈ stdLevel E n) (g : Gf E n) : finMultiplier (k * g * k') = finMultiplier g :=
  glMultiplier_mul_of_mem g.val hk hk'

/-- The multiplier of a product of two finite points of which, at each place, one has component
`1` is the product of their multipliers. -/
lemma finMultiplier_mul_of_forall_atPlace_eq_one_or {g g' : Gf E n}
    (h_atPlace : ∀ w : FinPlace E, g.atPlace w = 1 ∨ g'.atPlace w = 1) :
    finMultiplier (g * g') = finMultiplier g * finMultiplier g' :=
  glMultiplier_mul_of_map_evalAt_eq_one h_atPlace

/-- The number `(b(det g) * finMultiplier g ^ M)⁻¹` for a finite point `g`. For `M` the rank of
the second hermitian space of a pair it is the factor by which `g` changes the matrix coefficient
of a vacuum (`New.SiegelWeil.weilMatrixCoeff_mul`). -/
def vacuumCoeff (M : ℕ) (b : AutChar E) (g : Gf E n) : ℂ :=
  (b.val (detFin 1 g) * finMultiplier g ^ M)⁻¹

/-- For a coset `γ` of `localLevel n A`, the finite points integral at `A`, the component above
`A` and its conjugate of a chosen element of `γ`. It represents `γ` (`mk_cosetRep`) and is
supported on `A` and its conjugate. -/
def cosetRep (γ : Gf E n ⧸ localLevel n A) : supportedOn n A :=
  ⟨componentOn n A γ.out, componentOn_mem_supportedOn⟩

omit [WeilData E] in
lemma mk_cosetRep (q : Gf E n ⧸ localLevel n A) :
    ((cosetRep q).val : Gf E n ⧸ localLevel n A) = q := by
  conv_rhs => rw [← q.out_eq']
  rw [QuotientGroup.eq, mem_localLevel]
  exact fun w hw ↦ by simp [cosetRep, atPlace_componentOn, hw]

omit [WeilData E] in
lemma isOpen_coe_localLevel (A : Set (FinPlace E)) : IsOpen (localLevel n A : Set (Gf E n)) :=
  Subgroup.isOpen_mono stdLevel_le_localLevel isOpen_stdLevel

omit [WeilData E] in
lemma countable_quotient_localLevel (A : Set (FinPlace E)) :
    Countable (Gf E n ⧸ localLevel n A) := by
  have := QuotientGroup.discreteTopology (isOpen_coe_localLevel (n := n) A)
  exact TopologicalSpace.separableSpace_iff_countable.1 inferInstance

/-- The character `b ∘ det` is trivial on `stdLevel E n ⊓ supportedOn n A`, the integral finite
points whose component is `1` at every place outside `A` and its conjugate. -/
def IsUnramifiedOn (b : AutChar E) (n : Type) [Fintype n] [DecidableEq n]
    (A : Set (FinPlace E)) : Prop :=
  ∀ k ∈ stdLevel E n ⊓ supportedOn n A, b.val (detFin 1 k) = 1

omit [WeilData E] in
/-- If `b` has weight `γ` at the infinite places and a tame part `ψ` (the characters of the residue
fields through which `b` acts on integral units) that is trivial at `A` and its conjugate, then
`b ∘ det` is trivial on the integral finite points supported there. -/
lemma _root_.New.AutChar.HasWeight.isUnramifiedOn {γ : InfinitePlace E → ℤ}
    {ψ : ∀ w : FinPlace E, MulChar (ResField w) ℂ} (hb : b.HasWeight γ ψ)
    (hψ : ∀ w ∈ A.conjClosure, ψ w = 1) : IsUnramifiedOn b n A :=
  fun _k hk ↦ hb.apply_det_eq_one_of_supportedOn hψ hk

/-- Let `b ∘ det` be trivial on the integral points supported on `A` and its conjugate. The
coefficient of the vacuum is invariant on both sides under these points. -/
lemma vacuumCoeff_mul_mul_of_mem (hb : IsUnramifiedOn b n A) (M : ℕ) {k k' : Gf E n}
    (hk : k ∈ stdLevel E n ⊓ supportedOn n A) (hk' : k' ∈ stdLevel E n ⊓ supportedOn n A)
    (g : Gf E n) :
    vacuumCoeff M b (k * g * k') = vacuumCoeff M b g := by
  have h_det : detFin 1 (k * g * k') = detFin 1 k * detFin 1 g * detFin 1 k' := by simp [← map_mul]
  rw [vacuumCoeff, vacuumCoeff, h_det, finMultiplier_mul_mul_of_mem_stdLevel hk.1 hk'.1 g, map_mul,
    map_mul, hb _ hk, hb _ hk', one_mul, mul_one]

/-- Let `b ∘ det` be trivial on the integral finite points whose component is `1` outside `A` and
its conjugate (`IsUnramifiedOn`). Then for every `M : ℕ`, the coefficient of the vacuum `vacuumCoeff
M b k = (b(det k) · finMultiplier k ^ M)⁻¹` equals `1` at each such point `k`. -/
lemma vacuumCoeff_eq_one_of_mem (hb : IsUnramifiedOn b n A) (M : ℕ) {k : Gf E n}
    (hk : k ∈ stdLevel E n ⊓ supportedOn n A) : vacuumCoeff M b k = 1 := by
  simp [vacuumCoeff, hb _ hk, finMultiplier_eq_one_of_mem hk.1]

/-- The coefficient of the vacuum is multiplicative on two finite points of which, at each place,
one has component `1`. -/
lemma vacuumCoeff_mul_of_atPlace (M : ℕ) (b : AutChar E) {g g' : Gf E n}
    (h_atPlace : ∀ w : FinPlace E, g.atPlace w = 1 ∨ g'.atPlace w = 1) :
    vacuumCoeff M b (g * g') = vacuumCoeff M b g * vacuumCoeff M b g' := by
  have h_det : detFin 1 (g * g') = detFin 1 g * detFin 1 g' := by simp [← map_mul]
  rw [vacuumCoeff, vacuumCoeff, vacuumCoeff, h_det,
    finMultiplier_mul_of_forall_atPlace_eq_one_or h_atPlace,
    map_mul, Circle.coe_mul]
  ring

/-- The series `∑ mc(q) R(q) y` of right translates of a function `y` on the adelic points. The sum
is over the cosets `q`, in the finite points, of the subgroup of the points integral at `A`. The
coefficient of the vacuum `mc = vacuumCoeff M b` and the right translation `R` are taken at the
representative `cosetRep q`, which is supported on `A` and its conjugate; see
`mk_eq_mk_iff_of_supportedOn` for the cosets among such points and
`vacuumCoeff_mul_apply_cosetRep` for conditions under which the choice does not matter. The value
is `0` where the terms are not summable. -/
def rallisSeries (M : ℕ) (b : AutChar E) (A : Set (FinPlace E)) (y : G E s → ℂ) (g : G E s) : ℂ :=
  ∑' q : Gf E n ⧸ localLevel n A, vacuumCoeff M b (cosetRep q).val * y (g * (1, (cosetRep q).val))

omit [WeilData E] in
/-- Two finite points supported on `A` and its conjugate lie in the same coset of the points
integral at `A` exactly when they lie in the same coset of the integral points with such support. -/
lemma mk_eq_mk_iff_of_supportedOn {u u' : Gf E n} (hu : u ∈ supportedOn n A)
    (hu' : u' ∈ supportedOn n A) :
    (u : Gf E n ⧸ localLevel n A) = u' ↔ u⁻¹ * u' ∈ stdLevel E n ⊓ supportedOn n A := by
  rw [QuotientGroup.eq, Subgroup.mem_inf, and_iff_left (mul_mem (inv_mem hu) hu'),
    mem_stdLevel_iff_of_supportedOn (mul_mem (inv_mem hu) hu'), mem_localLevel]

omit [WeilData E] in
/-- The chosen representative of the coset of a point `u` supported on `A` and its conjugate differs
from `u` on the right by an integral point with such support. -/
lemma inv_mul_cosetRep_mem {u : Gf E n} (hu : u ∈ supportedOn n A) :
    u⁻¹ * (cosetRep (u : Gf E n ⧸ localLevel n A)).val ∈ stdLevel E n ⊓ supportedOn n A :=
  (mk_eq_mk_iff_of_supportedOn hu (cosetRep _).property).1 (mk_cosetRep _).symm

/-- The terms of `rallisSeries` do not depend on the representatives. Let `b ∘ det` be trivial on
the integral points supported on `A` and its conjugate, and let `y` be fixed by these points. The
term of the coset of a point `u` supported on `A` and its conjugate may be computed at `u`. -/
lemma vacuumCoeff_mul_apply_cosetRep (hb : IsUnramifiedOn b n A) (M : ℕ)
    (hy : HasLevel y (stdLevel E n ⊓ supportedOn n A)) {u : Gf E n} (hu : u ∈ supportedOn n A)
    (g : G E s) :
    vacuumCoeff M b (cosetRep (u : Gf E n ⧸ localLevel n A)).val *
        y (g * (1, (cosetRep (u : Gf E n ⧸ localLevel n A)).val)) =
      vacuumCoeff M b u * y (g * (1, u)) := by
  -- The representative is `u * j` with `j` integral and supported on `A` and its conjugate.
  let j : Gf E n := u⁻¹ * (cosetRep (u : Gf E n ⧸ localLevel n A)).val
  have hj : j ∈ stdLevel E n ⊓ supportedOn n A := inv_mul_cosetRep_mem hu
  have h_coeff : vacuumCoeff M b (u * j) = vacuumCoeff M b u := by
    simpa only [one_mul] using vacuumCoeff_mul_mul_of_mem hb M (one_mem _) hj u
  have h_assoc : g * (1, u * j) = g * (1, u) * (1, j) := by simp [mul_assoc]
  have h_rep : (cosetRep (u : Gf E n ⧸ localLevel n A)).val = u * j :=
    (mul_inv_cancel_left u _).symm
  rw [h_rep, h_coeff, h_assoc, hy j hj]

/-- The modulus of the coefficient of the vacuum at `g` is `‖finMultiplier g‖ ^ (-M)`; it does not
depend on the character. -/
lemma norm_vacuumCoeff (M : ℕ) (b : AutChar E) (g : Gf E n) :
    ‖vacuumCoeff M b g‖ = ‖finMultiplier g‖⁻¹ ^ M := by
  simp [vacuumCoeff, Circle.norm_coe]

/-- The multiplier of the chosen representative of the coset of a point `u` supported on `A` and its
conjugate is the multiplier of `u`. -/
lemma finMultiplier_cosetRep_mk {u : Gf E n} (hu : u ∈ supportedOn n A) :
    finMultiplier (cosetRep (u : Gf E n ⧸ localLevel n A)).val = finMultiplier u := by
  obtain ⟨h_int, -⟩ := Subgroup.mem_inf.1 (inv_mul_cosetRep_mem hu)
  have h_mult : finMultiplier (1 * u * (u⁻¹ * (cosetRep (u : Gf E n ⧸ localLevel n A)).val)) =
      finMultiplier u :=
    finMultiplier_mul_mul_of_mem_stdLevel (one_mem _) h_int u
  rwa [one_mul, mul_inv_cancel_left] at h_mult

/-- The coefficient of the vacuum has modulus `1` on the trivial coset. -/
lemma norm_vacuumCoeff_cosetRep_one (M : ℕ) (b : AutChar E) (A : Set (FinPlace E)) :
    ‖vacuumCoeff M b (cosetRep ((1 : Gf E n) : Gf E n ⧸ localLevel n A)).val‖ = 1 := by
  simp [norm_vacuumCoeff, finMultiplier_cosetRep_mk (one_mem _),
    finMultiplier_eq_one_of_mem (one_mem _)]

/-! ### Sums bounded by a walk -/

open scoped ENNReal in
/-- One stage of summation along a walk. Suppose that each point `x ≠ x₀` has a step `σ` that lowers
its height and satisfies `f x ≤ c σ * f (step σ x)`, and that each step is injective. Then the sum
of `f` over the points of height below `N + 1` is at most `f x₀` plus `∑ c` times the sum over the
points of height below `N`. -/
lemma _root_.New.tsum_ite_lt_succ_le_of_walk {X Step : Type*} {f : X → ℝ≥0∞}
    {c : Step → ℝ≥0∞} {height : X → ℕ} {step : Step → X → X} {x₀ : X}
    (h_inj : ∀ σ : Step, Function.Injective (step σ))
    (h_step : ∀ x : X, x ≠ x₀ →
      ∃ σ : Step, height (step σ x) < height x ∧ f x ≤ c σ * f (step σ x))
    (N : ℕ) :
    (∑' x : X, if height x < N + 1 then f x else 0) ≤
      f x₀ + (∑' σ : Step, c σ) * ∑' x : X, if height x < N then f x else 0 := by
  choose σ h_lt h_le using fun x : ({x₀}ᶜ : Set X) ↦ h_step x x.property
  let truncate (N : ℕ) (x : X) : ℝ≥0∞ := if height x < N then f x else 0
  have h_pair : Function.Injective fun x : ({x₀}ᶜ : Set X) ↦ (σ x, step (σ x) x) := by
    intro x x' h_eq
    obtain ⟨hσ, h_image⟩ : σ x = σ x' ∧ step (σ x) x = step (σ x') x' := Prod.mk.inj h_eq
    rw [hσ] at h_image
    exact Subtype.ext (h_inj (σ x') h_image)
  have h_term (x : ({x₀}ᶜ : Set X)) :
      truncate (N + 1) x ≤ c (σ x) * truncate N (step (σ x) x) := by
    by_cases hx : height x < N + 1
    · have h_next : height (step (σ x) x) < N := (h_lt x).trans_le (Nat.lt_succ_iff.1 hx)
      simpa only [truncate, ite_eq_left hx, ite_eq_left h_next] using h_le x
    · simp [truncate, hx]
  have h_base : truncate (N + 1) x₀ ≤ f x₀ := by
    by_cases hx : height x₀ < N + 1
    · simp [truncate, hx]
    · simp [truncate, hx]
  calc ∑' x : X, truncate (N + 1) x
      = truncate (N + 1) x₀ + ∑' x : ({x₀}ᶜ : Set X), truncate (N + 1) x := by
        rw [← tsum_singleton x₀ (truncate (N + 1)),
          ENNReal.summable.tsum_add_tsum_compl ENNReal.summable]
    _ ≤ f x₀ + ∑' x : ({x₀}ᶜ : Set X), c (σ x) * truncate N (step (σ x) x) :=
        add_le_add h_base (ENNReal.tsum_le_tsum h_term)
    _ ≤ f x₀ + ∑' p : Step × X, c p.1 * truncate N p.2 := add_le_add le_rfl
        (ENNReal.tsum_comp_le_tsum_of_injective h_pair fun p ↦ c p.1 * truncate N p.2)
    _ = f x₀ + (∑' σ : Step, c σ) * ∑' x : X, truncate N x := by
        simp only [ENNReal.tsum_prod', ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]

open scoped ENNReal in
/-- Summation along a walk. Suppose that each point `x ≠ x₀` has a step `σ` that lowers its height
and satisfies `f x ≤ c σ * f (step σ x)`, and that each step is injective. Then `∑ f ≤ B` for
every `B` with `f x₀ + (∑ c) * B ≤ B`, such as `f x₀` times the geometric series of ratio `∑ c`. -/
lemma _root_.New.tsum_le_of_walk {X Step : Type*} {f : X → ℝ≥0∞} {c : Step → ℝ≥0∞}
    {height : X → ℕ} {step : Step → X → X} {x₀ : X} {B : ℝ≥0∞}
    (h_inj : ∀ σ : Step, Function.Injective (step σ))
    (h_step : ∀ x : X, x ≠ x₀ →
      ∃ σ : Step, height (step σ x) < height x ∧ f x ≤ c σ * f (step σ x))
    (hB : f x₀ + (∑' σ : Step, c σ) * B ≤ B) :
    ∑' x : X, f x ≤ B := by
  -- Bound the sum over the points of height below `N` by induction on `N`.
  let truncate (N : ℕ) (x : X) : ℝ≥0∞ := if height x < N then f x else 0
  have h_trunc (N : ℕ) : ∑' x : X, truncate N x ≤ B := by
    induction N with
    | zero => simp [truncate]
    | succ N ih =>
      calc ∑' x : X, truncate (N + 1) x ≤ f x₀ + (∑' σ : Step, c σ) * ∑' x : X, truncate N x :=
            tsum_ite_lt_succ_le_of_walk h_inj h_step N
        _ ≤ f x₀ + (∑' σ : Step, c σ) * B := by gcongr
        _ ≤ B := hB
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun t ↦ ?_
  calc ∑ x ∈ t, f x = ∑ x ∈ t, truncate (t.sup height + 1) x :=
        Finset.sum_congr rfl fun x hx ↦ (ite_eq_left (Nat.lt_succ_of_le (Finset.le_sup hx))).symm
    _ ≤ B := (ENNReal.sum_le_tsum t).trans (h_trunc _)

/-! ### Two sets of places with disjoint supports -/

section Union

variable {A₁ A₂ : Set (FinPlace E)}

omit [WeilData E] in
/-- If `A₂` is disjoint from `A₁` and its conjugate, the points supported on `A₁` and its conjugate
are trivial at `A₂`. -/
lemma supportedOn_le_trivialOn_right (h_disj : Disjoint A₁.conjClosure A₂) :
    supportedOn n A₁ ≤ trivialOn n A₂ := fun _ hg ↦
  mem_trivialOn.2 fun w hw ↦ mem_supportedOn.1 hg w
    (fun hw₁ ↦ h_disj.notMem_of_mem_left (.inl hw₁) hw)
    (fun hw₁ ↦ h_disj.notMem_of_mem_left (.inr hw₁) hw)

omit [WeilData E] in
/-- If `A₂` is disjoint from `A₁` and its conjugate, the points supported on `A₂` and its conjugate
are trivial at `A₁`. -/
lemma supportedOn_le_trivialOn_left (h_disj : Disjoint A₁.conjClosure A₂) :
    supportedOn n A₂ ≤ trivialOn n A₁ := fun g hg ↦
  mem_trivialOn.2 fun w hw ↦ mem_supportedOn.1 hg w (h_disj.notMem_of_mem_left (.inl hw))
    (h_disj.notMem_of_mem_left (.inr (by simpa)))

omit [WeilData E] in
/-- Let `A₂` be disjoint from `A₁` and its conjugate, and let `u₁`, `u₂` be supported on `A₁`, `A₂`
and their conjugates. Then `u₁ * u₂` represents the coset of `g` at `A₁ ∪ A₂` exactly when `u₁`
represents it at `A₁` and `u₂` represents it at `A₂`. -/
lemma mk_mul_eq_mk_iff (h_disj : Disjoint A₁.conjClosure A₂) {u₁ u₂ : Gf E n}
    (hu₁ : u₁ ∈ supportedOn n A₁) (hu₂ : u₂ ∈ supportedOn n A₂) (g : Gf E n) :
    ((u₁ * u₂ : Gf E n) : Gf E n ⧸ localLevel n (A₁ ∪ A₂)) = g ↔
      (u₁ : Gf E n ⧸ localLevel n A₁) = g ∧ (u₂ : Gf E n ⧸ localLevel n A₂) = g := by
  have h_left : ∀ w ∈ A₁, u₂.atPlace w = 1 :=
    mem_trivialOn.1 (supportedOn_le_trivialOn_left h_disj hu₂)
  have h_right : ∀ w ∈ A₂, u₁.atPlace w = 1 :=
    mem_trivialOn.1 (supportedOn_le_trivialOn_right h_disj hu₁)
  have h_at₁ : ∀ w ∈ A₁, ((u₁ * u₂)⁻¹ * g).atPlace w = (u₁⁻¹ * g).atPlace w :=
    fun w hw ↦ by simp [h_left w hw]
  have h_at₂ : ∀ w ∈ A₂, ((u₁ * u₂)⁻¹ * g).atPlace w = (u₂⁻¹ * g).atPlace w :=
    fun w hw ↦ by simp [h_right w hw]
  simp +contextual only [QuotientGroup.eq, mem_localLevel, Set.mem_union, or_imp, forall_and,
    h_at₁, h_at₂]

omit [WeilData E] in
/-- Let `A₂` be disjoint from `A₁` and its conjugate. The cosets at `A₁ ∪ A₂` are the products of a
coset at `A₁` and a coset at `A₂`. -/
lemma bijective_mk_cosetRep_mul (h_disj : Disjoint A₁.conjClosure A₂) :
    Function.Bijective fun p : (Gf E n ⧸ localLevel n A₁) × (Gf E n ⧸ localLevel n A₂) ↦
      (((cosetRep p.1).val * (cosetRep p.2).val : Gf E n) : Gf E n ⧸ localLevel n (A₁ ∪ A₂)) := by
  -- The product represents the coset of `g` exactly when `p` is the pair of cosets of `g`.
  have h_iff (p : (Gf E n ⧸ localLevel n A₁) × (Gf E n ⧸ localLevel n A₂)) (g : Gf E n) :
      (((cosetRep p.1).val * (cosetRep p.2).val : Gf E n) : Gf E n ⧸ localLevel n (A₁ ∪ A₂)) = g ↔
        p = ((g : Gf E n ⧸ localLevel n A₁), (g : Gf E n ⧸ localLevel n A₂)) := by
    simp [mk_mul_eq_mk_iff h_disj (cosetRep _).property (cosetRep _).property, mk_cosetRep,
      Prod.ext_iff]
  refine ⟨fun p p' h_eq ↦ ((h_iff p _).1 h_eq).trans ((h_iff p' _).1 rfl).symm, fun q ↦ ?_⟩
  induction q using QuotientGroup.induction_on with
  | H g => exact ⟨_, (h_iff _ g).2 rfl⟩

/-- For `M : ℕ` and a character `b`, `vacuumCoeff M b g = (b(det g) · finMultiplier g ^ M)⁻¹` is the
factor by which a finite point `g` changes the matrix coefficient of a vacuum when `M` is the rank
of the second hermitian space. If `A₂` is disjoint from `A₁` and its conjugate, then `vacuumCoeff M
b (u₁ * u₂) = vacuumCoeff M b u₁ * vacuumCoeff M b u₂`. This holds whenever `u₁` is a finite point
supported on `A₁` and its conjugate, and `u₂` is one supported on `A₂` and its conjugate; supported
means having component `1` at every other place. -/
lemma vacuumCoeff_mul_of_disjoint (h_disj : Disjoint A₁.conjClosure A₂) (M : ℕ) (b : AutChar E)
    {u₁ u₂ : Gf E n} (hu₁ : u₁ ∈ supportedOn n A₁) (hu₂ : u₂ ∈ supportedOn n A₂) :
    vacuumCoeff M b (u₁ * u₂) = vacuumCoeff M b u₁ * vacuumCoeff M b u₂ :=
  vacuumCoeff_mul_of_atPlace M b
    (atPlace_eq_one_or hu₁ (supportedOn_le_trivialOn_left h_disj hu₂))

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.sum in
/-- Let `A₂` be disjoint from `A₁` and its conjugate. If the coefficients of the vacuum are
absolutely summable over the cosets at `A₁` and at `A₂`, they are so over the cosets at
`A₁ ∪ A₂`. -/
lemma summable_norm_vacuumCoeff_union (h_disj : Disjoint A₁.conjClosure A₂) {M : ℕ}
    (h₁ : Summable fun q : Gf E n ⧸ localLevel n A₁ ↦ ‖vacuumCoeff M b (cosetRep q).val‖)
    (h₂ : Summable fun q : Gf E n ⧸ localLevel n A₂ ↦ ‖vacuumCoeff M b (cosetRep q).val‖) :
    Summable fun q : Gf E n ⧸ localLevel n (A₁ ∪ A₂) ↦ ‖vacuumCoeff M b (cosetRep q).val‖ := by
  -- The terms at `A₁ ∪ A₂` are the products of a term at `A₁` and a term at `A₂`.
  have h_prod : Summable fun p : (Gf E n ⧸ localLevel n A₁) × (Gf E n ⧸ localLevel n A₂) ↦
      ‖vacuumCoeff M b (cosetRep p.1).val‖ * ‖vacuumCoeff M b (cosetRep p.2).val‖ :=
    h₁.mul_of_nonneg h₂ (fun _ ↦ norm_nonneg _) fun _ ↦ norm_nonneg _
  refine (Equiv.ofBijective _ (bijective_mk_cosetRep_mul h_disj)).summable_iff.1
    (h_prod.congr fun p ↦ ?_)
  have h_supp : (cosetRep p.1).val * (cosetRep p.2).val ∈ supportedOn n (A₁ ∪ A₂) :=
    mul_mem (supportedOn_mono Set.subset_union_left (cosetRep _).property)
      (supportedOn_mono Set.subset_union_right (cosetRep _).property)
  rw [← norm_mul,
    ← vacuumCoeff_mul_of_disjoint h_disj M b (cosetRep _).property (cosetRep _).property,
    Function.comp_apply, Equiv.ofBijective_apply, norm_vacuumCoeff, norm_vacuumCoeff,
    finMultiplier_cosetRep_mk h_supp]

end Union

/-! ### The number of steps at a place -/

omit [CMType E] [WeilData E] in
/-- If the CM field `E` contains a primitive root of unity of order `5040`, hence the third and
fourth roots of unity, the order `w.q` of the residue field at a finite place `w` is at least
`4`. -/
lemma _root_.New.FinPlace.four_le_q [NumberField E] [IsCMField E] [HasPrimitiveRoot5040 E]
    (w : FinPlace E) : 4 ≤ w.q := by
  -- The polynomial `1 + X + X ^ 2` has no root in the field with two elements, and `1 + X ^ 2` has
  -- none in the field with three elements; both have a root in the integers of `E`.
  obtain ⟨i, hi, -⟩ := HasPrimitiveRoot5040.exists_mul_self_eq_neg_one (E := E)
  obtain ⟨z, hz⟩ : ∃ z : 𝓞 E, IsPrimitiveRoot z 3 :=
    HasPrimitiveRoot5040.exists_isPrimitiveRoot_of_dvd (by norm_num)
  have hz_sum : 1 + z + z ^ 2 = 0 := by
    simpa [Finset.sum_range_succ] using hz.geom_sum_eq_zero (by norm_num)
  let φ : 𝓞 E →+* ResField w := algebraMap (𝓞 E) (ResField w)
  have hi' : φ i * φ i = -1 := by rw [← map_mul, hi, map_neg, map_one]
  have hz' : 1 + φ z + φ z ^ 2 = 0 := by simpa using congrArg φ hz_sum
  have : Fintype (ResField w) := Fintype.ofFinite _
  have h_card : card (ResField w) = w.q := Nat.card_eq_fintype_card.symm.trans (card_ResField w)
  have h_pow (a : ResField w) : a ^ w.q = a := by rw [← h_card, FiniteField.pow_card]
  have h_char : (w.q : ResField w) = 0 := by rw [← h_card, FiniteField.cast_card_eq_zero]
  by_contra! h_lt
  refine one_ne_zero (α := ResField w) ?_
  have h_one_lt := w.one_lt_q
  obtain hq | hq : w.q = 2 ∨ w.q = 3 := by omega
  · rw [hq] at h_pow h_char
    linear_combination hz' - h_pow (φ z) - φ z * h_char
  · rw [hq] at h_pow h_char
    linear_combination h_char - φ i * h_pow (φ i) + (φ i ^ 2 - 2) * hi'

omit [WeilData E] in
variable (n) in
/-- The steps at `w` from a lattice to a neighbour: a line in the `n`-space over the residue field
and one of the classes in `neighbourResidues w`, which tell apart the neighbours that belong to the
same line. -/
abbrev NeighbourStep (w : FinPlace E) : Type :=
  Projectivization (ResField w) (n → ResField w) × neighbourResidues w

omit [WeilData E] in
variable (n) in
/-- The number of steps at `w` (see `NeighbourStep`) times `q_w ^ (-M / 2)`, where `q_w = w.q` is
the order of the residue field at `w`. A step at `w` towards the standard lattice multiplies the
modulus of the coefficient of the vacuum `vacuumCoeff M b` by at least `q_w ^ (M / 2)`. -/
def stepWeight (M : ℕ) (w : FinPlace E) : ℝ := Nat.card (NeighbourStep n w) * (√w.q)⁻¹ ^ M

omit [WeilData E] [Fintype n] [DecidableEq n] in
lemma stepWeight_nonneg (M : ℕ) (w : FinPlace E) : 0 ≤ stepWeight n M w := by
  unfold stepWeight
  positivity

omit [WeilData E] [DecidableEq n] in
/-- For `2 n < M` the weight of the steps at `w` is at most the number of classes in
`neighbourResidues w` divided by `(q_w - 1) √q_w`: there are at most `q_w ^ n / (q_w - 1)` lines. -/
lemma stepWeight_le_card_div {M : ℕ} (h_rank : 2 * card n < M) (w : FinPlace E) :
    stepWeight n M w ≤ Nat.card (neighbourResidues w) / ((w.q - 1) * √w.q) := by
  have hq : (1 : ℝ) < w.q := by exact_mod_cast w.one_lt_q
  have hq_sub : (0 : ℝ) < w.q - 1 := sub_pos.2 hq
  have h_lines : (Nat.card (Projectivization (ResField w) (n → ResField w)) : ℝ) ≤
      w.q ^ card n / (w.q - 1) := by
    have h_eq : Nat.card (Projectivization (ResField w) (n → ResField w)) * (w.q - 1) =
        w.q ^ card n - 1 := by
      simpa [Nat.card_fun, card_ResField] using
        (Projectivization.card (ResField w) (n → ResField w)).symm
    rw [le_div_iff₀ hq_sub, ← Nat.cast_pred (zero_lt_one.trans w.one_lt_q)]
    exact_mod_cast h_eq.trans_le (Nat.sub_le _ 1)
  have h_pow : (w.q : ℝ) ^ card n * √w.q ≤ √w.q ^ M :=
    calc (w.q : ℝ) ^ card n * √w.q = √w.q ^ (2 * card n + 1) := by
          rw [pow_succ, pow_mul, Real.sq_sqrt (by positivity)]
      _ ≤ √w.q ^ M := pow_le_pow_right₀ (Real.one_le_sqrt.2 hq.le) h_rank
  calc stepWeight n M w
      = Nat.card (Projectivization (ResField w) (n → ResField w)) *
          Nat.card (neighbourResidues w) * (√w.q ^ M)⁻¹ := by
        rw [stepWeight, Nat.card_prod, Nat.cast_mul, inv_pow]
    _ ≤ w.q ^ card n / (w.q - 1) * Nat.card (neighbourResidues w) * (w.q ^ card n * √w.q)⁻¹ := by
        gcongr
    _ = Nat.card (neighbourResidues w) / ((w.q - 1) * √w.q) := by field_simp

omit [WeilData E] [DecidableEq n] in
/-- For `2 n < M` and `w` split, that is, different from its conjugate, the weight of the steps at
`w` is at most `1 / ((q_w - 1) √q_w)`. -/
lemma stepWeight_le_of_isSplit {M : ℕ} (h_rank : 2 * card n < M) {w : FinPlace E}
    (hw : w.IsSplit) : stepWeight n M w ≤ ((w.q - 1) * √w.q)⁻¹ := by
  have hq : (1 : ℝ) ≤ w.q := by exact_mod_cast w.one_lt_q.le
  have h_card : (Nat.card (neighbourResidues w) : ℝ) ≤ 1 := by
    exact_mod_cast card_neighbourResidues_le_one hw
  calc stepWeight n M w ≤ Nat.card (neighbourResidues w) / ((w.q - 1) * √w.q) :=
        stepWeight_le_card_div h_rank w
    _ ≤ 1 / ((w.q - 1) * √w.q) := by gcongr
    _ = ((w.q - 1) * √w.q)⁻¹ := one_div _

omit [DecidableEq n] in
/-- For `2 n < M` the weight of the steps at any place `w` is at most `1 / (q_w - 1)`, where
`q_w` is the order of the residue field at `w`. -/
lemma stepWeight_le {M : ℕ} (h_rank : 2 * card n < M) (w : FinPlace E) :
    stepWeight n M w ≤ (w.q - 1 : ℝ)⁻¹ := by
  have hq_sub : (0 : ℝ) < w.q - 1 := sub_pos.2 (by exact_mod_cast w.one_lt_q)
  calc stepWeight n M w ≤ Nat.card (neighbourResidues w) / ((w.q - 1) * √w.q) :=
        stepWeight_le_card_div h_rank w
    _ ≤ √w.q / ((w.q - 1) * √w.q) := by
        gcongr
        exact Real.le_sqrt_of_sq_le (by exact_mod_cast card_neighbourResidues_sq_le)
    _ = (w.q - 1 : ℝ)⁻¹ := by field_simp

omit [DecidableEq n] in
/-- For `2 n < M` the weights `stepWeight n M` of the steps at a place `w` and its conjugate add up
to at most `1 / 3`, since every residue field of `E` has at least four elements. -/
lemma tsum_stepWeight_conjClosure_singleton_le {M : ℕ} (h_rank : 2 * card n < M) (w : FinPlace E) :
    ∑' u : ({w} : Set (FinPlace E)).conjClosure, ENNReal.ofReal (stepWeight n M u.val) ≤ 3⁻¹ := by
  classical
  have h_split {u : FinPlace E} (hu : u.IsSplit) : stepWeight n M u ≤ 6⁻¹ := by
    have hq : (4 : ℝ) ≤ u.q := by exact_mod_cast u.four_le_q
    have h_sqrt : 2 ≤ √u.q := Real.le_sqrt_of_sq_le (by linarith)
    have h_six : (6 : ℝ) ≤ (u.q - 1) * √u.q := by nlinarith
    exact (stepWeight_le_of_isSplit h_rank hu).trans (inv_anti₀ (by norm_num) h_six)
  have h_sum : ∑ u ∈ {w, star w}, stepWeight n M u ≤ 3⁻¹ := by
    by_cases hw : star w = w
    · have hq : (4 : ℝ) ≤ w.q := by exact_mod_cast w.four_le_q
      simpa [hw] using (stepWeight_le h_rank w).trans (inv_anti₀ three_pos (by linarith))
    · have hw_star : (star w).IsSplit := fun h_eq ↦ hw (star_injective h_eq)
      rw [Finset.sum_pair (Ne.symm hw)]
      linarith [h_split hw, h_split hw_star]
  have h_set : ({w} : Set (FinPlace E)).conjClosure = ({w, star w} : Finset (FinPlace E)) := by
    ext u
    simp [eq_comm.trans eq_star_iff_eq_star]
  rw [h_set, Finset.tsum_subtype' _ fun u ↦ ENNReal.ofReal (stepWeight n M u),
    ← ENNReal.ofReal_sum_of_nonneg fun u _ ↦ stepWeight_nonneg M u,
    ENNReal.ofReal_le_iff_le_toReal (by finiteness)]
  simpa using h_sum

omit [DecidableEq n] in
lemma stepWeight_le_two_mul_inv {M : ℕ} (h_rank : 2 * card n < M) (w : FinPlace E) :
    stepWeight n M w ≤ 2 * (w.q : ℝ)⁻¹ := by
  have hq : (2 : ℝ) ≤ w.q := by exact_mod_cast w.one_lt_q
  calc stepWeight n M w ≤ (w.q - 1 : ℝ)⁻¹ := stepWeight_le h_rank w
    _ ≤ ((w.q : ℝ) / 2)⁻¹ := inv_anti₀ (by positivity) (by linarith)
    _ = 2 * (w.q : ℝ)⁻¹ := by rw [inv_div, div_eq_mul_inv]

omit [WeilData E] [DecidableEq n] in
/-- For `2 n < M` and `w` split the weight of the steps at `w` is at most `2 q_w ^ (-3 / 2)`. -/
lemma stepWeight_le_two_mul_rpow_of_isSplit {M : ℕ} (h_rank : 2 * card n < M) {w : FinPlace E}
    (hw : w.IsSplit) : stepWeight n M w ≤ 2 * (w.q : ℝ) ^ (-(3 / 2) : ℝ) := by
  have hq : (2 : ℝ) ≤ w.q := by exact_mod_cast w.one_lt_q
  have h_exp : (w.q : ℝ) ^ (-(3 / 2) : ℝ) = (w.q : ℝ)⁻¹ * (√w.q)⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg_one, ← Real.rpow_neg (by positivity),
      ← Real.rpow_add (by positivity)]
    norm_num
  calc stepWeight n M w ≤ ((w.q - 1) * √w.q)⁻¹ := stepWeight_le_of_isSplit h_rank hw
    _ ≤ ((w.q : ℝ) / 2 * √w.q)⁻¹ := by
        gcongr
        linarith
    _ = 2 * (w.q : ℝ) ^ (-(3 / 2) : ℝ) := by rw [h_exp, mul_inv, inv_div, div_eq_mul_inv, mul_assoc]

omit [DecidableEq n] in
/-- For `2 n < M` and `w` not split the weight of the steps at `w` is at most `2 / p ^ 2`, where
`p` is the least prime factor of `q_w`: the residue field at such a place is not of prime order. -/
lemma stepWeight_le_two_mul_inv_minFac_sq {M : ℕ} (h_rank : 2 * card n < M) {w : FinPlace E}
    (hw : ¬w.IsSplit) : stepWeight n M w ≤ 2 * (w.q.minFac ^ 2 : ℝ)⁻¹ := by
  have h_sq : (w.q.minFac ^ 2 : ℝ) ≤ w.q := by
    exact_mod_cast Nat.minFac_sq_le_self (zero_lt_one.trans w.one_lt_q)
      fun h_prime ↦ hw (isSplit_of_q_prime h_prime)
  have h_pos : (0 : ℝ) < w.q.minFac := Nat.cast_pos.2 w.q.minFac_pos
  exact (stepWeight_le_two_mul_inv h_rank w).trans (by gcongr)

omit [DecidableEq n] in
/-- For `2 n < M` the weights of the steps are summable over all finite places. -/
lemma summable_stepWeight {M : ℕ} (h_rank : 2 * card n < M) :
    Summable fun w : FinPlace E ↦ stepWeight n M w := by
  -- The weight is `O(q ^ (-3 / 2))` at a split place. At a place that is not split it is
  -- `O(1 / q)`, and `q` is at least the square of its least prime factor.
  have h_rpow : Summable fun w : FinPlace E ↦ (w.q : ℝ) ^ (-(3 / 2) : ℝ) :=
    (summable_absNorm_rpow (by norm_num)).comp_injective
      IsDedekindDomain.HeightOneSpectrum.asIdeal_injective
  have h_minFac : Summable fun w : FinPlace E ↦ (w.q.minFac ^ 2 : ℝ)⁻¹ :=
    summable_of_sum_le (fun _ ↦ by positivity) sum_inv_minFac_sq_le_finrank
  refine ((h_rpow.add h_minFac).mul_left 2).of_nonneg_of_le (stepWeight_nonneg M) fun w ↦ ?_
  by_cases hw : w.IsSplit
  · linarith [stepWeight_le_two_mul_rpow_of_isSplit h_rank hw,
      inv_nonneg.2 (sq_nonneg (w.q.minFac : ℝ))]
  · linarith [stepWeight_le_two_mul_inv_minFac_sq h_rank hw,
      Real.rpow_nonneg w.q.cast_nonneg (-(3 / 2) : ℝ)]

/-! ### The walk through neighbours -/

/-- One step of the walk through neighbours. For every set `A` of finite places there are elements
`ρ σ` of the finite adelic unitary group `Gf E n`, one for each step `σ` (a line in the `n`-space
over the residue field at `w` and a neighbour class) at a place `w` of `A` or its conjugate, with
the following property. Every nontrivial coset `q` of `localLevel n A` (the points integral at `A`)
has a step `σ` at some `w` such that
`q_w * ‖finMultiplier (cosetRep (ρ σ • q))‖ ^ 2 ≤ ‖finMultiplier (cosetRep q)‖ ^ 2`. Here
`finMultiplier` is the multiplier Δ_f (`glMultiplier` of the underlying matrix). -/
lemma exists_steps_q_mul_norm_finMultiplier_le (A : Set (FinPlace E)) :
    ∃ ρ : (Σ w : A.conjClosure, NeighbourStep n w.val) → Gf E n,
      ∀ q : Gf E n ⧸ localLevel n A, q ≠ (1 : Gf E n) →
        ∃ σ : Σ w : A.conjClosure, NeighbourStep n w.val,
          (σ.fst : FinPlace E).q * ‖finMultiplier (cosetRep (ρ σ • q)).val‖ ^ 2 ≤
            ‖finMultiplier (cosetRep q).val‖ ^ 2 := by
  -- The lattice of `γ = cosetRep q` holds a vector that defines a neighbour at a place `w` in the
  -- support of `γ`, and one of the points `ρ w p` maps this neighbour into the standard lattice.
  have h_family : ∀ w : FinPlace E, ∃ ρ : NeighbourStep n w → Gf E n,
      (∀ p : NeighbourStep n w, ρ p ∈ supportedOn n {w}) ∧
        ∀ x : n → 𝔸f E, IsNeighbourVector w x →
          ∃ p : NeighbourStep n w, MapsNeighbour (ρ p) x := exists_family_mapsNeighbour
  choose ρ h_supp h_cover using h_family
  refine ⟨fun σ ↦ ρ σ.fst σ.snd, fun q hq ↦ ?_⟩
  let γ : Gf E n := (cosetRep q).val
  have h_not_int : γ ∉ stdLevel E n := fun h_int ↦ hq <| by
    rw [← mk_cosetRep q, eq_comm, QuotientGroup.eq, inv_one, one_mul]
    exact stdLevel_le_localLevel h_int
  obtain ⟨w, hw_ne, z, hz, h_vec⟩ : ∃ w : FinPlace E, γ.atPlace w ≠ 1 ∧
      ∃ z ∈ stdLattice E n, IsNeighbourVector w (γ.val.val *ᵥ z) :=
    exists_isNeighbourVector_mulVec h_not_int
  obtain ⟨p, hp⟩ : ∃ p : NeighbourStep n w, MapsNeighbour (ρ w p) (γ.val.val *ᵥ z) :=
    h_cover w _ h_vec
  have hw : w ∈ A.conjClosure := by
    by_contra h_out
    exact hw_ne (mem_supportedOn.1 (cosetRep q).property w (h_out ∘ .inl) (h_out ∘ .inr))
  have hρ : ρ w p ∈ supportedOn n A := by
    refine mem_supportedOn.2 fun u hu hu_star ↦ mem_supportedOn.1 (h_supp w p) u ?_ ?_
    · rintro rfl
      exact hw.elim hu hu_star
    · rintro rfl
      exact hw.elim hu_star fun h ↦ hu (by simpa using h)
  have h_next : finMultiplier (cosetRep (ρ w p • q)).val = finMultiplier (ρ w p * γ) := by
    rw [← finMultiplier_cosetRep_mk (mul_mem hρ (cosetRep q).property), ← smul_eq_mul,
      ← MulAction.Quotient.smul_mk, mk_cosetRep]
  refine ⟨⟨⟨w, hw⟩, p⟩, ?_⟩
  rw [h_next]
  exact q_mul_norm_finMultiplier_mul_sq_le hz h_vec hp

/-- If `r > 0` and `r * ‖finMultiplier g'‖ ^ 2 ≤ ‖finMultiplier g‖ ^ 2`, then the coefficient of
the vacuum at `g` is at most `r ^ (-M / 2)` times the one at `g'` in modulus. -/
lemma norm_vacuumCoeff_le_of_mul_sq_le (M : ℕ) (b : AutChar E) {g g' : Gf E n} {r : ℝ} (hr : 0 < r)
    (h_sq_le : r * ‖finMultiplier g'‖ ^ 2 ≤ ‖finMultiplier g‖ ^ 2) :
    ‖vacuumCoeff M b g‖ ≤ (√r)⁻¹ ^ M * ‖vacuumCoeff M b g'‖ := by
  have h_pos : 0 < ‖finMultiplier g'‖ := norm_pos_iff.2 (finMultiplier_ne_zero g')
  have h_sqrt : √r * ‖finMultiplier g'‖ ≤ ‖finMultiplier g‖ :=
    (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).1
      (by rwa [mul_pow, Real.sq_sqrt hr.le])
  rw [norm_vacuumCoeff, norm_vacuumCoeff, ← mul_pow, ← mul_inv]
  gcongr

/-- The weight `stepWeight n M w` is the number of steps at `w` (a line in the `n`-space over the
residue field, together with a neighbour class) times `q_w ^ (-M / 2)`. If these weights, over the
places of `A` and their conjugates, add up to at most `1 / 3`, then the moduli of the vacuum
coefficients `vacuumCoeff M b g = (b(det g) * finMultiplier g ^ M)⁻¹` add up to at most
`1 / (1 - 1 / 3) = 3 / 2`, where `g = cosetRep q` runs over the representatives of the cosets `q` of
`localLevel n A` (the points integral at `A`) in the finite adelic unitary group `Gf E n`. -/
lemma tsum_ofReal_norm_vacuumCoeff_le (M : ℕ) (b : AutChar E)
    (hA : ∑' w : A.conjClosure, ENNReal.ofReal (stepWeight n M w.val) ≤ 3⁻¹) :
    ∑' q : Gf E n ⧸ localLevel n A, ENNReal.ofReal ‖vacuumCoeff M b (cosetRep q).val‖ ≤
      1 + 2⁻¹ := by
  -- Descend along the index `[L : L ∩ γ⁻¹ L] = ‖finMultiplier γ‖ ^ 2`, `L` the standard lattice.
  obtain ⟨ρ, h_step⟩ := exists_steps_q_mul_norm_finMultiplier_le (n := n) A
  let height (q : Gf E n ⧸ localLevel n A) : ℕ :=
    ((stdLattice E n).comap (cosetRep q).val.val.val.mulVecLin).relIndex (stdLattice E n)
  have h_height (q : Gf E n ⧸ localLevel n A) :
      (height q : ℝ) = ‖finMultiplier (cosetRep q).val‖ ^ 2 := (norm_finMultiplier_sq _).symm
  let f (q : Gf E n ⧸ localLevel n A) : ENNReal :=
    ENNReal.ofReal ‖vacuumCoeff M b (cosetRep q).val‖
  let c (σ : Σ w : A.conjClosure, NeighbourStep n w.val) : ENNReal :=
    ENNReal.ofReal ((√(σ.fst : FinPlace E).q)⁻¹ ^ M)
  have h_weights : ∑' σ, c σ = ∑' w : A.conjClosure, ENNReal.ofReal (stepWeight n M w.val) := by
    rw [ENNReal.tsum_sigma']
    refine tsum_congr fun w ↦ ?_
    have : Fintype (NeighbourStep n w.val) := Fintype.ofFinite _
    simp [c, stepWeight, tsum_fintype, ENNReal.ofReal_mul]
  have h_descent (q : Gf E n ⧸ localLevel n A) (hq : q ≠ (1 : Gf E n)) :
      ∃ σ : Σ w : A.conjClosure, NeighbourStep n w.val,
        height (ρ σ • q) < height q ∧ f q ≤ c σ * f (ρ σ • q) := by
    obtain ⟨σ, hσ⟩ := h_step q hq
    have hq_gt : (1 : ℝ) < (σ.fst : FinPlace E).q := by exact_mod_cast σ.fst.val.one_lt_q
    refine ⟨σ, ?_, ?_⟩
    · rw [← Nat.cast_lt (α := ℝ), h_height, h_height]
      exact (lt_mul_left (pow_pos (norm_pos_iff.2 (finMultiplier_ne_zero _)) 2) hq_gt).trans_le hσ
    · rw [← ENNReal.ofReal_mul (by positivity)]
      exact ENNReal.ofReal_le_ofReal
        (norm_vacuumCoeff_le_of_mul_sq_le M b (zero_lt_one.trans hq_gt) hσ)
  have h_bound : f (1 : Gf E n) + (∑' σ, c σ) * (1 + 2⁻¹) ≤ 1 + 2⁻¹ := by
    have h_arith : (3⁻¹ * (1 + 2⁻¹) : ENNReal) = 2⁻¹ := by
      rw [← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)]
      norm_num [ENNReal.toReal_add]
    simp only [f, norm_vacuumCoeff_cosetRep_one, ENNReal.ofReal_one, h_weights]
    grw [hA, h_arith]
  exact tsum_le_of_walk (fun σ ↦ MulAction.injective (ρ σ)) h_descent h_bound

end New.SiegelWeil

end
