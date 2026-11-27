import Lib.General.Groups.BesselGroups
import Lib.General.Measure.IntegralOperators

/-!
# Sieve systems over places: products, positivity and lower semicontinuity

An abstract sieve. A system `New.SieveSystem` over a ring `C` with a measure (a place, or a product
of places) consists of forms `J i p q`, `i ≤ n + 1`, on pairs of sequences ("heads"), each but the
last the integral of the next one over a common entry, with bounds `B₀`, `Λ`, `β`.

* `New.SieveSystem.pi`: a product of finitely many systems on `ℂ` (one for each real
  place in the application) and one more system is a system.
* `New.SieveSystem.integrable_sum_update`, `New.SieveSystem.integral_sum_update`,
  `New.SieveSystem.norm_integral_mul_sum_update_le`: sum the forms `J (i + 1)` over all pairs of
  heads from one finite family, with a common entry at position `i ≤ n`. The sum is integrable in
  the common entry, its integral is the sum of the `J i`, and its twisted integrals are bounded by
  `β` and `Λ`. `New.SieveSystem.integrable_and_integral_sum_update` collects the three.
* `New.SieveSystem.sum_nonneg`, `New.SieveSystem.lowerSemicontinuousAt_sum`: such a sum is
  nonnegative, and its real part is lower semicontinuous in a parameter `x : C` at each point where
  every head is continuous. `New.SieveSystem.sum_nonneg_and_lowerSemicontinuousAt` collects the two.
* `New.dampedPower`, `New.headWeight`: the decay in the frequency and the weights `Λ` of the heads
  at the real places.

## Relation to the literature

See `New.Spanning.MainTerm.GlobalSieve` for related work.
-/

noncomputable section

open MeasureTheory Finset Function Matrix ComplexOrder

namespace New

/-- The gain at the ratio `r`: the function `r ^ k * min 1 r ^ 6`. -/
def dampedPower (k : ℕ) (r : ℝ) : ℝ := r ^ k * min 1 r ^ 6

/-- The weight of a head `p` (with entries in `ℂˣ`) of length `i` at a real place. It is zero unless
the partial products `δ = p 0 * ⋯ * p l`, `l < i`, have modulus at most `R`, and then it is the
product of the numbers `max 1 ‖δ‖⁻¹ ^ K`. -/
def headWeight (R : ℝ) (K i : ℕ) (p : ℕ → ℂˣ) : ℝ :=
  ∏ l ∈ range i,
    let δ : ℂ := ∏ a ∈ range (l + 1), (p a : ℂ)
    if ‖δ‖ ≤ R then max 1 ‖δ‖⁻¹ ^ K else 0

lemma headWeight_nonneg (R : ℝ) (K i : ℕ) (p : ℕ → ℂˣ) : 0 ≤ headWeight R K i p :=
  prod_nonneg fun _ _ ↦ ite_nonneg (by positivity) le_rfl

variable {C U τ : Type} [CommRing C] [MeasureSpace C] [TopologicalSpace U] [Fintype τ]

/-- The axioms of the sieve at a place or a product of places: `C` is a ring with a measure, `u c`
is the entry given by `c ∈ C`, and `ι` maps entries back to `C` (in the applications `x ↦ x⁻¹`,
times a constant at the finite places). The forms `J i p q`, `i ≤ n + 1`, pair two sequences of
entries, called heads, with weights `Λ i p`. The field `integrable_and_integral_update` makes each
form but the top one the integral of the next over a common entry, and bounds the same integral
twisted by `ψ (ξ * c)` at a unit `ξ` in terms of the decay `β ξ`. The top form `J (n + 1)` is
continuous, and positive semidefinite on heads with a common entry at position `n`. The bottom form
`J 0` has modulus at most `En`. -/
structure SieveSystem (u : C → U) (ι : U → C) (n : ℕ) (J : ℕ → (ℕ → U) → (ℕ → U) → ℂ) (ψ : C → ℂ)
    (En : ℝ) (Λ : ℕ → (ℕ → U) → ℝ) (β : C → ℝ) : Prop where
  /-- The function `ψ` takes the value `1` at `0`. -/
  psi_zero : ψ 0 = 1
  /-- For `i ≤ n`, give both heads the entry `u c` at position `i`. Then `ψ (ξ * c)` times the form
  `J (i + 1)` is integrable in `c`; its integral is `J i p q` if `ξ = 0`, and has modulus at most
  `β ξ * (Λ i p * Λ i q)` if `ξ` is a unit. -/
  integrable_and_integral_update (i : ℕ) (p q : ℕ → U) (ξ : C) :
      i ≤ n →
      let f (c : C) : ℂ := ψ (ξ * c) * J (i + 1) (update p i (u c)) (update q i (u c))
      Integrable f ∧
      (ξ = 0 → ∫ c : C, f c = J i p q) ∧
      (IsUnit ξ → ‖∫ c : C, f c‖ ≤ β ξ * (Λ i p * Λ i q))
  /-- The top form `J (n + 1)` is a positive semidefinite kernel on heads with the same entry at
  position `n`. -/
  posSemidef {κ : Type} [Fintype κ] (a : κ → ℕ → U) (t : U) :
      (∀ i : κ, a i n = t) → (Matrix.of fun i j : κ ↦ J (n + 1) (a i) (a j)).PosSemidef
  /-- The top form `J (n + 1)` is jointly continuous. -/
  continuous : Continuous (J (n + 1)).uncurry
  /-- The bottom form `J 0` has modulus at most `En`. -/
  norm_bot_le (p q : ℕ → U) : ‖J 0 p q‖ ≤ En
  /-- For `i < n`, if `ξ = ι (p i) - ι (q i)` is a unit, then `J (i + 1) p q` has modulus at most
  `β ξ * (Λ (i + 1) p * Λ (i + 1) q)`. -/
  norm_le_of_isUnit_sub (i : ℕ) (p q : ℕ → U) :
      i < n →
      let ξ : C := ι (p i) - ι (q i)
      IsUnit ξ → ‖J (i + 1) p q‖ ≤ β ξ * (Λ (i + 1) p * Λ (i + 1) q)

variable {u : C → U} {ι : U → C} {n : ℕ} {J : ℕ → (ℕ → U) → (ℕ → U) → ℂ} {ψ : C → ℂ} {B₀ : ℝ}
  {Λ : ℕ → (ℕ → U) → ℝ} {β : C → ℝ}

/-- Bounds on the norms of finitely many complex factors `f v` and of one more factor `a` multiply
to a bound on the norm of their product. -/
lemma norm_prod_mul_le_prod_mul {f : τ → ℂ} {g : τ → ℝ} {a : ℂ} {b : ℝ}
    (hf : ∀ v : τ, ‖f v‖ ≤ g v) (ha : ‖a‖ ≤ b) : ‖(∏ v : τ, f v) * a‖ ≤ (∏ v : τ, g v) * b :=
  norm_mul_le_of_le ((norm_prod_le univ f).trans (by gcongr with v; exact hf v)) ha

/-- Schur's product theorem for finitely many kernels: the entrywise product of positive
semidefinite kernels `A v` over `v ∈ s` and `B` is positive semidefinite. -/
lemma posSemidef_prod_mul {σ κ : Type} [Fintype κ] {A : σ → κ → κ → ℂ} {B : κ → κ → ℂ}
    (hA : ∀ v : σ, (Matrix.of (A v)).PosSemidef) (hB : (Matrix.of B).PosSemidef) (s : Finset σ) :
    (Matrix.of fun i j : κ ↦ (∏ v ∈ s, A v i j) * B i j).PosSemidef := by
  classical
  induction s using Finset.induction with
  | empty => simpa only [prod_empty, one_mul] using hB
  | insert v s hv ih =>
    simp only [prod_insert hv, mul_assoc]
    exact (hA v).hadamard ih

/-- The component at the complex factor `v` of a head `p` with entries in `(τ → ℂˣ) × U`: the
sequence `k ↦ (p k).1 v`. -/
def headAt (v : τ) (p : ℕ → (τ → ℂˣ) × U) : ℕ → ℂˣ := (fun y : (τ → ℂˣ) × U ↦ y.1 v) ∘ p

/-- For `i ≤ n`, give both heads the entry `u c` at position `i`. Then `ψ (ξ * c)` times the form
`J (i + 1)` is integrable in `c`. -/
lemma SieveSystem.integrable_mul_update (K : SieveSystem u ι n J ψ B₀ Λ β) {i : ℕ} (hi : i ≤ n)
    (p q : ℕ → U) (ξ : C) :
    Integrable fun c : C ↦ ψ (ξ * c) * J (i + 1) (update p i (u c)) (update q i (u c)) :=
  (K.integrable_and_integral_update i p q ξ hi).1

/-- For `i ≤ n`, the form `J (i + 1)` is integrable in a common entry `u c` at position `i`. -/
lemma SieveSystem.integrable_update (K : SieveSystem u ι n J ψ B₀ Λ β) {i : ℕ} (hi : i ≤ n)
    (p q : ℕ → U) : Integrable fun c : C ↦ J (i + 1) (update p i (u c)) (update q i (u c)) := by
  simpa only [zero_mul, K.psi_zero, one_mul] using K.integrable_mul_update hi p q 0

/-- The recursion: for `i ≤ n`, the form `J i` is the integral of `J (i + 1)` over a common entry
`u c` at position `i`. -/
lemma SieveSystem.integral_update (K : SieveSystem u ι n J ψ B₀ Λ β) {i : ℕ} (hi : i ≤ n)
    (p q : ℕ → U) : ∫ c : C, J (i + 1) (update p i (u c)) (update q i (u c)) = J i p q := by
  obtain ⟨-, h_zero, -⟩ := K.integrable_and_integral_update i p q 0 hi
  simpa only [zero_mul, K.psi_zero, one_mul] using h_zero rfl

/-- For `i ≤ n` and a unit `ξ`, the integral of `J (i + 1)` over a common entry `u c` at position
`i`, twisted by `ψ (ξ * c)`, has modulus at most `β ξ * (Λ i p * Λ i q)`. -/
lemma SieveSystem.norm_integral_mul_update_le (K : SieveSystem u ι n J ψ B₀ Λ β) {i : ℕ}
    (hi : i ≤ n) (p q : ℕ → U) {ξ : C} (hξ : IsUnit ξ) :
    ‖∫ c : C, ψ (ξ * c) * J (i + 1) (update p i (u c)) (update q i (u c))‖ ≤
      β ξ * (Λ i p * Λ i q) := by
  obtain ⟨-, -, h_unit⟩ := K.integrable_and_integral_update i p q ξ hi
  exact h_unit hξ

/-- A finite product of sieve systems is a sieve system.

Let `K` be such a system on `C` (with s-finite volume), and for each `v` in the finite type `τ` take
a system on `ℂ` with forms `J' v`, bounds `B₀' v`, `Λ'`, `γ v`, entry map `unitOrOne`, map `ι'` back
to `ℂ` and twist `wave`. Then the products of the forms, twists and bounds make a system on
`(τ → ℂ) × C`, each form and weight being evaluated on the components of the heads in its factor:
`headAt v p = fun k ↦ (p k).1 v` at `v`, and `Prod.snd ∘ p` in `U`. -/
lemma SieveSystem.pi (K : SieveSystem u ι n J ψ B₀ Λ β) [SFinite (volume : Measure C)] {ι' : ℂˣ → ℂ}
    {Λ' : ℕ → (ℕ → ℂˣ) → ℝ} {J' : τ → ℕ → (ℕ → ℂˣ) → (ℕ → ℂˣ) → ℂ} {B₀' : τ → ℝ} {γ : τ → ℂ → ℝ}
    (h_factor : ∀ v : τ, SieveSystem unitOrOne ι' n (J' v) wave (B₀' v) Λ' (γ v)) :
    SieveSystem (Prod.map (fun x : τ → ℂ ↦ unitOrOne ∘ x) u)
      (Prod.map (fun y : τ → ℂˣ ↦ ι' ∘ y) ι) n
      (fun (i : ℕ) (p q : ℕ → (τ → ℂˣ) × U) ↦
        (∏ v : τ, J' v i (headAt v p) (headAt v q)) * J i (Prod.snd ∘ p) (Prod.snd ∘ q))
      (fun x : (τ → ℂ) × C ↦ (∏ v : τ, wave (x.1 v)) * ψ x.2)
      ((∏ v : τ, B₀' v) * B₀)
      (fun (i : ℕ) (p : ℕ → (τ → ℂˣ) × U) ↦ (∏ v : τ, Λ' i (headAt v p)) * Λ i (Prod.snd ∘ p))
      fun x : (τ → ℂ) × C ↦ (∏ v : τ, γ v (x.1 v)) * β x.2 := by
  classical
  -- Everything is checked factor by factor: Fubini for `integrable_and_integral_update`, Schur's
  -- product theorem for `posSemidef`, and products of the local bounds for
  -- `integrable_and_integral_update`, `norm_bot_le` and `norm_le_of_isUnit_sub`.
  constructor
  case psi_zero => simp [K.psi_zero, wave]
  case integrable_and_integral_update =>
    intro i p q ξ hi f
    -- The integrands in the factor `v` and in `C`.
    let g (v : τ) (z : ℂ) : ℂ := wave (ξ.1 v * z) *
      J' v (i + 1) (update (headAt v p) i (unitOrOne z)) (update (headAt v q) i (unitOrOne z))
    let gC (c : C) : ℂ := ψ (ξ.2 * c) *
      J (i + 1) (update (Prod.snd ∘ p) i (u c)) (update (Prod.snd ∘ q) i (u c))
    have hf : f = fun x : (τ → ℂ) × C ↦ (∏ v, g v (x.1 v)) * gC x.2 := by
      ext x
      simp [f, g, gC, headAt, comp_update, prod_mul_distrib, mul_mul_mul_comm]
    have h_fubini : ∫ x, f x = (∏ v, ∫ z, g v z) * ∫ c, gC c := by
      rw [hf, ← integral_fintype_prod_volume_eq_prod, ← integral_prod_mul, Measure.volume_eq_prod]
    refine ⟨?_, fun hξ ↦ ?_, fun hξ ↦ ?_⟩
    · rw [hf]
      exact .mul_prod (.fintype_prod fun v ↦ (h_factor v).integrable_mul_update hi _ _ _)
        (K.integrable_mul_update hi _ _ _)
    · -- Both twists are `1` at `0`, and the recursion holds in each factor.
      simp [h_fubini, g, gC, hξ, wave, K.psi_zero, (h_factor _).integral_update hi,
        K.integral_update hi]
    · rw [Prod.isUnit_iff, Pi.isUnit_iff] at hξ
      obtain ⟨hξ_factor, hξ_C⟩ := hξ
      rw [h_fubini]
      refine (norm_prod_mul_le_prod_mul
        (fun v ↦ (h_factor v).norm_integral_mul_update_le hi _ _ (hξ_factor v))
        (K.norm_integral_mul_update_le hi _ _ hξ_C)).trans_eq ?_
      simp [prod_mul_distrib, mul_mul_mul_comm]
  case posSemidef =>
    intro κ _ a t ha
    exact posSemidef_prod_mul (fun v ↦ (h_factor v).posSemidef _ (t.1 v) (by simp [headAt, ha]))
      (K.posSemidef _ t.2 (by simp [ha])) univ
  case continuous =>
    have h_cont_factor (v : τ) : Continuous (J' v (n + 1)).uncurry := (h_factor v).continuous
    have h_cont_C : Continuous (J (n + 1)).uncurry := K.continuous
    unfold headAt
    fun_prop
  case norm_bot_le =>
    exact fun p q ↦ norm_prod_mul_le_prod_mul (fun v ↦ (h_factor v).norm_bot_le _ _)
      (K.norm_bot_le _ _)
  case norm_le_of_isUnit_sub =>
    intro i p q hi ξ hξ
    rw [Prod.isUnit_iff, Pi.isUnit_iff] at hξ
    obtain ⟨hξ_factor, hξ_C⟩ := hξ
    refine (norm_prod_mul_le_prod_mul
      (fun v ↦ (h_factor v).norm_le_of_isUnit_sub i (headAt v p) (headAt v q) hi (hξ_factor v))
      (K.norm_le_of_isUnit_sub i (Prod.snd ∘ p) (Prod.snd ∘ q) hi hξ_C)).trans_eq ?_
    simp [ξ, headAt, prod_mul_distrib, mul_mul_mul_comm]

/-- For `i ≤ n` and finitely many heads `a p`, the sum of `J (i + 1)` over all pairs of heads is
integrable in a common entry `u c` at position `i`. -/
lemma SieveSystem.integrable_sum_update (K : SieveSystem u ι n J ψ B₀ Λ β) {i : ℕ} (hi : i ≤ n)
    (a : τ → ℕ → U) :
    Integrable fun c : C ↦
      ∑ p : τ, ∑ q : τ, J (i + 1) (update (a p) i (u c)) (update (a q) i (u c)) :=
  integrable_finsetSum _ fun _ _ ↦ integrable_finsetSum _ fun _ _ ↦ K.integrable_update hi _ _

/-- The recursion summed over all pairs from finitely many heads `a p`: for `i ≤ n`, the sum of the
forms `J i` is the integral of the sum of the forms `J (i + 1)` over a common entry `u c` at
position `i`. -/
lemma SieveSystem.integral_sum_update (K : SieveSystem u ι n J ψ B₀ Λ β) {i : ℕ} (hi : i ≤ n)
    (a : τ → ℕ → U) :
    ∫ c : C, ∑ p : τ, ∑ q : τ, J (i + 1) (update (a p) i (u c)) (update (a q) i (u c)) =
      ∑ p : τ, ∑ q : τ, J i (a p) (a q) := by
  simp [integral_finsetSum, integrable_finsetSum, K.integrable_update hi, K.integral_update hi]

/-- For `i ≤ n`, finitely many heads `a p` and a unit `ξ`, sum the forms `J (i + 1)` of the system
`K` over all pairs of heads with a common entry `u c` at position `i`. The integral of this sum
twisted by `ψ (ξ * c)` has modulus at most `β ξ * (∑ p, Λ i (a p)) ^ 2`, with `Λ` the head weights
and `β` the decay of `K`. -/
lemma SieveSystem.norm_integral_mul_sum_update_le (K : SieveSystem u ι n J ψ B₀ Λ β) {i : ℕ}
    (hi : i ≤ n) (a : τ → ℕ → U) {ξ : C} (hξ : IsUnit ξ) :
    ‖∫ c : C, ψ (ξ * c) *
        ∑ p : τ, ∑ q : τ, J (i + 1) (update (a p) i (u c)) (update (a q) i (u c))‖ ≤
      β ξ * (∑ p : τ, Λ i (a p)) ^ 2 :=
  calc _ = ‖∑ p, ∑ q,
        ∫ c, ψ (ξ * c) * J (i + 1) (update (a p) i (u c)) (update (a q) i (u c))‖ := by
        simp [mul_sum, integral_finsetSum, integrable_finsetSum, K.integrable_mul_update hi]
    _ ≤ ∑ p, ∑ q, β ξ * (Λ i (a p) * Λ i (a q)) :=
        norm_sum_le_of_le _ fun p _ ↦ norm_sum_le_of_le _ fun q _ ↦
          K.norm_integral_mul_update_le hi (a p) (a q) hξ
    _ = β ξ * (∑ p, Λ i (a p)) ^ 2 := by simp only [sq, sum_mul_sum, ← mul_sum]

/-- The summed recursion in one statement: for `i ≤ n`, let `F c` be the sum of the forms
`J (i + 1)` over all pairs from finitely many `heads` with entry `u c` put at position `i`. Then
`F` is integrable, its integral is the sum of the forms `J i`, and for a unit `ξ` the integral of
`ψ (ξ * c) * F c` has modulus at most `β ξ * (∑ p, Λ i (heads p)) ^ 2`, with `Λ` the head weights
and `β` the decay of the system. -/
lemma SieveSystem.integrable_and_integral_sum_update (K : SieveSystem u ι n J ψ B₀ Λ β) {i : ℕ}
    (hi : i ≤ n) (heads : τ → ℕ → U) :
    let F (c : C) : ℂ :=
      ∑ p : τ, ∑ q : τ, J (i + 1) (update (heads p) i (u c)) (update (heads q) i (u c))
    Integrable F ∧
    ∫ c : C, F c = ∑ p : τ, ∑ q : τ, J i (heads p) (heads q) ∧
    ∀ ξ : C, IsUnit ξ → ‖∫ c : C, ψ (ξ * c) * F c‖ ≤ β ξ * (∑ p : τ, Λ i (heads p)) ^ 2 :=
  ⟨K.integrable_sum_update hi heads, K.integral_sum_update hi heads,
    fun _ξ hξ ↦ K.norm_integral_mul_sum_update_le hi heads hξ⟩

/-- In a sieve system `K` with forms `J`, if finitely many heads `a p` have a common entry `t` at
position `i ≤ n`, then the sum of `J (i + 1)` over all pairs of heads is a nonnegative real
number. -/
lemma SieveSystem.sum_nonneg (K : SieveSystem u ι n J ψ B₀ Λ β) {i : ℕ} (hi : i ≤ n)
    (a : τ → ℕ → U) {t : U} (h_common : ∀ p : τ, a p i = t) :
    0 ≤ ∑ p : τ, ∑ q : τ, J (i + 1) (a p) (a q) := by
  -- Descend on `i`. At `i = n` the sum is the value of a positive semidefinite form on
  -- `(1, …, 1)`. Below, it is the integral over a common next entry of the same sums for `i + 1`.
  induction hi using Nat.decreasingInduction generalizing a t with
  | self =>
    simpa [mulVec, dotProduct] using (K.posSemidef a t h_common).dotProduct_mulVec_nonneg 1
  | of_succ i hi ih =>
    rw [← K.integral_sum_update hi a]
    exact integral_nonneg fun z ↦ ih _ fun p ↦ update_self (i + 1) (u z) (a p)

variable [TopologicalSpace C] [FirstCountableTopology C]

/-- In a sieve system `K` with forms `J`, let finitely many heads `b y p`, depending on `y : C`,
have a common entry `c y` at position `i ≤ n` for each `y`. The sum of `J (i + 1)` over all pairs
of heads, which is a nonnegative real number, is lower semicontinuous in `y` at each point `x` where
the heads are continuous. This is stated for `ENNReal.ofReal` of its real part. -/
lemma SieveSystem.lowerSemicontinuousAt_sum (K : SieveSystem u ι n J ψ B₀ Λ β) {i : ℕ}
    (hi : i ≤ n) (b : C → τ → ℕ → U) {c : C → U} (h_common : ∀ (y : C) (p : τ), b y p i = c y)
    {x : C} (h_cont : ∀ p : τ, ContinuousAt (fun y : C ↦ b y p) x) :
    LowerSemicontinuousAt
      (fun y : C ↦ ENNReal.ofReal (RCLike.re (∑ p : τ, ∑ q : τ, J (i + 1) (b y p) (b y q)))) x := by
  -- Descend on `i`. At `i = n` the sum is continuous at `x`. Below, it is the integral over a
  -- common next entry `u z` of the same sums for `i + 1`, and Fatou's lemma applies.
  induction hi using Nat.decreasingInduction generalizing b c with
  | self =>
    have hJ : Continuous (J (n + 1)).uncurry := K.continuous
    exact ContinuousAt.lowerSemicontinuousAt (by fun_prop [ENNReal.ofReal])
  | of_succ i hi ih =>
    -- `G y z` is the sum for `i + 1` at the heads `b y p` extended by the entry `u z`.
    let G (y z : C) : ℂ :=
      ∑ p, ∑ q, J (i + 1 + 1) (update (b y p) (i + 1) (u z)) (update (b y q) (i + 1) (u z))
    have h_lsc (z : C) : LowerSemicontinuousAt (fun y ↦ ENNReal.ofReal (RCLike.re (G y z))) x :=
      ih _ (fun y p ↦ update_self (i + 1) (u z) (b y p)) (by fun_prop)
    have h_int (y : C) : Integrable (G y) := K.integrable_sum_update hi (b y)
    have h_re (y : C) : ENNReal.ofReal (RCLike.re (∑ p, ∑ q, J (i + 1) (b y p) (b y q))) =
        ∫⁻ z, ENNReal.ofReal (RCLike.re (G y z)) := by
      have h_nonneg (z : C) : 0 ≤ G y z :=
        K.sum_nonneg hi _ fun p ↦ update_self (i + 1) (u z) (b y p)
      rw [← K.integral_sum_update hi (b y), ← integral_re (h_int y),
        ofReal_integral_eq_lintegral_ofReal (h_int y).re
          (.of_forall fun z ↦ (RCLike.nonneg_iff.1 (h_nonneg z)).1)]
    simp only [lowerSemicontinuousAt_iff_le_liminf, h_re] at h_lsc ⊢
    calc ∫⁻ z, ENNReal.ofReal (RCLike.re (G x z))
      _ ≤ ∫⁻ z, Filter.liminf (fun y ↦ ENNReal.ofReal (RCLike.re (G y z))) (nhds x) :=
          lintegral_mono h_lsc
      _ ≤ Filter.liminf (fun y ↦ ∫⁻ z, ENNReal.ofReal (RCLike.re (G y z))) (nhds x) :=
          lintegral_liminf_le' fun y ↦ (h_int y).re.aemeasurable.ennreal_ofReal

/-- In a sieve system `K` with forms `J`, let finitely many sequences `heads x p` have a common
entry `entry x` at position `i ≤ n` for each `x`. Then the sum `F x` of `J (i + 1)` over all pairs
of heads is a nonnegative real number, and `ENNReal.ofReal` of its real part is lower semicontinuous
at each `x` where the heads are continuous. -/
lemma SieveSystem.sum_nonneg_and_lowerSemicontinuousAt (K : SieveSystem u ι n J ψ B₀ Λ β) {i : ℕ}
    (hi : i ≤ n) (heads : C → τ → ℕ → U) {entry : C → U}
    (h_common : ∀ (x : C) (p : τ), heads x p i = entry x) :
    let F (x : C) : ℂ := ∑ p : τ, ∑ q : τ, J (i + 1) (heads x p) (heads x q)
    (∀ x : C, 0 ≤ F x) ∧
    ∀ x : C,
      (∀ p : τ, ContinuousAt (fun y : C ↦ heads y p) x) →
      LowerSemicontinuousAt (fun y : C ↦ ENNReal.ofReal (RCLike.re (F y))) x :=
  ⟨fun x ↦ K.sum_nonneg hi (heads x) (h_common x),
    fun _x h_cont ↦ K.lowerSemicontinuousAt_sum hi heads h_common h_cont⟩

end New

end
