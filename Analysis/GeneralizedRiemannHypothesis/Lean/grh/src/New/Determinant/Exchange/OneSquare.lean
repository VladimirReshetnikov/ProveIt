import Lib.Weil.Seesaw
import New.Determinant.Chain.SquareLaw
import New.Determinant.Exchange.TheoremForPartners

/-!
# One square: up then down against down then up

The exchange identity `New.Exchange.exchange_identity` for the space `U₁ ⊕ U₂`, read as a statement
on theta lifts of forms from `U₁` to `U₂`: its kernels are products of kernels for `U₁` and `U₂`.

* `New.Exchange.pairTransposedLift_comp_pairLift_mul`,
  `New.Exchange.pairLift_comp_pairTransposedLift_mul`: the path up to `A` and down, and the path
  down to `A'` and up, transform by the tame character.
* `New.Exchange.IsSquare`: the conditions on the four pairs of a square.
* `New.Exchange.exists_sum_pairLift_comp_pairTransposedLift_eq_smul`: for four pairs with their own
  splitting characters, the two paths agree on matched functions up to the factor `κ / c`, where `κ`
  may be zero.
* `New.Exchange.one_square_identity_of_isEdgeFamily`: the case of two families of characters indexed
  by finite types, in the form of the relation `New.Exchange.SquareLaw`.

Notions from other files:
* `New.modDatum S T 𝔪 Ψ v`: the theta datum on `Hom(S, T)` with real part the Fock vector `v`, given
  by the function `Ψ` on matrices modulo `𝔪` at the places dividing `𝔪` and by the vacuum elsewhere.
  The point datum at `x` is the case `Ψ = Pi.single x 1`, the indicator function of `x`;
* `New.Fock.fockMoment N v` is `∫ (1 + ‖z‖) ^ N * |v z| dz`, the moment of order `N` of the Fock
  vector `v`;
* a type of forms on a space is a function on its real unitary group, which prescribes the
  behavior of a form at the infinite places;
* `New.AutChar E`: the continuous characters of `[U(1)]`, the norm-one ideles of `E` modulo those
  from `E`;
* `New.Exchange.pairLift`, `New.Exchange.pairTransposedLift`: the lift and the transposed lift;
* `New.Exchange.IsPairEdge a b e e' P`, an edge `e → e'`: each of the families of characters `a`,
  `b` has a fixed weight, and for these weights the types `e`, `e'` and the Fock vector of `P` are
  such that the theta integral lifts forms of type `e` to forms of type `e'`;
  `New.Exchange.IsEdgeFamily` asks this of one family of characters indexed by finite types;

## Relation to the literature

A transposed lift followed by a lift is a multiple, possibly zero, of a lift followed by a
transposed lift. For forms on two unitary groups, the theta liftings through a group `A` and through
a group `A'` of no larger rank agree on matched ramified data, up to the L-value constant of the
exchange theorem and a factor free of the twist that may be zero. This moves lifts past each other
in chains. The seesaw principle and a rank-one exchange of periods are known in the literature.
Related work: Kudla, Seesaw dual reductive pairs, 1984; Chan, Period identities of CM forms on
quaternion algebras, 2020; He, Compositions of theta correspondences, 2005.
-/

noncomputable section

namespace New.Exchange

open MeasureTheory Matrix Fintype Fock Space WeilData Rows NumberField

variable {E n n' n₁ n₂ : Type} [Field E] [CMType E] [WeilData E] [Fintype n] [DecidableEq n]
  [Fintype n'] [DecidableEq n'] [Fintype n₁] [DecidableEq n₁] [Fintype n₂] [DecidableEq n₂]
  {s : n → ℤˣ} {s' : n' → ℤˣ} {s₁ : n₁ → ℤˣ} {s₂ : n₂ → ℤˣ}

/-! ### Point data and characters -/

/-- Let `k = liftMod g` be the chosen integral finite adelic point of `U(T)` with residue `g` modulo
`𝔪`. In the Weil representation `pairWeil S T α β` of `U(S) × U(T)`, twisted by the characters `α`,
`β`, let `k⁻¹` act in the finite part of `U(T)`, all other components being `1`. It sends the point
datum at `g x` to `(α (det k))⁻¹` times the point datum at `x`. -/
lemma pairWeil_modDatum_single_mul_left (S : Space E n s) (T : Space E n' s') {𝔪 : Modulus E}
    (α β : AutChar E) (g : GL n' 𝔪.ResidueRing) (x : Matrix n' n 𝔪.ResidueRing)
    (v : PairFock E s s') :
    pairWeil S T α β ((1, 1), 1, (liftMod g).val⁻¹) (modDatum S T 𝔪 (Pi.single (g.val * x) 1) v) =
      (α⁻¹.val (detFin s' (liftMod g).val) : ℂ) • modDatum S T 𝔪 (Pi.single x 1) v := by
  have h_coe (z : Circle) : Circle.coeHom z = (z : ℂ) := rfl
  simpa [pairChar, h_coe, Prod.mk_one_one, ← map_inv] using pairWeil_modDatum_single
    (a := α) (b := β) (v := v) (x := g.val * x) (y := x) 1 (liftMod g)⁻¹ (by simp)

/-- Let `k = liftMod g` be the chosen integral finite adelic point of `U(S)` with residue `g` modulo
`𝔪`. In the Weil representation `pairWeil S T α β` of `U(S) × U(T)`, twisted by the characters `α`,
`β`, let `k` act in the finite part of `U(S)`, all other components being `1`. It sends the point
datum at `y g` to `(β (det k))⁻¹` times the point datum at `y`. -/
lemma pairWeil_modDatum_single_mul_right (S : Space E n s) (T : Space E n' s') {𝔪 : Modulus E}
    (α β : AutChar E) (g : GL n 𝔪.ResidueRing) (y : Matrix n' n 𝔪.ResidueRing)
    (v : PairFock E s s') :
    pairWeil S T α β ((1, (liftMod g).val), 1, 1) (modDatum S T 𝔪 (Pi.single (y * g.val) 1) v) =
      (β⁻¹.val (detFin s (liftMod g).val) : ℂ) • modDatum S T 𝔪 (Pi.single y 1) v := by
  have h_coe (z : Circle) : Circle.coeHom z = (z : ℂ) := rfl
  simpa [pairChar, h_coe, Prod.mk_one_one] using pairWeil_modDatum_single
    (a := α) (b := β) (v := v) (x := y * g.val) (y := y) (liftMod g) 1 (by simp)

omit [WeilData E] [Fintype n] [DecidableEq n] [Fintype n'] in
/-- Let `Ψ`, `Ψ'` be matched for the character `χ` over the whole residue ring (`⊤`), the indices
being split by `σ`; in particular `Ψ` vanishes off the blocks of rows `n'` of invertible matrices.
Then `Ψ` vanishes off the onto matrices, those whose transpose has a left inverse. -/
lemma hasLeftInv_transpose_of_areMatched {𝔪 : Modulus E} {σ : n ⊕ n' ≃ n₁ ⊕ n₂}
    {χ : MulChar 𝔪.ResidueRing ℂ} {Ψ : Matrix n' (n₁ ⊕ n₂) 𝔪.ResidueRing → ℂ}
    {Ψ' : Matrix (n₁ ⊕ n₂) n 𝔪.ResidueRing → ℂ} (h_part : AreMatched ⊤ σ χ Ψ Ψ')
    {x : Matrix n' (n₁ ⊕ n₂) 𝔪.ResidueRing} (hx : Ψ x ≠ 0) : HasLeftInv xᵀ := by
  obtain ⟨k, -, rfl⟩ := h_part.supp_left x hx
  exact hasLeftInv_invLastRows_transpose σ k

omit [WeilData E] [Fintype n] [Fintype n'] [DecidableEq n'] in
/-- Let `Ψ`, `Ψ'` be matched for the character `χ` over the whole residue ring (`⊤`), the indices
being split by `σ`; in particular `Ψ'` vanishes off the blocks of columns `n` of invertible
matrices. Then `Ψ'` vanishes off the left invertible matrices. -/
lemma hasLeftInv_of_areMatched {𝔪 : Modulus E} {σ : n ⊕ n' ≃ n₁ ⊕ n₂}
    {χ : MulChar 𝔪.ResidueRing ℂ} {Ψ : Matrix n' (n₁ ⊕ n₂) 𝔪.ResidueRing → ℂ}
    {Ψ' : Matrix (n₁ ⊕ n₂) n 𝔪.ResidueRing → ℂ} (h_part : AreMatched ⊤ σ χ Ψ Ψ')
    {y : Matrix (n₁ ⊕ n₂) n 𝔪.ResidueRing} (hy : Ψ' y ≠ 0) : HasLeftInv y := by
  obtain ⟨k, -, rfl⟩ := h_part.supp_right y hy
  exact ⟨_, invFirstRows_mul_firstCols σ k⟩

/-- Let the character `ν` of `[U(1)]` be tame of weight `μ` for `(𝔪, χ)`: `𝔪 ≠ 1`, `ν` has weight
`μ` at the infinite places, its tame part is nontrivial exactly at the places dividing `𝔪`, and `χ`
is the character of the residue ring that the tame part defines. Then the inverse of
`rankTwist ν⁻¹ N = ν⁻¹ * upsilonU1 ^ (card N / 2)` is tame for `(𝔪, χ)`, of some weight `μ'`. -/
lemma IsTameFor.exists_inv_rankTwist_inv {𝔪 : Modulus E} {ν : AutChar E} {μ : InfinitePlace E → ℤ}
    {χ : MulChar 𝔪.ResidueRing ℂ} (h_tame : IsTameFor 𝔪 ν μ χ) (N : Type) [Fintype N] :
    ∃ μ' : InfinitePlace E → ℤ, IsTameFor 𝔪 (rankTwist ν⁻¹ N)⁻¹ μ' χ := by
  -- inverting turns `χ` into `χ⁻¹`; a power of `upsilonU1` changes only the weight
  have h_twist : IsTameFor 𝔪 (rankTwist ν⁻¹ N) (-μ + fun _ ↦ (↑(card N / 2) : ℤ)) χ⁻¹ :=
    h_tame.inv.mul (hasWeight_upsilonU1_pow _)
  exact ⟨_, by simpa only [inv_inv] using h_twist.inv⟩

omit [WeilData E] in
/-- Suppose each `F i` with nonzero coefficient `c i` is integrable for the product of the quotient
measures of `U₁`, `U₂` and `A`, with integral `r i`. Then the iterated integral of `∑ i, c i • F i`
equals `∑ i, c i • r i`. The inner integral is over `A` and the outer one over `U₁ × U₂`. -/
lemma integral_integral_sum_eq {A : Space E n' s'} {U₁ : Space E n₁ s₁} {U₂ : Space E n₂ s₂}
    {ι : Type*} [Fintype ι] {c r : ι → ℂ} {F : ι → (G E s₁ × G E s₂) × G E s' → ℂ}
    (hF_int : ∀ i : ι, c i ≠ 0 →
      Integrable (F i) ((U₁.quotMeasure.prod U₂.quotMeasure).prod A.quotMeasure))
    (hF_val : ∀ i : ι, c i ≠ 0 → ∫ q : (G E s₁ × G E s₂) × G E s', F i q
      ∂(U₁.quotMeasure.prod U₂.quotMeasure).prod A.quotMeasure = r i) :
    ∫ g : G E s₁ × G E s₂, ∫ h : G E s', ∑ i : ι, c i • F i (g, h) ∂A.quotMeasure
        ∂U₁.quotMeasure.prod U₂.quotMeasure = ∑ i : ι, c i • r i := by
  set μ : Measure (G E s₁ × G E s₂) := U₁.quotMeasure.prod U₂.quotMeasure
  -- a term with `c i = 0` vanishes, whether or not `F i` is integrable
  have h_int (i : ι) : Integrable (fun q ↦ c i • F i q) (μ.prod A.quotMeasure) := by
    by_cases hc : c i = 0
    · simp [hc]
    · exact (hF_int i hc).const_mul (c i)
  rw [integral_integral (integrable_finsetSum _ fun i _ ↦ h_int i),
    integral_finsetSum _ fun i _ ↦ h_int i]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  by_cases hc : c i = 0
  · simp [hc]
  · simp [integral_const_mul, hF_val i hc]

omit [WeilData E] in
/-- Let `s` be any sign vector and `fockSpace s` its Fock space. For `v` in it with finite moment
`fockMoment N v = ∫ (1 + ‖z‖) ^ N * |v z| dz`, let `K v` be a continuous kernel on `U₁ ⊕ U₂` and
`A`, bounded by a multiple of that moment times a power of the height on `U₁ ⊕ U₂`, uniformly in the
variable of `A`. Let `φ₁`, `φ₂` be rapidly decreasing functions on the adelic unitary groups of
`U₁`, `U₂`, and `ν₀` a character of `[U(1)]`. Then `φ₁ g₁ * φ₂ g₂ * ν₀ (det g₂) * K v (g₁ ⊕ g₂) z`,
as a function on `(U₁ × U₂) × A`, is integrable and bounded by a constant times a moment of `v`. -/
lemma exists_integrable_kernel_bound {A : Space E n' s'} {U₁ : Space E n₁ s₁}
    {U₂ : Space E n₂ s₂} {φ₁ : G E s₁ → ℂ} {φ₂ : G E s₂ → ℂ} (hφ₁ : φ₁ ∈ U₁.rapidFunctions)
    (hφ₂ : φ₂ ∈ U₂.rapidFunctions) (ν₀ : AutChar E)
    {K : fockSpace s → G E (s₁ ⊕ᵥ s₂) → G E s' → ℂ}
    (hK_le : ∃ (B N : ℕ) (C : ℝ), ∀ (v : fockSpace s) (g : G E (s₁ ⊕ᵥ s₂)) (z : G E s'),
      fockMoment N v ≠ ⊤ → ‖K v g z‖ ≤ C * (fockMoment N v).toReal * (U₁.sum U₂).height g ^ B)
    (hK_cont : ∀ v : fockSpace s, Continuous ↿(K v)) :
    ∃ (N : ℕ) (C : ℝ), ∀ v : fockSpace s, fockMoment N v ≠ ⊤ →
      let F : (G E s₁ × G E s₂) × G E s' → ℂ := fun ((g₁, g₂), z) ↦
        φ₁ g₁ * φ₂ g₂ * (ν₀.val g₂.det * K v (G.sum (g₁, g₂)) z)
      Integrable F ((U₁.quotMeasure.prod U₂.quotMeasure).prod A.quotMeasure) ∧
      ∀ q : (G E s₁ × G E s₂) × G E s', ‖F q‖ ≤ C * (fockMoment N v).toReal := by
  -- The kernel grows at most like `(height g₁ * height g₂) ^ B`, which the rapid decay of `φ₁` and
  -- `φ₂` absorbs; the character has modulus one. A bounded continuous function is integrable.
  obtain ⟨B, N, C, hK_le⟩ := hK_le
  obtain ⟨⟨hφ₁_cont, -⟩, hφ₁_decay⟩ := hφ₁
  obtain ⟨⟨hφ₂_cont, -⟩, hφ₂_decay⟩ := hφ₂
  obtain ⟨D, hD⟩ : ∃ D : ℝ, ∀ g : G E s₁, ‖φ₁ g‖ * U₁.height g ^ B ≤ D := hφ₁_decay B
  obtain ⟨D', hD'⟩ : ∃ D' : ℝ, ∀ g : G E s₂, ‖φ₂ g‖ * U₂.height g ^ B ≤ D' := hφ₂_decay B
  use N, |C| * |D| * D'
  intro v hv F
  set m : ℝ := (fockMoment N v).toReal
  have h_bound : ∀ q : (G E s₁ × G E s₂) × G E s', ‖F q‖ ≤ |C| * |D| * D' * m := by
    rintro ⟨⟨g₁, g₂⟩, z⟩
    have h_height₂ : 0 ≤ U₂.height g₂ := by simp [le_of_lt]
    have h_height : 0 ≤ (U₁.sum U₂).height (G.sum (g₁, g₂)) := by simp [le_of_lt]
    have h_K : ‖K v (G.sum (g₁, g₂)) z‖ ≤ |C| * m * (U₁.height g₁ * U₂.height g₂) ^ B := by
      grw [hK_le v _ z hv, le_abs_self C, height_sum_le]
    simp only [F, norm_mul, Circle.norm_coe, one_mul]
    calc
      _ ≤ ‖φ₁ g₁‖ * ‖φ₂ g₂‖ * (|C| * m * (U₁.height g₁ * U₂.height g₂) ^ B) := by gcongr
      _ = |C| * (‖φ₁ g₁‖ * U₁.height g₁ ^ B) * (‖φ₂ g₂‖ * U₂.height g₂ ^ B) * m := by ring
      _ ≤ |C| * |D| * D' * m := by grw [(hD g₁).trans (le_abs_self D), hD' g₂]
  have h_cont : Continuous F := by fun_prop
  exact ⟨.of_bound h_cont.aestronglyMeasurable _ (.of_forall h_bound), h_bound⟩

/-- Let `s` be a sign vector on a finite index type `n`, so that a polynomial `P` in variables
indexed by `n` has a Fock vector `polyVector s P`. Let numbers `Λ j v` depend on a Fock vector `v`,
each being Lipschitz for one moment `fockMoment N v = ∫ (1 + ‖z‖) ^ N * |v z| dz`. If, for every
polynomial `P`, the numbers `Λ j (polyVector s P)` are one multiple of given numbers `ρ j`, the same
holds for every vector `x` whose moments are all finite. -/
lemma exists_eq_mul_of_forall_polyVector {J : Type*} {Λ : J → fockSpace s → ℂ} {ρ : J → ℂ}
    (h_lipschitz : ∀ j : J, ∃ (N : ℕ) (D : ℝ), ∀ v w : fockSpace s,
      fockMoment N v ≠ ⊤ → fockMoment N w ≠ ⊤ → fockMoment N (w - v) ≠ ⊤ →
      ‖Λ j v - Λ j w‖ ≤ D * (fockMoment N (w - v)).toReal)
    (h_poly : ∀ P : MvPolynomial n ℂ, ∃ r : ℂ, ∀ j : J, Λ j (polyVector s P) = r * ρ j)
    {x : fockSpace s} (hx : IsSchwartzVector x) : ∃ κ : ℂ, ∀ j : J, Λ j x = κ * ρ j := by
  -- The functions `j ↦ Λ j (polyVector s (P m))` lie on the line through `ρ`, which is closed.
  obtain ⟨P, hP⟩ := exists_tendsto_fockMoment hx
  have h_tendsto (j : J) :
      Filter.Tendsto (fun m : ℕ ↦ Λ j (polyVector s (P m))) .atTop (nhds (Λ j x)) := by
    obtain ⟨N, D, h_le⟩ := h_lipschitz j
    have h_error : Filter.Tendsto
        (fun m : ℕ ↦ D * (fockMoment N (x - polyVector s (P m))).toReal) .atTop (nhds 0) := by
      simpa using ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hP N)).const_mul D
    refine tendsto_sub_nhds_zero_iff.1 (squeeze_zero_norm' ?_ h_error)
    filter_upwards [(hP N).eventually_ne ENNReal.zero_ne_top] with m hm
    exact h_le _ _ (fockMoment_polyVector_ne_top N (P m)) (hx N) hm
  have h_span (v : fockSpace s) :
      (fun j : J ↦ Λ j v) ∈ Submodule.span ℂ {ρ} ↔ ∃ r : ℂ, ∀ j : J, Λ j v = r * ρ j := by
    simp [Submodule.mem_span_singleton, funext_iff, eq_comm]
  exact (h_span x).1 ((Submodule.closed_of_finiteDimensional _).isSeqClosed
    (fun m ↦ (h_span _).2 (h_poly (P m))) (tendsto_pi_nhds.2 h_tendsto))

/-! ### The kernels multiply -/

section Kernels

variable (A' : Space E n s) (A : Space E n' s') (U₁ : Space E n₁ s₁) (U₂ : Space E n₂ s₂)
  {𝔪 : Modulus E} (ν₀ γ b : AutChar E) {f₁ : G E s₁ → ℂ} {f₂ : G E s₂ → ℂ}

/-- Let `U₁`, `U₂`, `A` be hermitian spaces, `ν₀` and `aᵢ`, `bᵢ` characters of `[U(1)]` with
`b₂ * ν₀ = b₁`. Take the indicator function of `x` and the product of `P₁` and `P₂`, read by
`renameRowsCols` in the variables of the two column blocks. Then the kernel of `(U₁ ⊕ U₂, A)` at
`g₁ ⊕ g₂`, for the characters `a₁ a₂` and `b₁`, is the product of the kernels of `(U₁, A)` and
`(U₂, A)`, for the column blocks of `x`, divided by `ν₀ (det g₂)`. -/
lemma modKernel_single_sum_left {a₁ a₂ b₁ b₂ : AutChar E} (hb : b₂ * ν₀ = b₁)
    (x : Matrix n' (n₁ ⊕ n₂) 𝔪.ResidueRing) (P₁ : MvPolynomial (InfinitePlace E × n' × n₁) ℂ)
    (P₂ : MvPolynomial (InfinitePlace E × n' × n₂) ℂ) (g₁ : G E s₁) (g₂ : G E s₂) (h : G E s') :
    ν₀.val g₂.det * modKernel (U₁.sum U₂) A (a₁ * a₂) b₁ 𝔪 (Pi.single x 1)
        (renameRowsCols id Sum.inl P₁ * renameRowsCols id Sum.inr P₂) (G.sum (g₁, g₂)) h =
      modKernel U₁ A a₁ b₁ 𝔪 (Pi.single x.toCols₁ 1) P₁ g₁ h *
        modKernel U₂ A a₂ b₂ 𝔪 (Pi.single x.toCols₂ 1) P₂ g₂ h := by
  have h_single : Pi.single x 1 = fun z : Matrix n' (n₁ ⊕ n₂) 𝔪.ResidueRing ↦
      (Pi.single x.toCols₁ 1 : Matrix n' n₁ 𝔪.ResidueRing → ℂ) z.toCols₁ *
        (Pi.single x.toCols₂ 1 : Matrix n' n₂ 𝔪.ResidueRing → ℂ) z.toCols₂ := by
    funext z
    simp [Pi.single_apply, ← ite_and, and_comm, ← fromCols_ext_iff]
  have h_twist : modKernel U₂ A a₂ b₁ 𝔪 (Pi.single x.toCols₂ 1) P₂ g₂ h =
      1 / ν₀.val g₂.det * modKernel U₂ A a₂ b₂ 𝔪 (Pi.single x.toCols₂ 1) P₂ g₂ h := by
    simpa [hb] using modKernel_twist U₂ A a₂ b₂ 𝔪 1 ν₀ _ P₂ g₂ h
  rw [h_single, modKernel_sum_left, h_twist]
  field_simp [Circle.coe_ne_zero]

/-- Let `A'`, `U₁`, `U₂` be hermitian spaces, `ν₀` and `aᵢ`, `bᵢ` characters of `[U(1)]` with
`b₁ * ν₀ = b₂`. Take the indicator function of `y` and the product of `P₁` and `P₂`, read by
`renameRowsCols` in the variables of the two row blocks. Then the kernel of `(A', U₁ ⊕ U₂)` at
`g₁ ⊕ g₂`, for the characters `b₁` and `a₁ a₂`, is the product of the kernels of `(A', U₁)` and
`(A', U₂)`, for the row blocks of `y`, divided by `ν₀ (det g₂)`. -/
lemma modKernel_single_sum_right {a₁ a₂ b₁ b₂ : AutChar E} (hb : b₁ * ν₀ = b₂)
    (y : Matrix (n₁ ⊕ n₂) n 𝔪.ResidueRing) (P₁ : MvPolynomial (InfinitePlace E × n₁ × n) ℂ)
    (P₂ : MvPolynomial (InfinitePlace E × n₂ × n) ℂ) (h : G E s) (g₁ : G E s₁) (g₂ : G E s₂) :
    ν₀.val g₂.det * modKernel A' (U₁.sum U₂) b₁ (a₁ * a₂) 𝔪 (Pi.single y 1)
        (renameRowsCols Sum.inl id P₁ * renameRowsCols Sum.inr id P₂) h (G.sum (g₁, g₂)) =
      modKernel A' U₁ b₁ a₁ 𝔪 (Pi.single y.toRows₁ 1) P₁ h g₁ *
        modKernel A' U₂ b₂ a₂ 𝔪 (Pi.single y.toRows₂ 1) P₂ h g₂ := by
  have h_single : Pi.single y 1 = fun z : Matrix (n₁ ⊕ n₂) n 𝔪.ResidueRing ↦
      (Pi.single y.toRows₁ 1 : Matrix n₁ n 𝔪.ResidueRing → ℂ) z.toRows₁ *
        (Pi.single y.toRows₂ 1 : Matrix n₂ n 𝔪.ResidueRing → ℂ) z.toRows₂ := by
    funext z
    simp [Pi.single_apply, ← ite_and, and_comm, ← fromRows_ext_iff]
  have h_twist : modKernel A' U₂ b₂ a₂ 𝔪 (Pi.single y.toRows₂ 1) P₂ h g₂ =
      ν₀.val g₂.det * modKernel A' U₂ b₁ a₂ 𝔪 (Pi.single y.toRows₂ 1) P₂ h g₂ := by
    simpa [hb] using modKernel_twist A' U₂ b₁ a₂ 𝔪 ν₀ 1 _ P₂ h g₂
  rw [h_single, modKernel_sum_right, h_twist, mul_left_comm]

/-- The theta kernel of `(U₁ ⊕ U₂, A)` for the point datum at `x` with real part `w`, at
`(g₁ ⊕ g₂, h)`, times `f₁ g₁ * f₂ g₂ * ν₀ (det g₂)`. The characters `γ`, `b` of `[U(1)]` twist the
Weil representation in the kernel by `γ (det h) * (b (det (g₁ ⊕ g₂)))⁻¹`. -/
def upIntegrand (f₁ : G E s₁ → ℂ) (f₂ : G E s₂ → ℂ) (x : Matrix n' (n₁ ⊕ n₂) 𝔪.ResidueRing)
    (w : PairFock E (s₁ ⊕ᵥ s₂) s') (q : (G E s₁ × G E s₂) × G E s') : ℂ :=
  f₁ q.1.1 * f₂ q.1.2 * (ν₀.val q.1.2.det *
    pairTheta (U₁.sum U₂) A γ b (modDatum (U₁.sum U₂) A 𝔪 (Pi.single x 1) w) (G.sum q.1, q.2))

/-- The theta kernel of `(A', U₁ ⊕ U₂)` for the point datum at `y` with real part `w`, at
`(h, g₁ ⊕ g₂)`, times `f₁ g₁ * f₂ g₂ * ν₀ (det g₂)`. The characters `γ`, `b` of `[U(1)]` twist the
Weil representation in the kernel by `(γ (det h))⁻¹ * b (det (g₁ ⊕ g₂))`. -/
def downIntegrand (f₁ : G E s₁ → ℂ) (f₂ : G E s₂ → ℂ) (y : Matrix (n₁ ⊕ n₂) n 𝔪.ResidueRing)
    (w : PairFock E s (s₁ ⊕ᵥ s₂)) (q : (G E s₁ × G E s₂) × G E s) : ℂ :=
  f₁ q.1.1 * f₂ q.1.2 * (ν₀.val q.1.2.det *
    pairTheta A' (U₁.sum U₂) b γ (modDatum A' (U₁.sum U₂) 𝔪 (Pi.single y 1) w) (q.2, G.sum q.1))

/-- The function `upIntegrand` is additive in its real datum, the Fock vector in
`PairFock E (s₁ ⊕ᵥ s₂) s'`: its value at `v + w` is the sum of its values at `v` and at `w`. -/
lemma upIntegrand_add (f₁ : G E s₁ → ℂ) (f₂ : G E s₂ → ℂ) (x : Matrix n' (n₁ ⊕ n₂) 𝔪.ResidueRing)
    (v w : PairFock E (s₁ ⊕ᵥ s₂) s') : upIntegrand A U₁ U₂ ν₀ γ b f₁ f₂ x (v + w) =
      upIntegrand A U₁ U₂ ν₀ γ b f₁ f₂ x v + upIntegrand A U₁ U₂ ν₀ γ b f₁ f₂ x w := by
  ext q
  simp [upIntegrand, pairTheta, modDatum, mul_add]

/-- The function `upIntegrand` respects differences in its real datum, the Fock vector in
`PairFock E (s₁ ⊕ᵥ s₂) s'`: its value at `v - w` is its value at `v` minus its value at `w`. -/
lemma upIntegrand_sub (f₁ : G E s₁ → ℂ) (f₂ : G E s₂ → ℂ) (x : Matrix n' (n₁ ⊕ n₂) 𝔪.ResidueRing)
    (v w : PairFock E (s₁ ⊕ᵥ s₂) s') : upIntegrand A U₁ U₂ ν₀ γ b f₁ f₂ x (v - w) =
      upIntegrand A U₁ U₂ ν₀ γ b f₁ f₂ x v - upIntegrand A U₁ U₂ ν₀ γ b f₁ f₂ x w := by
  rw [eq_sub_iff_add_eq, ← upIntegrand_add, sub_add_cancel]

/-- Let `x` be onto modulo an ideal `𝔪` with at least one prime divisor (`𝔪 ≠ 1`), let `f₁`, `f₂`
be automorphic functions of rapid decay for the hermitian spaces `U₁`, `U₂`, and let `ν₀`, `γ`, `b`
be any characters of `[U(1)]`. At `((g₁, g₂), h)`, `upIntegrand` is `f₁ g₁ * f₂ g₂ * ν₀ (det g₂)`
times the theta kernel of `(U₁ ⊕ U₂, A)`, twisted by `γ (det h) * (b (det (g₁ ⊕ g₂)))⁻¹`, for the
point datum at `x` with real part `w`: the theta datum whose part at `𝔪` is the indicator function
of `x` and whose part at infinity is `w`, a vector of the Fock space of the pair (`PairFock`).
There are `N` and `D` such that, whenever `fockMoment N w = ∫ (1 + ‖z‖) ^ N * |w z| dz` is finite,
this function is integrable for the product of the quotient measures of `U₁`, `U₂`, `A` and
bounded by `D * fockMoment N w`. -/
lemma exists_upIntegrand_bound (h𝔪 : Nonempty 𝔪.places) (hf₁ : f₁ ∈ U₁.rapidFunctions)
    (hf₂ : f₂ ∈ U₂.rapidFunctions) {x : Matrix n' (n₁ ⊕ n₂) 𝔪.ResidueRing} (hx : HasLeftInv xᵀ) :
    ∃ (N : ℕ) (D : ℝ), ∀ w : PairFock E (s₁ ⊕ᵥ s₂) s', fockMoment N w ≠ ⊤ →
      Integrable (upIntegrand A U₁ U₂ ν₀ γ b f₁ f₂ x w)
        ((U₁.quotMeasure.prod U₂.quotMeasure).prod A.quotMeasure) ∧
      ∀ q : (G E s₁ × G E s₂) × G E s',
        ‖upIntegrand A U₁ U₂ ν₀ γ b f₁ f₂ x w q‖ ≤ D * (fockMoment N w).toReal := by
  let K (w : PairFock E (s₁ ⊕ᵥ s₂) s') (g : G E (s₁ ⊕ᵥ s₂)) (h : G E s') : ℂ :=
    pairTheta (U₁.sum U₂) A γ b (modDatum (U₁.sum U₂) A 𝔪 (Pi.single x 1) w) (g, h)
  have h_le : ∃ (B N : ℕ) (C : ℝ), ∀ w g h, fockMoment N w ≠ ⊤ →
      ‖K w g h‖ ≤ C * (fockMoment N w).toReal * (U₁.sum U₂).height g ^ B := by
    simpa only [pow_zero, mul_one] using pairTheta_modDatum_decay_of_rightInv (U₁.sum U₂) A γ b
      (Ψ := Pi.single x 1) h𝔪 (by simpa using hx) 0
  exact exists_integrable_kernel_bound hf₁ hf₂ ν₀ (K := K) h_le fun w ↦ by fun_prop

/-- Let `𝔪` have at least one prime divisor (`𝔪.places` nonempty), and let `x` be a matrix modulo
`𝔪` whose transpose `xᵀ` has a left inverse. Let `f₁`, `f₂` be automorphic functions of rapid decay
for `U₁`, `U₂`. Let all moments `fockMoment N w` of the Fock vector `w` be finite. Then
`upIntegrand` at `x` and `w`, for any characters `ν₀`, `γ`, `b` of `[U(1)]`, is integrable for the
product of the quotient measures of `U₁`, `U₂`, `A`. -/
lemma integrable_upIntegrand (h𝔪 : Nonempty 𝔪.places) (hf₁ : f₁ ∈ U₁.rapidFunctions)
    (hf₂ : f₂ ∈ U₂.rapidFunctions) {x : Matrix n' (n₁ ⊕ n₂) 𝔪.ResidueRing} (hx : HasLeftInv xᵀ)
    {w : PairFock E (s₁ ⊕ᵥ s₂) s'} (hw : IsSchwartzVector w) :
    Integrable (upIntegrand A U₁ U₂ ν₀ γ b f₁ f₂ x w)
      ((U₁.quotMeasure.prod U₂.quotMeasure).prod A.quotMeasure) := by
  obtain ⟨N, D, h_bound⟩ := exists_upIntegrand_bound A U₁ U₂ ν₀ γ b h𝔪 hf₁ hf₂ hx
  exact (h_bound w (hw N)).left

/-- Let `x` be onto modulo `𝔪 ≠ 1`, let `f₁`, `f₂` be automorphic functions of rapid decay for `U₁`,
`U₂`, and let `ν₀`, `γ`, `b` be any characters of `[U(1)]`. Here `upIntegrand` is the product of
`f₁ g₁`, `f₂ g₂`, `ν₀ (det g₂)` and the theta kernel of `(U₁ ⊕ U₂, A)`, twisted by `γ`, `b`, for the
indicator of `x` modulo `𝔪` and a vector `v` of the Fock space, the real part of the datum. Let
`J v` be its integral for `μA`, the product of the quotient measures of `U₁`, `U₂`, `A`. There are
`N` and `D` with `‖J v - J v'‖ ≤ D * fockMoment N (v' - v)` whenever `v`, `v'` and `v' - v` have a
finite moment of order `N`. -/
lemma exists_norm_integral_upIntegrand_sub_le (h𝔪 : Nonempty 𝔪.places)
    (hf₁ : f₁ ∈ U₁.rapidFunctions) (hf₂ : f₂ ∈ U₂.rapidFunctions)
    {x : Matrix n' (n₁ ⊕ n₂) 𝔪.ResidueRing} (hx : HasLeftInv xᵀ) :
    let μA : Measure ((G E s₁ × G E s₂) × G E s') :=
      (U₁.quotMeasure.prod U₂.quotMeasure).prod A.quotMeasure
    ∃ (N : ℕ) (D : ℝ), ∀ v v' : PairFock E (s₁ ⊕ᵥ s₂) s',
      fockMoment N v ≠ ⊤ → fockMoment N v' ≠ ⊤ → fockMoment N (v' - v) ≠ ⊤ →
      ‖∫ q : (G E s₁ × G E s₂) × G E s', upIntegrand A U₁ U₂ ν₀ γ b f₁ f₂ x v q ∂μA -
          ∫ q : (G E s₁ × G E s₂) × G E s', upIntegrand A U₁ U₂ ν₀ γ b f₁ f₂ x v' q ∂μA‖ ≤
        D * (fockMoment N (v' - v)).toReal := by
  intro μA
  obtain ⟨N, D, h_bound⟩ := exists_upIntegrand_bound A U₁ U₂ ν₀ γ b h𝔪 hf₁ hf₂ hx
  refine ⟨N, D * μA.real .univ, fun v v' hv hv' hvv' ↦ ?_⟩
  rw [norm_sub_rev, ← integral_sub (h_bound v' hv').left (h_bound v hv).left, mul_right_comm]
  refine norm_integral_le_of_norm_le_const (.of_forall fun q ↦ ?_)
  simpa only [upIntegrand_sub, Pi.sub_apply] using (h_bound (v' - v) hvv').right q

/-- Let `y` be left invertible modulo `𝔪 ≠ 1`, let `f₁`, `f₂` be automorphic functions of rapid
decay for `U₁`, `U₂`, and let `ν₀`, `γ`, `b` be any characters of `[U(1)]`. At `((g₁, g₂), h)`,
`downIntegrand` is `f₁ g₁ * f₂ g₂ * ν₀ (det g₂)` times the theta kernel of `(A', U₁ ⊕ U₂)`, twisted
by `(γ (det h))⁻¹ * b (det (g₁ ⊕ g₂))`, for the point datum at `y` with real part the Fock vector
`w`. If all moments `fockMoment N w = ∫ (1 + ‖z‖) ^ N * |w z| dz` are finite, it is integrable for
the product of the quotient measures of `U₁`, `U₂`, `A'`. -/
lemma integrable_downIntegrand (h𝔪 : Nonempty 𝔪.places) (hf₁ : f₁ ∈ U₁.rapidFunctions)
    (hf₂ : f₂ ∈ U₂.rapidFunctions) {y : Matrix (n₁ ⊕ n₂) n 𝔪.ResidueRing} (hy : HasLeftInv y)
    {w : PairFock E s (s₁ ⊕ᵥ s₂)} (hw : IsSchwartzVector w) :
    Integrable (downIntegrand A' U₁ U₂ ν₀ γ b f₁ f₂ y w)
      ((U₁.quotMeasure.prod U₂.quotMeasure).prod A'.quotMeasure) := by
  let K (v : PairFock E s (s₁ ⊕ᵥ s₂)) (g : G E (s₁ ⊕ᵥ s₂)) (h : G E s) : ℂ :=
    pairTheta A' (U₁.sum U₂) b γ (modDatum A' (U₁.sum U₂) 𝔪 (Pi.single y 1) v) (h, g)
  have h_le : ∃ (B N : ℕ) (C : ℝ), ∀ v g h, fockMoment N v ≠ ⊤ →
      ‖K v g h‖ ≤ C * (fockMoment N v).toReal * (U₁.sum U₂).height g ^ B := by
    simpa only [pow_zero, mul_one] using pairTheta_modDatum_decay A' (U₁.sum U₂) b γ
      (Ψ := Pi.single y 1) h𝔪 (by simpa using hy) 0
  obtain ⟨N, D, h_bound⟩ :=
    exists_integrable_kernel_bound (A := A') hf₁ hf₂ ν₀ (K := K) h_le fun v ↦ by fun_prop
  exact (h_bound w (hw N)).left

/-- Let `b₂ * ν₀ = b₁`, let `x` be a matrix modulo `𝔪` and let `P₁`, `P₂` be polynomials on the
pairs `(U₁, A)`, `(U₂, A)`. `upIntegrand` is `f₁ g₁ * f₂ g₂ * ν₀ (det g₂)` times the theta kernel of
`(U₁ ⊕ U₂, A)`. Here it is taken for the point datum at `x`, the Fock vector of `P₁ P₂` and the
characters `a₁ a₂`, `b₁`. If it is integrable, its integral is the integral over `A` of the product
of the theta lifts of `f₁`, `f₂`. -/
lemma integral_upIntegrand {a₁ a₂ b₁ b₂ : AutChar E} (hb : b₂ * ν₀ = b₁)
    {x : Matrix n' (n₁ ⊕ n₂) 𝔪.ResidueRing} {P₁ : MvPolynomial (InfinitePlace E × n' × n₁) ℂ}
    {P₂ : MvPolynomial (InfinitePlace E × n' × n₂) ℂ}
    (h_int : Integrable (upIntegrand A U₁ U₂ ν₀ (a₁ * a₂) b₁ f₁ f₂ x
        (polyVector (realSigns E (homSigns (s₁ ⊕ᵥ s₂) s'))
          (renameRowsCols id Sum.inl P₁ * renameRowsCols id Sum.inr P₂)))
      ((U₁.quotMeasure.prod U₂.quotMeasure).prod A.quotMeasure)) :
    ∫ q : (G E s₁ × G E s₂) × G E s', upIntegrand A U₁ U₂ ν₀ (a₁ * a₂) b₁ f₁ f₂ x
        (polyVector (realSigns E (homSigns (s₁ ⊕ᵥ s₂) s'))
          (renameRowsCols id Sum.inl P₁ * renameRowsCols id Sum.inr P₂)) q
        ∂(U₁.quotMeasure.prod U₂.quotMeasure).prod A.quotMeasure =
      ∫ h : G E s', lift (pairThetaKer U₁ A a₁ b₁)
          (modDatum U₁ A 𝔪 (Pi.single x.toCols₁ 1) (polyVector (realSigns E (homSigns s₁ s')) P₁))
          f₁ h *
        lift (pairThetaKer U₂ A a₂ b₂)
          (modDatum U₂ A 𝔪 (Pi.single x.toCols₂ 1) (polyVector (realSigns E (homSigns s₂ s')) P₂))
          f₂ h ∂A.quotMeasure := by
  simp_rw [integral_prod_symm _ h_int, lift, ← integral_prod_mul]
  refine integral_congr_ae (.of_forall fun h ↦ integral_congr_ae (.of_forall fun g ↦ ?_))
  -- `modKernel` is by definition the theta kernel at the datum of a polynomial.
  change f₁ g.1 * f₂ g.2 * (ν₀.val g.2.det * modKernel (U₁.sum U₂) A (a₁ * a₂) b₁ 𝔪 (Pi.single x 1)
      (renameRowsCols id Sum.inl P₁ * renameRowsCols id Sum.inr P₂) (G.sum g) h) =
    (modKernel U₁ A a₁ b₁ 𝔪 (Pi.single x.toCols₁ 1) P₁ g.1 h * f₁ g.1) *
      (modKernel U₂ A a₂ b₂ 𝔪 (Pi.single x.toCols₂ 1) P₂ g.2 h * f₂ g.2)
  linear_combination (f₁ g.1 * f₂ g.2) * modKernel_single_sum_left A U₁ U₂ ν₀ hb x P₁ P₂ g.1 g.2 h

/-- Let `b₂ = b₁ ν₀`, let `y` be a matrix modulo `𝔪` and let `P₁`, `P₂` be polynomials on the pairs
`(A', U₁)`, `(A', U₂)` of spaces. Suppose `downIntegrand` is integrable for `y` and the Fock vector
`polyVector` of `P₁ P₂`, with the characters `a₁ a₂` and `b₁`. Then its integral is the integral
over `A'` of a product of two transposed lifts (`swap`). These are the lifts of `f₁` and `f₂` for
the theta kernels `pairThetaKer A' Uᵢ bᵢ aᵢ`. -/
lemma integral_downIntegrand {a₁ a₂ b₁ b₂ : AutChar E} (hb : b₁ * ν₀ = b₂)
    {y : Matrix (n₁ ⊕ n₂) n 𝔪.ResidueRing} {P₁ : MvPolynomial (InfinitePlace E × n₁ × n) ℂ}
    {P₂ : MvPolynomial (InfinitePlace E × n₂ × n) ℂ}
    (h_int : Integrable (downIntegrand A' U₁ U₂ ν₀ (a₁ * a₂) b₁ f₁ f₂ y
        (polyVector (realSigns E (homSigns s (s₁ ⊕ᵥ s₂)))
          (renameRowsCols Sum.inl id P₁ * renameRowsCols Sum.inr id P₂)))
      ((U₁.quotMeasure.prod U₂.quotMeasure).prod A'.quotMeasure)) :
    ∫ q : (G E s₁ × G E s₂) × G E s, downIntegrand A' U₁ U₂ ν₀ (a₁ * a₂) b₁ f₁ f₂ y
        (polyVector (realSigns E (homSigns s (s₁ ⊕ᵥ s₂)))
          (renameRowsCols Sum.inl id P₁ * renameRowsCols Sum.inr id P₂)) q
        ∂(U₁.quotMeasure.prod U₂.quotMeasure).prod A'.quotMeasure =
      ∫ h : G E s, lift (pairThetaKer A' U₁ b₁ a₁).swap
          (modDatum A' U₁ 𝔪 (Pi.single y.toRows₁ 1) (polyVector (realSigns E (homSigns s s₁)) P₁))
          f₁ h *
        lift (pairThetaKer A' U₂ b₂ a₂).swap
          (modDatum A' U₂ 𝔪 (Pi.single y.toRows₂ 1) (polyVector (realSigns E (homSigns s s₂)) P₂))
          f₂ h ∂A'.quotMeasure := by
  simp_rw [integral_prod_symm _ h_int, lift, ← integral_prod_mul]
  refine integral_congr_ae (.of_forall fun h ↦ integral_congr_ae (.of_forall fun g ↦ ?_))
  -- `modKernel` is by definition the theta kernel at the datum of a polynomial.
  change f₁ g.1 * f₂ g.2 * (ν₀.val g.2.det * modKernel A' (U₁.sum U₂) b₁ (a₁ * a₂) 𝔪 (Pi.single y 1)
      (renameRowsCols Sum.inl id P₁ * renameRowsCols Sum.inr id P₂) h (G.sum g)) =
    (modKernel A' U₁ b₁ a₁ 𝔪 (Pi.single y.toRows₁ 1) P₁ h g.1 * f₁ g.1) *
      (modKernel A' U₂ b₂ a₂ 𝔪 (Pi.single y.toRows₂ 1) P₂ h g.2 * f₂ g.2)
  linear_combination (f₁ g.1 * f₂ g.2) * modKernel_single_sum_right A' U₁ U₂ ν₀ hb y P₁ P₂ h g.1 g.2

/-- Suppose that at `g = (g₁, g₂)` the theta integral `thetaIntegral` of `(U₁ ⊕ U₂, A)` with the
datum `modDatum` of `Ψ` and `w` is `c` times the integral over `A'` of the theta kernel `pairTheta`
of `(A', U₁ ⊕ U₂)` with the datum of `Ψ'` and `v`. Then the integral over `A` in `k` of
`∑ x, Ψ x • upIntegrand … x w (g, k)` is `c` times the integral over `A'` in `k` of
`∑ y, Ψ' y • downIntegrand … y v (g, k)`. -/
lemma integral_sum_upIntegrand_eq_mul {a b₀ b₀' : AutChar E} {w : PairFock E (s₁ ⊕ᵥ s₂) s'}
    {v : PairFock E s (s₁ ⊕ᵥ s₂)} {Ψ : Matrix n' (n₁ ⊕ n₂) 𝔪.ResidueRing → ℂ}
    {Ψ' : Matrix (n₁ ⊕ n₂) n 𝔪.ResidueRing → ℂ} {c : ℂ} {g : G E s₁ × G E s₂}
    (h_theta : thetaIntegral (U₁.sum U₂) A a b₀ (modDatum (U₁.sum U₂) A 𝔪 Ψ w) (G.sum g) =
      c * ∫ k : G E s, pairTheta A' (U₁.sum U₂) b₀' a
        (modDatum A' (U₁.sum U₂) 𝔪 Ψ' v) (k, G.sum g) ∂A'.quotMeasure) :
    ∫ k : G E s', ∑ x : Matrix n' (n₁ ⊕ n₂) 𝔪.ResidueRing,
        Ψ x • upIntegrand A U₁ U₂ ν₀ a b₀ f₁ f₂ x w (g, k) ∂A.quotMeasure =
      c * ∫ k : G E s, ∑ y : Matrix (n₁ ⊕ n₂) n 𝔪.ResidueRing,
        Ψ' y • downIntegrand A' U₁ U₂ ν₀ a b₀' f₁ f₂ y v (g, k) ∂A'.quotMeasure := by
  -- expand both data in point data; the factors that depend on `g` alone leave the integrals
  simp only [thetaIntegral, pairTheta, modDatum_eq_sum _ _ Ψ, modDatum_eq_sum _ _ Ψ', map_sum,
    map_smul] at h_theta
  simp only [upIntegrand, downIntegrand, pairTheta, ← mul_smul_comm, ← Finset.mul_sum,
    integral_const_mul, h_theta, mul_left_comm c]

end Kernels

section Edges

variable (A' : Space E n s) (A : Space E n' s') (U₁ : Space E n₁ s₁) (U₂ : Space E n₂ s₂)
  {I : Type*} {e : GInf E s' → ℂ} {e' : GInf E s → ℂ} {e₁ : GInf E s₁ → ℂ}
  {e₂ : GInf E s₂ → ℂ} {a₁ a₂ b₁ b₂ a₁' a₂' b₁' b₂' : I → AutChar E}
  {P₁ : MvPolynomial (InfinitePlace E × n' × n₁) ℂ}
  {P₂ : MvPolynomial (InfinitePlace E × n' × n₂) ℂ}
  {P₁' : MvPolynomial (InfinitePlace E × n₁ × n) ℂ}
  {P₂' : MvPolynomial (InfinitePlace E × n₂ × n) ℂ}

/-- Let `(U₁, A)` and `(U₂, A)` be edges `e₁ → e` and `ē₂ → ē`: with the real data of the
polynomials `P₁`, `P₂`, the theta integrals lift forms of type `e₁`, `ē₂` to forms of type `e`, `ē`
on `A`. Let `w` be a real datum with finite moments, and let `b₂ i * ν₀ i = b₁ i` and `𝔪 i ≠ 1` for
all `i`. There is one number `κ` such that for every member `i` of the family, every `x` onto modulo
`𝔪 i` and all forms `f₁`, `f₂`, the integral of `upIntegrand` is `κ` times the pairing of `f₂` with
the lift of `f₁` to `A` followed by the transposed lift to `U₂`. -/
lemma exists_integral_upIntegrand_eq_mul_integral_lift {ν₀ : I → AutChar E} {𝔪 : I → Modulus E}
    (h₁ : IsPairEdge a₁ b₁ e₁ e P₁) (h₂ : IsPairEdge a₂ b₂ (star e₂) (star e) P₂)
    (hb : ∀ i : I, b₂ i * ν₀ i = b₁ i) (h𝔪 : ∀ i : I, Nonempty (𝔪 i).places)
    {w : PairFock E (s₁ ⊕ᵥ s₂) s'} (hw : IsSchwartzVector w) :
    ∃ κ : ℂ, ∀ (i : I) (x : Matrix n' (n₁ ⊕ n₂) (𝔪 i).ResidueRing), HasLeftInv xᵀ →
      ∀ (f₁ : U₁.Form e₁) (f₂ : U₂.Form (star e₂)),
      ∫ q : (G E s₁ × G E s₂) × G E s', upIntegrand A U₁ U₂ (ν₀ i) (a₁ i * a₂ i) (b₁ i) f₁ f₂ x w q
          ∂(U₁.quotMeasure.prod U₂.quotMeasure).prod A.quotMeasure =
        κ * ∫ g : G E s₂, f₂ g * pairTransposedLift U₂ A (a₂ i) (b₂ i) P₂ (Pi.single x.toCols₂ 1)
          e e₂ (pairLift U₁ A (a₁ i) (b₁ i) P₁ (Pi.single x.toCols₁ 1) e₁ e f₁) g
          ∂U₂.quotMeasure := by
  -- A case is a member of the family, an onto matrix and a form on each `Uᵢ`.
  let Case : Type _ := Σ i : I, {x : Matrix n' (n₁ ⊕ n₂) (𝔪 i).ResidueRing // HasLeftInv xᵀ} ×
    U₁.Form e₁ × U₂.Form (star e₂)
  let μA : Measure ((G E s₁ × G E s₂) × G E s') :=
    (U₁.quotMeasure.prod U₂.quotMeasure).prod A.quotMeasure
  let F : Case → PairFock E (s₁ ⊕ᵥ s₂) s' → (G E s₁ × G E s₂) × G E s' → ℂ :=
    fun ⟨i, x, f₁, f₂⟩ ↦ upIntegrand A U₁ U₂ (ν₀ i) (a₁ i * a₂ i) (b₁ i) f₁ f₂ x.val
  let path : Case → ℂ := fun ⟨i, x, f₁, f₂⟩ ↦
    ∫ h, pairLift U₁ A (a₁ i) (b₁ i) P₁ (Pi.single x.val.toCols₁ 1) e₁ e f₁ h *
      pairLift U₂ A (a₂ i) (b₂ i) P₂ (Pi.single x.val.toCols₂ 1) (star e₂) (star e) f₂ h
      ∂A.quotMeasure
  have hf₁ (f : U₁.Form e₁) : f.val ∈ U₁.rapidFunctions := f.prop.mem_rapidFunctions h₁.isCuspKernel
  have hf₂ (f : U₂.Form (star e₂)) : f.val ∈ U₂.rapidFunctions :=
    f.prop.mem_rapidFunctions h₂.isCuspKernel
  have h_int : ∀ (j : Case) (P : MvPolynomial (InfinitePlace E × n' × (n₁ ⊕ n₂)) ℂ),
      Integrable (F j (polyVector _ P)) μA := fun ⟨i, x, f₁, f₂⟩ P ↦
    integrable_upIntegrand A U₁ U₂ _ _ _ (h𝔪 i) (hf₁ f₁) (hf₂ f₂) x.prop
      fun N ↦ fockMoment_polyVector_ne_top N P
  -- A polynomial is a sum of products `Q₁ Q₂` of polynomials on `(U₁, A)` and `(U₂, A)`.
  have h_poly (Q : MvPolynomial (InfinitePlace E × n' × (n₁ ⊕ n₂)) ℂ) :
      ∃ r : ℂ, ∀ j : Case, ∫ q, F j (polyVector _ Q) q ∂μA = r * path j := by
    refine Submodule.mul_induction_on (mem_rename_range_mul (Prod.map id (Prod.map id Sum.inl))
      (Prod.map id (Prod.map id Sum.inr)) (by simp) Q) ?_ ?_
    · rintro _ ⟨Q₁, rfl⟩ _ ⟨Q₂, rfl⟩
      -- The lifts with `Q₁`, `Q₂` are real averages of the lifts along the edges, and averaging
      -- multiplies the pairing on `A` by a number fixed by the real data.
      obtain ⟨α₁, h_lift₁⟩ := h₁.exists_lift_eq_realConv Q₁
      obtain ⟨α₂, h_lift₂⟩ := h₂.exists_lift_eq_realConv Q₂
      obtain ⟨r, h_avg⟩ := exists_integral_realConv_mul_realConv A h₁.isCuspKernel_star α₁ α₂
      refine ⟨r, fun ⟨i, x, f₁, f₂⟩ ↦ ?_⟩
      refine (integral_upIntegrand A U₁ U₂ (ν₀ i) (hb i) (h_int ⟨i, x, f₁, f₂⟩ _)).trans ?_
      rw [h_lift₁, h_lift₂, h_avg]
    · rintro Q Q' ⟨r, hr⟩ ⟨r', hr'⟩
      refine ⟨r + r', fun j ↦ ?_⟩
      rw [map_add, add_mul, ← hr j, ← hr' j, ← integral_add (h_int j Q) (h_int j Q')]
      obtain ⟨i, x, f₁, f₂⟩ := j
      simp only [F, upIntegrand_add, Pi.add_apply]
  -- The integral is Lipschitz in the real datum, so the relation passes from polynomials to `w`.
  obtain ⟨κ, hκ⟩ : ∃ κ : ℂ, ∀ j : Case, ∫ q, F j w q ∂μA = κ * path j := by
    refine exists_eq_mul_of_forall_polyVector (Λ := fun j v ↦ ∫ q, F j v q ∂μA)
      (fun ⟨i, x, f₁, f₂⟩ ↦ ?_) h_poly hw
    exact exists_norm_integral_upIntegrand_sub_le A U₁ U₂ _ _ _ (h𝔪 i) (hf₁ f₁) (hf₂ f₂) x.prop
  refine ⟨κ, fun i x hx f₁ f₂ ↦ (hκ ⟨i, ⟨x, hx⟩, f₁, f₂⟩).trans (congrArg (κ * ·) ?_)⟩
  -- the lift from `U₂` to `A` is adjoint to the transposed lift
  obtain ⟨h_arrow, -⟩ := h₂.isArrow (S := U₂) (T := A) (Ψ := Pi.single x.toCols₂ 1) i
  exact h_arrow.integral_mul_formLift_swap (h₂.isArrow_swap i) f₂ _

/-- Let `U₁`, `U₂`, `A` be hermitian spaces, `I` a set and, for `i` in `I`, let `(a₁ i, b₁ i)`,
`(a₂ i, b₂ i)` be the characters of `[U(1)]` on the pairs `(U₁, A)`, `(U₂, A)`. Let these pairs be
edges `e₁ → e` and `ē₂ → ē` (`IsPairEdge`): with the real data of the polynomials `P₁`, `P₂`, theta
integrals lift forms of the first type to forms of the second, a bar being complex conjugation. Take
the lift from `U₁` to `A` followed by the transposed lift to `U₂`, the data modulo `𝔪` being the
indicator functions of the two column blocks of a matrix `x` with rows `n'`, the index set of `A`.
Replacing `x` by `g x` multiplies this map by `χ (det g)`, if `(a₁ i * a₂ i)⁻¹` is tame for
`(𝔪, χ)`: it has some weight `μ` at the infinite places, and its tame part is nontrivial exactly at
the places dividing `𝔪 ≠ 1` and defines `χ` on the residue ring. -/
lemma pairTransposedLift_comp_pairLift_mul (h₁ : IsPairEdge a₁ b₁ e₁ e P₁)
    (h₂ : IsPairEdge a₂ b₂ (star e₂) (star e) P₂) (i : I) {𝔪 : Modulus E} {μ : InfinitePlace E → ℤ}
    {χ : MulChar 𝔪.ResidueRing ℂ} (h_tame : IsTameFor 𝔪 (a₁ i * a₂ i)⁻¹ μ χ)
    (g : GL n' 𝔪.ResidueRing) (x : Matrix n' (n₁ ⊕ n₂) 𝔪.ResidueRing) :
    pairTransposedLift U₂ A (a₂ i) (b₂ i) P₂ (Pi.single (g.val * x).toCols₂ 1) e e₂ ∘ₗ
        pairLift U₁ A (a₁ i) (b₁ i) P₁ (Pi.single (g.val * x).toCols₁ 1) e₁ e =
      χ g.val.det • (pairTransposedLift U₂ A (a₂ i) (b₂ i) P₂ (Pi.single x.toCols₂ 1) e e₂ ∘ₗ
        pairLift U₁ A (a₁ i) (b₁ i) P₁ (Pi.single x.toCols₁ 1) e₁ e) := by
  -- Translate the lifted form by the inverse of an integral point `k` of `U(A)` with residue `g`.
  ext1 f
  let k : Gf E n' := liftMod g
  let lifted : A.Form e := pairLift U₁ A (a₁ i) (b₁ i) P₁ (Pi.single (g.val * x.toCols₁) 1) e₁ e f
  have h_char : χ g.val.det = (a₂ i)⁻¹.val (detFin s' k) * (a₁ i)⁻¹.val (detFin s' k) := by
    simpa [mul_comm] using (h_tame.apply_det (s := s') (liftMod g)).symm
  have h_first : A.formRep e k⁻¹ lifted = ((a₁ i)⁻¹.val (detFin s' k) : ℂ) •
      pairLift U₁ A (a₁ i) (b₁ i) P₁ (Pi.single x.toCols₁ 1) e₁ e f := by
    simpa only [map_one, Module.End.one_apply] using (h₁.isArrow i).left.formRep_formLift_of_eq_smul
      (pairWeil_modDatum_single_mul_left U₁ A (a₁ i) (b₁ i) g x.toCols₁ _) f
  have h_second :
      pairTransposedLift U₂ A (a₂ i) (b₂ i) P₂ (Pi.single (g.val * x.toCols₂) 1) e e₂ lifted =
        ((a₂ i)⁻¹.val (detFin s' k) : ℂ) •
          pairTransposedLift U₂ A (a₂ i) (b₂ i) P₂ (Pi.single x.toCols₂ 1) e e₂
            (A.formRep e k⁻¹ lifted) := by
    simpa only [map_one, Module.End.one_apply] using (h₂.isArrow_swap i).formRep_formLift_of_eq_smul
      (pairWeil_modDatum_single_mul_left U₂ A (a₂ i) (b₂ i) g x.toCols₂ _) lifted
  rw [h_first, map_smul, smul_smul, ← h_char] at h_second
  -- the column blocks of `g * x` are by definition `g` times those of `x`
  exact h_second

/-- Let `A'`, `U₁`, `U₂` be hermitian spaces, `I` a set and, for `i` in `I`, let `(b₁' i, a₁' i)`,
`(b₂' i, a₂' i)` be the characters of `[U(1)]` on the pairs `(A', U₁)`, `(A', U₂)`. Let these pairs
be edges `ē' → ē₁` and `e' → e₂` (`IsPairEdge`): with the real data of the polynomials `P₁'`, `P₂'`,
theta integrals lift forms of the first type to forms of the second, a bar being complex
conjugation. Take the transposed lift from `U₁` to `A'` followed by the lift to `U₂`, the data
modulo `𝔪` being the indicator functions of the two row blocks of a matrix `y` with columns `n`,
the index set of `A'`. Replacing `y` by `y g` multiplies this map by `χ (det g)`, if
`(a₁' i * a₂' i)⁻¹` is tame for `(𝔪, χ)`: it has some weight `μ` at the infinite places, and its
tame part is nontrivial exactly at the places dividing `𝔪 ≠ 1` and defines `χ` on the residue
ring. -/
lemma pairLift_comp_pairTransposedLift_mul (h₁ : IsPairEdge b₁' a₁' (star e') (star e₁) P₁')
    (h₂ : IsPairEdge b₂' a₂' e' e₂ P₂') (i : I) {𝔪 : Modulus E} {μ : InfinitePlace E → ℤ}
    {χ : MulChar 𝔪.ResidueRing ℂ} (h_tame : IsTameFor 𝔪 (a₁' i * a₂' i)⁻¹ μ χ)
    (g : GL n 𝔪.ResidueRing) (y : Matrix (n₁ ⊕ n₂) n 𝔪.ResidueRing) :
    pairLift A' U₂ (b₂' i) (a₂' i) P₂' (Pi.single (y * g.val).toRows₂ 1) e' e₂ ∘ₗ
        pairTransposedLift A' U₁ (b₁' i) (a₁' i) P₁' (Pi.single (y * g.val).toRows₁ 1) e₁ e' =
      χ g.val.det • (pairLift A' U₂ (b₂' i) (a₂' i) P₂' (Pi.single y.toRows₂ 1) e' e₂ ∘ₗ
        pairTransposedLift A' U₁ (b₁' i) (a₁' i) P₁' (Pi.single y.toRows₁ 1) e₁ e') := by
  -- Translate the transposed lift of `f` by an integral point `k` of `U(A')` with residue `g`.
  ext1 f
  let k : Gf E n := liftMod g
  let lifted : A'.Form e' :=
    pairTransposedLift A' U₁ (b₁' i) (a₁' i) P₁' (Pi.single (y.toRows₁ * g.val) 1) e₁ e' f
  have h_char : χ g.val.det = (a₂' i)⁻¹.val (detFin s k) * (a₁' i)⁻¹.val (detFin s k) := by
    simpa [mul_comm] using (h_tame.apply_det (s := s) (liftMod g)).symm
  have h_first : A'.formRep e' k lifted = ((a₁' i)⁻¹.val (detFin s k) : ℂ) •
      pairTransposedLift A' U₁ (b₁' i) (a₁' i) P₁' (Pi.single y.toRows₁ 1) e₁ e' f := by
    simpa only [map_one, Module.End.one_apply] using (h₁.isArrow_swap i).formRep_formLift_of_eq_smul
      (pairWeil_modDatum_single_mul_right A' U₁ (b₁' i) (a₁' i) g y.toRows₁ _) f
  have h_second :
      pairLift A' U₂ (b₂' i) (a₂' i) P₂' (Pi.single (y.toRows₂ * g.val) 1) e' e₂ lifted =
        ((a₂' i)⁻¹.val (detFin s k) : ℂ) • pairLift A' U₂ (b₂' i) (a₂' i) P₂'
          (Pi.single y.toRows₂ 1) e' e₂ (A'.formRep e' k lifted) := by
    simpa only [map_one, Module.End.one_apply] using (h₂.isArrow i).left.formRep_formLift_of_eq_smul
      (pairWeil_modDatum_single_mul_right A' U₂ (b₂' i) (a₂' i) g y.toRows₂ _) lifted
  rw [h_first, map_smul, smul_smul, ← h_char] at h_second
  -- the row blocks of `y * g` are by definition those of `y` times `g`
  exact h_second

/-- Let `A'`, `U₁`, `U₂` be hermitian spaces with signs `s`, `s₁`, `s₂`, let the characters
`(b₁' i, a₁' i)`, `(b₂' i, a₂' i)` of `[U(1)]` be attached to the pairs `(A', U₁)`, `(A', U₂)`, and
let these be edges `ē' → ē₁` and `e' → e₂` (`IsPairEdge`): with the real data of `P₁'`, `P₂'`, theta
integrals lift forms of the first type to forms of the second. For forms `f₁`, `f₂` on `U₁`, `U₂` of
types `e₁`, `ē₂`, the integral over the adelic unitary group of `A'`, for its quotient measure
`quotMeasure`, of the product of the transposed lifts of `f₁` and `f₂` is the pairing on `U₂` of
`f₂` with the transposed lift of `f₁` to `A'` followed by the lift to `U₂`. -/
lemma integral_transposedLift_mul_transposedLift (h₁ : IsPairEdge b₁' a₁' (star e') (star e₁) P₁')
    (h₂ : IsPairEdge b₂' a₂' e' e₂ P₂') (i : I) {𝔪 : Modulus E} (Ψ₁ : Matrix n₁ n 𝔪.ResidueRing → ℂ)
    (Ψ₂ : Matrix n₂ n 𝔪.ResidueRing → ℂ) (f₁ : U₁.Form e₁) (f₂ : U₂.Form (star e₂)) :
    ∫ h : G E s, lift (pairThetaKer A' U₁ (b₁' i) (a₁' i)).swap
          (modDatum A' U₁ 𝔪 Ψ₁ (polyVector (realSigns E (homSigns s s₁)) P₁')) f₁ h *
        lift (pairThetaKer A' U₂ (b₂' i) (a₂' i)).swap
          (modDatum A' U₂ 𝔪 Ψ₂ (polyVector (realSigns E (homSigns s s₂)) P₂')) f₂ h
        ∂A'.quotMeasure =
      ∫ g : G E s₂, f₂ g * pairLift A' U₂ (b₂' i) (a₂' i) P₂' Ψ₂ e' e₂
        (pairTransposedLift A' U₁ (b₁' i) (a₁' i) P₁' Ψ₁ e₁ e' f₁) g ∂U₂.quotMeasure := by
  obtain ⟨h_lift, h_descent⟩ := h₂.isArrow (S := A') (T := U₂) (Ψ := Ψ₂) i
  rw [h_lift.integral_mul_formLift_swap h_descent, (h₁.isArrow_swap i).coe_formLift,
    h_descent.coe_formLift]

/-- Let `A'`, `U₁`, `U₂` be hermitian spaces with pairs `(A', U₁)`, `(A', U₂)` that are edges
`star e' → star e₁`, `e' → e₂` for the characters `(b₁' i, a₁' i)`, `(b₂' i, a₂' i)` of `[U(1)]`.
Let `b₁' i * ν₀ = b₂' i`, let `𝔪 ≠ 1`, let `Ψ'` vanish off the left invertible matrices, and let the
forms `f₁`, `f₂` of types `e₁`, `star e₂` be rapidly decreasing (`rapidFunctions`). Here
`downIntegrand` at `y` is the theta kernel of `(A', U₁ ⊕ U₂)` for the point datum at `y` with real
part the Fock vector of `P₁' P₂'`, the variables renamed to the two row blocks by `renameRowsCols`,
times `f₁`, `f₂` and `ν₀ ∘ det`. The integral over `U₁ × U₂` and `A'` (quotient measures) of its sum
over `y`, weighted by `Ψ'`, is the sum, weighted by `Ψ'`, of the pairings of `f₂` with the
transposed lift of `f₁` to `A'` followed by the lift to `U₂`. -/
lemma integral_integral_sum_downIntegrand (h₁ : IsPairEdge b₁' a₁' (star e') (star e₁) P₁')
    (h₂ : IsPairEdge b₂' a₂' e' e₂ P₂') (i : I) {ν₀ : AutChar E} (hb : b₁' i * ν₀ = b₂' i)
    {𝔪 : Modulus E} (h𝔪 : Nonempty 𝔪.places) {Ψ' : Matrix (n₁ ⊕ n₂) n 𝔪.ResidueRing → ℂ}
    (hΨ' : ∀ y : Matrix (n₁ ⊕ n₂) n 𝔪.ResidueRing, Ψ' y ≠ 0 → HasLeftInv y) {f₁ : U₁.Form e₁}
    {f₂ : U₂.Form (star e₂)} (hf₁ : f₁.val ∈ U₁.rapidFunctions) (hf₂ : f₂.val ∈ U₂.rapidFunctions) :
    ∫ g : G E s₁ × G E s₂, ∫ h : G E s, ∑ y : Matrix (n₁ ⊕ n₂) n 𝔪.ResidueRing,
        Ψ' y • downIntegrand A' U₁ U₂ ν₀ (a₁' i * a₂' i) (b₁' i) f₁ f₂ y
          (polyVector (realSigns E (homSigns s (s₁ ⊕ᵥ s₂)))
            (renameRowsCols Sum.inl id P₁' * renameRowsCols Sum.inr id P₂')) (g, h)
        ∂A'.quotMeasure ∂U₁.quotMeasure.prod U₂.quotMeasure =
      ∑ y : Matrix (n₁ ⊕ n₂) n 𝔪.ResidueRing, Ψ' y • ∫ g : G E s₂, f₂ g *
        pairLift A' U₂ (b₂' i) (a₂' i) P₂' (Pi.single y.toRows₂ 1) e' e₂
          (pairTransposedLift A' U₁ (b₁' i) (a₁' i) P₁' (Pi.single y.toRows₁ 1) e₁ e' f₁) g
        ∂U₂.quotMeasure := by
  let v : PairFock E s (s₁ ⊕ᵥ s₂) :=
    polyVector _ (renameRowsCols Sum.inl id P₁' * renameRowsCols Sum.inr id P₂')
  have hv : IsSchwartzVector v := fun N ↦ fockMoment_polyVector_ne_top N _
  have h_int (y : Matrix (n₁ ⊕ n₂) n 𝔪.ResidueRing) (hy : Ψ' y ≠ 0) :
      Integrable (downIntegrand A' U₁ U₂ ν₀ (a₁' i * a₂' i) (b₁' i) f₁ f₂ y v)
        ((U₁.quotMeasure.prod U₂.quotMeasure).prod A'.quotMeasure) :=
    integrable_downIntegrand A' U₁ U₂ ν₀ (a₁' i * a₂' i) (b₁' i) h𝔪 hf₁ hf₂ (hΨ' y hy) hv
  refine integral_integral_sum_eq h_int fun y hy ↦ ?_
  rw [integral_downIntegrand A' U₁ U₂ ν₀ hb (h_int y hy),
    integral_transposedLift_mul_transposedLift _ _ _ h₁ h₂]

lemma ne_zero_of_norm_sq_eq {c : ℂ} {r : ℝ} (h : ‖c‖ ^ 2 = r) (hr : r ≠ 0) : c ≠ 0 := by
  rintro rfl
  exact hr (by simpa using h.symm)

variable (e e' e₁ e₂ a₁ a₂ b₁ b₂ a₁' a₂' b₁' b₂' P₁ P₂ P₁' P₂') in
/-- A family of squares with the same real data. The corners are spaces `U₁`, `U₂`, `A`, `A'` with
signs `s₁`, `s₂`, `s'`, `s`, and `W = U₁ ⊕ U₂`. The pairs `(U₁, A)`, `(U₂, A)`, `(A', U₁)`,
`(A', U₂)` carry the characters `(a₁, b₁)`, `(a₂, b₂)`, `(b₁', a₁')`, `(b₂', a₂')`, which depend on
the member `i` of the family, and the polynomials `P₁`, `P₂`, `P₁'`, `P₂'`. For a character `α` of
`[U(1)]`, `α.baseChange` is the Hecke character `x ↦ α (x / x̄)`, and the splitting character of a
space of rank `m` that carries `α` is `α.spaceChar m = α.baseChange * υ⁻¹ ^ m`. -/
structure IsSquare (t : ℕ) (μ : InfinitePlace E → ℤ) (𝔪 : I → Modulus E) (ν : I → AutChar E)
    (χ : ∀ i : I, MulChar (𝔪 i).ResidueRing ℂ) : Prop where
  /-- `W` has as many negative signs as `A` and `A'` together. -/
  negCount_eq : negCount (s₁ ⊕ᵥ s₂) = negCount s' + negCount s
  /-- The ranks of `A` and `A'` differ by `2 t`. -/
  card_eq : card n' = card n + 2 * t
  /-- Half the rank of `W` exceeds the number of its negative signs. -/
  negCount_lt_half : 2 * negCount (s₁ ⊕ᵥ s₂) + 2 ≤ card (n₁ ⊕ n₂)
  /-- The weights are at least this excess. -/
  card_le_weight (τ : InfinitePlace E) : card (n₁ ⊕ n₂) ≤ 2 * μ τ + 2 * negCount (s₁ ⊕ᵥ s₂)
  /-- The character `ν i` of `[U(1)]` is tame of weight `μ` for `(𝔪 i, χ i)`. -/
  tame (i : I) : IsTameFor (𝔪 i) (ν i) μ (χ i)
  /-- The pair `(U₁, A)` is an edge `e₁ → e`. -/
  edge₁ : IsPairEdge a₁ b₁ e₁ e P₁
  /-- The pair `(U₂, A)` is an edge `ē₂ → ē`. -/
  edge₂ : IsPairEdge a₂ b₂ (star e₂) (star e) P₂
  /-- The pair `(A', U₁)` is an edge `ē' → ē₁`. -/
  edge₁' : IsPairEdge b₁' a₁' (star e') (star e₁) P₁'
  /-- The pair `(A', U₂)` is an edge `e' → e₂`. -/
  edge₂' : IsPairEdge b₂' a₂' e' e₂ P₂'
  /-- On the side of `A`, the splitting characters of `U₁`, `U₂` multiply to `ν̃⁻¹`, the inverse
  base change of `ν`. -/
  spaceChar_mul_up (i : I) : (a₁ i).spaceChar (card n₁) * (a₂ i).spaceChar (card n₂) =
    (ν i).baseChange⁻¹
  /-- So do those on the side of `A'`. -/
  spaceChar_mul_down (i : I) :
    (a₁' i).spaceChar (card n₁) * (a₂' i).spaceChar (card n₂) = (ν i).baseChange⁻¹
  /-- At `U₁`, the splitting characters of `A`, `A'` multiply to `ν̃⁻¹`. -/
  spaceChar_mul_first (i : I) : (b₁ i).spaceChar (card n') * (b₁' i).spaceChar (card n) =
    (ν i).baseChange⁻¹
  /-- So do those at `U₂`. -/
  spaceChar_mul_second (i : I) :
    (b₂ i).spaceChar (card n') * (b₂' i).spaceChar (card n) = (ν i).baseChange⁻¹

end Edges

/-- On matched functions, a transposed lift followed by a lift is a multiple, possibly zero, of a
lift followed by a transposed lift.

The family satisfies `IsSquare`: the four pairs are edges; `ν i` is tame for `𝔪 i ≠ 1`: weight `μ`
at infinity, tame part nontrivial exactly at the places dividing `𝔪 i`, defining `χ i` on the
residue ring; `card n' = card n + 2 t`; the number `N` of negative signs of `W = U₁ ⊕ U₂` is that of
`A` and `A'` together, with `2 N + 2 ≤ card (n₁ ⊕ n₂) ≤ 2 μ τ + 2 N`; the splitting characters
`x ↦ α (x / x̄) * υ x ^ (-m)` of spaces of rank `m` with character `α`, `υ` being the splitting
character of the Weil data, multiply in pairs to the inverse base change of `ν i`. Let `σ` order the
index set of `W` as that of `A'` followed by that of `A`. Let `Θ i x` be the lift from `U₁` to `A`
followed by the transposed lift to `U₂`, and `Θ' i y` the transposed lift to `A'` followed by the
lift to `U₂`, the data modulo `𝔪 i` being the indicator functions of the blocks of `x`, `y`.

There are `C > 0` and `κ`, possibly zero, and for each `i` a number `c` with
`‖c‖ ^ 2 = C * lValueProd (𝔪 i).places (ν i) t ≠ 0`, such that
`∑ Ψ' y • Θ' i y = (κ / c) • ∑ Ψ x • Θ i x` for all matched functions `Ψ`, `Ψ'` of matrices modulo
`𝔪 i`. Here `lValueProd S ν t = ∏_{w ∈ S} q_w ^ (t ^ 2) ∏_{1 ≤ z ≤ t} |L^S(z, ν)| ^ 2`, with `q_w`
the residue cardinality and `L^S(z, ν)` the Euler product of the base change of `ν` outside
`S ∪ S̄`. Matched over the whole residue ring (`⊤`) means: as `k` runs over the invertible matrices
indexed by `n₁ ⊕ n₂`, `Ψ` vanishes off the blocks `x` of rows `n'` of `k⁻¹`, `Ψ'` vanishes off the
blocks `y` of columns `n` of `k`, and `Ψ x = χ i (det k) * Ψ' y` for the two blocks of one `k`. -/
theorem exists_sum_pairLift_comp_pairTransposedLift_eq_smul
    (A' : Space E n s) (A : Space E n' s') (U₁ : Space E n₁ s₁) (U₂ : Space E n₂ s₂)
    {I : Type*} {e : GInf E s' → ℂ} {e' : GInf E s → ℂ} {e₁ : GInf E s₁ → ℂ} {e₂ : GInf E s₂ → ℂ}
    {a₁ a₂ b₁ b₂ a₁' a₂' b₁' b₂' : I → AutChar E}
    {P₁ : MvPolynomial (InfinitePlace E × n' × n₁) ℂ}
    {P₂ : MvPolynomial (InfinitePlace E × n' × n₂) ℂ}
    {P₁' : MvPolynomial (InfinitePlace E × n₁ × n) ℂ}
    {P₂' : MvPolynomial (InfinitePlace E × n₂ × n) ℂ} (σ : n ⊕ n' ≃ n₁ ⊕ n₂) {t : ℕ}
    {μ : InfinitePlace E → ℤ} {𝔪 : I → Modulus E} {ν : I → AutChar E}
    {χ : ∀ i : I, MulChar (𝔪 i).ResidueRing ℂ}
    (h_square : IsSquare e e' e₁ e₂ a₁ a₂ b₁ b₂ a₁' a₂' b₁' b₂' P₁ P₂ P₁' P₂' t μ 𝔪 ν χ) :
    let Θ (i : I) (x : Matrix n' (n₁ ⊕ n₂) (𝔪 i).ResidueRing) : U₁.Form e₁ →ₗ[ℂ] U₂.Form e₂ :=
      pairTransposedLift U₂ A (a₂ i) (b₂ i) P₂ (Pi.single x.toCols₂ 1) e e₂ ∘ₗ
        pairLift U₁ A (a₁ i) (b₁ i) P₁ (Pi.single x.toCols₁ 1) e₁ e
    let Θ' (i : I) (y : Matrix (n₁ ⊕ n₂) n (𝔪 i).ResidueRing) : U₁.Form e₁ →ₗ[ℂ] U₂.Form e₂ :=
      pairLift A' U₂ (b₂' i) (a₂' i) P₂' (Pi.single y.toRows₂ 1) e' e₂ ∘ₗ
        pairTransposedLift A' U₁ (b₁' i) (a₁' i) P₁' (Pi.single y.toRows₁ 1) e₁ e'
    ∃ C : ℝ, 0 < C ∧ ∃ κ : ℂ, ∀ i : I, ∃ c : ℂ,
      ‖c‖ ^ 2 = C * lValueProd (𝔪 i).places (ν i) t ∧
      C * lValueProd (𝔪 i).places (ν i) t ≠ 0 ∧
      ∀ (Ψ : Matrix n' (n₁ ⊕ n₂) (𝔪 i).ResidueRing → ℂ)
        (Ψ' : Matrix (n₁ ⊕ n₂) n (𝔪 i).ResidueRing → ℂ),
        AreMatched ⊤ σ (χ i) Ψ Ψ' →
          ∑ y : Matrix (n₁ ⊕ n₂) n (𝔪 i).ResidueRing, Ψ' y • Θ' i y =
            (κ / c) • ∑ x : Matrix n' (n₁ ⊕ n₂) (𝔪 i).ResidueRing, Ψ x • Θ i x := by
  intro Θ Θ'
  obtain ⟨h_signs, h_rank, h_few_neg, hμ, h_tame, h₁, h₂, h₁', h₂', ha, ha', hb₁, hb₂⟩ := h_square
  -- All four products of characters of `[U(1)]` are the character `rankTwist ν⁻¹` of `W`.
  have h_card : card (n₁ ⊕ n₂) = card n' + card n := by simp [← card_congr σ, add_comm]
  have h_even : 2 ∣ card (n₁ ⊕ n₂) := ⟨card n + t, by omega⟩
  replace ha (i : I) : a₁ i * a₂ i = rankTwist (ν i)⁻¹ (n₁ ⊕ n₂) :=
    (spaceChar_mul_spaceChar_eq_iff card_sum h_even).1 (ha i)
  replace ha' (i : I) : a₁' i * a₂' i = rankTwist (ν i)⁻¹ (n₁ ⊕ n₂) :=
    (spaceChar_mul_spaceChar_eq_iff card_sum h_even).1 (ha' i)
  have hb (i : I) : b₁ i * b₁' i = b₂ i * b₂' i := by
    rw [(spaceChar_mul_spaceChar_eq_iff h_card h_even).1 (hb₁ i),
      (spaceChar_mul_spaceChar_eq_iff h_card h_even).1 (hb₂ i)]
  have h𝔪 (i : I) : Nonempty (𝔪 i).places := by
    obtain ⟨h_places, -⟩ := h_tame i
    exact h_places
  -- One character `ν₀` relates both pairs: `b₂ * ν₀ = b₁` on `A` and `b₁' * ν₀ = b₂'` on `A'`.
  let ν₀ (i : I) : AutChar E := b₁ i / b₂ i
  have hν₀ (i : I) : b₂ i * ν₀ i = b₁ i := mul_div_cancel (b₂ i) (b₁ i)
  have hν₀' (i : I) : b₁' i * ν₀ i = b₂' i := by
    rw [← mul_div_assoc, mul_comm, hb, mul_div_cancel_left]
  -- Apply the exchange identity to the Fock vector `v` of the product of `P₁'` and `P₂'`.
  let v : PairFock E s (s₁ ⊕ᵥ s₂) :=
    polyVector _ (renameRowsCols Sum.inl id P₁' * renameRowsCols Sum.inr id P₂')
  have hv : IsSchwartzVector v := fun N ↦ fockMoment_polyVector_ne_top N _
  obtain ⟨C, hC, w, hw, h_exch⟩ :=
    exchange_identity (U₁.sum U₂) A A' σ h_signs h_rank h_few_neg hμ hv
  obtain ⟨κ, hκ⟩ := exists_integral_upIntegrand_eq_mul_integral_lift A U₁ U₂ h₁ h₂ hν₀ h𝔪 hw
  refine ⟨C, hC, κ, fun i ↦ ?_⟩
  obtain ⟨c, h_size, h_ne, h_exch_i⟩ := h_exch (𝔪 i) (ν i) (χ i) (h_tame i)
  refine ⟨c, h_size, h_ne, fun Ψ Ψ' h_part ↦ ?_⟩
  have hc : c ≠ 0 := ne_zero_of_norm_sq_eq h_size h_ne
  -- Forms are determined by their pairings with the forms `f₂ = conj z` of type `ē₂`.
  refine LinearMap.ext fun f₁ ↦ ext_inner_left ℂ fun z ↦ ?_
  let f₂ : U₂.Form (star e₂) := conjForm rfl z
  have hf₁ : f₁.val ∈ U₁.rapidFunctions := f₁.prop.mem_rapidFunctions h₁.isCuspKernel
  have hf₂ : f₂.val ∈ U₂.rapidFunctions := f₂.prop.mem_rapidFunctions h₂.isCuspKernel
  have h_inner (L : U₂.Form e₂) : inner ℂ z L = ∫ g, f₂ g * L g ∂U₂.quotMeasure := rfl
  let μU : Measure (G E s₁ × G E s₂) := U₁.quotMeasure.prod U₂.quotMeasure
  let F (x : Matrix n' (n₁ ⊕ n₂) (𝔪 i).ResidueRing) : (G E s₁ × G E s₂) × G E s' → ℂ :=
    upIntegrand A U₁ U₂ (ν₀ i) (a₁ i * a₂ i) (b₁ i) f₁ f₂ x w
  let F' (y : Matrix (n₁ ⊕ n₂) n (𝔪 i).ResidueRing) : (G E s₁ × G E s₂) × G E s → ℂ :=
    downIntegrand A' U₁ U₂ (ν₀ i) (a₁' i * a₂' i) (b₁' i) f₁ f₂ y v
  -- The exchange identity at `g₁ ⊕ g₂`, expanded in point data and multiplied by
  -- `f₁ g₁ * f₂ g₂ * ν₀ (det g₂)`.
  have h_exch_at (g : G E s₁ × G E s₂) : ∫ h, ∑ x, Ψ x • F x (g, h) ∂A.quotMeasure =
      c * ∫ h, ∑ y, Ψ' y • F' y (g, h) ∂A'.quotMeasure := by
    have h_theta : thetaIntegral (U₁.sum U₂) A (rankTwist (ν i)⁻¹ (n₁ ⊕ n₂)) (b₁ i)
          (modDatum (U₁.sum U₂) A (𝔪 i) Ψ w) (G.sum g) =
        c * ∫ h, pairTheta A' (U₁.sum U₂) (b₁' i) (rankTwist (ν i)⁻¹ (n₁ ⊕ n₂))
          (modDatum A' (U₁.sum U₂) (𝔪 i) Ψ' v) (h, G.sum g) ∂A'.quotMeasure :=
      h_exch_i (b₁ i) (b₁' i) (hb₁ i) Ψ Ψ' h_part (G.sum g)
    simp only [F, F', ha, ha']
    exact integral_sum_upIntegrand_eq_mul A' A U₁ U₂ (ν₀ i) h_theta
  -- The side of `A`: `Ψ` lives on onto matrices.
  have h_up : ∫ g, ∫ h, ∑ x, Ψ x • F x (g, h) ∂A.quotMeasure ∂μU =
      ∑ x, Ψ x • (κ * inner ℂ z (Θ i x f₁)) := by
    refine integral_integral_sum_eq (fun x hx ↦ ?_) fun x hx ↦ ?_
    · exact integrable_upIntegrand A U₁ U₂ (ν₀ i) (a₁ i * a₂ i) (b₁ i) (h𝔪 i) hf₁ hf₂
        (hasLeftInv_transpose_of_areMatched h_part hx) hw
    · rw [h_inner]
      exact hκ i x (hasLeftInv_transpose_of_areMatched h_part hx) f₁ f₂
  -- The side of `A'`: `Ψ'` lives on left invertible matrices.
  have h_down : ∫ g, ∫ h, ∑ y, Ψ' y • F' y (g, h) ∂A'.quotMeasure ∂μU =
      ∑ y, Ψ' y • inner ℂ z (Θ' i y f₁) := by
    simp only [h_inner]
    exact integral_integral_sum_downIntegrand A' U₁ U₂ h₁' h₂' i (hν₀' i) (h𝔪 i)
      (fun y hy ↦ hasLeftInv_of_areMatched h_part hy) hf₁ hf₂
  have h_scalar : κ * ∑ x, Ψ x * inner ℂ z (Θ i x f₁) =
      c * ∑ y, Ψ' y * inner ℂ z (Θ' i y f₁) := by
    -- integrate `h_exch_at` over `U₁ × U₂`
    have h_eq : ∑ x, Ψ x • (κ * inner ℂ z (Θ i x f₁)) =
        c * ∑ y, Ψ' y • inner ℂ z (Θ' i y f₁) := by
      rw [← h_up, ← h_down, ← integral_const_mul]
      exact integral_congr_ae (.of_forall h_exch_at)
    simpa only [smul_eq_mul, mul_left_comm (Ψ _), ← Finset.mul_sum] using h_eq
  calc
    inner ℂ z ((∑ y, Ψ' y • Θ' i y) f₁) = ∑ y, Ψ' y * inner ℂ z (Θ' i y f₁) := by
      simp
    _ = κ / c * ∑ x, Ψ x * inner ℂ z (Θ i x f₁) := by
      rw [div_mul_eq_mul_div, h_scalar, mul_div_cancel_left₀ _ hc]
    _ = inner ℂ z (((κ / c) • ∑ x, Ψ x • Θ i x) f₁) := by simp

/-- One square: two ways to lift forms from `U₁` to `U₂`, through `A` or through `A'`, transform by
the same character and agree on matched functions up to a constant.

Let `E` be a CM field with Weil data, which fix a splitting Hecke character `υ` of `E`. Let `A'`,
`A`, `U₁`, `U₂` be hermitian spaces over `E` with index sets `n`, `n'`, `n₁`, `n₂` and signs `s`,
`s'`, `s₁`, `s₂` at the infinite places (`A'` goes with the unprimed letters). Let `σ` order the
index set of `W = U₁ ⊕ U₂` as `n` followed by `n'`. The types `e'`, `e`, `e₁`, `e₂` are functions on
the real unitary groups (`GInf`) of the four spaces; a type prescribes the behavior of a form at the
infinite places, and `U₁.Form e₁` is the space of forms of type `e₁` on `U₁`. For `i` in a set `I`,
the pairs `(U₁, A)`, `(U₂, A)`, `(A', U₁)`, `(A', U₂)` carry the characters `(a₁ i, b₁ i)`,
`(a₂ i, b₂ i)`, `(b₁' i, a₁' i)`, `(b₂' i, a₂' i)` of `[U(1)]`, the norm-one ideles of `E` modulo
those from `E`, and the polynomials `P₁`, `P₂`, `P₁'`, `P₂'`, whose Fock vectors are the real theta
data.

The hypothesis `IsSquare` says:
* the rank of `A` is that of `A'` plus `2 t`;
* the number `N` of negative signs of `W` is that of `A` and `A'` together, and
  `2 N + 2 ≤ card (n₁ ⊕ n₂) ≤ 2 μ τ + 2 N` at every infinite place `τ`;
* `ν i` is tame for `𝔪 i ≠ 1`: it has weight `μ` at the infinite places, and its tame part is
  nontrivial exactly at the places dividing `𝔪 i` and defines the character `χ i` of the residue
  ring `R = 𝓞 E / 𝔪 i`;
* the four pairs are edges `e₁ → e`, `ē₂ → ē`, `ē' → ē₁`, `e' → e₂`, a bar being complex conjugation
  (`New.Exchange.IsPairEdge`): the characters have weights independent of `i`, and the theta
  integral lifts forms of the first type to forms of the second;
* with `α[m]` the Hecke character `x ↦ α (x / x̄) * υ x ^ (-m)`, each of the four products
  `a₁[card n₁] a₂[card n₂]`, `a₁'[card n₁] a₂'[card n₂]`, `b₁[card n'] b₁'[card n]`,
  `b₂[card n'] b₂'[card n]` at `i` is the inverse of the base change `x ↦ ν i (x / x̄)`.

For a matrix `x` over `R`, `Θ i x` is the theta lift (`pairLift`) from `U₁` to `A` followed by the
transposed lift (`pairTransposedLift`) to `U₂`; the data modulo `𝔪 i` are the indicator functions of
the two column blocks of `x`. For a matrix `y` over `R`, `Θ' i y` is the transposed lift from `U₁`
to `A'` followed by the lift to `U₂`, for the indicator functions of the two row blocks of `y`.
Then:

(a) `Θ i (g x) = χ i (det g) • Θ i x` and `Θ' i (y g) = χ i (det g) • Θ' i y` for invertible `g`.

(b) There are `C > 0` and a number `κ`, possibly zero, both independent of `i`, and for each `i` a
number `c` with `‖c‖ ^ 2 = C * lValueProd S (ν i) t ≠ 0`, such that
`∑ Ψ' y • Θ' i y = (κ / c) • ∑ Ψ x • Θ i x` for all matched `Ψ`, `Ψ'`. Here `S` is the set of places
dividing `𝔪 i`, and `lValueProd S ν t = ∏_{w ∈ S} q_w ^ (t ^ 2) ∏_{1 ≤ z ≤ t} |L^S(z, ν)| ^ 2`, with
`q_w` the residue cardinality and `L^S(z, ν)` the Euler product of the base change of `ν` outside
`S ∪ S̄`. -/
theorem equivariant_and_exists_sum_eq_of_areMatched {E n n' n₁ n₂ : Type} [Field E] [CMType E]
    [WeilData E] [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
    [Fintype n₁] [DecidableEq n₁] [Fintype n₂] [DecidableEq n₂]
    {s : n → ℤˣ} {s' : n' → ℤˣ} {s₁ : n₁ → ℤˣ} {s₂ : n₂ → ℤˣ}
    (A' : Space E n s) (A : Space E n' s') (U₁ : Space E n₁ s₁) (U₂ : Space E n₂ s₂) {I : Type*}
    {e : GInf E s' → ℂ} {e' : GInf E s → ℂ} {e₁ : GInf E s₁ → ℂ} {e₂ : GInf E s₂ → ℂ}
    {a₁ a₂ b₁ b₂ a₁' a₂' b₁' b₂' : I → AutChar E}
    {P₁ : MvPolynomial (InfinitePlace E × n' × n₁) ℂ}
    {P₂ : MvPolynomial (InfinitePlace E × n' × n₂) ℂ}
    {P₁' : MvPolynomial (InfinitePlace E × n₁ × n) ℂ}
    {P₂' : MvPolynomial (InfinitePlace E × n₂ × n) ℂ} (σ : n ⊕ n' ≃ n₁ ⊕ n₂) {t : ℕ}
    {μ : InfinitePlace E → ℤ} {𝔪 : I → Modulus E} {ν : I → AutChar E}
    {χ : ∀ i : I, MulChar (𝔪 i).ResidueRing ℂ}
    (h_square : IsSquare e e' e₁ e₂ a₁ a₂ b₁ b₂ a₁' a₂' b₁' b₂' P₁ P₂ P₁' P₂' t μ 𝔪 ν χ) :
    let Θ (i : I) (x : Matrix n' (n₁ ⊕ n₂) (𝔪 i).ResidueRing) : U₁.Form e₁ →ₗ[ℂ] U₂.Form e₂ :=
      pairTransposedLift U₂ A (a₂ i) (b₂ i) P₂ (Pi.single x.toCols₂ 1) e e₂ ∘ₗ
        pairLift U₁ A (a₁ i) (b₁ i) P₁ (Pi.single x.toCols₁ 1) e₁ e
    let Θ' (i : I) (y : Matrix (n₁ ⊕ n₂) n (𝔪 i).ResidueRing) : U₁.Form e₁ →ₗ[ℂ] U₂.Form e₂ :=
      pairLift A' U₂ (b₂' i) (a₂' i) P₂' (Pi.single y.toRows₂ 1) e' e₂ ∘ₗ
        pairTransposedLift A' U₁ (b₁' i) (a₁' i) P₁' (Pi.single y.toRows₁ 1) e₁ e'
    -- (a)
    (∀ (i : I) (g : GL n' (𝔪 i).ResidueRing) (x : Matrix n' (n₁ ⊕ n₂) (𝔪 i).ResidueRing),
      Θ i (g.val * x) = χ i g.val.det • Θ i x) ∧
    (∀ (i : I) (g : GL n (𝔪 i).ResidueRing) (y : Matrix (n₁ ⊕ n₂) n (𝔪 i).ResidueRing),
      Θ' i (y * g.val) = χ i g.val.det • Θ' i y) ∧
    -- (b)
    ∃ C : ℝ, 0 < C ∧ ∃ κ : ℂ, ∀ i : I, ∃ c : ℂ,
      ‖c‖ ^ 2 = C * lValueProd (𝔪 i).places (ν i) t ∧
      C * lValueProd (𝔪 i).places (ν i) t ≠ 0 ∧
      ∀ (Ψ : Matrix n' (n₁ ⊕ n₂) (𝔪 i).ResidueRing → ℂ)
        (Ψ' : Matrix (n₁ ⊕ n₂) n (𝔪 i).ResidueRing → ℂ),
        AreMatched ⊤ σ (χ i) Ψ Ψ' →
          ∑ y : Matrix (n₁ ⊕ n₂) n (𝔪 i).ResidueRing, Ψ' y • Θ' i y =
            (κ / c) • ∑ x : Matrix n' (n₁ ⊕ n₂) (𝔪 i).ResidueRing, Ψ x • Θ i x := by
  intro Θ Θ'
  -- Both products of characters of `U₁` and `U₂` are the character `rankTwist ν⁻¹` of `W`, whose
  -- inverse is tame for `(𝔪, χ)`.
  have h_card : card (n₁ ⊕ n₂) = card n' + card n := by simp [← card_congr σ, add_comm]
  have h_rank : card n' = card n + 2 * t := h_square.card_eq
  have h_even : 2 ∣ card (n₁ ⊕ n₂) := ⟨card n + t, by omega⟩
  have h_tame_inv (i : I) {α₁ α₂ : AutChar E}
      (hα : α₁.spaceChar (card n₁) * α₂.spaceChar (card n₂) = (ν i).baseChange⁻¹) :
      ∃ μ' : InfinitePlace E → ℤ, IsTameFor (𝔪 i) (α₁ * α₂)⁻¹ μ' (χ i) := by
    rw [(spaceChar_mul_spaceChar_eq_iff card_sum h_even).1 hα]
    exact (h_square.tame i).exists_inv_rankTwist_inv (n₁ ⊕ n₂)
  refine ⟨fun i ↦ ?_, fun i ↦ ?_, ?_⟩
  · obtain ⟨μ', h_tame'⟩ : ∃ μ' : InfinitePlace E → ℤ,
        IsTameFor (𝔪 i) (a₁ i * a₂ i)⁻¹ μ' (χ i) := h_tame_inv i (h_square.spaceChar_mul_up i)
    exact pairTransposedLift_comp_pairLift_mul A U₁ U₂ h_square.edge₁ h_square.edge₂ i h_tame'
  · obtain ⟨μ', h_tame'⟩ : ∃ μ' : InfinitePlace E → ℤ,
        IsTameFor (𝔪 i) (a₁' i * a₂' i)⁻¹ μ' (χ i) := h_tame_inv i (h_square.spaceChar_mul_down i)
    exact pairLift_comp_pairTransposedLift_mul A' U₁ U₂ h_square.edge₁' h_square.edge₂' i h_tame'
  · exact exists_sum_pairLift_comp_pairTransposedLift_eq_smul A' A U₁ U₂ σ h_square

/-- The case of `New.Exchange.equivariant_and_exists_sum_eq_of_areMatched` in which the characters
of `[U(1)]` come from two families `a`, `b` indexed by finite types: `a` on the pairs `(U₁, A)` and
`(A', U₂)`, `b` on `(U₂, A)` and `(A', U₁)`, with `a i p * b i q = rankTwist (ν i)⁻¹ (n₁ ⊕ n₂)`
whenever `card p + card q = card n₁ + card n₂`; here `rankTwist α N = α * upsilonU1 ^ (card N / 2)`,
with `upsilonU1` the restriction to `[U(1)]` of the fixed splitting character. A type of forms is a
function on the real unitary group (`GInf`); `k₁`, `k₂`, `k`, `k'` are pairs of conjugate types on
`U₁`, `U₂`, `A`, `A'`, the edges `h₂`, `h₁'` of the family `b` are taken at `d`, the edges `h₁`,
`h₂'` of the family `a` at `!d`, and the forms in the conclusion have types `k₁ !d`, `k₂ !d`. The
four edges are edge families: the characters of each family have fixed weights, a common tame part,
and the theta integral with the Fock vector of the given polynomial lifts forms of the type at that
edge's index (`d` or `!d`) to forms of the type at the same index. The number `N` of negative signs
of `W = U₁ ⊕ U₂` is that of `A` and `A'` together, the rank of `A` is that of `A'` plus `2 t`,
`2 N + 2 ≤ card (n₁ ⊕ n₂) ≤ 2 μ τ + 2 N` at every infinite place `τ`, and `ν i` is tame of weight
`μ` for the modulus `𝔪 i`: it has weight `μ` at infinity, and its tame part is ramified exactly at
the primes of `𝔪 i` and defines the character `χ i` of the residue ring.

Send a form `f` from `U₁` to `U₂` through `A` (`Θ i x`: lift, then transposed lift) or through `A'`
(`Θ' i y`: transposed lift, then lift), the data modulo `𝔪 i` being the indicator functions of the
blocks of `x` or `y`. There are `C` and `κ`, and for each `i` some `c ≠ 0` with
`‖c‖ ^ 2 = C * lValueProd (𝔪 i).places (ν i) t`, such that for every functional `l` the functions
`L x = l (Θ i x f)` and `L' y = l (Θ' i y f)` satisfy `New.Exchange.SquareLaw` with constant
`κ / c`: both transform by `χ i ∘ det`, and `∑ Ψ' L' = (κ / c) ∑ Ψ L` for all matched `Ψ`, `Ψ'`. -/
lemma one_square_identity_of_isEdgeFamily (A' : Space E n s) (A : Space E n' s')
    (U₁ : Space E n₁ s₁) (U₂ : Space E n₂ s₂) {I : Type*}
    {k₁ : Bool → GInf E s₁ → ℂ} {k₂ : Bool → GInf E s₂ → ℂ} {d : Bool}
    {k : Bool → GInf E s' → ℂ} {Φ₁ : MvPolynomial (InfinitePlace E × n' × n₁) ℂ}
    {Φ₂ : MvPolynomial (InfinitePlace E × n' × n₂) ℂ} {k' : Bool → GInf E s → ℂ}
    {Φ₁' : MvPolynomial (InfinitePlace E × n₁ × n) ℂ}
    {Φ₂' : MvPolynomial (InfinitePlace E × n₂ × n) ℂ}
    {a b : I → ∀ (m : Type) [Fintype m], AutChar E} {ν : I → AutChar E} {𝔪 : I → Modulus E}
    {χ : ∀ i : I, MulChar (𝔪 i).ResidueRing ℂ}
    (h₂ : IsEdgeFamily b k₂ k d Φ₂) (h₁ : IsEdgeFamily a k₁ k (!d) Φ₁)
    (h₂' : IsEdgeFamily a k' k₂ (!d) Φ₂') (h₁' : IsEdgeFamily b k' k₁ d Φ₁') (σ : n ⊕ n' ≃ n₁ ⊕ n₂)
    (h_signs : negCount (s₁ ⊕ᵥ s₂) = negCount s' + negCount s) (t : ℕ)
    (h_rank : card n' = card n + 2 * t) (h_few_neg : 2 * negCount (s₁ ⊕ᵥ s₂) + 2 ≤ card (n₁ ⊕ n₂))
    {μ : InfinitePlace E → ℤ}
    (hμ : ∀ τ : InfinitePlace E, card (n₁ ⊕ n₂) ≤ 2 * μ τ + 2 * negCount (s₁ ⊕ᵥ s₂))
    (h_tame : ∀ i : I, IsTameFor (𝔪 i) (ν i) μ (χ i))
    (h_chars : ∀ (i : I) {p q : Type} [Fintype p] [Fintype q],
      card p + card q = card n₁ + card n₂ → a i p * b i q = rankTwist (ν i)⁻¹ (n₁ ⊕ n₂)) :
    let Θ (i : I) (x : Matrix n' (n₁ ⊕ n₂) (𝔪 i).ResidueRing) :
        U₁.Form (k₁ !d) →ₗ[ℂ] U₂.Form (k₂ !d) :=
      modTransposedLift U₂ A (b i) Φ₂ (Pi.single x.toCols₂ 1) (k !d) (k₂ !d) ∘ₗ
        modLift U₁ A (a i) Φ₁ (Pi.single x.toCols₁ 1) (k₁ !d) (k !d)
    let Θ' (i : I) (y : Matrix (n₁ ⊕ n₂) n (𝔪 i).ResidueRing) :
        U₁.Form (k₁ !d) →ₗ[ℂ] U₂.Form (k₂ !d) :=
      modLift A' U₂ (a i) Φ₂' (Pi.single y.toRows₂ 1) (k' !d) (k₂ !d) ∘ₗ
        modTransposedLift A' U₁ (b i) Φ₁' (Pi.single y.toRows₁ 1) (k₁ !d) (k' !d)
    ∃ (C : ℝ) (κ : ℂ), ∀ i : I, ∃ c : ℂ,
      c ≠ 0 ∧
      ‖c‖ ^ 2 = C * lValueProd (𝔪 i).places (ν i) t ∧
      ∀ (f : U₁.Form (k₁ !d)) (l : U₂.Form (k₂ !d) →ₗ[ℂ] ℂ),
        SquareLaw (χ i) σ (κ / c) (fun x : Matrix n' (n₁ ⊕ n₂) (𝔪 i).ResidueRing ↦ l (Θ i x f))
          (fun y : Matrix (n₁ ⊕ n₂) n (𝔪 i).ResidueRing ↦ l (Θ' i y f)) := by
  intro Θ Θ'
  have h_card : card (n₁ ⊕ n₂) = card n' + card n := by simp [← card_congr σ, add_comm]
  have h_card' : card n' + card n = card n₁ + card n₂ := h_card.symm.trans card_sum
  have h_even : 2 ∣ card (n₁ ⊕ n₂) := ⟨card n + t, by omega⟩
  -- in each pair of ranks the two splitting characters multiply to the inverse base change of `ν`
  have h_ab (i : I) {p q : Type} [Fintype p] [Fintype q]
      (hpq : card p + card q = card n₁ + card n₂) :
      (a i p).spaceChar (card p) * (b i q).spaceChar (card q) = (ν i).baseChange⁻¹ :=
    (spaceChar_mul_spaceChar_eq_iff (card_sum.trans hpq.symm) h_even).2 (h_chars i hpq)
  have h_ba (i : I) {p q : Type} [Fintype p] [Fintype q]
      (hpq : card p + card q = card n₁ + card n₂) :
      (b i p).spaceChar (card p) * (a i q).spaceChar (card q) = (ν i).baseChange⁻¹ := by
    rw [mul_comm, h_ab i ((add_comm (card q) (card p)).trans hpq)]
  obtain ⟨h_left, h_right, C, -, κ, h_law⟩ :=
    equivariant_and_exists_sum_eq_of_areMatched A' A U₁ U₂ σ
    { negCount_eq := h_signs
      card_eq := h_rank
      negCount_lt_half := h_few_neg
      card_le_weight := hμ
      tame := h_tame
      edge₁ := h₁.isPairEdge
      edge₂ := h₂.isPairEdge_star
      edge₁' := h₁'.isPairEdge_star
      edge₂' := h₂'.isPairEdge
      spaceChar_mul_up := fun i ↦ h_ab i rfl
      spaceChar_mul_down := fun i ↦ h_ba i rfl
      spaceChar_mul_first := fun i ↦ h_ab i h_card'
      spaceChar_mul_second := fun i ↦ h_ba i h_card' }
  refine ⟨C, κ, fun i ↦ ?_⟩
  obtain ⟨c, h_size, h_ne, h_part⟩ := h_law i
  have hc : c ≠ 0 := ne_zero_of_norm_sq_eq h_size h_ne
  -- each clause is an identity of linear maps, evaluated at `f` and followed by `l`
  refine ⟨c, hc, h_size, fun f l ↦
    { left_mul := fun g x ↦ ?_
      right_mul := fun g y ↦ ?_
      sum_eq_of_areMatched := fun Ψ Ψ' hΨ ↦ ?_ }⟩
  · have h_map : Θ i (g.val * x) = χ i g.val.det • Θ i x := h_left i g x
    rw [h_map, LinearMap.smul_apply, map_smul, smul_eq_mul]
  · have h_map : Θ' i (y * g.val) = χ i g.val.det • Θ' i y := h_right i g y
    rw [h_map, LinearMap.smul_apply, map_smul, smul_eq_mul]
  · have h_map : ∑ y, Ψ' y • Θ' i y = (κ / c) • ∑ x, Ψ x • Θ i x := h_part Ψ Ψ' hΨ
    simpa using congrArg (fun L ↦ l (L f)) h_map

end New.Exchange

end
