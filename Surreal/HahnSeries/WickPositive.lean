import Surreal.HahnSeries.WickDomain
import Mathlib.Tactic.Module
import Mathlib.Algebra.CharP.Algebra

/-!
# The positive-covariance criterion for Wick summability

This file proves `wick:thm:positive` (with `wick:eq:delta`, `wick:eq:deltacriterion` and
`wick:eq:explicitpositivebalance`) and the exact-criterion and observable clauses of
`wick:cor:stationary` (with `wick:eq:stationarycone` and `wick:eq:quarticthreshold`) in
`docs/surcomplex/wick-summability-certificates/article.tex`.

**Setting.** As in `Surreal.WickDomain`: `Γ` is a nonzero ordered `ℚ`-vector space (the source's
nonzero divisible ordered abelian group), couplings `gₐ` and covariance entries are nonzero Hahn
series over a field `R` of characteristic zero (the source's `K = ℂ((t^Γ))`), and strong
summability is `Surreal.WickDomain.StronglySummable` of the actual Wick atoms
`Surreal.WickDomain.atom`. The invariant `δₐ = λₐ + ½ ∑ᵢ αᵃᵢ cᵢᵢ` of `wick:eq:delta` is
`delta`, with `λₐ = v(gₐ)` and `cᵢᵢ = v(C_ii)`.

**Main results.**
* `forall_weight_pos_iff`, `forall_wickWeight_pos_iff`: the collapse of the Wick valuation cone.
  If every color carries a loop edge and every edge `e = (u, w)` satisfies the valuation
  Cauchy–Schwarz inequality `c_uu + c_ww ≤ 2 cₑ`, then `L > 0` on `S ∖ {0}` iff `δₐ > 0` for
  every `a`. Necessity uses the element `m = 2eₐ`, `k_ii = αᵃᵢ` of `S` (`diagWitness`), of
  weight `2δₐ`; sufficiency uses `L(m, k) ≥ ∑ₐ mₐ δₐ` on `S`
  (`sum_nsmul_le_two_nsmul_weight`) and `m ≠ 0` on `S ∖ {0}` (`exists_inl_ne_zero`).
* `stronglySummable_atom_iff_delta_pos` (abstract edges) and
  `stronglySummable_matrix_iff_delta_pos` (a covariance matrix with nonzero diagonal satisfying
  `wick:eq:valCS`), with their sector forms `stronglySummable_atom_sector_iff_delta_pos`,
  `stronglySummable_matrix_sector_iff_delta_pos` and full-family forms
  `stronglySummable_atom_forall_iff_delta_pos`, `stronglySummable_matrix_forall_iff_delta_pos`:
  through `Surreal.WickDomain.main_tfae`, the vacuum Wick atom family, the family of every
  pairable sector, and the families of all sectors `Q_β` together (the full Wick family,
  condition (v) of `wick:thm:main`) are strongly summable iff `δₐ > 0` for every `a`.
* `stronglySummable_posDef_iff`, `stronglySummable_posDef_sector_iff` and
  `stronglySummable_posDef_forall_iff`: `wick:thm:positive` for a symmetric positive-definite
  matrix `C` over the real Hahn field `F((t^Γ))` with its lexicographic order (the source's
  `K_R = ℝ((t^Γ))`), with couplings over any field `R` receiving `F` through `φ : F →+* R`
  (`realCov`; the source's `ℝ ⊆ ℂ`, so complex couplings are allowed). The inequality
  `wick:eq:valCS` is `valCS_order`, from `Surreal.Wick.valuation_cauchySchwarz`.
* `stronglySummable_diagonal_iff`, `stronglySummable_diagonal_sector_iff` and
  `stronglySummable_diagonal_forall_iff`: the diagonal case over any `R`, with nonzero diagonal
  entries and no positivity assumption.
* `posDef_explicit_balance`, `posDef_explicit_balance_of_lt_div` and
  `posDef_exists_explicit_balance`: `wick:eq:explicitpositivebalance`. The vector
  `pᵢ = cᵢᵢ / 2 - ε` solves the balancing system `wick:eq:balance` whenever `ε > 0` and
  `|αᵃ| ε < δₐ` for every `a` (for `αᵃ ≠ 0`, `ε < δₐ / |αᵃ|`), and such an `ε` exists when all
  `δₐ > 0` (`exists_eps`; `posDef_exists_explicit_balance` returns it together with its bound).
  `matrix_explicit_balance` is the same statement for any matrix satisfying `wick:eq:valCS`.
* `delta_stationary`, `stronglySummable_stationary_iff`,
  `stronglySummable_stationary_sector_iff` and `stronglySummable_stationary_forall_iff`:
  `wick:cor:stationary`. For the action `𝒮 = ½ ∑ᵢ qᵢ xᵢ² + ∑ₐ uₐ x^{αᵃ}`, the normalized
  expansion with `C_ii = ħ / qᵢ` and `gₐ = -uₐ / ħ` has `δₐ = Δₐ`, so its vacuum family, every
  pairable monomial insertion, and the families of all sectors together, are strongly summable
  iff `Δₐ > 0` for every `a`.
* `stationaryDelta_quartic` and `stronglySummable_quartic_iff`: `wick:eq:quarticthreshold`,
  `Δ = b + h - 2a` for one quartic term.

**Generality.** The source's conventions `d, s ≥ 1` and `αᵃ ≠ 0`, and the hypothesis
`|αᵃ| ≥ 3` of `wick:cor:stationary` (used there only for the connected clause), are not needed.
The collapse is proved for arbitrary finite edge data with loops and the edge form of
`wick:eq:valCS`, which covers both the positive-definite and the diagonal case.

**Pending.** The connected-vacuum clause of `wick:cor:stationary`, which rests on
`wick:thm:connected` (not formalized). The remarks after `wick:eq:quarticthreshold` (equal
leading exponents at equality and descending ones below it) are the necessity mechanism of
`wick:thm:main` (`Surreal.WickDomain.not_stronglySummable_atom_multiples`) and are not restated,
and the definition of a polynomial insertion as a finite combination of its monomial sectors is
not formalized.
-/

namespace Surreal.WickPositive

open _root_.HahnSeries Surreal.Wick Surreal.WickDomain Surreal.Alternative Matrix

noncomputable section

/-! ### The collapsed invariant `δₐ` -/

section Delta

variable {Γ V A : Type*} [AddCommGroup Γ] [Module ℚ Γ] [Fintype V] (α : A → V → ℕ)

/-- The invariant `δₐ = λₐ + ½ ∑ᵢ αᵃᵢ cᵢᵢ` of `wick:eq:delta`, for coupling valuations
`λₐ = lam a` and diagonal covariance valuations `cᵢᵢ = d i`. -/
def delta (lam : A → Γ) (d : V → Γ) (a : A) : Γ :=
  lam a + (2 : ℚ)⁻¹ • ∑ i, α a i • d i

/-- Clearing the factor `½` in `wick:eq:delta`: `2δₐ = 2λₐ + ∑ᵢ αᵃᵢ cᵢᵢ`. -/
theorem two_nsmul_delta (lam : A → Γ) (d : V → Γ) (a : A) :
    2 • delta α lam d a = 2 • lam a + ∑ i, α a i • d i := by
  rw [delta, smul_add, two_nsmul ((2 : ℚ)⁻¹ • _), ← add_smul]
  norm_num

/-- The condition `δₐ > 0` of `wick:eq:deltacriterion`, with the factor `½` cleared:
`δₐ > 0` iff `2λₐ + ∑ᵢ αᵃᵢ cᵢᵢ > 0`. -/
theorem delta_pos_iff [LinearOrder Γ] [IsOrderedAddMonoid Γ] (lam : A → Γ) (d : V → Γ)
    (a : A) : 0 < delta α lam d a ↔ 0 < 2 • lam a + ∑ i, α a i • d i := by
  rw [← two_nsmul_delta, nsmul_pos_iff two_ne_zero]

end Delta

/-! ### The kernel `S` and the collapse inequality -/

section Kernel

variable {Γ V A E : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  [Fintype V] [DecidableEq V] [Fintype A] [Fintype E] (α : A → V → ℕ) (ends : E → V × V)

/-- Exchanging two finite sums of natural multiples. -/
theorem sum_nsmul_sum_nsmul {ι κ M : Type*} [Fintype ι] [Fintype κ] [AddCommMonoid M]
    (f : ι → ℕ) (B : ι → κ → ℕ) (x : κ → M) :
    ∑ j, f j • ∑ k, B j k • x k = ∑ k, (∑ j, f j * B j k) • x k := by
  simp only [Finset.smul_sum, Finset.sum_smul, smul_smul]
  exact Finset.sum_comm

/-- The weight `L(m, k) = ∑ₐ mₐ λₐ + ∑ₑ kₑ cₑ` of `wick:eq:weight` for abstract valuation data
`λ = lam` and `c`. -/
def weight (lam : A → Γ) (c : E → Γ) (q : A ⊕ E → ℕ) : Γ :=
  ∑ a, q (Sum.inl a) • lam a + ∑ e, q (Sum.inr e) • c e

omit [LinearOrder Γ] [IsOrderedAddMonoid Γ] in
/-- On `S`, contracting the diagonal valuations along the edges equals contracting them along
the vertices: `∑ₑ kₑ (d_u + d_w) = ∑ᵢ (Dk)ᵢ dᵢ = ∑ᵢ (Am)ᵢ dᵢ = ∑ₐ mₐ ∑ᵢ αᵃᵢ dᵢ`. -/
theorem sum_edge_eq_sum_vertex {q : A ⊕ E → ℕ} (hq : q ∈ sector α ends 0) (d : V → Γ) :
    ∑ e, q (Sum.inr e) • (d (ends e).1 + d (ends e).2) =
      ∑ a, q (Sum.inl a) • ∑ i, α a i • d i := by
  have h := mem_sector_iff.1 hq
  rw [add_zero] at h
  calc ∑ e, q (Sum.inr e) • (d (ends e).1 + d (ends e).2)
      = ∑ e, q (Sum.inr e) • ∑ i, edgeVec ends e i • d i := by
        simp only [sum_edgeVec_smul]
    _ = ∑ i, edgeCount ends q i • d i := sum_nsmul_sum_nsmul _ _ _
    _ = ∑ i, vertexCount α q i • d i := by rw [h]
    _ = ∑ a, q (Sum.inl a) • ∑ i, α a i • d i := (sum_nsmul_sum_nsmul _ _ _).symm

/-- The collapse inequality in the sufficiency half of `wick:thm:positive`: if every edge
`e = (u, w)` satisfies `d_u + d_w ≤ 2 cₑ` (valuation Cauchy–Schwarz), then on `S`
`∑ₐ mₐ (2λₐ + ∑ᵢ αᵃᵢ dᵢ) ≤ 2 L(m, k)`, that is, `L(m, k) ≥ ∑ₐ mₐ δₐ`. -/
theorem sum_nsmul_le_two_nsmul_weight {lam : A → Γ} {c : E → Γ} {d : V → Γ}
    (hCS : ∀ e, d (ends e).1 + d (ends e).2 ≤ 2 • c e) {q : A ⊕ E → ℕ}
    (hq : q ∈ sector α ends 0) :
    ∑ a, q (Sum.inl a) • (2 • lam a + ∑ i, α a i • d i) ≤ 2 • weight lam c q := by
  rw [weight, smul_add, Finset.smul_sum, Finset.smul_sum]
  simp only [smul_add, Finset.sum_add_distrib]
  rw [← sum_edge_eq_sum_vertex α ends hq d]
  refine add_le_add (le_of_eq (Finset.sum_congr rfl fun a _ => smul_comm _ _ _))
    (Finset.sum_le_sum fun e _ => ?_)
  rw [smul_comm 2]
  exact nsmul_le_nsmul_right (hCS e) _

omit [Fintype V] in
/-- A nonzero element `(m, k)` of `S` has `m ≠ 0`: `Dk = 0` with `k ≥ 0` forces `k = 0`. -/
theorem exists_inl_ne_zero {q : A ⊕ E → ℕ} (hq : q ∈ sector α ends 0) (hq0 : q ≠ 0) :
    ∃ a, q (Sum.inl a) ≠ 0 := by
  by_contra! hm
  apply hq0
  have h := mem_sector_iff.1 hq
  have hv : vertexCount α q = 0 := funext fun i => by simp [vertexCount, hm]
  rw [hv, add_zero] at h
  funext j
  rcases j with a | e
  · exact hm a
  · have h1 : q (Sum.inr e) * edgeVec ends e (ends e).1 ≤ edgeCount ends q (ends e).1 :=
      Finset.single_le_sum (f := fun e' => q (Sum.inr e') * edgeVec ends e' (ends e).1)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ e)
    have h2 : 1 ≤ edgeVec ends e (ends e).1 := by
      simp only [edgeVec, Pi.add_apply, Pi.single_eq_same]
      omega
    have h0 : edgeCount ends q (ends e).1 = 0 := (congrFun h (ends e).1).symm
    rw [h0, Nat.le_zero] at h1
    rcases Nat.mul_eq_zero.1 h1 with h4 | h4
    · exact h4
    · omega

/-- The count vector `m = 2 e_a`, `k_ii = αᵃᵢ` (all other counts zero) of the necessity half of
`wick:thm:positive`: two vertices of type `a` with all their slots paired along loops. -/
def diagWitness [DecidableEq A] [DecidableEq E] (loop : V → E) (a : A) : A ⊕ E → ℕ :=
  Sum.elim (Pi.single a 2) fun e => ∑ i, if loop i = e then α a i else 0

omit [DecidableEq V] [Fintype A] [Fintype E] in
/-- The witness `diagWitness` has `mₐ = 2`; in particular it is nonzero. -/
theorem diagWitness_inl_self [DecidableEq A] [DecidableEq E] (loop : V → E) (a : A) :
    diagWitness α loop a (Sum.inl a) = 2 := by
  simp [diagWitness]

/-- The witness `m = 2eₐ`, `k_ii = αᵃᵢ` lies in `S`: when `loop i` is the loop `(i, i)`, its
edge counts `Dk = 2αᵃ` match its vertex counts `Am = 2αᵃ`. -/
theorem diagWitness_mem [DecidableEq A] [DecidableEq E] (loop : V → E)
    (hloop : ∀ i, ends (loop i) = (i, i)) (a : A) :
    diagWitness α loop a ∈ sector α ends 0 := by
  rw [mem_sector_iff, add_zero]
  funext j
  have hl : ∀ i, edgeVec ends (loop i) j = if j = i then 2 else 0 := by
    intro i
    simp only [edgeVec, hloop, Pi.add_apply, Pi.single_apply]
    split_ifs <;> rfl
  simp only [vertexCount, edgeCount, diagWitness, Sum.elim_inl, Sum.elim_inr, Finset.sum_mul,
    ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp [hl, Pi.single_apply, mul_comm]

omit [LinearOrder Γ] [IsOrderedAddMonoid Γ] [DecidableEq V] in
/-- The weight of the witness `m = 2eₐ`, `k_ii = αᵃᵢ` is `2λₐ + ∑ᵢ αᵃᵢ c_{loop i}`, that is,
`2δₐ` with `cᵢᵢ` the valuation carried by the loop at `i`. -/
theorem weight_diagWitness [DecidableEq A] [DecidableEq E] (lam : A → Γ) (c : E → Γ)
    (loop : V → E) (a : A) :
    weight lam c (diagWitness α loop a) = 2 • lam a + ∑ i, α a i • c (loop i) := by
  simp only [weight, diagWitness, Sum.elim_inl, Sum.elim_inr, Finset.sum_smul, ite_smul,
    zero_smul]
  rw [Finset.sum_comm (γ := E)]
  simp [Pi.single_apply]

/-- `wick:thm:positive` at the level of the vacuum semigroup: if every vertex `i` carries a loop
edge `loop i` and every edge `e = (u, w)` satisfies `c_{uu} + c_{ww} ≤ 2 cₑ`, then
`L > 0` on `S ∖ {0}` iff `2λₐ + ∑ᵢ αᵃᵢ cᵢᵢ > 0` for every `a`. -/
theorem forall_weight_pos_iff (lam : A → Γ) (c : E → Γ) (loop : V → E)
    (hloop : ∀ i, ends (loop i) = (i, i))
    (hCS : ∀ e, c (loop (ends e).1) + c (loop (ends e).2) ≤ 2 • c e) :
    (∀ q ∈ sector α ends 0, q ≠ 0 → 0 < weight lam c q) ↔
      ∀ a, 0 < 2 • lam a + ∑ i, α a i • c (loop i) := by
  classical
  constructor
  · intro h a
    rw [← weight_diagWitness α lam c loop a]
    refine h _ (diagWitness_mem α ends loop hloop a) fun h0 => ?_
    have := congrFun h0 (Sum.inl a)
    rw [diagWitness_inl_self] at this
    exact two_ne_zero this
  · intro h q hq hq0
    obtain ⟨a, ha⟩ := exists_inl_ne_zero α ends hq hq0
    have hpos : 0 < ∑ b, q (Sum.inl b) • (2 • lam b + ∑ i, α b i • c (loop i)) :=
      Finset.sum_pos' (fun b _ => nsmul_nonneg (h b).le _)
        ⟨a, Finset.mem_univ _, nsmul_pos (h a) ha⟩
    exact (nsmul_pos_iff two_ne_zero).1
      (hpos.trans_le (sum_nsmul_le_two_nsmul_weight α ends (d := fun i => c (loop i)) hCS hq))

end Kernel

/-! ### The criterion for the Wick atoms -/

section Atoms

variable {Γ R V A E : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  [Module ℚ Γ] [Field R] [Fintype V] [DecidableEq V] [Fintype A] [Fintype E]
  (α : A → V → ℕ) (ends : E → V × V) {g : A → R⟦Γ⟧} {C : E → R⟦Γ⟧}

/-- `wick:thm:positive`, criterion on `S`, for the Wick weight `L = wickWeight g C`: under the
edge form of valuation Cauchy–Schwarz, `L > 0` on `S ∖ {0}` iff `δₐ > 0` for every `a`. -/
theorem forall_wickWeight_pos_iff (loop : V → E) (hloop : ∀ i, ends (loop i) = (i, i))
    (hCS : ∀ e, (C (loop (ends e).1)).order + (C (loop (ends e).2)).order ≤ 2 • (C e).order) :
    (∀ q ∈ sector α ends 0, q ≠ 0 → 0 < wickWeight g C q) ↔
      ∀ a, 0 < delta α (fun a => (g a).order) (fun i => (C (loop i)).order) a := by
  have e : ∀ q, wickWeight g C q = weight (fun a => (g a).order) (fun e => (C e).order) q :=
    fun q => wickWeight_apply g C q
  simp only [e, delta_pos_iff]
  exact forall_weight_pos_iff α ends (fun a => (g a).order) (fun e => (C e).order) loop hloop
    hCS

/-- **Positive-covariance criterion** (`wick:thm:positive`) for abstract edge data: if every
color `i` has a loop edge `loop i = (i, i)` and every edge `e = (u, w)` satisfies the valuation
Cauchy–Schwarz inequality `c_{uu} + c_{ww} ≤ 2 cₑ` (`wick:eq:valCS`), then the vacuum Wick atom
family is strongly summable iff `δₐ = λₐ + ½ ∑ᵢ αᵃᵢ cᵢᵢ > 0` for every `a`. -/
theorem stronglySummable_atom_iff_delta_pos [CharZero R] [Nontrivial Γ] (hg : ∀ a, g a ≠ 0)
    (hC : ∀ e, C e ≠ 0) (loop : V → E) (hloop : ∀ i, ends (loop i) = (i, i))
    (hCS : ∀ e, (C (loop (ends e).1)).order + (C (loop (ends e).2)).order ≤ 2 • (C e).order) :
    StronglySummable (atom α ends g C 0) ↔
      ∀ a, 0 < delta α (fun a => (g a).order) (fun i => (C (loop i)).order) a :=
  ((main_tfae α ends hg hC).out 0 1).trans (forall_wickWeight_pos_iff α ends loop hloop hCS)

/-- The same criterion governs every pairable sector `Q_β ≠ ∅`. -/
theorem stronglySummable_atom_sector_iff_delta_pos [CharZero R] [Nontrivial Γ]
    (hg : ∀ a, g a ≠ 0) (hC : ∀ e, C e ≠ 0) (loop : V → E)
    (hloop : ∀ i, ends (loop i) = (i, i))
    (hCS : ∀ e, (C (loop (ends e).1)).order + (C (loop (ends e).2)).order ≤ 2 • (C e).order)
    {β : V → ℕ} (hβ : (sector α ends β).Nonempty) :
    StronglySummable (atom α ends g C β) ↔
      ∀ a, 0 < delta α (fun a => (g a).order) (fun i => (C (loop i)).order) a :=
  (stronglySummable_atom_iff_vacuum α ends hg hC hβ).trans
    (stronglySummable_atom_iff_delta_pos α ends hg hC loop hloop hCS)

/-- The criterion for the full Wick family (condition (v) of `wick:thm:main`): the Wick atom
family is strongly summable in every sector `Q_β`, `β ∈ ℕ^V`, iff `δₐ > 0` for every `a`. -/
theorem stronglySummable_atom_forall_iff_delta_pos [CharZero R] [Nontrivial Γ]
    (hg : ∀ a, g a ≠ 0) (hC : ∀ e, C e ≠ 0) (loop : V → E)
    (hloop : ∀ i, ends (loop i) = (i, i))
    (hCS : ∀ e, (C (loop (ends e).1)).order + (C (loop (ends e).2)).order ≤ 2 • (C e).order) :
    (∀ β : V → ℕ, StronglySummable (atom α ends g C β)) ↔
      ∀ a, 0 < delta α (fun a => (g a).order) (fun i => (C (loop i)).order) a :=
  ((main_tfae α ends hg hC).out 4 0).trans
    (stronglySummable_atom_iff_delta_pos α ends hg hC loop hloop hCS)

end Atoms

/-! ### The explicit balancing vector -/

section Balance

variable {Γ V A : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  [Module ℚ Γ] [Fintype V] (α : A → V → ℕ)

omit [LinearOrder Γ] [IsOrderedAddMonoid Γ] in
/-- The vertex inequality of `wick:eq:explicitpositivebalance`:
`λₐ + αᵃ ⬝ p = δₐ - |αᵃ| ε` for `pᵢ = cᵢᵢ / 2 - ε`. -/
theorem vertex_explicit (lam : A → Γ) (d : V → Γ) (ε : Γ) (a : A) :
    lam a + ∑ i, α a i • ((2 : ℚ)⁻¹ • d i - ε) = delta α lam d a - (∑ i, α a i) • ε := by
  have h1 : ∑ i, α a i • ((2 : ℚ)⁻¹ • d i) = (2 : ℚ)⁻¹ • ∑ i, α a i • d i := by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
  rw [delta, Finset.sum_smul]
  simp only [smul_sub, Finset.sum_sub_distrib, h1]
  abel

/-- The edge inequality of `wick:eq:explicitpositivebalance`: if `x + y ≤ 2z` then
`z - (x/2 - ε) - (y/2 - ε) ≥ 2ε > 0`. -/
theorem edge_explicit {x y z ε : Γ} (h : x + y ≤ 2 • z) (hε : 0 < ε) :
    0 < z - ((2 : ℚ)⁻¹ • x - ε) - ((2 : ℚ)⁻¹ • y - ε) := by
  have h1 : (2 : ℚ)⁻¹ • (x + y) ≤ z := by
    refine le_of_nsmul_le_nsmul_right two_ne_zero ?_
    have h2 : ((2 : ℚ)⁻¹ + (2 : ℚ)⁻¹) = 1 := by norm_num
    rw [two_nsmul ((2 : ℚ)⁻¹ • (x + y)), ← add_smul, h2, one_smul]
    exact h
  have h3 : z - ((2 : ℚ)⁻¹ • x - ε) - ((2 : ℚ)⁻¹ • y - ε) =
      (z - (2 : ℚ)⁻¹ • (x + y)) + (ε + ε) := by
    rw [smul_add]
    abel
  rw [h3]
  exact add_pos_of_nonneg_of_pos (sub_nonneg.2 h1) (add_pos hε hε)

/-- A suitable `ε` exists (`wick:eq:explicitpositivebalance`): if every `δₐ` is positive, some
`ε > 0` has `|αᵃ| ε < δₐ` for every `a`. -/
theorem exists_eps [Nontrivial Γ] [Fintype A] (lam : A → Γ) (d : V → Γ)
    (h : ∀ a, 0 < delta α lam d a) :
    ∃ ε : Γ, 0 < ε ∧ ∀ a, (∑ i, α a i) • ε < delta α lam d a := by
  classical
  obtain ⟨γ₀, hγ₀⟩ := exists_zero_lt (α := Γ)
  let f : A → Γ := fun a => (((∑ i, α a i : ℕ) : ℚ) + 1)⁻¹ • delta α lam d a
  have hf : ∀ a, 0 < f a := fun a => qsmul_pos (by positivity) (h a)
  have hfa : ∀ a, (∑ i, α a i) • f a < delta α lam d a := by
    intro a
    have hn : (0 : ℚ) < ((∑ i, α a i : ℕ) : ℚ) + 1 := by positivity
    have hlt : ((∑ i, α a i : ℕ) : ℚ) * (((∑ i, α a i : ℕ) : ℚ) + 1)⁻¹ < 1 := by
      rw [mul_inv_lt_iff₀ hn]
      linarith
    have := qsmul_pos (sub_pos.2 hlt) (h a)
    rw [sub_smul, one_smul, sub_pos, ← smul_smul, Nat.cast_smul_eq_nsmul] at this
    exact this
  let s : Finset Γ := insert γ₀ (Finset.univ.image f)
  have hs : s.Nonempty := Finset.insert_nonempty _ _
  refine ⟨s.min' hs, ?_, fun a => ?_⟩
  · rcases Finset.mem_insert.1 (s.min'_mem hs) with h1 | h1
    · rw [h1]
      exact hγ₀
    · obtain ⟨b, _, hb⟩ := Finset.mem_image.1 h1
      rw [← hb]
      exact hf b
  · have hle : s.min' hs ≤ f a :=
      Finset.min'_le s _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem f (Finset.mem_univ a)))
    exact (nsmul_le_nsmul_right hle _).trans_lt (hfa a)

/-- For `n ≠ 0`, `n ε < δ` iff `ε < δ / n`; this turns the condition `|αᵃ| ε < δₐ` used here
into the source's `ε < δₐ / |αᵃ|` when `αᵃ ≠ 0`. -/
theorem nsmul_lt_iff_lt_inv_qsmul {n : ℕ} (hn : n ≠ 0) {ε δ : Γ} :
    n • ε < δ ↔ ε < ((n : ℚ))⁻¹ • δ := by
  have hq : (0 : ℚ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hc : ((n : ℚ))⁻¹ • ((n : ℚ) • ε) = ε := by
    rw [smul_smul, inv_mul_cancel₀ hq.ne', one_smul]
  have hd : (n : ℚ) • (((n : ℚ))⁻¹ • δ) = δ := by
    rw [smul_smul, mul_inv_cancel₀ hq.ne', one_smul]
  rw [← Nat.cast_smul_eq_nsmul ℚ]
  constructor
  · intro h
    have := qsmul_lt_qsmul (inv_pos.2 hq) h
    rwa [hc] at this
  · intro h
    have := qsmul_lt_qsmul hq h
    rwa [hd] at this

end Balance

/-! ### Covariance matrices -/

section Matrix

variable {Γ R V A : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  [Field R] [Fintype V] [LinearOrder V] [Fintype A] (α : A → V → ℕ)

/-- The loop `(i, i)` of a covariance matrix with nonzero diagonal, as an edge of
`E = {(i, j) : i ≤ j, C_ij ≠ 0}`. -/
def matrixLoop {C : Matrix V V R⟦Γ⟧} (hdiag : ∀ i, C i i ≠ 0) (i : V) : MatrixEdge C :=
  ⟨(i, i), le_rfl, hdiag i⟩

/-- **Positive-covariance criterion** (`wick:thm:positive`) for a covariance matrix `C` over
`R((t^Γ))` with nonzero diagonal whose nonzero entries satisfy the valuation Cauchy–Schwarz
inequality `v(C_ii) + v(C_jj) ≤ 2 v(C_ij)` (`wick:eq:valCS`): the vacuum Wick atom family is
strongly summable iff `δₐ > 0` for every `a`. -/
theorem stronglySummable_matrix_iff_delta_pos [Module ℚ Γ] [Nontrivial Γ] [CharZero R]
    {g : A → R⟦Γ⟧} (hg : ∀ a, g a ≠ 0) (C : Matrix V V R⟦Γ⟧) (hdiag : ∀ i, C i i ≠ 0)
    (hCS : ∀ i j, i ≤ j → C i j ≠ 0 → (C i i).order + (C j j).order ≤ 2 • (C i j).order) :
    StronglySummable (atom α Subtype.val g (matrixCov C) 0) ↔
      ∀ a, 0 < delta α (fun a => (g a).order) (fun i => (C i i).order) a :=
  stronglySummable_atom_iff_delta_pos α Subtype.val hg (fun e => e.2.2) (matrixLoop hdiag)
    (fun _ => rfl) fun e => hCS _ _ e.2.1 e.2.2

/-- The matrix criterion in every pairable sector `Q_β ≠ ∅`. -/
theorem stronglySummable_matrix_sector_iff_delta_pos [Module ℚ Γ] [Nontrivial Γ] [CharZero R]
    {g : A → R⟦Γ⟧} (hg : ∀ a, g a ≠ 0) (C : Matrix V V R⟦Γ⟧) (hdiag : ∀ i, C i i ≠ 0)
    (hCS : ∀ i j, i ≤ j → C i j ≠ 0 → (C i i).order + (C j j).order ≤ 2 • (C i j).order)
    {β : V → ℕ} (hβ : (sector α (Subtype.val : MatrixEdge C → V × V) β).Nonempty) :
    StronglySummable (atom α Subtype.val g (matrixCov C) β) ↔
      ∀ a, 0 < delta α (fun a => (g a).order) (fun i => (C i i).order) a :=
  (stronglySummable_atom_iff_vacuum α Subtype.val hg (fun e => e.2.2) hβ).trans
    (stronglySummable_matrix_iff_delta_pos α hg C hdiag hCS)

/-- The matrix criterion for the full Wick family: the Wick atom family is strongly summable in
every sector `Q_β`, `β ∈ ℕ^V`, iff `δₐ > 0` for every `a`. -/
theorem stronglySummable_matrix_forall_iff_delta_pos [Module ℚ Γ] [Nontrivial Γ] [CharZero R]
    {g : A → R⟦Γ⟧} (hg : ∀ a, g a ≠ 0) (C : Matrix V V R⟦Γ⟧) (hdiag : ∀ i, C i i ≠ 0)
    (hCS : ∀ i j, i ≤ j → C i j ≠ 0 → (C i i).order + (C j j).order ≤ 2 • (C i j).order) :
    (∀ β : V → ℕ, StronglySummable (atom α Subtype.val g (matrixCov C) β)) ↔
      ∀ a, 0 < delta α (fun a => (g a).order) (fun i => (C i i).order) a :=
  ((main_tfae_matrix α hg C).out 4 0).trans
    (stronglySummable_matrix_iff_delta_pos α hg C hdiag hCS)

omit [IsOrderedAddMonoid Γ] [Fintype V] in
/-- A diagonal covariance satisfies the valuation Cauchy–Schwarz inequality trivially: its only
edges are loops, where it is an equality. -/
theorem valCS_of_offDiag_eq_zero {C : Matrix V V R⟦Γ⟧} (hoff : ∀ i j, i ≠ j → C i j = 0) :
    ∀ i j, i ≤ j → C i j ≠ 0 → (C i i).order + (C j j).order ≤ 2 • (C i j).order := by
  intro i j _ hij
  obtain rfl : i = j := by
    by_contra h
    exact hij (hoff i j h)
  rw [two_nsmul]

/-- **Positive-covariance criterion, diagonal case** (`wick:thm:positive`): for a diagonal
covariance matrix over `R((t^Γ))` (any field `R` of characteristic zero, e.g. `K = ℂ((t^Γ))`)
with nonzero diagonal entries, and no positivity assumption, the vacuum Wick atom family is
strongly summable iff `δₐ > 0` for every `a`. -/
theorem stronglySummable_diagonal_iff [Module ℚ Γ] [Nontrivial Γ] [CharZero R]
    {g : A → R⟦Γ⟧} (hg : ∀ a, g a ≠ 0) {C : Matrix V V R⟦Γ⟧}
    (hoff : ∀ i j, i ≠ j → C i j = 0) (hdiag : ∀ i, C i i ≠ 0) :
    StronglySummable (atom α Subtype.val g (matrixCov C) 0) ↔
      ∀ a, 0 < delta α (fun a => (g a).order) (fun i => (C i i).order) a :=
  stronglySummable_matrix_iff_delta_pos α hg C hdiag (valCS_of_offDiag_eq_zero hoff)

/-- The diagonal criterion in every pairable sector `Q_β ≠ ∅`. -/
theorem stronglySummable_diagonal_sector_iff [Module ℚ Γ] [Nontrivial Γ] [CharZero R]
    {g : A → R⟦Γ⟧} (hg : ∀ a, g a ≠ 0) {C : Matrix V V R⟦Γ⟧}
    (hoff : ∀ i j, i ≠ j → C i j = 0) (hdiag : ∀ i, C i i ≠ 0) {β : V → ℕ}
    (hβ : (sector α (Subtype.val : MatrixEdge C → V × V) β).Nonempty) :
    StronglySummable (atom α Subtype.val g (matrixCov C) β) ↔
      ∀ a, 0 < delta α (fun a => (g a).order) (fun i => (C i i).order) a :=
  stronglySummable_matrix_sector_iff_delta_pos α hg C hdiag (valCS_of_offDiag_eq_zero hoff) hβ

/-- The diagonal criterion for the full Wick family: the Wick atom family is strongly summable
in every sector `Q_β`, `β ∈ ℕ^V`, iff `δₐ > 0` for every `a`. -/
theorem stronglySummable_diagonal_forall_iff [Module ℚ Γ] [Nontrivial Γ] [CharZero R]
    {g : A → R⟦Γ⟧} (hg : ∀ a, g a ≠ 0) {C : Matrix V V R⟦Γ⟧}
    (hoff : ∀ i j, i ≠ j → C i j = 0) (hdiag : ∀ i, C i i ≠ 0) :
    (∀ β : V → ℕ, StronglySummable (atom α Subtype.val g (matrixCov C) β)) ↔
      ∀ a, 0 < delta α (fun a => (g a).order) (fun i => (C i i).order) a :=
  stronglySummable_matrix_forall_iff_delta_pos α hg C hdiag (valCS_of_offDiag_eq_zero hoff)

omit [Fintype A] in
/-- The explicit balancing vector `pᵢ = cᵢᵢ / 2 - ε` (`wick:eq:explicitpositivebalance`) for a
covariance matrix satisfying valuation Cauchy–Schwarz: if `ε > 0` and `|αᵃ| ε < δₐ` for every
`a`, then `p` solves the balancing system `wick:eq:balance`. -/
theorem matrix_explicit_balance [Module ℚ Γ] {g : A → R⟦Γ⟧} (C : Matrix V V R⟦Γ⟧)
    (hCS : ∀ i j, i ≤ j → C i j ≠ 0 → (C i i).order + (C j j).order ≤ 2 • (C i j).order)
    {ε : Γ} (hε : 0 < ε)
    (hεa : ∀ a, (∑ i, α a i) • ε < delta α (fun a => (g a).order) (fun i => (C i i).order) a) :
    (∀ a, 0 < (g a).order + ∑ i, α a i • ((2 : ℚ)⁻¹ • (C i i).order - ε)) ∧
      ∀ i j, i ≤ j → C i j ≠ 0 →
        0 < (C i j).order - ((2 : ℚ)⁻¹ • (C i i).order - ε) - ((2 : ℚ)⁻¹ • (C j j).order - ε) :=
  ⟨fun a => lt_of_lt_of_eq (sub_pos.2 (hεa a)) (vertex_explicit α _ _ ε a).symm,
    fun i j hij h0 => edge_explicit (hCS i j hij h0) hε⟩

end Matrix

/-! ### Positive-definite covariance over the real Hahn field -/

section PosDef

section Map

variable {Γ F R : Type*} [Zero Γ] [LinearOrder Γ] [Field F] [Field R]

omit [Zero Γ] in
/-- Applying an embedding of coefficient fields to a Hahn series does not change whether it is
zero. -/
theorem hahnMap_ne_zero_iff (φ : F →+* R) {x : F⟦Γ⟧} : x.map φ ≠ 0 ↔ x ≠ 0 := by
  refine not_congr ⟨fun h => ?_, fun h => ?_⟩
  · ext γ
    have := congrArg (fun y => y.coeff γ) h
    simpa using this
  · subst h
    ext γ
    simp

/-- Applying an embedding of coefficient fields to a Hahn series does not change its
valuation. -/
theorem order_hahnMap (φ : F →+* R) (x : F⟦Γ⟧) : (x.map φ).order = x.order := by
  by_cases hx : x = 0
  · subst hx
    have h0 : (0 : F⟦Γ⟧).map φ = 0 := by
      ext
      simp
    rw [h0, order_zero, order_zero]
  · have hm : x.map φ ≠ 0 := (hahnMap_ne_zero_iff φ).2 hx
    apply le_antisymm
    · apply order_le_of_coeff_ne_zero
      rw [map_coeff, map_ne_zero]
      exact coeff_order_eq_zero.not.2 hx
    · apply order_le_of_coeff_ne_zero
      have := coeff_order_eq_zero.not.2 hm
      rw [map_coeff, map_eq_zero] at this
      exact this

end Map

variable {Γ F R V A : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  [Field F] [LinearOrder F] [IsStrictOrderedRing F] [Field R] [Fintype V] [LinearOrder V]
  [Fintype A] (α : A → V → ℕ)

/-- A real covariance matrix `C` over `F((t^Γ))` (the source's `K_R = ℝ((t^Γ))`, with the
lexicographic order), viewed in `R((t^Γ))` through a coefficient embedding `φ : F →+* R` (the
source's `ℝ((t^Γ)) ⊆ ℂ((t^Γ)) = K`, so that the couplings may be complex). -/
def realCov (φ : F →+* R) (C : Matrix V V (Lex F⟦Γ⟧)) : Matrix V V R⟦Γ⟧ :=
  fun i j => (ofLex (C i j)).map φ

omit [LinearOrder V] [Fintype A] in
/-- A positive-definite matrix has positive diagonal entries. -/
theorem diag_pos [DecidableEq V] {C : Matrix V V (Lex F⟦Γ⟧)}
    (hpd : ∀ x : V → Lex F⟦Γ⟧, x ≠ 0 → 0 < x ⬝ᵥ (C *ᵥ x)) (i : V) : 0 < C i i := by
  have h := hpd (Pi.single i 1) (by simp)
  simpa [mulVec_single_one, single_dotProduct, Matrix.transpose_apply] using h

omit [Fintype A] in
/-- `wick:lem:valCS` in the form used here: for a symmetric positive-definite `C` over the real
Hahn field, every nonzero entry has `v(C_ii) + v(C_jj) ≤ 2 v(C_ij)`. -/
theorem valCS_order {C : Matrix V V (Lex F⟦Γ⟧)} (hC : C.IsSymm)
    (hpd : ∀ x : V → Lex F⟦Γ⟧, x ≠ 0 → 0 < x ⬝ᵥ (C *ᵥ x)) {i j : V} (hij : C i j ≠ 0) :
    (ofLex (C i i)).order + (ofLex (C j j)).order ≤ 2 • (ofLex (C i j)).order := by
  rcases eq_or_ne i j with rfl | hne
  · rw [two_nsmul]
  · obtain ⟨-, hle⟩ := valuation_cauchySchwarz hC hpd hne
    have hi : ofLex (C i i) ≠ 0 := (diag_pos hpd i).ne'
    have hj : ofLex (C j j) ≠ 0 := (diag_pos hpd j).ne'
    have hij' : ofLex (C i j) ≠ 0 := hij
    rw [← order_eq_orderTop_of_ne_zero hi, ← order_eq_orderTop_of_ne_zero hj,
      ← order_eq_orderTop_of_ne_zero hij', ← WithTop.coe_add, ← WithTop.coe_add,
      WithTop.coe_le_coe] at hle
    rw [two_nsmul]
    exact hle

omit [AddCommGroup Γ] [IsOrderedAddMonoid Γ] [LinearOrder F] [IsStrictOrderedRing F]
  [Fintype V] [LinearOrder V] [Fintype A] in
/-- An entry of `realCov φ C` is nonzero iff the corresponding entry of `C` is, so `realCov φ C`
and `C` have the same edge set. -/
theorem realCov_ne_zero_iff (φ : F →+* R) (C : Matrix V V (Lex F⟦Γ⟧)) (i j : V) :
    realCov φ C i j ≠ 0 ↔ C i j ≠ 0 :=
  hahnMap_ne_zero_iff φ

omit [IsOrderedAddMonoid Γ] [LinearOrder F] [IsStrictOrderedRing F] [Fintype V]
  [LinearOrder V] [Fintype A] in
/-- The entries of `realCov φ C` have the same valuations `c_ij = v(C_ij)` as those of `C`. -/
theorem order_realCov (φ : F →+* R) (C : Matrix V V (Lex F⟦Γ⟧)) (i j : V) :
    (realCov φ C i j).order = (ofLex (C i j)).order :=
  order_hahnMap φ _

/-- **Positive-covariance criterion** (`wick:thm:positive`, positive-definite case). Let `C` be
a symmetric positive-definite matrix over the real Hahn field `F((t^Γ))` (`x ⬝ Cx > 0` for every
nonzero `x`, in the lexicographic order; the source takes `F = ℝ`), let `φ : F →+* R` embed the
coefficients into a field `R` (the source's `ℝ ⊆ ℂ`), and let `gₐ ∈ R((t^Γ))` be nonzero
couplings. The vacuum Wick atom family is strongly summable iff
`δₐ = λₐ + ½ ∑ᵢ αᵃᵢ cᵢᵢ > 0` for every `a`, with `λₐ = v(gₐ)` and `cᵢᵢ = v(C_ii)`. -/
theorem stronglySummable_posDef_iff [Module ℚ Γ] [Nontrivial Γ] (φ : F →+* R)
    {g : A → R⟦Γ⟧} (hg : ∀ a, g a ≠ 0) {C : Matrix V V (Lex F⟦Γ⟧)} (hC : C.IsSymm)
    (hpd : ∀ x : V → Lex F⟦Γ⟧, x ≠ 0 → 0 < x ⬝ᵥ (C *ᵥ x)) :
    StronglySummable (atom α Subtype.val g (matrixCov (realCov φ C)) 0) ↔
      ∀ a, 0 < delta α (fun a => (g a).order) (fun i => (ofLex (C i i)).order) a := by
  haveI : CharZero R := charZero_of_injective_ringHom φ.injective
  have h := stronglySummable_matrix_iff_delta_pos α hg (realCov φ C)
    (fun i => (realCov_ne_zero_iff φ C i i).2 (diag_pos hpd i).ne')
    fun i j _ hij => by
      simp only [order_realCov]
      exact valCS_order hC hpd ((realCov_ne_zero_iff φ C i j).1 hij)
  have e : (fun i => (realCov φ C i i).order) = fun i => (ofLex (C i i)).order :=
    funext fun i => order_realCov φ C i i
  rwa [e] at h

/-- The positive-definite criterion in every pairable sector `Q_β ≠ ∅`. -/
theorem stronglySummable_posDef_sector_iff [Module ℚ Γ] [Nontrivial Γ] (φ : F →+* R)
    {g : A → R⟦Γ⟧} (hg : ∀ a, g a ≠ 0) {C : Matrix V V (Lex F⟦Γ⟧)} (hC : C.IsSymm)
    (hpd : ∀ x : V → Lex F⟦Γ⟧, x ≠ 0 → 0 < x ⬝ᵥ (C *ᵥ x)) {β : V → ℕ}
    (hβ : (sector α (Subtype.val : MatrixEdge (realCov φ C) → V × V) β).Nonempty) :
    StronglySummable (atom α Subtype.val g (matrixCov (realCov φ C)) β) ↔
      ∀ a, 0 < delta α (fun a => (g a).order) (fun i => (ofLex (C i i)).order) a := by
  haveI : CharZero R := charZero_of_injective_ringHom φ.injective
  exact (stronglySummable_atom_iff_vacuum α Subtype.val hg (fun e => e.2.2) hβ).trans
    (stronglySummable_posDef_iff α φ hg hC hpd)

/-- `wick:thm:positive` for the full Wick family, positive-definite case: the Wick atom family
of `(g, realCov φ C)` is strongly summable in every sector `Q_β`, `β ∈ ℕ^V` (condition (v) of
`wick:thm:main`), iff `δₐ > 0` for every `a`. -/
theorem stronglySummable_posDef_forall_iff [Module ℚ Γ] [Nontrivial Γ] (φ : F →+* R)
    {g : A → R⟦Γ⟧} (hg : ∀ a, g a ≠ 0) {C : Matrix V V (Lex F⟦Γ⟧)} (hC : C.IsSymm)
    (hpd : ∀ x : V → Lex F⟦Γ⟧, x ≠ 0 → 0 < x ⬝ᵥ (C *ᵥ x)) :
    (∀ β : V → ℕ, StronglySummable (atom α Subtype.val g (matrixCov (realCov φ C)) β)) ↔
      ∀ a, 0 < delta α (fun a => (g a).order) (fun i => (ofLex (C i i)).order) a := by
  haveI : CharZero R := charZero_of_injective_ringHom φ.injective
  exact ((main_tfae_matrix α hg (realCov φ C)).out 4 0).trans
    (stronglySummable_posDef_iff α φ hg hC hpd)

omit [Fintype A] in
/-- **Explicit balancing vector** (`wick:eq:explicitpositivebalance`). For a symmetric
positive-definite `C` over the real Hahn field, if `ε > 0` and `|αᵃ| ε < δₐ` for every `a`
(for `αᵃ ≠ 0` this is `ε < δₐ / |αᵃ|`), then `pᵢ = cᵢᵢ / 2 - ε` satisfies the balancing system
`wick:eq:balance`: `λₐ + αᵃ ⬝ p > 0` and `c_ij - p_i - p_j > 0` for every nonzero `C_ij`. -/
theorem posDef_explicit_balance [Module ℚ Γ] {g : A → R⟦Γ⟧} {C : Matrix V V (Lex F⟦Γ⟧)}
    (hC : C.IsSymm) (hpd : ∀ x : V → Lex F⟦Γ⟧, x ≠ 0 → 0 < x ⬝ᵥ (C *ᵥ x)) {ε : Γ}
    (hε : 0 < ε)
    (hεa : ∀ a, (∑ i, α a i) • ε <
      delta α (fun a => (g a).order) (fun i => (ofLex (C i i)).order) a) :
    (∀ a, 0 < (g a).order + ∑ i, α a i • ((2 : ℚ)⁻¹ • (ofLex (C i i)).order - ε)) ∧
      ∀ i j, C i j ≠ 0 → 0 < (ofLex (C i j)).order -
        ((2 : ℚ)⁻¹ • (ofLex (C i i)).order - ε) - ((2 : ℚ)⁻¹ • (ofLex (C j j)).order - ε) :=
  ⟨fun a => lt_of_lt_of_eq (sub_pos.2 (hεa a)) (vertex_explicit α _ _ ε a).symm,
    fun _ _ h0 => edge_explicit (valCS_order hC hpd h0) hε⟩

omit [Fintype A] in
/-- `wick:eq:explicitpositivebalance` with the source's bound: if every `αᵃ` is nonzero and
`0 < ε < δₐ / |αᵃ|` for every `a`, then `pᵢ = cᵢᵢ / 2 - ε` solves the balancing system. -/
theorem posDef_explicit_balance_of_lt_div [Module ℚ Γ] {g : A → R⟦Γ⟧}
    {C : Matrix V V (Lex F⟦Γ⟧)} (hC : C.IsSymm)
    (hpd : ∀ x : V → Lex F⟦Γ⟧, x ≠ 0 → 0 < x ⬝ᵥ (C *ᵥ x)) (hα : ∀ a, ∑ i, α a i ≠ 0) {ε : Γ}
    (hε : 0 < ε)
    (hεa : ∀ a, ε < (((∑ i, α a i : ℕ) : ℚ))⁻¹ •
      delta α (fun a => (g a).order) (fun i => (ofLex (C i i)).order) a) :
    (∀ a, 0 < (g a).order + ∑ i, α a i • ((2 : ℚ)⁻¹ • (ofLex (C i i)).order - ε)) ∧
      ∀ i j, C i j ≠ 0 → 0 < (ofLex (C i j)).order -
        ((2 : ℚ)⁻¹ • (ofLex (C i i)).order - ε) - ((2 : ℚ)⁻¹ • (ofLex (C j j)).order - ε) :=
  posDef_explicit_balance α hC hpd hε fun a => (nsmul_lt_iff_lt_inv_qsmul (hα a)).2 (hεa a)

/-- `wick:thm:positive`, last clause: for symmetric positive-definite `C` with `δₐ > 0` for
every `a` (`wick:eq:deltacriterion`), some `ε > 0` with `|αᵃ| ε < δₐ` for every `a` (the bound
of `wick:eq:explicitpositivebalance`, which for `αᵃ ≠ 0` reads `ε < δₐ / |αᵃ|`) makes
`pᵢ = cᵢᵢ / 2 - ε` a solution of the balancing system `wick:eq:balance` of the Wick data
`(g, realCov φ C)`. -/
theorem posDef_exists_explicit_balance [Module ℚ Γ] [Nontrivial Γ] (φ : F →+* R)
    {g : A → R⟦Γ⟧} {C : Matrix V V (Lex F⟦Γ⟧)} (hC : C.IsSymm)
    (hpd : ∀ x : V → Lex F⟦Γ⟧, x ≠ 0 → 0 < x ⬝ᵥ (C *ᵥ x))
    (hδ : ∀ a, 0 < delta α (fun a => (g a).order) (fun i => (ofLex (C i i)).order) a) :
    ∃ ε : Γ, 0 < ε ∧
      (∀ a, (∑ i, α a i) • ε <
        delta α (fun a => (g a).order) (fun i => (ofLex (C i i)).order) a) ∧
      (∀ a, 0 < (g a).order + ∑ i, α a i • ((2 : ℚ)⁻¹ • (ofLex (C i i)).order - ε)) ∧
      ∀ i j, i ≤ j → realCov φ C i j ≠ 0 → 0 < (realCov φ C i j).order -
        ((2 : ℚ)⁻¹ • (ofLex (C i i)).order - ε) - ((2 : ℚ)⁻¹ • (ofLex (C j j)).order - ε) := by
  obtain ⟨ε, hε, hεa⟩ := exists_eps α _ _ hδ
  obtain ⟨h1, h2⟩ := posDef_explicit_balance α (g := g) hC hpd hε hεa
  refine ⟨ε, hε, hεa, h1, fun i j _ hij => ?_⟩
  rw [order_realCov]
  exact h2 i j ((realCov_ne_zero_iff φ C i j).1 hij)

end PosDef

/-! ### The algebraic stationary-phase domain -/

section Stationary

section Order

variable {Γ R : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [Field R]

/-- `v(x⁻¹) = -v(x)` in the Hahn field. -/
theorem order_inv_eq {x : R⟦Γ⟧} (hx : x ≠ 0) : x⁻¹.order = -x.order := by
  have h := order_mul hx (inv_ne_zero hx)
  rw [mul_inv_cancel₀ hx, order_one] at h
  rw [eq_neg_iff_add_eq_zero, add_comm]
  exact h.symm

/-- `v(x / y) = v(x) - v(y)` in the Hahn field. -/
theorem order_div_eq {x y : R⟦Γ⟧} (hx : x ≠ 0) (hy : y ≠ 0) :
    (x / y).order = x.order - y.order := by
  rw [div_eq_mul_inv, order_mul hx (inv_ne_zero hy), order_inv_eq hy, sub_eq_add_neg]

end Order

variable {Γ R V A : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  [Module ℚ Γ] [Field R] [Fintype V] [LinearOrder V] [Fintype A] (α : A → V → ℕ)

/-- The stationary-phase invariant
`Δₐ = bₐ + (|αᵃ|/2 - 1) h - ½ ∑ᵢ αᵃᵢ aᵢ` of `wick:eq:stationarycone`. -/
def stationaryDelta (b : A → Γ) (h : Γ) (a' : V → Γ) (a : A) : Γ :=
  b a + (((∑ i, α a i : ℕ) : ℚ) / 2 - 1) • h - (2 : ℚ)⁻¹ • ∑ i, α a i • a' i

omit [LinearOrder Γ] [IsOrderedAddMonoid Γ] [LinearOrder V] [Fintype A] in
/-- `wick:cor:stationary`, first step: substituting `λₐ = bₐ - h` and `cᵢᵢ = h - aᵢ` into
`wick:eq:delta` gives `δₐ = Δₐ`. -/
theorem delta_stationary (b : A → Γ) (h : Γ) (a' : V → Γ) (a : A) :
    delta α (fun a => b a - h) (fun i => h - a' i) a = stationaryDelta α b h a' a := by
  simp only [delta, stationaryDelta, smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul]
  rw [← Nat.cast_smul_eq_nsmul ℚ (∑ i, α a i) h]
  module

omit [LinearOrder Γ] [IsOrderedAddMonoid Γ] in
/-- `wick:eq:quarticthreshold`: for one quartic term in one variable,
`Δ = b + h - 2a`. -/
theorem stationaryDelta_quartic (b h a : Γ) :
    stationaryDelta (fun (_ : Unit) (_ : Unit) => 4) (fun _ => b) h (fun _ => a) () =
      b + h - 2 • a := by
  simp only [stationaryDelta, Finset.univ_unique, Finset.sum_singleton]
  rw [← Nat.cast_smul_eq_nsmul ℚ 4 a, ← Nat.cast_smul_eq_nsmul ℚ 2 a]
  module

/-- **Sharp multiscale power counting** (`wick:cor:stationary`, exact criterion). For the action
`𝒮(x) = ½ ∑ᵢ qᵢ xᵢ² + ∑ₐ uₐ x^{αᵃ}` with `qᵢ, uₐ, ħ` nonzero in `R((t^Γ))`, the normalized
Wick expansion has diagonal covariance `C_ii = ħ / qᵢ` and couplings `gₐ = -uₐ / ħ`. Its vacuum
Wick atom family is strongly summable iff `Δₐ > 0` for every `a`, where `h = v(ħ)`,
`aᵢ = v(qᵢ)` and `bₐ = v(uₐ)`. -/
theorem stronglySummable_stationary_iff [Nontrivial Γ] [CharZero R] {ħ : R⟦Γ⟧}
    {qc : V → R⟦Γ⟧} {u : A → R⟦Γ⟧} (hħ : ħ ≠ 0) (hq : ∀ i, qc i ≠ 0) (hu : ∀ a, u a ≠ 0) :
    StronglySummable
        (atom α Subtype.val (fun a => -u a / ħ) (matrixCov (diagonal fun i => ħ / qc i)) 0) ↔
      ∀ a, 0 < stationaryDelta α (fun a => (u a).order) ħ.order (fun i => (qc i).order) a := by
  have hg : ∀ a, -u a / ħ ≠ 0 := fun a => div_ne_zero (neg_ne_zero.2 (hu a)) hħ
  rw [stronglySummable_diagonal_iff α hg (fun i j h => diagonal_apply_ne _ h)
    fun i => by rw [diagonal_apply_eq]; exact div_ne_zero hħ (hq i)]
  have e1 : (fun a => (-u a / ħ).order) = fun a => (u a).order - ħ.order :=
    funext fun a => by rw [order_div_eq (neg_ne_zero.2 (hu a)) hħ, order_neg]
  have e2 : (fun i => ((diagonal fun i => ħ / qc i) i i).order) =
      fun i => ħ.order - (qc i).order :=
    funext fun i => by rw [diagonal_apply_eq, order_div_eq hħ (hq i)]
  rw [e1, e2]
  simp only [delta_stationary]

/-- `wick:cor:stationary`, observable clause: the same criterion governs every pairable monomial
insertion, that is, every sector `Q_β ≠ ∅`. -/
theorem stronglySummable_stationary_sector_iff [Nontrivial Γ] [CharZero R] {ħ : R⟦Γ⟧}
    {qc : V → R⟦Γ⟧} {u : A → R⟦Γ⟧} (hħ : ħ ≠ 0) (hq : ∀ i, qc i ≠ 0) (hu : ∀ a, u a ≠ 0)
    {β : V → ℕ}
    (hβ : (sector α (Subtype.val : MatrixEdge (diagonal fun i => ħ / qc i) → V × V) β).Nonempty) :
    StronglySummable
        (atom α Subtype.val (fun a => -u a / ħ) (matrixCov (diagonal fun i => ħ / qc i)) β) ↔
      ∀ a, 0 < stationaryDelta α (fun a => (u a).order) ħ.order (fun i => (qc i).order) a :=
  (stronglySummable_atom_iff_vacuum α Subtype.val
    (fun a => div_ne_zero (neg_ne_zero.2 (hu a)) hħ) (fun e => e.2.2) hβ).trans
    (stronglySummable_stationary_iff α hħ hq hu)

/-- `wick:cor:stationary` for the full normalized Wick expansion: its atom family is strongly
summable in every sector `Q_β`, `β ∈ ℕ^V`, iff `Δₐ > 0` for every `a`. -/
theorem stronglySummable_stationary_forall_iff [Nontrivial Γ] [CharZero R] {ħ : R⟦Γ⟧}
    {qc : V → R⟦Γ⟧} {u : A → R⟦Γ⟧} (hħ : ħ ≠ 0) (hq : ∀ i, qc i ≠ 0) (hu : ∀ a, u a ≠ 0) :
    (∀ β : V → ℕ, StronglySummable
        (atom α Subtype.val (fun a => -u a / ħ) (matrixCov (diagonal fun i => ħ / qc i)) β)) ↔
      ∀ a, 0 < stationaryDelta α (fun a => (u a).order) ħ.order (fun i => (qc i).order) a :=
  ((main_tfae_matrix α (fun a => div_ne_zero (neg_ne_zero.2 (hu a)) hħ)
    (diagonal fun i => ħ / qc i)).out 4 0).trans (stronglySummable_stationary_iff α hħ hq hu)

omit [Fintype V] [LinearOrder V] [Fintype A] in
/-- `wick:eq:quarticthreshold` as a summability criterion: for one quartic term `u x⁴` in one
variable with quadratic coefficient `q` and nonzero `q, u, ħ`, the normalized Wick expansion is
diagramwise strongly summable iff `b + h - 2a > 0`, where `b = v(u)`, `h = v(ħ)`, `a = v(q)`. -/
theorem stronglySummable_quartic_iff [Nontrivial Γ] [CharZero R] {ħ q u : R⟦Γ⟧} (hħ : ħ ≠ 0)
    (hq : q ≠ 0) (hu : u ≠ 0) :
    StronglySummable (atom (fun (_ : Unit) (_ : Unit) => 4) Subtype.val (fun _ => -u / ħ)
        (matrixCov (diagonal fun _ : Unit => ħ / q)) 0) ↔
      0 < u.order + ħ.order - 2 • q.order := by
  refine (stronglySummable_stationary_iff (fun (_ : Unit) (_ : Unit) => 4) (qc := fun _ => q)
    (u := fun _ => u) hħ (fun _ => hq) fun _ => hu).trans ?_
  rw [← stationaryDelta_quartic]
  exact ⟨fun h => h (), fun h _ => h⟩

end Stationary

end

end Surreal.WickPositive
