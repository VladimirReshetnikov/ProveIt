import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.RingTheory.Polynomial.Pochhammer
import Surreal.HahnSeries.EscapeChain
import Surreal.HahnSeries.UnitOrbitPolynomials

/-!
# Differential rigidity for strongly entire Hahn power series

This file formalizes Theorem A, `hol:main:ode`, of
`docs/surcomplex/holonomic-rigidity-for-entire-hahn-functions/article.tex`, together with the two
results its proof consists of, `hol:lem:drec` and `hol:prop:precursive`, and the definition of
D-finiteness in `hol:def:operators` (`hol:eq:dlinear`).

The exponent group `Γ` is an arbitrary linearly ordered abelian group: divisibility is not used,
and neither is `Γ ≠ 0` (`hol:conv:group`). The coefficient field `ℂ` of the source is generalized
to any field `K` of characteristic zero. The operator
`L = ∑_{r ≤ R} c_r(z) D_z^r` has coefficients `c_r ∈ K⟦Γ⟧[z]`, and `D_z` is
`PowerSeries.derivative`, which kills `K⟦Γ⟧`. The operator is nonzero in the sense of the source,
`(c_0, …, c_R) ≠ 0`. Strong summability, the strong domain and entireness are those of
`Surreal.Holonomic` (`hol:def:entire`).

* `linDiffOp c R f` is `L f`, and `IsDFinite` is `hol:eq:dlinear`.
* `hol:lem:drec` is proved in layers: the coefficient formula and the forward recurrence over an
  arbitrary commutative ring `A`, the nonvanishing clauses over any domain, and the `s = 0`
  clause over `K⟦Γ⟧` in characteristic zero. For any `m` bounding the degrees of the `c_r`,
  `coeff_linDiffOp` is `hol:eq:odecoeff`: the coefficient of `z^{u+m}` in `L f` is
  `∑_{j ≤ R+m} T_j(u) a_{u+j}`, where `recPoly c R m j` is
  `T_j(X) = Q_{j-m}(X + m) = ∑_{r + m = j + k} c_{r,k} (X + j)_r`. This is the source formula
  with `n = u + m` and the integer shift `s = j - m ∈ [-m, R]` made nonnegative.
  `exists_recPoly_ne_zero` is "at least one `Q_s` is nonzero", by the distinct-degree argument of
  the source; `recPoly_eq_zero_of_lt` shows that no shift beyond `R` is active.
  `exists_leastShift` gives the least active shift `j₀ = s₀ + m`, and `forward_recurrence` is
  `hol:eq:precursive`: with `P_j = forwardPoly c R m j₀ j`, that is
  `P_j(X) = T_{j₀+j}(X - j₀) = Q_{s₀+j}(X - s₀)`, every formal solution satisfies
  `∑_{j ≤ s} P_j(u) a_{u+j} = 0` for all `u ≥ j₀`, with `s = R + m - j₀ = R - s₀` and `P_0 ≠ 0`
  (`forwardPoly_zero_ne_zero`). `exists_forward_recurrence` packages this. The last sentence of
  `hol:lem:drec` (if `s = 0`, every formal solution is a polynomial) is
  `eventually_zero_of_leastShift_eq`, over `K⟦Γ⟧` with `CharZero K`, uniformly in the solution.
* `hol:prop:precursive` is `eq_zero_of_precursive`, with the explicit bound
  `recBound P s = max({0} ∪ {β(P_0) - β(P_j) : 1 ≤ j ≤ s, P_j ≠ 0})` of the source, where
  `polyVal P = β(P) = min_{p_k ≠ 0} v(p_k)`, and one threshold `N ≥ N₁` valid for every sequence
  satisfying the recurrence. It is derived from `hol:lem:integer`
  (`Surreal.HolonomicOrbit.exists_forall_ge_eval_natCast`) and `hol:cor:boundedcost`
  (`Surreal.Holonomic.eq_zero_of_boundedCost`). The case in which no `P_j` with `j ≥ 1` is
  nonzero, where every solution terminates without any evaluation hypothesis, is
  `eq_zero_of_precursive_of_forall_eq_zero`.
* `hol:main:ode`: `linDiffOp_uniform_obstruction` gives `B_L ≥ 0` and `N_L` depending only on
  `L` such that every formal solution of `L f = 0` that is strongly evaluable at one `x ≠ 0`
  with `v(x) ≤ -B_L` has `a_n = 0` for all `n ≥ N_L`; `exists_degree_lt_of_linDiffOp_eq_zero`
  states this as "`f` is a polynomial of degree `< N_L`". Both only assert that some `B_L` and
  `N_L` exist; `linDiffOp_uniform_obstruction_recBound` exposes the source's choice
  `B_L = B` of `hol:prop:precursive`, namely `recBound (forwardPoly c R m j₀) (R + m - j₀)` for a
  degree bound `m` and the least active shift `j₀`. The class equality
  `{f ∈ E : f is D-finite} = K⟦Γ⟧[z]` is `setOf_isStronglyEntire_and_isDFinite`, with the
  pointwise form `isStronglyEntire_and_isDFinite_iff`; the converse direction uses
  `coe_isStronglyEntire` and `coe_isDFinite`.

The divisible refinement `B_rec` of `hol:eq:refinedthreshold` (which needs `hol:cor:periodic`),
`hol:cor:algebraic`, `hol:cor:systems`, `hol:prop:inhomogeneous` and the example `hol:ex:airy`
are not formalized here.
-/

namespace Surreal.DifferentialRigidity

open scoped Polynomial
open scoped _root_.HahnSeries
open _root_.HahnSeries (single)
open Surreal.Holonomic (StronglySummable strongDomain IsStronglyEntire)

noncomputable section

section Operator

variable {A : Type*} [CommRing A]

/-- The linear differential operator `L = ∑_{r ≤ R} c_r(z) D_z^r` with polynomial coefficients
`c_r ∈ A[z]` (`hol:eq:operator`), applied to a formal power series. The derivative `D_z` kills
the constants `A`. -/
def linDiffOp (c : ℕ → A[X]) (R : ℕ) (f : PowerSeries A) : PowerSeries A :=
  ∑ r ∈ Finset.range (R + 1), (c r : PowerSeries A) * (⇑(PowerSeries.derivative A))^[r] f

/-- `hol:def:operators`: a formal power series is D-finite (`hol:eq:dlinear`, with polynomial
coefficients in `A[z]`) if it is annihilated by a linear differential operator
`∑_{r ≤ R} c_r(z) D_z^r` with `c_r ∈ A[z]` and `(c_0, …, c_R) ≠ 0`. For `A = K⟦Γ⟧` this is
D-finiteness over `K⟦Γ⟧(z)`, since rational coefficients can be cleared of denominators. -/
def IsDFinite (f : PowerSeries A) : Prop :=
  ∃ (R : ℕ) (c : ℕ → A[X]), (∃ r ≤ R, c r ≠ 0) ∧ linDiffOp c R f = 0

/-- The `n`th coefficient of `D_z^r f` is `(n + r)_r a_{n+r}`. -/
theorem coeff_iterate_derivative (f : PowerSeries A) (r n : ℕ) :
    PowerSeries.coeff n ((⇑(PowerSeries.derivative A))^[r] f) =
      ((n + r).descFactorial r : A) * PowerSeries.coeff (n + r) f := by
  induction r generalizing f with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply, ih, PowerSeries.coeff_derivative,
      show n + (r + 1) = n + r + 1 by omega, Nat.succ_descFactorial_succ]
    push_cast
    ring

/-- The coefficient of `z^{u+m}` in `p(z) g(z)` when `deg p ≤ m`. -/
theorem coeff_coe_mul_of_natDegree_le (p : A[X]) (g : PowerSeries A) {m : ℕ}
    (hp : p.natDegree ≤ m) (u : ℕ) :
    PowerSeries.coeff (u + m) ((p : PowerSeries A) * g) =
      ∑ k ∈ Finset.range (m + 1), p.coeff k * PowerSeries.coeff (u + m - k) g := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [Polynomial.coeff_coe]
  symm
  refine Finset.sum_subset (Finset.range_subset_range.mpr (by omega)) fun k _ hk => ?_
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by simp at hk; omega), zero_mul]

/-- The shifted falling factorial `(X + j)_r = (X + j)(X + j - 1) ⋯ (X + j - r + 1)`. -/
def fallShift (r j : ℕ) : A[X] :=
  (descPochhammer A r).comp (Polynomial.X + Polynomial.C (j : A))

/-- `(X + j)_r` evaluated at `u` is `(u + j)_r`. -/
theorem eval_fallShift (r j u : ℕ) :
    (fallShift r j : A[X]).eval (u : A) = ((u + j).descFactorial r : A) := by
  rw [fallShift, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_C, ← Nat.cast_add, descPochhammer_eval_eq_descFactorial]

/-- The recurrence coefficient `T_j(X) = Q_{j-m}(X + m) = ∑_{r + m = j + k} c_{r,k} (X + j)_r`
of `hol:eq:odecoeff`, for the operator of order `R` and a degree bound `m`. The source shift
`s = j - m` ranges over `[-m, R]`. -/
def recPoly (c : ℕ → A[X]) (R m j : ℕ) : A[X] :=
  ∑ p ∈ Finset.range (R + 1) ×ˢ Finset.range (m + 1),
    if p.1 + m = j + p.2 then Polynomial.C ((c p.1).coeff p.2) * fallShift p.1 j else 0

/-- `T_j(u) = ∑_{r + m = j + k} c_{r,k} (u + j)_r` at a natural number `u`. -/
theorem eval_recPoly (c : ℕ → A[X]) (R m j u : ℕ) :
    (recPoly c R m j).eval (u : A) = ∑ p ∈ Finset.range (R + 1) ×ˢ Finset.range (m + 1),
      if p.1 + m = j + p.2 then (c p.1).coeff p.2 * ((u + j).descFactorial p.1 : A) else 0 := by
  rw [recPoly, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun p _ => ?_
  split_ifs
  · rw [Polynomial.eval_mul, Polynomial.eval_C, eval_fallShift]
  · rw [Polynomial.eval_zero]

/-- No shift beyond `R` is active: `T_j = 0` for `j > R + m`. -/
theorem recPoly_eq_zero_of_lt (c : ℕ → A[X]) {R m j : ℕ} (hj : R + m < j) :
    recPoly c R m j = 0 := by
  refine Finset.sum_eq_zero fun p hp => ?_
  have hp1 := Finset.mem_range.mp (Finset.mem_product.mp hp).1
  have hne : ¬ (p.1 + m = j + p.2) := by omega
  rw [if_neg hne]

/-- `hol:lem:drec`, equation `hol:eq:odecoeff`: if `m` bounds the degrees of the coefficients
`c_0, …, c_R`, then for every `u` the coefficient of `z^{u+m}` in `L f` is
`∑_{j ≤ R+m} T_j(u) a_{u+j}`, which is `∑_{s=-m}^{R} Q_s(n) a_{n+s}` at `n = u + m`. -/
theorem coeff_linDiffOp (c : ℕ → A[X]) (R m : ℕ) (hm : ∀ r ≤ R, (c r).natDegree ≤ m)
    (f : PowerSeries A) (u : ℕ) :
    PowerSeries.coeff (u + m) (linDiffOp c R f) =
      ∑ j ∈ Finset.range (R + m + 1),
        (recPoly c R m j).eval (u : A) * PowerSeries.coeff (u + j) f := by
  have hL : PowerSeries.coeff (u + m) (linDiffOp c R f) =
      ∑ p ∈ Finset.range (R + 1) ×ˢ Finset.range (m + 1), (c p.1).coeff p.2 *
        (((u + (p.1 + m - p.2)).descFactorial p.1 : A) *
          PowerSeries.coeff (u + (p.1 + m - p.2)) f) := by
    rw [linDiffOp, map_sum, Finset.sum_product]
    refine Finset.sum_congr rfl fun r hr => ?_
    have hr' : r ≤ R := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
    rw [coeff_coe_mul_of_natDegree_le _ _ (hm r hr') u]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [coeff_iterate_derivative, show u + m - k + r = u + (r + m - k) by omega]
  rw [hL]
  simp only [eval_recPoly, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp1 := Finset.mem_range.mp (Finset.mem_product.mp hp).1
  have hp2 := Finset.mem_range.mp (Finset.mem_product.mp hp).2
  rw [Finset.sum_eq_single_of_mem (p.1 + m - p.2) (Finset.mem_range.mpr (by omega))]
  · have hpos : p.1 + m = p.1 + m - p.2 + p.2 := by omega
    rw [if_pos hpos, mul_assoc]
  · intro j _ hj
    have hneg : ¬ (p.1 + m = j + p.2) := by omega
    rw [if_neg hneg]

/-- The forward recurrence polynomial `P_j(X) = T_{j₀+j}(X - j₀)` of `hol:eq:precursive`,
where `j₀ = s₀ + m`; in the notation of the source, `P_j(X) = Q_{s₀+j}(X - s₀)`. -/
def forwardPoly (c : ℕ → A[X]) (R m j₀ j : ℕ) : A[X] :=
  (recPoly c R m (j₀ + j)).comp (Polynomial.X - Polynomial.C (j₀ : A))

/-- `P_j(w + j₀) = T_{j₀+j}(w)` at a natural number `w`. -/
theorem eval_forwardPoly (c : ℕ → A[X]) (R m j₀ j w : ℕ) :
    (forwardPoly c R m j₀ j).eval ((w + j₀ : ℕ) : A) = (recPoly c R m (j₀ + j)).eval (w : A) := by
  rw [forwardPoly, Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, Nat.cast_add, add_sub_cancel_right]

/-- `P_0 ≠ 0` as soon as the shift `j₀` is active. -/
theorem forwardPoly_zero_ne_zero (c : ℕ → A[X]) (R m j₀ : ℕ) (h : recPoly c R m j₀ ≠ 0) :
    forwardPoly c R m j₀ 0 ≠ 0 := by
  rw [forwardPoly, add_zero, sub_eq_add_neg, ← Polynomial.C_neg]
  exact Polynomial.comp_X_add_C_ne_zero_iff.mpr h

/-- `hol:lem:drec`, equation `hol:eq:precursive`: if no shift below `j₀` is active, every formal
solution of `L f = 0` satisfies `∑_{j=0}^{s} P_j(u) a_{u+j} = 0` for all `u ≥ j₀`, with
`s = R + m - j₀` and `P_j = forwardPoly c R m j₀ j`. -/
theorem forward_recurrence (c : ℕ → A[X]) (R m : ℕ) (hm : ∀ r ≤ R, (c r).natDegree ≤ m)
    {j₀ : ℕ} (hle : j₀ ≤ R + m) (hlt : ∀ j < j₀, recPoly c R m j = 0) {f : PowerSeries A}
    (hf : linDiffOp c R f = 0) {u : ℕ} (hu : j₀ ≤ u) :
    ∑ j ∈ Finset.range (R + m - j₀ + 1),
      (forwardPoly c R m j₀ j).eval (u : A) * PowerSeries.coeff (u + j) f = 0 := by
  obtain ⟨w, rfl⟩ : ∃ w, u = w + j₀ := ⟨u - j₀, by omega⟩
  have h := coeff_linDiffOp c R m hm f w
  rw [hf, map_zero, show R + m + 1 = j₀ + (R + m - j₀ + 1) by omega,
    Finset.sum_range_add] at h
  have h0 : ∑ j ∈ Finset.range j₀,
      (recPoly c R m j).eval (w : A) * PowerSeries.coeff (w + j) f = 0 :=
    Finset.sum_eq_zero fun j hj => by
      rw [hlt j (Finset.mem_range.mp hj), Polynomial.eval_zero, zero_mul]
  rw [h0, zero_add] at h
  refine (Finset.sum_congr rfl fun j _ => ?_).trans h.symm
  rw [eval_forwardPoly, add_assoc]

/-- A formal solution all of whose coefficients from `N` on vanish is the polynomial
`trunc N f`, of degree less than `N`. -/
theorem eq_coe_trunc_of_coeff_eq_zero {f : PowerSeries A} {N : ℕ}
    (h : ∀ n, N ≤ n → PowerSeries.coeff n f = 0) :
    f = (PowerSeries.trunc N f : PowerSeries A) := by
  ext n
  rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
  split_ifs with hn
  · rfl
  · exact h n (not_lt.mp hn)

/-- `D_z^r` of a polynomial is the polynomial `r`th derivative. -/
theorem iterate_derivative_coe (p : A[X]) (r : ℕ) :
    (⇑(PowerSeries.derivative A))^[r] (p : PowerSeries A) =
      (((⇑Polynomial.derivative)^[r] p : A[X]) : PowerSeries A) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply', ih, PowerSeries.derivative_coe,
      ← Function.iterate_succ_apply' (⇑Polynomial.derivative)]

/-- The converse half of `hol:main:ode`, D-finite part: a polynomial is annihilated by a
sufficiently high derivative. -/
theorem coe_isDFinite [Nontrivial A] (p : A[X]) : IsDFinite (p : PowerSeries A) := by
  refine ⟨p.natDegree + 1, fun r => if r = p.natDegree + 1 then 1 else 0,
    ⟨p.natDegree + 1, le_rfl, by simp⟩, ?_⟩
  rw [linDiffOp, Finset.sum_eq_single_of_mem (p.natDegree + 1) (Finset.self_mem_range_succ _)]
  · rw [if_pos rfl, Polynomial.coe_one, one_mul, iterate_derivative_coe,
      Polynomial.iterate_derivative_eq_zero (Nat.lt_succ_self _), Polynomial.coe_zero]
  · intro r _ hr
    rw [if_neg hr, Polynomial.coe_zero, zero_mul]

section Domain

variable [IsDomain A]

/-- Over a domain, `(X + j)_r` has degree exactly `r`. -/
theorem natDegree_fallShift (r j : ℕ) : (fallShift r j : A[X]).natDegree = r := by
  rw [fallShift, Polynomial.natDegree_comp, descPochhammer_natDegree,
    Polynomial.natDegree_X_add_C, mul_one]

/-- `(X + j)_r` is monic. -/
theorem monic_fallShift (r j : ℕ) : (fallShift r j : A[X]).Monic :=
  (monic_descPochhammer A r).comp_X_add_C _

/-- `hol:lem:drec`: at least one `Q_s` is nonzero. For the shift `j` of a nonzero coefficient,
the terms of `T_j` have pairwise distinct degrees, so the one of largest degree survives. -/
theorem exists_recPoly_ne_zero (c : ℕ → A[X]) (R m : ℕ) (hm : ∀ r ≤ R, (c r).natDegree ≤ m)
    (hc : ∃ r ≤ R, c r ≠ 0) : ∃ j ≤ R + m, recPoly c R m j ≠ 0 := by
  classical
  obtain ⟨r₁, hr₁, hc₁⟩ := hc
  obtain ⟨k₁, hk₁, hdeg⟩ : ∃ k, (c r₁).coeff k ≠ 0 ∧ k ≤ m :=
    ⟨_, Polynomial.leadingCoeff_ne_zero.mpr hc₁, hm r₁ hr₁⟩
  refine ⟨r₁ + m - k₁, by omega, ?_⟩
  let S := (Finset.range (R + 1) ×ˢ Finset.range (m + 1)).filter
    fun p => p.1 + m = r₁ + m - k₁ + p.2 ∧ (c p.1).coeff p.2 ≠ 0
  have hS : (r₁, k₁) ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    exact ⟨⟨by omega, by omega⟩, by omega, hk₁⟩
  obtain ⟨q, hqS, hmax⟩ := S.exists_max_image Prod.fst ⟨_, hS⟩
  obtain ⟨hq, hqj, hqc⟩ : q ∈ Finset.range (R + 1) ×ˢ Finset.range (m + 1) ∧
      q.1 + m = r₁ + m - k₁ + q.2 ∧ (c q.1).coeff q.2 ≠ 0 := by
    simpa only [S, Finset.mem_filter, and_assoc] using hqS
  intro h0
  apply hqc
  have hone : (fallShift q.1 (r₁ + m - k₁) : A[X]).coeff q.1 = 1 := by
    have := (monic_fallShift (A := A) q.1 (r₁ + m - k₁)).coeff_natDegree
    rwa [natDegree_fallShift] at this
  have hcoeff := congrArg (fun P => P.coeff q.1) h0
  simp only [recPoly, Polynomial.finsetSum_coeff, Polynomial.coeff_zero] at hcoeff
  rw [Finset.sum_eq_single_of_mem q hq] at hcoeff
  · rwa [if_pos hqj, Polynomial.coeff_C_mul, hone, mul_one] at hcoeff
  · intro p hp hne
    split_ifs with hcond
    · rw [Polynomial.coeff_C_mul]
      by_cases hcp : (c p.1).coeff p.2 = 0
      · rw [hcp, zero_mul]
      · have hle := hmax p (Finset.mem_filter.mpr ⟨hp, hcond, hcp⟩)
        rcases lt_or_eq_of_le hle with hlt | heq
        · have hz : (fallShift p.1 (r₁ + m - k₁) : A[X]).coeff q.1 = 0 :=
            Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [natDegree_fallShift]; exact hlt)
          rw [hz, mul_zero]
        · exact absurd (Prod.ext heq (by omega)) hne
    · exact Polynomial.coeff_zero _

/-- `hol:lem:drec`: the least active shift `j₀ = s₀ + m` exists, lies in `[0, R + m]`, and every
smaller shift is inactive. -/
theorem exists_leastShift (c : ℕ → A[X]) (R m : ℕ) (hm : ∀ r ≤ R, (c r).natDegree ≤ m)
    (hc : ∃ r ≤ R, c r ≠ 0) :
    ∃ j₀ ≤ R + m, recPoly c R m j₀ ≠ 0 ∧ ∀ j < j₀, recPoly c R m j = 0 := by
  classical
  obtain ⟨j, hjle, hj⟩ := exists_recPoly_ne_zero c R m hm hc
  have h : ∃ j, recPoly c R m j ≠ 0 := ⟨j, hj⟩
  exact ⟨Nat.find h, (Nat.find_min' h hj).trans hjle, Nat.find_spec h,
    fun i hi => not_not.mp (Nat.find_min h hi)⟩

/-- `hol:lem:drec`, packaged: a nonzero operator yields a forward recurrence
`∑_{j=0}^{s} P_j(u) a_{u+j} = 0`, valid for all `u ≥ u₀` and every formal solution, with
`P_0 ≠ 0`. -/
theorem exists_forward_recurrence (c : ℕ → A[X]) (R : ℕ) (hc : ∃ r ≤ R, c r ≠ 0) :
    ∃ (s u₀ : ℕ) (P : ℕ → A[X]), P 0 ≠ 0 ∧ ∀ f : PowerSeries A, linDiffOp c R f = 0 →
      ∀ u, u₀ ≤ u →
        ∑ j ∈ Finset.range (s + 1), (P j).eval (u : A) * PowerSeries.coeff (u + j) f = 0 := by
  obtain ⟨m, hm⟩ : ∃ m, ∀ r ≤ R, (c r).natDegree ≤ m :=
    ⟨(Finset.range (R + 1)).sup fun r => (c r).natDegree, fun r hr =>
      Finset.le_sup (f := fun r => (c r).natDegree) (Finset.mem_range.mpr (by omega))⟩
  obtain ⟨j₀, hle, hne, hlt⟩ := exists_leastShift c R m hm hc
  exact ⟨R + m - j₀, j₀, forwardPoly c R m j₀, forwardPoly_zero_ne_zero c R m j₀ hne,
    fun f hf u hu => forward_recurrence c R m hm hle hlt hf hu⟩

end Domain

end Operator

/-- Splitting off the leading term of the recurrence: `∑_{j=0}^{s} g_j = g_0 + ∑_{j=1}^{s} g_j`. -/
theorem sum_range_succ_eq_add_sum_Icc {M : Type*} [AddCommMonoid M] (g : ℕ → M) (s : ℕ) :
    ∑ j ∈ Finset.range (s + 1), g j = g 0 + ∑ j ∈ Finset.Icc 1 s, g j := by
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega), zero_add,
    Finset.Ico_add_one_right_eq_Icc]

section Hahn

variable {Γ K : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [Field K]

open Classical in
/-- `β(P) = min_{p_k ≠ 0} v(p_k)` for a nonzero polynomial with Hahn coefficients; the junk value
at `P = 0` is `0` and is never used. -/
def polyVal (P : K⟦Γ⟧[X]) : Γ :=
  if h : P = 0 then 0
  else P.support.inf' (Polynomial.support_nonempty.mpr h) fun k => (P.coeff k).order

/-- For `P ≠ 0`, `β(P)` is the least order of a nonzero coefficient of `P`. -/
theorem polyVal_of_ne_zero {P : K⟦Γ⟧[X]} (hP : P ≠ 0) :
    polyVal P = P.support.inf' (Polynomial.support_nonempty.mpr hP)
      fun k => (P.coeff k).order :=
  dif_neg hP

open Classical in
/-- The bound `B = max({0} ∪ {β_0 - β_j : 1 ≤ j ≤ s, P_j ≠ 0})` of `hol:prop:precursive`. -/
def recBound (P : ℕ → K⟦Γ⟧[X]) (s : ℕ) : Γ :=
  ((Finset.Icc 1 s).filter fun j => P j ≠ 0).fold max 0
    fun j => polyVal (P 0) - polyVal (P j)

/-- The bound of `hol:prop:precursive` satisfies `B ≥ 0`. -/
theorem recBound_nonneg (P : ℕ → K⟦Γ⟧[X]) (s : ℕ) : 0 ≤ recBound P s := by
  unfold recBound
  exact (Finset.le_fold_max 0).mpr (Or.inl le_rfl)

/-- `β_0 - β_j ≤ B` for every nonzero `P_j` with `1 ≤ j ≤ s`. -/
theorem sub_le_recBound {P : ℕ → K⟦Γ⟧[X]} {s j : ℕ} (hj : j ∈ Finset.Icc 1 s)
    (hPj : P j ≠ 0) : polyVal (P 0) - polyVal (P j) ≤ recBound P s := by
  classical
  unfold recBound
  exact (Finset.le_fold_max _).mpr (Or.inr ⟨j, Finset.mem_filter.mpr ⟨hj, hPj⟩, le_rfl⟩)

/-- `hol:lem:integer` for finitely many polynomials at once: beyond one threshold, every nonzero
`P_j` with `j ≤ s` satisfies `P_j(n) ≠ 0` and `v(P_j(n)) = β(P_j)`. -/
theorem exists_forall_ge_eval_order [CharZero K] (P : ℕ → K⟦Γ⟧[X]) (s : ℕ) :
    ∃ N : ℕ, ∀ n, N ≤ n → ∀ j ≤ s, P j ≠ 0 →
      (P j).eval (n : K⟦Γ⟧) ≠ 0 ∧ ((P j).eval (n : K⟦Γ⟧)).order = polyVal (P j) := by
  have h : ∀ j, ∃ N : ℕ, P j ≠ 0 → ∀ n, N ≤ n →
      (P j).eval (n : K⟦Γ⟧) ≠ 0 ∧ ((P j).eval (n : K⟦Γ⟧)).order = polyVal (P j) := by
    intro j
    by_cases hj : P j = 0
    · exact ⟨0, fun h => absurd hj h⟩
    · obtain ⟨N, hN⟩ := HolonomicOrbit.exists_forall_ge_eval_natCast (P j) hj
      exact ⟨N, fun _ n hn => by rw [polyVal_of_ne_zero hj]; exact hN n hn⟩
  choose Nf hNf using h
  refine ⟨(Finset.range (s + 1)).sup Nf, fun n hn j hj hPj => hNf j hPj n (le_trans ?_ hn)⟩
  exact Finset.le_sup (Finset.mem_range.mpr (by omega))

/-- `hol:prop:precursive`: suppose `(a_n)` satisfies `∑_{j=0}^{s} P_j(n) a_{n+j} = 0` for all
`n ≥ N₁`, with `P_0 ≠ 0`, and let `B = recBound P s ≥ 0`. There is `N ≥ N₁`, depending only on
`P`, `s` and `N₁`, such that for every `x ≠ 0` with `v(x) ≤ -B`, strong summability of
`(a_n x^n)` forces `a_n = 0` for all `n ≥ N`. -/
theorem eq_zero_of_precursive [CharZero K] (P : ℕ → K⟦Γ⟧[X]) (s N₁ : ℕ) (hP0 : P 0 ≠ 0) :
    ∃ N, N₁ ≤ N ∧ ∀ a : ℕ → K⟦Γ⟧,
      (∀ n, N₁ ≤ n → ∑ j ∈ Finset.range (s + 1), (P j).eval (n : K⟦Γ⟧) * a (n + j) = 0) →
      ∀ x : K⟦Γ⟧, x ≠ 0 → x.order ≤ -recBound P s →
        StronglySummable (fun n => a n * x ^ n) → ∀ n, N ≤ n → a n = 0 := by
  obtain ⟨N₂, hN₂⟩ := exists_forall_ge_eval_order P s
  refine ⟨max N₁ N₂, le_max_left _ _, fun a ha x hx hxB hsum => ?_⟩
  have hB0 := recBound_nonneg P s
  refine Holonomic.eq_zero_of_boundedCost (c := fun j n => (P j).eval (n : K⟦Γ⟧)) (s := s)
    (fun n hn => ?_) (fun n hn => (hN₂ n (le_of_max_le_right hn) 0 (Nat.zero_le _) hP0).1)
    (recBound P s) (fun n hn j hj hcj => ?_) hx (by rwa [max_eq_left hB0]) hsum
  · have := ha n (le_of_max_le_left hn)
    rw [sum_range_succ_eq_add_sum_Icc] at this
    simpa only [add_zero] using this
  · have hPj : P j ≠ 0 := fun h => hcj (by simp only [h, Polynomial.eval_zero])
    have hjs : j ≤ s := (Finset.mem_Icc.mp hj).2
    have hN : N₂ ≤ n := le_of_max_le_right hn
    rw [(hN₂ n hN 0 (Nat.zero_le _) hP0).2, (hN₂ n hN j hjs hPj).2]
    exact sub_le_recBound hj hPj

/-- `hol:prop:precursive`, degenerate case: if every `P_j` with `j ≥ 1` vanishes, the recurrence
forces `a_n = 0` for all `n ≥ N` without any evaluation hypothesis. The threshold `N ≥ N₁` is
produced here on its own; the statement does not identify it with the `N` of
`eq_zero_of_precursive`, although the maximum of the two serves both clauses. -/
theorem eq_zero_of_precursive_of_forall_eq_zero [CharZero K] (P : ℕ → K⟦Γ⟧[X]) (s N₁ : ℕ)
    (hP0 : P 0 ≠ 0) (hP : ∀ j ∈ Finset.Icc 1 s, P j = 0) :
    ∃ N, N₁ ≤ N ∧ ∀ a : ℕ → K⟦Γ⟧,
      (∀ n, N₁ ≤ n → ∑ j ∈ Finset.range (s + 1), (P j).eval (n : K⟦Γ⟧) * a (n + j) = 0) →
      ∀ n, N ≤ n → a n = 0 := by
  obtain ⟨N₂, hN₂⟩ := exists_forall_ge_eval_order P s
  refine ⟨max N₁ N₂, le_max_left _ _, fun a ha n hn => ?_⟩
  have h := ha n (le_of_max_le_left hn)
  have hrest : ∑ j ∈ Finset.Icc 1 s, (P j).eval (n : K⟦Γ⟧) * a (n + j) = 0 :=
    Finset.sum_eq_zero fun j hj => by rw [hP j hj, Polynomial.eval_zero, zero_mul]
  rw [sum_range_succ_eq_add_sum_Icc, hrest, add_zero, add_zero] at h
  exact (mul_eq_zero.mp h).resolve_left (hN₂ n (le_of_max_le_right hn) 0 (Nat.zero_le _) hP0).1

/-- The last sentence of `hol:lem:drec`: if the least active shift is `j₀ = R + m` (so `s = 0`),
every formal solution of `L f = 0` is a polynomial, with one degree bound for all solutions: its
coefficients vanish from one `N` on (see `eq_coe_trunc_of_coeff_eq_zero`). -/
theorem eventually_zero_of_leastShift_eq [CharZero K] (c : ℕ → K⟦Γ⟧[X]) (R m : ℕ)
    (hm : ∀ r ≤ R, (c r).natDegree ≤ m) {j₀ : ℕ} (hne : recPoly c R m j₀ ≠ 0)
    (hlt : ∀ j < j₀, recPoly c R m j = 0) (hs : j₀ = R + m) :
    ∃ N, ∀ f : PowerSeries K⟦Γ⟧, linDiffOp c R f = 0 →
      ∀ n, N ≤ n → PowerSeries.coeff n f = 0 := by
  obtain ⟨N, -, hN⟩ := eq_zero_of_precursive_of_forall_eq_zero (forwardPoly c R m j₀)
    (R + m - j₀) j₀ (forwardPoly_zero_ne_zero c R m j₀ hne)
    (fun j hj => absurd (Finset.mem_Icc.mp hj) (by omega))
  exact ⟨N, fun f hf => hN (fun n => PowerSeries.coeff n f)
    fun n hn => forward_recurrence c R m hm hs.le hlt hf hn⟩

/-- `hol:main:ode`, uniform exterior obstruction: for a nonzero operator `L` with coefficients
in `K⟦Γ⟧[z]` there are `B_L ≥ 0` and `N_L`, depending only on `L`, such that every formal
solution of `L f = 0` that is strongly evaluable at one `x ≠ 0` with `v(x) ≤ -B_L` has
`a_n = 0` for all `n ≥ N_L`. The statement only asserts that `B_L` and `N_L` exist; the explicit
choice of the source is `linDiffOp_uniform_obstruction_recBound`. -/
theorem linDiffOp_uniform_obstruction [CharZero K] (c : ℕ → K⟦Γ⟧[X]) (R : ℕ)
    (hc : ∃ r ≤ R, c r ≠ 0) :
    ∃ B : Γ, 0 ≤ B ∧ ∃ N : ℕ, ∀ f : PowerSeries K⟦Γ⟧, linDiffOp c R f = 0 →
      ∀ x : K⟦Γ⟧, x ≠ 0 → x.order ≤ -B → x ∈ strongDomain f →
        ∀ n, N ≤ n → PowerSeries.coeff n f = 0 := by
  obtain ⟨s, u₀, P, hP0, hrec⟩ := exists_forward_recurrence c R hc
  obtain ⟨N, -, hN⟩ := eq_zero_of_precursive P s u₀ hP0
  exact ⟨recBound P s, recBound_nonneg P s, N, fun f hf x hx hxB hxf =>
    hN (fun n => PowerSeries.coeff n f) (hrec f hf) x hx hxB hxf⟩

/-- `hol:main:ode` with the source's threshold: for a bound `m` on the degrees of the `c_r` and
an active shift `j₀` below which every shift is inactive (the least active shift, which exists by
`exists_leastShift` when `L ≠ 0`), one may take `B_L = B` of `hol:prop:precursive` for the
forward recurrence of `hol:lem:drec`, that is `B_L = recBound (forwardPoly c R m j₀) (R + m - j₀)`
(which is `≥ 0` by `recBound_nonneg`). There is `N_L` such that every formal solution of
`L f = 0` strongly evaluable at one `x ≠ 0` with `v(x) ≤ -B_L` has `a_n = 0` for all
`n ≥ N_L`. -/
theorem linDiffOp_uniform_obstruction_recBound [CharZero K] (c : ℕ → K⟦Γ⟧[X]) (R m : ℕ)
    (hm : ∀ r ≤ R, (c r).natDegree ≤ m) {j₀ : ℕ} (hne : recPoly c R m j₀ ≠ 0)
    (hlt : ∀ j < j₀, recPoly c R m j = 0) :
    ∃ N : ℕ, ∀ f : PowerSeries K⟦Γ⟧, linDiffOp c R f = 0 →
      ∀ x : K⟦Γ⟧, x ≠ 0 → x.order ≤ -recBound (forwardPoly c R m j₀) (R + m - j₀) →
        x ∈ strongDomain f → ∀ n, N ≤ n → PowerSeries.coeff n f = 0 := by
  have hle : j₀ ≤ R + m := not_lt.mp fun h => hne (recPoly_eq_zero_of_lt c h)
  obtain ⟨N, -, hN⟩ := eq_zero_of_precursive (forwardPoly c R m j₀) (R + m - j₀) j₀
    (forwardPoly_zero_ne_zero c R m j₀ hne)
  exact ⟨N, fun f hf x hx hxB hxf => hN (fun n => PowerSeries.coeff n f)
    (fun n hn => forward_recurrence c R m hm hle hlt hf hn) x hx hxB hxf⟩

/-- `hol:main:ode`, first sentence as stated: every formal solution strongly evaluable at one
`x ≠ 0` with `v(x) ≤ -B_L` is a polynomial of degree less than `N_L`. -/
theorem exists_degree_lt_of_linDiffOp_eq_zero [CharZero K] (c : ℕ → K⟦Γ⟧[X]) (R : ℕ)
    (hc : ∃ r ≤ R, c r ≠ 0) :
    ∃ B : Γ, 0 ≤ B ∧ ∃ N : ℕ, ∀ f : PowerSeries K⟦Γ⟧, linDiffOp c R f = 0 →
      (∃ x : K⟦Γ⟧, x ≠ 0 ∧ x.order ≤ -B ∧ x ∈ strongDomain f) →
        ∃ p : K⟦Γ⟧[X], p.degree < N ∧ f = p := by
  obtain ⟨B, hB0, N, hN⟩ := linDiffOp_uniform_obstruction c R hc
  exact ⟨B, hB0, N, fun f hf ⟨x, hx, hxB, hxf⟩ => ⟨PowerSeries.trunc N f,
    PowerSeries.degree_trunc_lt f N, eq_coe_trunc_of_coeff_eq_zero (hN f hf x hx hxB hxf)⟩⟩

/-- The converse half of `hol:main:ode`, entire part: a polynomial is strongly evaluable
everywhere, since its evaluation family has only finitely many nonzero members. -/
theorem coe_isStronglyEntire (p : K⟦Γ⟧[X]) : IsStronglyEntire (p : PowerSeries K⟦Γ⟧) := by
  refine Set.eq_univ_of_forall fun x => ?_
  show ∃ s : _root_.HahnSeries.SummableFamily Γ K ℕ,
    ∀ n, s n = PowerSeries.coeff n (p : PowerSeries K⟦Γ⟧) * x ^ n
  refine ⟨_root_.HahnSeries.SummableFamily.ofFinsupp
    (Finsupp.onFinset p.support (fun n => p.coeff n * x ^ n) fun n hn =>
      Polynomial.mem_support_iff.mpr (left_ne_zero_of_mul hn)), fun n => ?_⟩
  simp [Polynomial.coeff_coe]

/-- `hol:main:ode`, class equality, pointwise: a formal power series is strongly entire and
D-finite over `K⟦Γ⟧(z)` exactly when it is a polynomial. -/
theorem isStronglyEntire_and_isDFinite_iff [CharZero K] (f : PowerSeries K⟦Γ⟧) :
    IsStronglyEntire f ∧ IsDFinite f ↔ ∃ p : K⟦Γ⟧[X], f = p := by
  constructor
  · rintro ⟨hE, R, c, hc, hf⟩
    obtain ⟨B, hB0, N, hN⟩ := linDiffOp_uniform_obstruction c R hc
    obtain ⟨hx0, hxB⟩ := Holonomic.single_neg_witness (R := K) B B (by rw [max_eq_left hB0])
    have hE' : strongDomain f = Set.univ := hE
    have hmem : single (-B) (1 : K) ∈ strongDomain f := by
      rw [hE']
      exact Set.mem_univ _
    rw [max_eq_left hB0] at hxB
    exact ⟨_, eq_coe_trunc_of_coeff_eq_zero (hN f hf _ hx0 hxB hmem)⟩
  · rintro ⟨p, rfl⟩
    exact ⟨coe_isStronglyEntire p, coe_isDFinite p⟩

/-- `hol:main:ode`, class equality: `{f ∈ E : f is D-finite over K⟦Γ⟧(z)} = K⟦Γ⟧[z]`. -/
theorem setOf_isStronglyEntire_and_isDFinite [CharZero K] :
    {f : PowerSeries K⟦Γ⟧ | IsStronglyEntire f ∧ IsDFinite f} =
      Set.range fun p : K⟦Γ⟧[X] => (p : PowerSeries K⟦Γ⟧) := by
  ext f
  rw [Set.mem_setOf_eq, isStronglyEntire_and_isDFinite_iff, Set.mem_range]
  exact ⟨fun ⟨p, hp⟩ => ⟨p, hp.symm⟩, fun ⟨p, hp⟩ => ⟨p, hp.symm⟩⟩

end Hahn

end

end Surreal.DifferentialRigidity
