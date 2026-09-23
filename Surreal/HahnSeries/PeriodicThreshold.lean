import Mathlib.GroupTheory.Divisible
import Surreal.HahnSeries.DifferentialRigidity
import Surreal.HahnSeries.TorsionCovariance
import Surreal.HahnSeries.UnitOrbitPolynomials

/-!
# The refined periodic threshold and faithfulness of constant evaluation

This file formalizes two results of
`docs/surcomplex/holonomic-rigidity-for-entire-hahn-functions/article.tex`: the refined
periodic threshold `hol:cor:periodic`, with its constant `hol:eq:radiusbound` and its excluded
region `hol:eq:excludedball`, and the faithfulness of evaluation at ordinary constants
`hol:prop:faithful`. The period-one case also gives the divisible refinement
`hol:eq:refinedthreshold` of `hol:prop:precursive`.

Strong summability, the strong domain `Dom(f)` and strong entireness are those of
`Surreal.Holonomic` (`hol:def:entire`, in `EscapeChain.lean`). The valuation `v` is
`HahnSeries.order`, with junk value `order 0 = 0`; every order in a hypothesis or conclusion
below is that of an element assumed nonzero, or sits next to the alternative `x = 0`.

## The refined periodic threshold

The exponent group `Γ` is any linearly ordered abelian group and the coefficient ring any
semiring without zero divisors (the source has `ℂ`). The recurrence is
`hol:eq:generalrecurrence`, `c₀(n) a_n + ∑_{j=1}^s c_j(n) a_{n+j} = 0` for `n ≥ N` with
`c₀(n) ≠ 0`, encoded by `c : ℕ → ℕ → R⟦Γ⟧` as in `EscapeChain.lean`.

* `eq_zero_of_periodicCost` is the division-free core. If `v(c_j(n)) = α_{j, n mod m}`
  whenever `n ≥ N` and `c_j(n) ≠ 0` (`m ≥ 1`), and `α_{0,r} - α_{j,r} ≤ j B` for every residue
  `r < m` and every active forward slot `j` (one with `c_j(n) ≠ 0` for some `n ≥ N`), then
  strong summability of `(a_n x^n)` at any `x ≠ 0` with `v(x) ≤ -B` forces `a_n = 0` for all
  `n ≥ N`. Slots are not required to be identically zero or nowhere zero here; the source's
  dichotomy is needed only to read `α` off the recurrence.
* Under `[DivisibleBy Γ ℕ]`, `recThreshold c α s N m` is `B_rec` of `hol:eq:radiusbound`: the
  maximum of `(α_{0,r} - α_{j,r}) / j` over residues `r < m` and active forward slots
  `j ∈ activeSlots c s N`, and `0` if there is no active forward slot
  (`recThreshold_of_activeSlots_eq_empty`). With `α` free, a class on which an active slot
  vanishes still contributes its value `α_{j,r}`; this is harmless for the conclusions and
  cannot occur under the source's slot dichotomy. `sub_le_nsmul_recThreshold` is the step
  `j B_rec ≥ α_{0,r} - α_{j,r}` of the proof, and `eq_zero_of_stronglySummable_recThreshold`
  is the main clause of `hol:cor:periodic`. `eq_zero_of_activeSlots_eq_empty` is the clause
  for no active forward slot: then `a_n = 0` for all `n ≥ N` with no evaluation hypothesis and
  without divisibility. `strongDomain_subset_recThreshold` is `hol:eq:excludedball` for every
  solution with a nonzero coefficient `a_{n₀}`, `n₀ ≥ N`, and
  `exists_coeff_ne_zero_of_not_polynomial` supplies such a coefficient for every
  nonpolynomial series.
* The source's hypothesis on the slots (each slot `j ∈ {0, …, s}` is identically zero for
  `n ≥ N`, or nonzero for all `n ≥ N` with `v(c_j(n + m)) = v(c_j(n))`) is the hypothesis
  `hslot` of `eq_zero_of_stronglySummable_periodicThreshold`,
  `strongDomain_subset_periodicThreshold` and
  `strongDomain_subset_periodicThreshold_of_not_polynomial`. There `α_{j,r}` is
  `slotValuation c N m j r`, the valuation at the representative `N m + r ≥ N` of the residue
  class of `r`; `order_eq_slotValuation_of_slot` shows that it is the valuation on the whole
  class, and `periodicThreshold c s N m` is the resulting `B_rec`.
* Application, a prerequisite for the divisible clause of `hol:cor:unitrigid`: for recurrence
  coefficients `c_j(n) = P_j(q^n)` over a field of characteristic zero, with `v(q) = 0`, `q` of
  infinite multiplicative order and `P₀ ≠ 0`, `hol:thm:unitorbit` (`UnitOrbitPolynomials.lean`)
  gives the slot hypothesis beyond some `N`, with the common period `unitPeriod q`, that is
  `orderOf res(q)` when `res(q)` is a root of unity and `1` otherwise
  (`exists_forall_ge_unitOrbit`). This yields `eq_zero_of_stronglySummable_unitOrbit` and
  `strongDomain_subset_unitOrbit`. The recurrence `hol:eq:qrec` of `hol:lem:qrec` is not
  derived here, so `hol:cor:unitrigid` itself remains pending.
* Period `m = 1`: `refinedThreshold P s` is `B_rec` of `hol:eq:refinedthreshold` for a
  P-recursive recurrence `∑_{j=0}^s P_j(n) a_{n+j} = 0` (`hol:eq:precursive`), and
  `eq_zero_of_precursive_refinedThreshold` is the divisible refinement of
  `hol:prop:precursive`, over a field of characteristic zero, with one threshold `N ≥ N₁` for
  every solution. It combines `hol:lem:integer` (through
  `DifferentialRigidity.exists_forall_ge_eval_order`) with `eq_zero_of_periodicCost`.

## Faithfulness of evaluation at constants

Here `Γ` is any ordered cancellative commutative monoid and the coefficient ring `R` is
commutative; the vanishing statements need an integral domain. A constant `c ∈ R` is the Hahn
series `C c`, and the strong value `f(c)` is `s.hsum` for any summable family `s` whose terms
are `a_n (C c)^n` (by `SummableFamily.coeff_hsum` the sum depends only on the terms).

* `finite_support_coeff_of_one_mem`: strong evaluability at `1` makes every coefficient family
  `n ↦ (a_n)_γ` finitely supported, so `coeffPolyAt f γ`, the polynomial
  `P_γ(T) = ∑_n (a_n)_γ T^n` of the proof, has exactly these coefficients (`coeff_coeffPolyAt`),
  and its value at `c` is the coefficient of `t^γ` in `f(c)`
  (`coeff_hsum_eq_eval_coeffPolyAt`). `C_mem_strongDomain`: `1 ∈ Dom(f)` gives `c ∈ Dom(f)` for
  every constant `c`.
* `eq_zero_of_hsum_const_eq_zero` is the first sentence of `hol:prop:faithful`, assuming only
  `1 ∈ Dom(f)` and vanishing at the constants of an infinite set;
  `eq_zero_of_isStronglyEntire` is the statement for `f ∈ E` over any integral domain, and
  `eq_zero_of_isStronglyEntire_complex` the source's statement over `ℂ((t^Γ))`.
* The second sentence is `sum_mul_eq_zero_of_eval_const`, over any field `K` and ordered
  abelian group `Γ`, for a linear expression `∑_r (p_r / q_r) g_r` with finitely many series
  `g_r` and rational coefficients (`p_r, q_r ∈ K⟦Γ⟧[z]`, `q_r ≠ 0`): if its value vanishes at
  every constant of an infinite set at which all denominators are nonzero, then the cleared
  identity `∑_r p_r (∏_{r' ≠ r} q_{r'}) g_r = 0` holds formally. The series `g_r` are assumed
  strongly evaluable at `1`; for `g_r = D_z^r f` or `f(q^ℓ z)` with `f ∈ E` the source obtains
  this from `hol:prop:closure`, which is not proved here. The multiplicativity at constants,
  `(p g)(c) = p(c) g(c)` for a polynomial `p`, is `exists_family_polynomial_mul`, and
  `exists_family_sum_mul` is its version for finite sums.
-/

namespace Surreal.PeriodicThreshold

open _root_.HahnSeries
open Surreal.Holonomic

noncomputable section

section Threshold

variable {Γ R : Type*} [PartialOrder Γ] [Zero R]

/-- The active forward slots of `hol:eq:generalrecurrence`: the shifts `j ∈ {1, …, s}` whose
coefficient `c_j(n)` is nonzero for some `n ≥ N`, that is `c_j ≢ 0` from `N` on. -/
def activeSlots (c : ℕ → ℕ → R⟦Γ⟧) (s N : ℕ) : Finset ℕ := by
  classical exact {j ∈ Finset.Icc 1 s | ∃ n, N ≤ n ∧ c j n ≠ 0}

theorem mem_activeSlots {c : ℕ → ℕ → R⟦Γ⟧} {s N j : ℕ} :
    j ∈ activeSlots c s N ↔ j ∈ Finset.Icc 1 s ∧ ∃ n, N ≤ n ∧ c j n ≠ 0 := by
  classical
  unfold activeSlots
  exact Finset.mem_filter

end Threshold

section Cost

variable {Γ R : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  [Semiring R] [NoZeroDivisors R]

/-- `hol:cor:periodic`, division-free core: if the slot valuations depend only on the residue
of `n` modulo `m ≥ 1`, `v(c_j(n)) = α_{j, n mod m}` whenever `n ≥ N` and `c_j(n) ≠ 0`
(`j ≤ s`), and `B` satisfies `α_{0,r} - α_{j,r} ≤ j B` for all residues `r < m` and all active
forward slots `j`, then strong summability of `(a_n x^n)` at any `x ≠ 0` with `v(x) ≤ -B`
forces `a_n = 0` for all `n ≥ N`. -/
theorem eq_zero_of_periodicCost {a : ℕ → R⟦Γ⟧} {c : ℕ → ℕ → R⟦Γ⟧} {s N m : ℕ} (hm : 0 < m)
    (hrec : ∀ n, N ≤ n → c 0 n * a n + ∑ j ∈ Finset.Icc 1 s, c j n * a (n + j) = 0)
    (hc0 : ∀ n, N ≤ n → c 0 n ≠ 0) (α : ℕ → ℕ → Γ)
    (hα : ∀ j ≤ s, ∀ n, N ≤ n → c j n ≠ 0 → (c j n).order = α j (n % m)) (B : Γ)
    (hB : ∀ j ∈ Finset.Icc 1 s, (∃ n, N ≤ n ∧ c j n ≠ 0) → ∀ r < m, α 0 r - α j r ≤ j • B)
    {x : R⟦Γ⟧} (hx : x ≠ 0) (hxB : x.order ≤ -B)
    (hs : StronglySummable fun n => a n * x ^ n) : ∀ n, N ≤ n → a n = 0 := by
  refine eq_zero_of_stronglySummable_escape hrec hc0 hx (fun n hn j hj hcj => ?_) hs
  rw [hα 0 (Nat.zero_le s) n hn (hc0 n hn), hα j (Finset.mem_Icc.mp hj).2 n hn hcj]
  have h1 := hB j hj ⟨n, hn, hcj⟩ (n % m) (Nat.mod_lt n hm)
  have h2 : j • x.order ≤ -(j • B) := by
    rw [← smul_neg]
    exact nsmul_le_nsmul_right hxB j
  calc α 0 (n % m) - α j (n % m) + j • x.order ≤ j • B + -(j • B) := add_le_add h1 h2
    _ = 0 := add_neg_cancel _

/-- `hol:cor:periodic`, the case with no active forward slot: the recurrence alone forces
`a_n = 0` for all `n ≥ N`. -/
theorem eq_zero_of_activeSlots_eq_empty {a : ℕ → R⟦Γ⟧} {c : ℕ → ℕ → R⟦Γ⟧} {s N : ℕ}
    (hrec : ∀ n, N ≤ n → c 0 n * a n + ∑ j ∈ Finset.Icc 1 s, c j n * a (n + j) = 0)
    (hc0 : ∀ n, N ≤ n → c 0 n ≠ 0) (h : activeSlots c s N = ∅) : ∀ n, N ≤ n → a n = 0 := by
  intro n hn
  have hsum : ∑ j ∈ Finset.Icc 1 s, c j n * a (n + j) = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    have hcj : c j n = 0 := by
      by_contra hcj
      have hmem : j ∈ activeSlots c s N := mem_activeSlots.mpr ⟨hj, n, hn, hcj⟩
      rw [h] at hmem
      exact Finset.notMem_empty _ hmem
    rw [hcj, zero_mul]
  have h0 := hrec n hn
  rw [hsum, add_zero] at h0
  exact (mul_eq_zero.mp h0).resolve_left (hc0 n hn)

end Cost

section Divisible

variable {Γ R : Type*} [AddCommGroup Γ] [LinearOrder Γ] [DivisibleBy Γ ℕ]

section Def

variable [Zero R]

/-- `hol:eq:radiusbound`: for a divisible `Γ`, the refined threshold
`B_rec = max_{0 ≤ r < m, j active} (α_{0,r} - α_{j,r}) / j`, set to `0` if no forward slot
is active. Here `α` is arbitrary and the maximum runs over every residue `r < m` of each active
slot `j`, so a value `α_{j,r}` also enters on a class where `c_j` vanishes from `N` on; the
theorems below only use `α_{j, n mod m}` where `c_j(n) ≠ 0`. Under the slot dichotomy of
`hol:cor:periodic` an active slot is nonzero on every class (`periodicThreshold`). -/
def recThreshold (c : ℕ → ℕ → R⟦Γ⟧) (α : ℕ → ℕ → Γ) (s N m : ℕ) : Γ :=
  if h : (activeSlots c s N ×ˢ Finset.range m).Nonempty then
    (activeSlots c s N ×ˢ Finset.range m).sup' h
      fun p => DivisibleBy.div (α 0 p.2 - α p.1 p.2) p.1
  else 0

/-- `hol:eq:radiusbound`: with no active forward slot, `B_rec = 0`. -/
theorem recThreshold_of_activeSlots_eq_empty {c : ℕ → ℕ → R⟦Γ⟧} {α : ℕ → ℕ → Γ} {s N : ℕ}
    (h : activeSlots c s N = ∅) (m : ℕ) : recThreshold c α s N m = 0 := by
  rw [recThreshold, dif_neg]
  rw [h, Finset.empty_product]
  exact Finset.not_nonempty_empty

variable [IsOrderedAddMonoid Γ]

/-- The step of the proof of `hol:cor:periodic`: multiplying `(α_{0,r} - α_{j,r}) / j ≤ B_rec`
by the positive integer `j` gives `α_{0,r} - α_{j,r} ≤ j B_rec`. -/
theorem sub_le_nsmul_recThreshold {c : ℕ → ℕ → R⟦Γ⟧} {α : ℕ → ℕ → Γ} {s N m j r : ℕ}
    (hj : j ∈ activeSlots c s N) (hr : r < m) :
    α 0 r - α j r ≤ j • recThreshold c α s N m := by
  have hmem : (j, r) ∈ activeSlots c s N ×ˢ Finset.range m :=
    Finset.mem_product.mpr ⟨hj, Finset.mem_range.mpr hr⟩
  have hj0 : j ≠ 0 := by
    have := (Finset.mem_Icc.mp (mem_activeSlots.mp hj).1).1
    omega
  rw [recThreshold, dif_pos ⟨_, hmem⟩]
  calc α 0 r - α j r = j • DivisibleBy.div (α 0 r - α j r) j :=
        (DivisibleBy.div_cancel _ hj0).symm
    _ ≤ _ := nsmul_le_nsmul_right
        (Finset.le_sup' (fun p : ℕ × ℕ => DivisibleBy.div (α 0 p.2 - α p.1 p.2) p.1) hmem) j

end Def

variable [IsOrderedAddMonoid Γ] [Semiring R] [NoZeroDivisors R]

/-- `hol:cor:periodic`, main clause: for divisible `Γ`, if the slot valuations are
`v(c_j(n)) = α_{j, n mod m}` (`m ≥ 1`) whenever `n ≥ N` and `c_j(n) ≠ 0` (`j ≤ s`), then for
every `x ≠ 0` with `v(x) ≤ -B_rec`, strong summability of `(a_n x^n)` forces `a_n = 0` for all
`n ≥ N`. -/
theorem eq_zero_of_stronglySummable_recThreshold {a : ℕ → R⟦Γ⟧} {c : ℕ → ℕ → R⟦Γ⟧}
    {s N m : ℕ} (hm : 0 < m)
    (hrec : ∀ n, N ≤ n → c 0 n * a n + ∑ j ∈ Finset.Icc 1 s, c j n * a (n + j) = 0)
    (hc0 : ∀ n, N ≤ n → c 0 n ≠ 0) (α : ℕ → ℕ → Γ)
    (hα : ∀ j ≤ s, ∀ n, N ≤ n → c j n ≠ 0 → (c j n).order = α j (n % m))
    {x : R⟦Γ⟧} (hx : x ≠ 0) (hxB : x.order ≤ -recThreshold c α s N m)
    (hs : StronglySummable fun n => a n * x ^ n) : ∀ n, N ≤ n → a n = 0 :=
  eq_zero_of_periodicCost hm hrec hc0 α hα _
    (fun _ hj hact _ hr => sub_le_nsmul_recThreshold (mem_activeSlots.mpr ⟨hj, hact⟩) hr) hx
    hxB hs

/-- `hol:eq:excludedball`: a solution `f = ∑ a_n z^n` with `a_{n₀} ≠ 0` for some `n₀ ≥ N`
satisfies `Dom(f) ⊆ {0} ∪ {x ≠ 0 : v(x) > -B_rec}`. -/
theorem strongDomain_subset_recThreshold {f : PowerSeries R⟦Γ⟧} {c : ℕ → ℕ → R⟦Γ⟧}
    {s N m : ℕ} (hm : 0 < m)
    (hrec : ∀ n, N ≤ n → c 0 n * PowerSeries.coeff n f +
      ∑ j ∈ Finset.Icc 1 s, c j n * PowerSeries.coeff (n + j) f = 0)
    (hc0 : ∀ n, N ≤ n → c 0 n ≠ 0) (α : ℕ → ℕ → Γ)
    (hα : ∀ j ≤ s, ∀ n, N ≤ n → c j n ≠ 0 → (c j n).order = α j (n % m))
    {n₀ : ℕ} (hn₀ : N ≤ n₀) (ha : PowerSeries.coeff n₀ f ≠ 0) :
    strongDomain f ⊆ {0} ∪ {x | x ≠ 0 ∧ -recThreshold c α s N m < x.order} := by
  intro x hx
  by_cases hx0 : x = 0
  · exact Or.inl hx0
  · refine Or.inr ⟨hx0, not_le.mp fun hle => ha ?_⟩
    exact eq_zero_of_stronglySummable_recThreshold (a := fun n => PowerSeries.coeff n f) hm hrec
      hc0 α hα hx0 hle hx n₀ hn₀

end Divisible

/-- A nonpolynomial formal power series has a nonzero coefficient beyond every index. -/
theorem exists_coeff_ne_zero_of_not_polynomial {A : Type*} [Semiring A] {f : PowerSeries A}
    (hf : ∀ p : Polynomial A, (p : PowerSeries A) ≠ f) (N : ℕ) :
    ∃ n, N ≤ n ∧ PowerSeries.coeff n f ≠ 0 := by
  by_contra h
  push Not at h
  refine hf (PowerSeries.trunc N f) ?_
  ext n
  rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
  split_ifs with hn
  · rfl
  · exact (h n (not_lt.mp hn)).symm

section Periodic

variable {Γ R : Type*} [AddCommGroup Γ] [LinearOrder Γ] [Zero R]

/-- The valuation `α_{j,r}` of slot `j` on the residue class `r mod m`, read off at the
representative `N m + r`, which is at least `N` when `m ≥ 1`. -/
def slotValuation (c : ℕ → ℕ → R⟦Γ⟧) (N m j r : ℕ) : Γ :=
  (c j (N * m + r)).order

/-- A sequence of orders that is `m`-periodic from `N` on takes equal values at congruent
indices `≥ N`. -/
theorem order_eq_of_mod_eq {g : ℕ → R⟦Γ⟧} {N m : ℕ}
    (hper : ∀ n, N ≤ n → (g (n + m)).order = (g n).order) {n n' : ℕ} (hn : N ≤ n)
    (hn' : N ≤ n') (hmod : n % m = n' % m) : (g n).order = (g n').order := by
  have key : ∀ k n, N ≤ n → (g (n + m * k)).order = (g n).order := by
    intro k
    induction k with
    | zero => intro n _; rw [mul_zero, add_zero]
    | succ k ih =>
      intro n hn
      rw [mul_add, mul_one, ← add_assoc, hper _ (by omega), ih n hn]
  rcases le_total n n' with h | h
  · obtain ⟨k, hk⟩ : m ∣ n' - n :=
      Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq hmod.symm)
    rw [show n' = n + m * k by omega, key k n hn]
  · obtain ⟨k, hk⟩ : m ∣ n - n' :=
      Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq hmod)
    rw [show n = n' + m * k by omega, key k n' hn']

/-- For a slot whose valuation is `m`-periodic from `N` on, `v(c_j(n)) = α_{j, n mod m}` for
every `n ≥ N`. -/
theorem order_eq_slotValuation {c : ℕ → ℕ → R⟦Γ⟧} {N m j : ℕ} (hm : 0 < m)
    (hper : ∀ n, N ≤ n → (c j (n + m)).order = (c j n).order) {n : ℕ} (hn : N ≤ n) :
    (c j n).order = slotValuation c N m j (n % m) :=
  order_eq_of_mod_eq hper hn ((Nat.le_mul_of_pos_right N hm).trans (Nat.le_add_right _ _))
    (by rw [Nat.add_comm (N * m), Nat.add_mul_mod_self_right, Nat.mod_mod])

/-- The slot hypothesis of `hol:cor:periodic` (each slot identically zero from `N` on, or
nonzero from `N` on with `m`-periodic valuation) gives the residue-class valuations
`α_{j,r} = slotValuation c N m j r`. -/
theorem order_eq_slotValuation_of_slot {c : ℕ → ℕ → R⟦Γ⟧} {s N m : ℕ} (hm : 0 < m)
    (hslot : ∀ j ≤ s, (∀ n, N ≤ n → c j n = 0) ∨
      ((∀ n, N ≤ n → c j n ≠ 0) ∧ ∀ n, N ≤ n → (c j (n + m)).order = (c j n).order)) :
    ∀ j ≤ s, ∀ n, N ≤ n → c j n ≠ 0 → (c j n).order = slotValuation c N m j (n % m) := by
  intro j hj n hn hcj
  rcases hslot j hj with h0 | ⟨-, hper⟩
  · exact absurd (h0 n hn) hcj
  · exact order_eq_slotValuation hm hper hn

/-- `hol:eq:radiusbound` for a recurrence with periodic slot valuations: `B_rec` formed from
the residue-class valuations `α_{j,r} = slotValuation c N m j r`. -/
def periodicThreshold [DivisibleBy Γ ℕ] (c : ℕ → ℕ → R⟦Γ⟧) (s N m : ℕ) : Γ :=
  recThreshold c (slotValuation c N m) s N m

end Periodic

section PeriodicMain

variable {Γ R : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  [DivisibleBy Γ ℕ] [Semiring R] [NoZeroDivisors R]

/-- `hol:cor:periodic` with the source's hypotheses: `Γ` divisible, every slot identically zero
for `n ≥ N` or nonzero for all `n ≥ N` with valuation of common period `m ≥ 1`. For every
`x ≠ 0` with `v(x) ≤ -B_rec`, strong summability of `(a_n x^n)` forces `a_n = 0` for all
`n ≥ N`. -/
theorem eq_zero_of_stronglySummable_periodicThreshold {a : ℕ → R⟦Γ⟧} {c : ℕ → ℕ → R⟦Γ⟧}
    {s N m : ℕ} (hm : 0 < m)
    (hrec : ∀ n, N ≤ n → c 0 n * a n + ∑ j ∈ Finset.Icc 1 s, c j n * a (n + j) = 0)
    (hc0 : ∀ n, N ≤ n → c 0 n ≠ 0)
    (hslot : ∀ j ≤ s, (∀ n, N ≤ n → c j n = 0) ∨
      ((∀ n, N ≤ n → c j n ≠ 0) ∧ ∀ n, N ≤ n → (c j (n + m)).order = (c j n).order))
    {x : R⟦Γ⟧} (hx : x ≠ 0) (hxB : x.order ≤ -periodicThreshold c s N m)
    (hs : StronglySummable fun n => a n * x ^ n) : ∀ n, N ≤ n → a n = 0 :=
  eq_zero_of_stronglySummable_recThreshold hm hrec hc0 _
    (order_eq_slotValuation_of_slot hm hslot) hx hxB hs

/-- `hol:eq:excludedball` with the source's hypotheses: every solution with `a_{n₀} ≠ 0` for
some `n₀ ≥ N` has `Dom(f) ⊆ {0} ∪ {x ≠ 0 : v(x) > -B_rec}`. -/
theorem strongDomain_subset_periodicThreshold {f : PowerSeries R⟦Γ⟧} {c : ℕ → ℕ → R⟦Γ⟧}
    {s N m : ℕ} (hm : 0 < m)
    (hrec : ∀ n, N ≤ n → c 0 n * PowerSeries.coeff n f +
      ∑ j ∈ Finset.Icc 1 s, c j n * PowerSeries.coeff (n + j) f = 0)
    (hc0 : ∀ n, N ≤ n → c 0 n ≠ 0)
    (hslot : ∀ j ≤ s, (∀ n, N ≤ n → c j n = 0) ∨
      ((∀ n, N ≤ n → c j n ≠ 0) ∧ ∀ n, N ≤ n → (c j (n + m)).order = (c j n).order))
    {n₀ : ℕ} (hn₀ : N ≤ n₀) (ha : PowerSeries.coeff n₀ f ≠ 0) :
    strongDomain f ⊆ {0} ∪ {x | x ≠ 0 ∧ -periodicThreshold c s N m < x.order} :=
  strongDomain_subset_recThreshold hm hrec hc0 _ (order_eq_slotValuation_of_slot hm hslot) hn₀ ha

/-- `hol:eq:excludedball` for every nonpolynomial solution. -/
theorem strongDomain_subset_periodicThreshold_of_not_polynomial {f : PowerSeries R⟦Γ⟧}
    {c : ℕ → ℕ → R⟦Γ⟧} {s N m : ℕ} (hm : 0 < m)
    (hrec : ∀ n, N ≤ n → c 0 n * PowerSeries.coeff n f +
      ∑ j ∈ Finset.Icc 1 s, c j n * PowerSeries.coeff (n + j) f = 0)
    (hc0 : ∀ n, N ≤ n → c 0 n ≠ 0)
    (hslot : ∀ j ≤ s, (∀ n, N ≤ n → c j n = 0) ∨
      ((∀ n, N ≤ n → c j n ≠ 0) ∧ ∀ n, N ≤ n → (c j (n + m)).order = (c j n).order))
    (hf : ∀ p : Polynomial R⟦Γ⟧, (p : PowerSeries R⟦Γ⟧) ≠ f) :
    strongDomain f ⊆ {0} ∪ {x | x ≠ 0 ∧ -periodicThreshold c s N m < x.order} := by
  obtain ⟨n₀, hn₀, ha⟩ := exists_coeff_ne_zero_of_not_polynomial hf N
  exact strongDomain_subset_periodicThreshold hm hrec hc0 hslot hn₀ ha

end PeriodicMain

section UnitOrbit

open Surreal.HolonomicOrbit

variable {Γ K : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [Field K]

/-- The common period of the valuations `v(P(q^n))` for a unit `q`: the order of `res(q)` when
it is a root of unity, and `1` otherwise. -/
def unitPeriod (q : K⟦Γ⟧) : ℕ := by
  classical exact if IsOfFinOrder (q.coeff 0) then orderOf (q.coeff 0) else 1

/-- `hol:thm:unitorbit` in the form used by `hol:cor:periodic`: for `v(q) = 0`, `q` of infinite
order and `P ≠ 0`, eventually `P(q^n) ≠ 0` and `v(P(q^n))` is `unitPeriod q`-periodic. -/
theorem exists_forall_ge_unitOrbit [CharZero K] {q : K⟦Γ⟧} (hq : q.orderTop = 0)
    (hqt : ¬ IsOfFinOrder q) {P : Polynomial K⟦Γ⟧} (hP : P ≠ 0) :
    0 < unitPeriod q ∧ ∃ N : ℕ, ∀ n, N ≤ n → P.eval (q ^ n) ≠ 0 ∧
      (P.eval (q ^ (n + unitPeriod q))).order = (P.eval (q ^ n)).order := by
  obtain ⟨h, hh, hfin, hinf, ⟨N₂, hN₂⟩, N₃, hN₃⟩ :=
    exists_eventually_periodic_order_eval_pow hq hqt P hP
  have hper : h = unitPeriod q := by
    unfold unitPeriod
    split_ifs with hζ
    · exact hfin hζ
    · exact hinf hζ
  subst hper
  exact ⟨hh, max N₂ N₃, fun n hn =>
    ⟨hN₂ n (le_of_max_le_left hn), hN₃ n (le_of_max_le_right hn)⟩⟩

/-- A prerequisite for the divisible clause of `hol:cor:unitrigid`: for a recurrence
`∑_{j=0}^s P_j(q^n) a_{n+j} = 0` (`n ≥ N₁`, the shape of `hol:eq:qrec`) over a field of
characteristic zero, with `Γ` divisible, `v(q) = 0`, `q` of infinite order and `P₀ ≠ 0`, there is
`N ≥ N₁`, independent of the solution, such that `hol:cor:periodic` applies with period
`unitPeriod q`: for every solution and every `x ≠ 0` with `v(x) ≤ -B_rec`, where `B_rec` is
`periodicThreshold` of the slots `c_j(n) = P_j(q^n)` from `N` on, strong summability of
`(a_n x^n)` forces `a_n = 0` for all `n ≥ N`. -/
theorem eq_zero_of_stronglySummable_unitOrbit [CharZero K] [DivisibleBy Γ ℕ] {q : K⟦Γ⟧}
    (hq : q.orderTop = 0) (hqt : ¬ IsOfFinOrder q) (P : ℕ → Polynomial K⟦Γ⟧) (s N₁ : ℕ)
    (hP0 : P 0 ≠ 0) :
    ∃ N, N₁ ≤ N ∧ ∀ a : ℕ → K⟦Γ⟧,
      (∀ n, N₁ ≤ n → (P 0).eval (q ^ n) * a n +
        ∑ j ∈ Finset.Icc 1 s, (P j).eval (q ^ n) * a (n + j) = 0) →
      ∀ x : K⟦Γ⟧, x ≠ 0 →
        x.order ≤ -periodicThreshold (fun j n => (P j).eval (q ^ n)) s N (unitPeriod q) →
        (StronglySummable fun n => a n * x ^ n) → ∀ n, N ≤ n → a n = 0 := by
  have hj : ∀ j, ∃ Nj : ℕ, P j ≠ 0 → ∀ n, Nj ≤ n → (P j).eval (q ^ n) ≠ 0 ∧
      ((P j).eval (q ^ (n + unitPeriod q))).order = ((P j).eval (q ^ n)).order := fun j => by
    by_cases hPj : P j = 0
    · exact ⟨0, fun h => absurd hPj h⟩
    · obtain ⟨-, Nj, hNj⟩ := exists_forall_ge_unitOrbit hq hqt hPj
      exact ⟨Nj, fun _ => hNj⟩
  choose Nj hNj using hj
  have hm : 0 < unitPeriod q := (exists_forall_ge_unitOrbit hq hqt hP0).1
  refine ⟨N₁ + ∑ j ∈ Finset.range (s + 1), Nj j, Nat.le_add_right _ _,
    fun a hrec x hx hxB hs => ?_⟩
  have hle : ∀ j ≤ s, ∀ n, N₁ + ∑ i ∈ Finset.range (s + 1), Nj i ≤ n → Nj j ≤ n :=
    fun j hj n hn => le_trans (le_trans (Finset.single_le_sum (fun i _ => Nat.zero_le (Nj i))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))) (Nat.le_add_left _ _)) hn
  refine eq_zero_of_stronglySummable_periodicThreshold (c := fun j n => (P j).eval (q ^ n)) hm
    (fun n hn => hrec n (le_trans (Nat.le_add_right _ _) hn))
    (fun n hn => (hNj 0 hP0 n (hle 0 (Nat.zero_le s) n hn)).1) (fun j hj => ?_) hx hxB hs
  by_cases hPj : P j = 0
  · exact Or.inl fun n _ => by simp [hPj]
  · exact Or.inr ⟨fun n hn => (hNj j hPj n (hle j hj n hn)).1,
      fun n hn => (hNj j hPj n (hle j hj n hn)).2⟩

/-- The domain form of `eq_zero_of_stronglySummable_unitOrbit`: every nonpolynomial solution
of the recurrence satisfies `hol:eq:excludedball` with the eventual residue-class threshold. -/
theorem strongDomain_subset_unitOrbit [CharZero K] [DivisibleBy Γ ℕ] {q : K⟦Γ⟧}
    (hq : q.orderTop = 0) (hqt : ¬ IsOfFinOrder q) (P : ℕ → Polynomial K⟦Γ⟧) (s N₁ : ℕ)
    (hP0 : P 0 ≠ 0) :
    ∃ N, N₁ ≤ N ∧ ∀ f : PowerSeries K⟦Γ⟧,
      (∀ n, N₁ ≤ n → (P 0).eval (q ^ n) * PowerSeries.coeff n f +
        ∑ j ∈ Finset.Icc 1 s, (P j).eval (q ^ n) * PowerSeries.coeff (n + j) f = 0) →
      (∀ p : Polynomial K⟦Γ⟧, (p : PowerSeries K⟦Γ⟧) ≠ f) →
      strongDomain f ⊆ {0} ∪ {x | x ≠ 0 ∧
        -periodicThreshold (fun j n => (P j).eval (q ^ n)) s N (unitPeriod q) < x.order} := by
  obtain ⟨N, hN, h⟩ := eq_zero_of_stronglySummable_unitOrbit hq hqt P s N₁ hP0
  refine ⟨N, hN, fun f hrec hf x hx => ?_⟩
  obtain ⟨n₀, hn₀, ha⟩ := exists_coeff_ne_zero_of_not_polynomial hf N
  by_cases hx0 : x = 0
  · exact Or.inl hx0
  · exact Or.inr ⟨hx0, not_le.mp fun hle =>
      ha (h (fun n => PowerSeries.coeff n f) hrec x hx0 hle hx n₀ hn₀)⟩

end UnitOrbit

section Precursive

variable {Γ K : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  [DivisibleBy Γ ℕ] [Field K]

open Classical in
/-- `hol:eq:refinedthreshold`: for divisible `Γ`, the threshold
`B_rec = max {(β_0 - β_j) / j : 1 ≤ j ≤ s, P_j ≠ 0}` of `hol:prop:precursive`, where
`β_j = β(P_j)` is `DifferentialRigidity.polyVal (P j)`, set to `0` if no `P_j` with `j ≥ 1` is
nonzero. -/
def refinedThreshold (P : ℕ → Polynomial K⟦Γ⟧) (s : ℕ) : Γ :=
  if h : ((Finset.Icc 1 s).filter fun j => P j ≠ 0).Nonempty then
    ((Finset.Icc 1 s).filter fun j => P j ≠ 0).sup' h
      fun j => DivisibleBy.div (DifferentialRigidity.polyVal (P 0) -
        DifferentialRigidity.polyVal (P j)) j
  else 0

/-- `j B_rec ≥ β_0 - β_j` for every nonzero `P_j` with `1 ≤ j ≤ s`. -/
theorem sub_le_nsmul_refinedThreshold {P : ℕ → Polynomial K⟦Γ⟧} {s j : ℕ}
    (hj : j ∈ Finset.Icc 1 s) (hPj : P j ≠ 0) :
    DifferentialRigidity.polyVal (P 0) - DifferentialRigidity.polyVal (P j) ≤
      j • refinedThreshold P s := by
  classical
  have hmem : j ∈ (Finset.Icc 1 s).filter fun j => P j ≠ 0 := Finset.mem_filter.mpr ⟨hj, hPj⟩
  have hj0 : j ≠ 0 := by
    have := (Finset.mem_Icc.mp hj).1
    omega
  rw [refinedThreshold, dif_pos ⟨_, hmem⟩]
  calc DifferentialRigidity.polyVal (P 0) - DifferentialRigidity.polyVal (P j)
      = j • DivisibleBy.div (DifferentialRigidity.polyVal (P 0) -
          DifferentialRigidity.polyVal (P j)) j := (DivisibleBy.div_cancel _ hj0).symm
    _ ≤ _ := nsmul_le_nsmul_right (Finset.le_sup' (fun i => DivisibleBy.div
        (DifferentialRigidity.polyVal (P 0) - DifferentialRigidity.polyVal (P i)) i) hmem) j

/-- `hol:prop:precursive` with the divisible refinement `hol:eq:refinedthreshold`, that is
`hol:cor:periodic` with period `m = 1`: over a field `K` of characteristic zero and for divisible
`Γ`, suppose `(a_n)` satisfies `∑_{j=0}^{s} P_j(n) a_{n+j} = 0` for all `n ≥ N₁`, with
`P_0 ≠ 0`. There is `N ≥ N₁`, depending only on `P`, `s` and `N₁`, such that for every `x ≠ 0`
with `v(x) ≤ -B_rec` (`B_rec = refinedThreshold P s`), strong summability of `(a_n x^n)`
forces `a_n = 0` for all `n ≥ N`. -/
theorem eq_zero_of_precursive_refinedThreshold [CharZero K] (P : ℕ → Polynomial K⟦Γ⟧)
    (s N₁ : ℕ) (hP0 : P 0 ≠ 0) :
    ∃ N, N₁ ≤ N ∧ ∀ a : ℕ → K⟦Γ⟧,
      (∀ n, N₁ ≤ n → ∑ j ∈ Finset.range (s + 1), (P j).eval (n : K⟦Γ⟧) * a (n + j) = 0) →
      ∀ x : K⟦Γ⟧, x ≠ 0 → x.order ≤ -refinedThreshold P s →
        StronglySummable (fun n => a n * x ^ n) → ∀ n, N ≤ n → a n = 0 := by
  obtain ⟨N₂, hN₂⟩ := DifferentialRigidity.exists_forall_ge_eval_order P s
  refine ⟨max N₁ N₂, le_max_left _ _, fun a ha x hx hxB hsum => ?_⟩
  refine eq_zero_of_periodicCost (c := fun j n => (P j).eval (n : K⟦Γ⟧)) (s := s) one_pos
    (fun n hn => ?_) (fun n hn => (hN₂ n (le_of_max_le_right hn) 0 (Nat.zero_le _) hP0).1)
    (fun j _ => DifferentialRigidity.polyVal (P j)) (fun j hj n hn hcj => ?_)
    (refinedThreshold P s) (fun j hj hact _ _ => ?_) hx hxB hsum
  · have := ha n (le_of_max_le_left hn)
    rw [DifferentialRigidity.sum_range_succ_eq_add_sum_Icc] at this
    simpa only [add_zero] using this
  · have hPj : P j ≠ 0 := fun h => hcj (by simp only [h, Polynomial.eval_zero])
    exact (hN₂ n (le_of_max_le_right hn) j hj hPj).2
  · obtain ⟨n, -, hcj⟩ := hact
    exact sub_le_nsmul_refinedThreshold hj fun h => hcj (by simp only [h, Polynomial.eval_zero])

end Precursive

section Faithful

variable {Γ R : Type*} [AddCommMonoid Γ] [PartialOrder Γ] [IsOrderedCancelAddMonoid Γ]

section CommSemiring

variable [CommSemiring R]

/-- Strong evaluability at `1` makes each coefficient family `n ↦ (a_n)_γ` finitely supported
(local finiteness at `1`, as in the proof of `hol:prop:faithful`). -/
theorem finite_support_coeff_of_one_mem {f : PowerSeries R⟦Γ⟧}
    (h1 : (1 : R⟦Γ⟧) ∈ strongDomain f) (γ : Γ) :
    (Function.support fun n => (PowerSeries.coeff n f).coeff γ).Finite := by
  have h1' : StronglySummable fun n => PowerSeries.coeff n f * (1 : R⟦Γ⟧) ^ n := h1
  have h := ((stronglySummable_iff _).mp h1').2 γ
  simp only [one_pow, mul_one] at h
  exact h

open Classical in
/-- The coefficient polynomial `P_γ(T) = ∑_n (a_n)_γ T^n` of the proof of `hol:prop:faithful`
(set to `0` when the sum is infinite, which cannot happen when `1 ∈ Dom(f)`). -/
def coeffPolyAt (f : PowerSeries R⟦Γ⟧) (γ : Γ) : Polynomial R :=
  if h : (Function.support fun n => (PowerSeries.coeff n f).coeff γ).Finite then
    ∑ n ∈ h.toFinset, Polynomial.monomial n ((PowerSeries.coeff n f).coeff γ)
  else 0

/-- `hol:prop:faithful`: if `1 ∈ Dom(f)`, then `P_γ` is a polynomial whose `n`-th coefficient
is `(a_n)_γ`. -/
theorem coeff_coeffPolyAt {f : PowerSeries R⟦Γ⟧} (h1 : (1 : R⟦Γ⟧) ∈ strongDomain f) (γ : Γ)
    (n : ℕ) : (coeffPolyAt f γ).coeff n = (PowerSeries.coeff n f).coeff γ := by
  have h := finite_support_coeff_of_one_mem h1 γ
  rw [coeffPolyAt, dif_pos h, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial, Finset.sum_ite_eq']
  split_ifs with hn
  · rfl
  · rw [Set.Finite.mem_toFinset, Function.mem_support, not_not] at hn
    exact hn.symm

/-- `hol:prop:faithful`: if `1 ∈ Dom(f)`, the value of `P_γ` at an ordinary constant `c` is the
coefficient of `t^γ` in the strong value `f(c) = ∑_n a_n c^n`. -/
theorem coeff_hsum_eq_eval_coeffPolyAt {f : PowerSeries R⟦Γ⟧}
    (h1 : (1 : R⟦Γ⟧) ∈ strongDomain f) (c : R) (s : SummableFamily Γ R ℕ)
    (hs : ∀ n, s n = PowerSeries.coeff n f * C c ^ n) (γ : Γ) :
    s.hsum.coeff γ = (coeffPolyAt f γ).eval c := by
  have h := finite_support_coeff_of_one_mem h1 γ
  have hterm : ∀ n, (s n).coeff γ = (PowerSeries.coeff n f).coeff γ * c ^ n := fun n => by
    rw [hs, ← map_pow, C_apply, coeff_mul_single_zero]
  have hsub : {n | (s n).coeff γ ≠ 0} ⊆ (h.toFinset : Set ℕ) := fun n hn => by
    rw [Set.mem_setOf_eq, hterm] at hn
    rw [Set.Finite.coe_toFinset, Function.mem_support]
    exact left_ne_zero_of_mul hn
  rw [coeffPolyAt, dif_pos h, Polynomial.eval_finsetSum,
    SummableFamily.coeff_hsum_eq_sum_of_subset hsub]
  simp only [Polynomial.eval_monomial, hterm]

/-- Strong evaluability at `1` gives strong evaluability at every ordinary constant `c`. -/
theorem C_mem_strongDomain {f : PowerSeries R⟦Γ⟧} (h1 : (1 : R⟦Γ⟧) ∈ strongDomain f) (c : R) :
    C c ∈ strongDomain f := by
  have h := Surreal.HolonomicTorsion.mul_mem_strongDomain h1 (u := C c) fun g hg => by
    rw [C_apply] at hg
    exact le_of_eq (Set.mem_singleton_iff.mp (support_single_subset hg)).symm
  rwa [one_mul] at h

/-- `C_mem_strongDomain` as the existence of an evaluation family at the constant `c`. -/
theorem exists_family_const {f : PowerSeries R⟦Γ⟧} (h1 : (1 : R⟦Γ⟧) ∈ strongDomain f)
    (c : R) : ∃ G : SummableFamily Γ R ℕ, ∀ n, G n = PowerSeries.coeff n f * C c ^ n :=
  C_mem_strongDomain h1 c

omit [AddCommMonoid Γ] [PartialOrder Γ] [IsOrderedCancelAddMonoid Γ] in
/-- The coefficients of `a z^i ⋅ g`. -/
theorem coeff_coe_monomial_mul {A : Type*} [CommSemiring A] (i n : ℕ) (a : A)
    (g : PowerSeries A) :
    PowerSeries.coeff n ((Polynomial.monomial i a : PowerSeries A) * g) =
      if i ≤ n then a * PowerSeries.coeff (n - i) g else 0 := by
  rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coe_mul, Polynomial.coe_C,
    Polynomial.coe_pow, Polynomial.coe_X, mul_assoc, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X_pow_mul', mul_ite, mul_zero]

/-- Multiplicativity of strong evaluation at a constant, used for the second sentence of
`hol:prop:faithful`: if `(g_n c^n)` is strongly summable, so is the evaluation family of
`p ⋅ g` for any polynomial `p ∈ R⟦Γ⟧[z]`, and its sum is `p(c) g(c)`. -/
theorem exists_family_polynomial_mul (p : Polynomial R⟦Γ⟧) {g : PowerSeries R⟦Γ⟧} {c : R}
    (G : SummableFamily Γ R ℕ) (hG : ∀ n, G n = PowerSeries.coeff n g * C c ^ n) :
    ∃ T : SummableFamily Γ R ℕ,
      (∀ n, T n = PowerSeries.coeff n ((p : PowerSeries R⟦Γ⟧) * g) * C c ^ n) ∧
        T.hsum = p.eval (C c) * G.hsum := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨Tp, hTp, hp'⟩ := hp
    obtain ⟨Tq, hTq, hq'⟩ := hq
    refine ⟨Tp + Tq, fun n => ?_, ?_⟩
    · rw [SummableFamily.add_apply, hTp, hTq, Polynomial.coe_add, add_mul, map_add, add_mul]
    · rw [SummableFamily.hsum_add, hp', hq', Polynomial.eval_add, add_mul]
  | monomial i a =>
    refine ⟨((a * C c ^ i) • G).embDomain (addRightEmbedding i), fun n => ?_, ?_⟩
    · rw [coeff_coe_monomial_mul]
      by_cases hin : i ≤ n
      · obtain ⟨k, rfl⟩ : ∃ k, n = k + i := ⟨n - i, by omega⟩
        have h : ((a * C c ^ i) • G).embDomain (addRightEmbedding i) (k + i) =
            ((a * C c ^ i) • G) k := SummableFamily.embDomain_image _ _
        rw [h, SummableFamily.smul_apply, of_symm_smul_of_eq_mul, hG, if_pos hin,
          Nat.add_sub_cancel, pow_add]
        ring
      · rw [SummableFamily.embDomain_notin_range, if_neg hin, zero_mul]
        rintro ⟨k, hk⟩
        rw [addRightEmbedding_apply] at hk
        omega
    · rw [SummableFamily.hsum_embDomain, SummableFamily.hsum_smul, Polynomial.eval_monomial]

/-- `exists_family_polynomial_mul` for a finite linear combination `∑_r p_r g_r`. -/
theorem exists_family_sum_mul {ι : Type*} (t : Finset ι) (p : ι → Polynomial R⟦Γ⟧)
    (g : ι → PowerSeries R⟦Γ⟧) {c : R} (G : ι → SummableFamily Γ R ℕ)
    (hG : ∀ r n, G r n = PowerSeries.coeff n (g r) * C c ^ n) :
    ∃ T : SummableFamily Γ R ℕ,
      (∀ n, T n = PowerSeries.coeff n (∑ r ∈ t, (p r : PowerSeries R⟦Γ⟧) * g r) * C c ^ n) ∧
        T.hsum = ∑ r ∈ t, (p r).eval (C c) * (G r).hsum := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨0, fun n => by simp, by simp⟩
  | insert r t hr ih =>
    obtain ⟨T, hT, hT'⟩ := ih
    obtain ⟨U, hU, hU'⟩ := exists_family_polynomial_mul (p r) (G r) (hG r)
    refine ⟨U + T, fun n => ?_, ?_⟩
    · rw [SummableFamily.add_apply, hU, hT, Finset.sum_insert hr, map_add, add_mul]
    · rw [SummableFamily.hsum_add, hU', hT', Finset.sum_insert hr]

end CommSemiring

variable [CommRing R] [IsDomain R]

/-- `hol:prop:faithful`, first sentence, assuming only `1 ∈ Dom(f)`: if the strong value
`f(c)` vanishes at every constant `c` of an infinite set, then `f = 0`. -/
theorem eq_zero_of_hsum_const_eq_zero {f : PowerSeries R⟦Γ⟧}
    (h1 : (1 : R⟦Γ⟧) ∈ strongDomain f) {S : Set R} (hS : S.Infinite)
    (hz : ∀ c ∈ S, ∃ s : SummableFamily Γ R ℕ,
      (∀ n, s n = PowerSeries.coeff n f * C c ^ n) ∧ s.hsum = 0) : f = 0 := by
  have hP : ∀ γ, coeffPolyAt f γ = 0 := fun γ =>
    Polynomial.eq_zero_of_infinite_isRoot _ (hS.mono fun c hc => by
      obtain ⟨s, hs, h0⟩ := hz c hc
      change Polynomial.IsRoot _ c
      rw [Polynomial.IsRoot.def, ← coeff_hsum_eq_eval_coeffPolyAt h1 c s hs γ, h0, coeff_zero])
  ext n γ
  rw [← coeff_coeffPolyAt h1, hP, Polynomial.coeff_zero, map_zero, coeff_zero]

/-- `hol:prop:faithful`, first sentence: a strongly entire `f` whose strong value vanishes at
infinitely many distinct ordinary constants is `0` as a formal series. -/
theorem eq_zero_of_isStronglyEntire {f : PowerSeries R⟦Γ⟧} (hf : IsStronglyEntire f)
    {S : Set R} (hS : S.Infinite)
    (hz : ∀ c ∈ S, ∀ s : SummableFamily Γ R ℕ,
      (∀ n, s n = PowerSeries.coeff n f * C c ^ n) → s.hsum = 0) : f = 0 := by
  have h1 : (1 : R⟦Γ⟧) ∈ strongDomain f := by
    rw [hf]
    trivial
  refine eq_zero_of_hsum_const_eq_zero h1 hS fun c hc => ?_
  obtain ⟨s, hs⟩ : StronglySummable fun n => PowerSeries.coeff n f * C c ^ n :=
    C_mem_strongDomain h1 c
  exact ⟨s, hs, hz c hc s hs⟩

end Faithful

/-- `hol:prop:faithful`, first sentence, over the source's field `ℂ((t^Γ))`. -/
theorem eq_zero_of_isStronglyEntire_complex {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ] {f : PowerSeries ℂ⟦Γ⟧} (hf : IsStronglyEntire f) {S : Set ℂ}
    (hS : S.Infinite)
    (hz : ∀ c ∈ S, ∀ s : SummableFamily Γ ℂ ℕ,
      (∀ n, s n = PowerSeries.coeff n f * C c ^ n) → s.hsum = 0) : f = 0 :=
  eq_zero_of_isStronglyEntire hf hS hz

section Formal

variable {Γ K : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [Field K]

/-- A nonzero polynomial denominator in `K⟦Γ⟧[z]` vanishes at only finitely many ordinary
constants. -/
theorem finite_setOf_eval_C_eq_zero {q : Polynomial K⟦Γ⟧} (hq : q ≠ 0) :
    {c : K | q.eval (C c) = 0}.Finite :=
  (Polynomial.finite_setOf_isRoot hq).preimage C_injective.injOn

/-- `hol:prop:faithful`, second sentence: let `∑_r (p_r / q_r) g_r` be a linear expression with
rational coefficients (`q_r ≠ 0`) in finitely many series `g_r`, each strongly evaluable at
`1`. If its strong value vanishes at every constant `c` of an infinite set at which all
denominators are nonzero, then the identity with cleared denominators,
`∑_r p_r (∏_{r' ≠ r} q_{r'}) g_r = 0`, holds formally. -/
theorem sum_mul_eq_zero_of_eval_const {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p q : ι → Polynomial K⟦Γ⟧) (hq : ∀ r, q r ≠ 0) (g : ι → PowerSeries K⟦Γ⟧)
    (hg : ∀ r, (1 : K⟦Γ⟧) ∈ strongDomain (g r)) {S : Set K} (hS : S.Infinite)
    (hpt : ∀ c ∈ S, (∀ r, (q r).eval (C c) ≠ 0) → ∀ G : ι → SummableFamily Γ K ℕ,
      (∀ r n, G r n = PowerSeries.coeff n (g r) * C c ^ n) →
        ∑ r, (p r).eval (C c) / (q r).eval (C c) * (G r).hsum = 0) :
    ∑ r, ((p r * ∏ r' ∈ Finset.univ.erase r, q r' : Polynomial K⟦Γ⟧) : PowerSeries K⟦Γ⟧) *
      g r = 0 := by
  have h1 : (1 : K⟦Γ⟧) ∈ strongDomain
      (∑ r, ((p r * ∏ r' ∈ Finset.univ.erase r, q r' : Polynomial K⟦Γ⟧) :
        PowerSeries K⟦Γ⟧) * g r) := by
    choose G hG using fun r => exists_family_const (hg r) 1
    obtain ⟨T, hT, -⟩ := exists_family_sum_mul Finset.univ
      (fun r => p r * ∏ r' ∈ Finset.univ.erase r, q r') g G hG
    refine ⟨T, fun n => ?_⟩
    rw [hT, C_one]
  have hE : (⋃ r, {c : K | (q r).eval (C c) = 0}).Finite :=
    Set.finite_iUnion fun r => finite_setOf_eval_C_eq_zero (hq r)
  refine eq_zero_of_hsum_const_eq_zero h1 (hS.sdiff hE) fun c hc => ?_
  have hqc : ∀ r, (q r).eval (C c) ≠ 0 := fun r h => hc.2 (Set.mem_iUnion.mpr ⟨r, h⟩)
  choose G hG using fun r => exists_family_const (hg r) c
  obtain ⟨T, hT, hT'⟩ := exists_family_sum_mul Finset.univ
    (fun r => p r * ∏ r' ∈ Finset.univ.erase r, q r') g G hG
  refine ⟨T, hT, ?_⟩
  rw [hT']
  calc ∑ r, (p r * ∏ r' ∈ Finset.univ.erase r, q r').eval (C c) * (G r).hsum
      = (∏ r, (q r).eval (C c)) *
          ∑ r, (p r).eval (C c) / (q r).eval (C c) * (G r).hsum := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [Polynomial.eval_mul, Polynomial.eval_prod,
          ← Finset.mul_prod_erase Finset.univ (fun r => (q r).eval (C c)) (Finset.mem_univ r)]
        calc (p r).eval (C c) * (∏ r' ∈ Finset.univ.erase r, (q r').eval (C c)) * (G r).hsum
            = ((q r).eval (C c) * ((p r).eval (C c) / (q r).eval (C c))) *
                (∏ r' ∈ Finset.univ.erase r, (q r').eval (C c)) * (G r).hsum := by
              rw [mul_div_cancel₀ _ (hqc r)]
          _ = _ := by ring
    _ = 0 := by rw [hpt c hc.1 hqc G hG, mul_zero]

end Formal

end

end Surreal.PeriodicThreshold
