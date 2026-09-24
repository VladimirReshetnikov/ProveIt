import Surreal.HahnSeries.WickDomain
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Tactic.LinearCombination

/-!
# Algebraic Gaussian integration by parts

This file proves `wick:lem:ibp` (algebraic Gaussian integration by parts) of
`docs/surcomplex/wick-summability-certificates/article.tex`, together with the integrality
clause of `wick:lem:wickcount` and the finiteness and edge-set independence of its moment sum;
`E_C` is defined here by that moment formula (see **Pending**), and for symmetric `C` it is the
only normalized linear functional satisfying the identity of `wick:lem:ibp` (`eq_expect_of_ibp`).

**Setting.** The colors form a finite linearly ordered type `V` (the source's `{1, …, d}`), the
scalars form an arbitrary commutative semiring `K` (the source takes the Hahn field
`K = ℂ((t^Γ))`), and `C : Matrix V V K` is a symmetric bilinear covariance: it may be singular,
no positivity is assumed and no conjugation occurs. For a finite edge type `E` with endpoints
`ends e = (i, j)` (parallel edges allowed) and an edge-count vector `k : E → ℕ`, the color counts
`Dk` are `edgeTotal ends k`, with the incidence columns `D_e = 2 e_i` for a loop and `e_i + e_j`
otherwise (`Surreal.WickDomain.edgeVec`). The closed formula `wick:eq:W`,
`W(M, k) = ∏ᵢ Mᵢ! / (∏_{loops} 2^{kₑ} kₑ! ∏_{other edges} kₑ!)`, is `Surreal.WickDomain.wickW`.

**Main results.**
* `wickNat` is the natural number of the source's proof of `wick:lem:wickcount`: the product
  over the colors of the multinomial coefficients distributing the slots of each color among
  the edges, times `(2kₑ - 1)‼ = (2kₑ)!/(2^{kₑ} kₑ!)` for a loop and `kₑ!` for another edge.
  `factorialProd_edgeTotal` is the identity `∏ᵢ (Dk)ᵢ! = wickNat k · ∏ 2^{k_ii} k_ii! ∏ k_ij!`,
  so `wickW_eq_wickNat` and `exists_nat_eq_wickW` give the integrality clause of
  `wick:lem:wickcount`: if `Dk = M`, then `W(M, k)` is a positive integer.
* `moment C M` is the Wick moment `E_C[x^M] = ∑_{Dk = M} W(M, k) C^k`, a finite sum
  (`finite_edgeTotal_fiber`) over the edge counts on all pairs `i ≤ j`. The rational form with
  the closed formula `wickW` is `moment_eq_sum_wickW`, and `moment_eq_sum_restrict` shows that
  the same sum over the source's edge set `E = {(i, j) : i ≤ j, C_ij ≠ 0}` gives the same
  value; `moment_eq_sum_matrixEdge` is this for `Surreal.WickDomain.MatrixEdge` over a Hahn
  field, and `moment_eq_sum_matrixEdge_wickW` is its form with the closed formula `wickW`. The
  empty moment is `1` (`moment_zero`) and odd moments vanish (`moment_eq_zero_of_odd`).
* `wickNat_eq_sum` is the partner recursion `W(M + eᵢ, k) = ∑ⱼ M_j W(M - e_j, k - δ_{ij})`
  over the `j` with `k_{ij} > 0` (`wickW_add_single` states it for the closed formula `wickW`),
  and `moment_add_single` is its consequence
  `E_C[x^{M + eᵢ}] = ∑ⱼ C_ij M_j E_C[x^{M - e_j}]`, which is `wick:lem:ibp` on monomials.
* `expect C : K[x] →ₗ[K] K` is the linear extension of `x^M ↦ E_C[x^M]`, normalized by
  `expect_one`, and `expect_X_mul` is `wick:lem:ibp`:
  `E_C[xᵢ f] = ∑ⱼ C_ij E_C[∂ⱼ f]` for every polynomial `f`, with `∂ⱼ = MvPolynomial.pderiv j`.
* `eq_expect_of_ibp`: for a symmetric `C`, `expect C` is the only `K`-linear functional `L`
  with `L 1 = 1` and `L(xᵢ f) = ∑ⱼ C_ij L(∂ⱼ f)` for all `i` and `f`.

**Proof.** The source removes the pair containing the distinguished additional `i`-slot. On
the level of edge counts this is the partner recursion: for `u = (i, j)` and `k = k' + δ_u`,
`W(k) (k_u) (D_u)ᵢ = M_j W(k') (M_i + 1)` (`wickNat_step`), and summing over `j` uses
`∑ⱼ k_{ij} (D_{ij})ᵢ = (Dk)ᵢ = Mᵢ + 1` (`sum_upper_mul_edgeVec`). The reindexing
`k ↦ k - δ_{ij}` between `{Dk = M + eᵢ, k_{ij} > 0}` and `{Dk = M - e_j}` gives
`moment_add_single`; symmetry of `C` is used only to identify `C_{min(i,j) max(i,j)}` with `C_ij`.
Uniqueness (`eq_expect_of_ibp`) is an induction on the total degree of a monomial `x^s`: writing
`x^s = xᵢ x^{s - eᵢ}`, the identity expresses both functionals at `x^s` through their values at
monomials of smaller degree.

**Pending.** The combinatorial clause of `wick:lem:wickcount`, that `W(M, k)` is the number of
pairings of `|M|` distinguishable colored slots with edge counts `k`, is not formalized; the
source defines `E_C` through these pairings, while here `E_C` is defined by the resulting
closed moment formula, so `expect_X_mul` is `wick:lem:ibp` for that closed-formula `E_C`. By
`eq_expect_of_ibp`, any normalized linear functional satisfying the identity of `wick:lem:ibp`,
such as the pairing-defined `E_C` of the source, coincides with `expect C`; that the
pairing-defined functional has these properties is not formalized. Integrality of `W` is
proved directly from the multinomial and double-factorial factorization of the source's proof.
-/

namespace Surreal.WickIBP

open Finset
open scoped Nat

noncomputable section

/-! ### Unit steps of count vectors -/

section Single

variable {ι : Type*} [DecidableEq ι]

/-- Removing and restoring one unit at a positive coordinate. -/
theorem sub_add_single {k : ι → ℕ} {u : ι} (h : 0 < k u) :
    k - Pi.single u 1 + Pi.single u 1 = k := by
  funext e
  by_cases he : e = u
  · subst he
    simp only [Pi.add_apply, Pi.sub_apply, Pi.single_eq_same]
    omega
  · simp only [Pi.add_apply, Pi.sub_apply, Pi.single_eq_of_ne he]
    omega

/-- Adding and removing one unit. -/
theorem add_single_sub (k : ι → ℕ) (u : ι) : k + Pi.single u 1 - Pi.single u 1 = k := by
  funext e
  simp only [Pi.add_apply, Pi.sub_apply]
  omega

end Single

/-! ### Edge counts and the integrality of `W(M, k)` -/

section Count

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] (ends : E → V × V)

/-- The color counts `(Dk)ᵢ = ∑ₑ kₑ (D_e)ᵢ` of an edge-count vector `k`. -/
def edgeTotal (k : E → ℕ) : V → ℕ :=
  fun i => ∑ e, k e * WickDomain.edgeVec ends e i

omit [Fintype V] in
/-- `k ↦ Dk` is additive. -/
theorem edgeTotal_add (k l : E → ℕ) :
    edgeTotal ends (k + l) = edgeTotal ends k + edgeTotal ends l := by
  funext i
  simp [edgeTotal, add_mul, sum_add_distrib]

omit [Fintype V] in
/-- `D δₑ = D_e`. -/
theorem edgeTotal_single [DecidableEq E] (e : E) :
    edgeTotal ends (Pi.single e 1) = WickDomain.edgeVec ends e := by
  funext i
  simp only [edgeTotal]
  rw [Finset.sum_eq_single e (fun b _ hb => by simp [hb]) (by simp)]
  simp

omit [Fintype V] [Fintype E] in
theorem one_le_edgeVec_fst (e : E) : 1 ≤ WickDomain.edgeVec ends e (ends e).1 := by
  simp only [WickDomain.edgeVec, Pi.add_apply, Pi.single_eq_same]
  omega

omit [Fintype V] in
/-- Each edge count is bounded by the color count at the first endpoint. -/
theorem le_edgeTotal (k : E → ℕ) (e : E) : k e ≤ edgeTotal ends k (ends e).1 :=
  calc k e ≤ k e * WickDomain.edgeVec ends e (ends e).1 :=
        Nat.le_mul_of_pos_right _ (one_le_edgeVec_fst ends e)
    _ ≤ edgeTotal ends k (ends e).1 :=
        Finset.single_le_sum (f := fun e' => k e' * WickDomain.edgeVec ends e' (ends e).1)
          (fun _ _ => Nat.zero_le _) (mem_univ e)

omit [Fintype E] in
/-- Every edge has two endpoint slots. -/
theorem sum_edgeVec (e : E) : ∑ i, WickDomain.edgeVec ends e i = 2 := by
  have := WickDomain.sum_edgeVec_smul ends e fun _ => (1 : ℕ)
  simpa using this

/-- The total number of slots is twice the number of edges: `∑ᵢ (Dk)ᵢ = 2 ∑ₑ kₑ`. -/
theorem sum_edgeTotal (k : E → ℕ) : ∑ i, edgeTotal ends k i = 2 * ∑ e, k e := by
  simp only [edgeTotal]
  rw [Finset.sum_comm, mul_sum]
  refine sum_congr rfl fun e _ => ?_
  rw [← mul_sum, sum_edgeVec, mul_comm]

omit [Fintype V] in
/-- The fiber `{k : Dk = M}` is finite. -/
theorem finite_edgeTotal_fiber (M : V → ℕ) : {k : E → ℕ | edgeTotal ends k = M}.Finite := by
  refine (Set.Finite.pi fun e => Set.finite_Iic (M (ends e).1)).subset fun k hk => ?_
  simp only [Set.mem_setOf_eq] at hk
  simp only [Set.mem_pi, Set.mem_univ, Set.mem_Iic, forall_const]
  intro e
  rw [← hk]
  exact le_edgeTotal ends k e

/-- The finite set of edge-count vectors `k` with `Dk = M`. -/
def edgeFiber (M : V → ℕ) : Finset (E → ℕ) :=
  (finite_edgeTotal_fiber ends M).toFinset

omit [Fintype V] in
theorem mem_edgeFiber {M : V → ℕ} {k : E → ℕ} : k ∈ edgeFiber ends M ↔ edgeTotal ends k = M := by
  simp [edgeFiber]

omit [Fintype V] in
/-- The only edge-count vector with no slots is `0`. -/
theorem edgeFiber_zero : edgeFiber ends (0 : V → ℕ) = {0} := by
  ext k
  rw [mem_edgeFiber, mem_singleton]
  constructor
  · intro hk
    funext e
    have := le_edgeTotal ends k e
    rw [hk] at this
    simpa using this
  · rintro rfl
    funext i
    simp [edgeTotal]

/-- The numerator `∏ᵢ Mᵢ!` of `wick:eq:W`. -/
def factorialProd (M : V → ℕ) : ℕ :=
  ∏ i, (M i)!

omit [Fintype E] in
/-- `∏ (M + eᵢ)! = (∏ M!) (Mᵢ + 1)`. -/
theorem factorialProd_add_single (M : V → ℕ) (i : V) :
    factorialProd (M + Pi.single i 1) = factorialProd M * (M i + 1) := by
  unfold factorialProd
  rw [Fintype.prod_eq_mul_prod_compl i, Fintype.prod_eq_mul_prod_compl i (fun l => (M l)!)]
  have : ∏ l ∈ {i}ᶜ, ((M + Pi.single i 1 : V → ℕ) l)! = ∏ l ∈ {i}ᶜ, (M l)! := by
    refine prod_congr rfl fun l hl => ?_
    rw [mem_compl, mem_singleton] at hl
    simp [hl]
  rw [this]
  simp [Nat.factorial_succ]
  ring

/-- The loop factor: `2` for a loop and `1` for any other edge. -/
def loopFactor (e : E) : ℕ :=
  if (ends e).1 = (ends e).2 then 2 else 1

/-- The denominator `∏ 2^{k_ii} k_ii! ∏ k_ij!` of `wick:eq:W`. -/
def edgeDen (k : E → ℕ) : ℕ :=
  ∏ e, (if (ends e).1 = (ends e).2 then 2 ^ k e else 1) * (k e)!

omit [Fintype V] in
theorem edgeDen_pos (k : E → ℕ) : 0 < edgeDen ends k :=
  prod_pos fun e _ => by split_ifs <;> positivity

omit [Fintype V] in
/-- Adding one edge `e` multiplies the denominator of `wick:eq:W` by `(kₑ + 1)` times the loop
factor. -/
theorem edgeDen_add_single [DecidableEq E] (k : E → ℕ) (e : E) :
    edgeDen ends (k + Pi.single e 1) = edgeDen ends k * ((k e + 1) * loopFactor ends e) := by
  unfold edgeDen
  rw [Fintype.prod_eq_mul_prod_compl e,
    Fintype.prod_eq_mul_prod_compl e (fun e => (if (ends e).1 = (ends e).2 then 2 ^ k e else 1) *
      (k e)!)]
  have : ∏ l ∈ {e}ᶜ, (if (ends l).1 = (ends l).2 then 2 ^ (k + Pi.single e 1 : E → ℕ) l else 1) *
      ((k + Pi.single e 1 : E → ℕ) l)! =
      ∏ l ∈ {e}ᶜ, (if (ends l).1 = (ends l).2 then 2 ^ k l else 1) * (k l)! := by
    refine prod_congr rfl fun l hl => ?_
    rw [mem_compl, mem_singleton] at hl
    simp [hl]
  rw [this, loopFactor]
  simp only [Pi.add_apply, Pi.single_eq_same, Nat.factorial_succ]
  split_ifs <;> ring

/-- The integer value of `W(Dk, k)`, following the proof of `wick:lem:wickcount`: for each color
`i`, the multinomial coefficient distributing the `(Dk)ᵢ` slots among the edges, times the
number `(2kₑ - 1)‼ = (2kₑ)!/(2^{kₑ} kₑ!)` of pairings of the loop slots of a loop and the number
`kₑ!` of bijections between the two slot sets of another edge. -/
def wickNat (k : E → ℕ) : ℕ :=
  (∏ i, Nat.multinomial univ fun e => k e * WickDomain.edgeVec ends e i) *
    ∏ e, if (ends e).1 = (ends e).2 then (2 * k e - 1)‼ else (k e)!

/-- `W` is positive. -/
theorem wickNat_pos (k : E → ℕ) : 0 < wickNat ends k := by
  unfold wickNat
  refine Nat.mul_pos (prod_pos fun i _ => Nat.multinomial_pos _ _) (prod_pos fun e _ => ?_)
  split_ifs
  · exact Nat.doubleFactorial_pos _
  · exact Nat.factorial_pos _

/-- The empty edge-count vector has `W = 1`. -/
theorem wickNat_zero : wickNat ends 0 = 1 := by
  simp [wickNat, Nat.multinomial]

omit [Fintype E] in
/-- The slot factorials of `k` copies of one edge: `(2k)!` for a loop and `k! k!` otherwise. -/
theorem prod_factorial_mul_edgeVec (c : ℕ) (e : E) :
    ∏ i, (c * WickDomain.edgeVec ends e i)! =
      if (ends e).1 = (ends e).2 then (2 * c)! else c ! * c ! := by
  have hsingle : ∀ a : V, ∏ i, (c * (Pi.single a 1 : V → ℕ) i)! = c ! := fun a => by
    rw [Finset.prod_eq_single a (fun i _ hi => by simp [Pi.single_eq_of_ne hi]) (by simp)]
    simp
  split_ifs with h
  · rw [Finset.prod_eq_single (ends e).1
      (fun i _ hi => by simp [WickDomain.edgeVec, ← h, Pi.single_eq_of_ne hi]) (by simp)]
    simp only [WickDomain.edgeVec, ← h, Pi.add_apply, Pi.single_eq_same]
    ring_nf
  · rw [show c ! * c ! = (∏ i, (c * (Pi.single (ends e).1 1 : V → ℕ) i)!) *
        ∏ i, (c * (Pi.single (ends e).2 1 : V → ℕ) i)! by rw [hsingle, hsingle],
      ← prod_mul_distrib]
    refine prod_congr rfl fun i _ => ?_
    simp only [WickDomain.edgeVec, Pi.add_apply, Pi.single_apply]
    split_ifs with h1 h2 h2 <;> simp_all

/-- `(2n - 1)‼ · 2ⁿ n! = (2n)!` (the source's count of pairings of the loop slots,
`(2k)!/(2^k k!)`). -/
theorem doubleFactorial_mul (n : ℕ) : (2 * n - 1)‼ * (2 ^ n * n !) = (2 * n)! := by
  cases n with
  | zero => rfl
  | succ n =>
    have h : 2 * (n + 1) = 2 * n + 1 + 1 := by ring
    rw [← Nat.doubleFactorial_two_mul, h, Nat.factorial_eq_mul_doubleFactorial, Nat.add_sub_cancel,
      mul_comm]

/-- The integer identity behind `wick:lem:wickcount`:
`∏ᵢ (Dk)ᵢ! = W · ∏ 2^{k_ii} k_ii! ∏ k_ij!`. -/
theorem factorialProd_edgeTotal (k : E → ℕ) :
    factorialProd (edgeTotal ends k) = wickNat ends k * edgeDen ends k := by
  have hspec : ∀ i, (∏ e, (k e * WickDomain.edgeVec ends e i)!) *
      Nat.multinomial univ (fun e => k e * WickDomain.edgeVec ends e i) =
      (edgeTotal ends k i)! := fun i => Nat.multinomial_spec _ _
  unfold factorialProd
  simp_rw [← hspec]
  rw [prod_mul_distrib, Finset.prod_comm]
  simp_rw [prod_factorial_mul_edgeVec]
  unfold wickNat edgeDen
  rw [mul_comm, mul_assoc, ← prod_mul_distrib]
  congr 1
  refine prod_congr rfl fun e _ => ?_
  split_ifs
  · exact (doubleFactorial_mul _).symm
  · ring

/-- The closed formula `wick:eq:W` evaluates to the natural number `wickNat` on `Dk = M`. -/
theorem wickW_eq_wickNat {M : V → ℕ} {k : E → ℕ} (h : edgeTotal ends k = M) :
    WickDomain.wickW ends M k = wickNat ends k := by
  have hden : (0 : ℚ) < ∏ e, ((if (ends e).1 = (ends e).2 then (2 : ℚ) ^ k e else 1) *
      ((k e)! : ℚ)) := prod_pos fun e _ => by split_ifs <;> positivity
  unfold WickDomain.wickW
  rw [div_eq_iff hden.ne', ← h]
  have := congrArg (Nat.cast : ℕ → ℚ) (factorialProd_edgeTotal ends k)
  push_cast [factorialProd, edgeDen, Nat.cast_ite] at this
  exact this

/-- **Integrality of the colored matching multiplicity** (`wick:lem:wickcount`, "in
particular"): if `Dk = M`, then `W(M, k)` of `wick:eq:W` is a positive integer. -/
theorem exists_nat_eq_wickW {M : V → ℕ} {k : E → ℕ} (h : edgeTotal ends k = M) :
    ∃ n : ℕ, 0 < n ∧ (n : ℚ) = WickDomain.wickW ends M k :=
  ⟨wickNat ends k, wickNat_pos ends k, (wickW_eq_wickNat ends h).symm⟩

end Count

/-! ### Upper edges `(i, j)` with `i ≤ j` -/

section Upper

variable {V : Type*} [LinearOrder V]

/-- The edge set `{(i, j) : i ≤ j}` of `wick:sec:wick`, keeping also the pairs with
`C_ij = 0`. -/
abbrev UpperEdge (V : Type*) [LinearOrder V] : Type _ :=
  {e : V × V // e.1 ≤ e.2}

/-- The endpoints of an upper edge. -/
abbrev upperEnds : UpperEdge V → V × V :=
  Subtype.val

/-- The upper edge `(min i j, max i j)` joining the colors `i` and `j`. -/
def upper (i j : V) : UpperEdge V :=
  ⟨(min i j, max i j), min_le_max⟩

theorem upper_comm (i j : V) : upper i j = upper j i := by
  simp [upper, min_comm, max_comm]

theorem upper_fst_snd (e : UpperEdge V) : upper e.1.1 e.1.2 = e :=
  Subtype.ext (by simp only [upper, min_eq_left e.2, max_eq_right e.2])

/-- The other endpoint of an edge at `i`. -/
def partner (i : V) (e : UpperEdge V) : V :=
  if e.1.1 = i then e.1.2 else e.1.1

theorem partner_upper (i j : V) : partner i (upper i j) = j := by
  unfold partner upper
  rcases le_total i j with h | h
  · simp only [min_eq_left h, max_eq_right h, if_true]
  · simp only [min_eq_right h, max_eq_left h]
    split_ifs with hij
    · exact hij.symm
    · rfl

theorem upper_injective (i : V) : Function.Injective (upper i) :=
  Function.LeftInverse.injective (partner_upper i)

theorem upper_loop_iff (i j : V) : (upper i j).1.1 = (upper i j).1.2 ↔ i = j := by
  unfold upper
  rcases le_total i j with h | h
  · simp only [min_eq_left h, max_eq_right h]
  · simp only [min_eq_right h, max_eq_left h]
    exact eq_comm

theorem edgeVec_upper (i j : V) :
    WickDomain.edgeVec upperEnds (upper i j) = Pi.single i 1 + Pi.single j 1 := by
  show Pi.single (min i j) 1 + Pi.single (max i j) 1 = _
  rcases le_total i j with h | h
  · simp only [min_eq_left h, max_eq_right h]
  · simp only [min_eq_right h, max_eq_left h]
    exact add_comm _ _

theorem loopFactor_upper (i j : V) :
    loopFactor upperEnds (upper i j) = WickDomain.edgeVec upperEnds (upper i j) i := by
  unfold loopFactor
  rw [edgeVec_upper]
  split_ifs with h'
  · have hij : i = j := (upper_loop_iff i j).1 h'
    subst hij
    simp
  · have hij : i ≠ j := fun hij => h' ((upper_loop_iff i j).2 hij)
    simp [Pi.single_eq_of_ne hij]

theorem edgeTotal_add_upper [Fintype V] (k : UpperEdge V → ℕ) (i j : V) :
    edgeTotal upperEnds (k + Pi.single (upper i j) 1) =
      edgeTotal upperEnds k + Pi.single i 1 + Pi.single j 1 := by
  rw [edgeTotal_add, edgeTotal_single, edgeVec_upper, add_assoc]

/-- Summing over the partners `j` of `i` visits every edge at `i` once. -/
theorem sum_upper_mul_edgeVec [Fintype V] (k : UpperEdge V → ℕ) (i : V) :
    ∑ j, k (upper i j) * WickDomain.edgeVec upperEnds (upper i j) i =
      edgeTotal upperEnds k i := by
  refine Fintype.sum_of_injective (upper i) (upper_injective i) _
    (fun e => k e * WickDomain.edgeVec upperEnds e i) (fun e he => ?_) (fun j => rfl)
  by_contra hne
  apply he
  have hi : i = e.1.1 ∨ i = e.1.2 := by
    by_contra h
    push Not at h
    apply hne
    simp [WickDomain.edgeVec, Pi.single_eq_of_ne h.1, Pi.single_eq_of_ne h.2]
  rcases hi with h | h
  · exact ⟨e.1.2, by rw [h, upper_fst_snd]⟩
  · exact ⟨e.1.1, by rw [h, upper_comm, upper_fst_snd]⟩

/-- For a symmetric matrix, the entry on the upper edge joining `i` and `j` is `C i j`. -/
theorem cov_upper {K : Type*} {C : Matrix V V K} (hC : C.IsSymm) (i j : V) :
    C (upper i j).1.1 (upper i j).1.2 = C i j := by
  show C (min i j) (max i j) = C i j
  rcases le_total i j with h | h
  · simp only [min_eq_left h, max_eq_right h]
  · simp only [min_eq_right h, max_eq_left h]
    exact hC.apply i j

end Upper

/-! ### The partner recursion for `W` -/

section Recursion

variable {V : Type*} [Fintype V] [LinearOrder V]

/-- One contraction step: adding one edge `(i, j)` to `k` multiplies `W` as in the proof of
`wick:lem:ibp`. -/
theorem wickNat_step (i j : V) {M : V → ℕ} {k : UpperEdge V → ℕ}
    (hk : edgeTotal upperEnds k + Pi.single j 1 = M) :
    wickNat upperEnds (k + Pi.single (upper i j) 1) *
        ((k (upper i j) + 1) * WickDomain.edgeVec upperEnds (upper i j) i) =
      M j * wickNat upperEnds k * (M i + 1) := by
  have hN : edgeTotal upperEnds (k + Pi.single (upper i j) 1) = M + Pi.single i 1 := by
    rw [edgeTotal_add_upper, ← hk, add_right_comm]
  have hFM : factorialProd M = wickNat upperEnds k * edgeDen upperEnds k * M j := by
    rw [← hk, factorialProd_add_single, factorialProd_edgeTotal]
    simp
  have hF := factorialProd_edgeTotal upperEnds (k + Pi.single (upper i j) 1)
  rw [hN, factorialProd_add_single, hFM, edgeDen_add_single, loopFactor_upper] at hF
  apply Nat.eq_of_mul_eq_mul_left (edgeDen_pos upperEnds k)
  linear_combination hF.symm

/-- **The partner recursion** for `W`: if `Dk = M + eᵢ`, then
`W(M + eᵢ, k) = ∑_{j : k_{ij} > 0} M_j W(M - e_j, k - δ_{ij})`. -/
theorem wickNat_eq_sum (i : V) {M : V → ℕ} {k : UpperEdge V → ℕ}
    (hk : edgeTotal upperEnds k = M + Pi.single i 1) :
    wickNat upperEnds k = ∑ j, if 0 < k (upper i j) then
      M j * wickNat upperEnds (k - Pi.single (upper i j) 1) else 0 := by
  apply Nat.eq_of_mul_eq_mul_right (Nat.succ_pos (M i))
  rw [sum_mul]
  have hterm : ∀ j, (if 0 < k (upper i j) then
      M j * wickNat upperEnds (k - Pi.single (upper i j) 1) else 0) * (M i + 1) =
      wickNat upperEnds k * (k (upper i j) * WickDomain.edgeVec upperEnds (upper i j) i) := by
    intro j
    split_ifs with hpos
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + Pi.single (upper i j) 1 :=
        ⟨k - Pi.single (upper i j) 1, (sub_add_single hpos).symm⟩
      have hP : edgeTotal upperEnds k' + Pi.single j 1 = M := by
        rw [edgeTotal_add_upper] at hk
        funext l
        have := congrFun hk l
        simp only [Pi.add_apply] at this ⊢
        omega
      rw [add_single_sub, ← wickNat_step i j hP]
      simp
    · have : k (upper i j) = 0 := by omega
      simp [this]
  rw [sum_congr rfl fun j _ => hterm j, ← mul_sum, sum_upper_mul_edgeVec, hk]
  simp

/-- The partner recursion in terms of the closed formula `wick:eq:W`: if `Dk = M + eᵢ`, then
`W(M + eᵢ, k) = ∑_{j : k_{ij} > 0} M_j W(M - e_j, k - δ_{ij})`. -/
theorem wickW_add_single (i : V) {M : V → ℕ} {k : UpperEdge V → ℕ}
    (hk : edgeTotal upperEnds k = M + Pi.single i 1) :
    WickDomain.wickW upperEnds (M + Pi.single i 1) k = ∑ j, if 0 < k (upper i j) then
      (M j : ℚ) * WickDomain.wickW upperEnds (M - Pi.single j 1) (k - Pi.single (upper i j) 1)
      else 0 := by
  rw [wickW_eq_wickNat upperEnds hk, wickNat_eq_sum i hk, Nat.cast_sum]
  refine sum_congr rfl fun j _ => ?_
  split_ifs with hpos
  · have hP : edgeTotal upperEnds (k - Pi.single (upper i j) 1) = M - Pi.single j 1 := by
      have h2 := hk
      rw [← sub_add_single hpos, edgeTotal_add_upper] at h2
      funext l
      have := congrFun h2 l
      simp only [Pi.add_apply, Pi.sub_apply] at this ⊢
      omega
    rw [wickW_eq_wickNat upperEnds hP]
    exact Nat.cast_mul _ _
  · exact Nat.cast_zero

end Recursion

/-! ### Wick moments and the integration-by-parts identity -/

section Moment

variable {V K : Type*} [Fintype V] [LinearOrder V] [CommSemiring K]

/-- The covariance monomial `C^k = ∏_{i ≤ j} C_ij^{k_ij}`. -/
def covMonomial (C : Matrix V V K) (k : UpperEdge V → ℕ) : K :=
  ∏ e, C e.1.1 e.1.2 ^ k e

/-- Adding one edge `e` multiplies `C^k` by `C_e`. -/
theorem covMonomial_add_single (C : Matrix V V K) (k : UpperEdge V → ℕ) (e : UpperEdge V) :
    covMonomial C (k + Pi.single e 1) = covMonomial C k * C e.1.1 e.1.2 := by
  simp only [covMonomial, Pi.add_apply, pow_add, prod_mul_distrib]
  congr 1
  rw [Finset.prod_eq_single e (fun b _ hb => by simp [Pi.single_eq_of_ne hb]) (by simp)]
  simp

/-- The Wick moment `E_C[x^M] = ∑_{Dk = M} W(M, k) C^k` of `wick:lem:wickcount`, summed over
the edge counts on all pairs `i ≤ j`, with `W` the positive integer `wickNat`. -/
def moment (C : Matrix V V K) (M : V → ℕ) : K :=
  ∑ k ∈ edgeFiber upperEnds M, (wickNat upperEnds k : K) * covMonomial C k

/-- The empty moment is `1`. -/
theorem moment_zero (C : Matrix V V K) : moment C 0 = 1 := by
  rw [moment, edgeFiber_zero, sum_singleton, wickNat_zero]
  simp [covMonomial]

/-- Odd moments vanish. -/
theorem moment_eq_zero_of_odd (C : Matrix V V K) {M : V → ℕ} (hM : Odd (∑ i, M i)) :
    moment C M = 0 := by
  refine sum_eq_zero fun k hk => ?_
  rw [mem_edgeFiber] at hk
  rw [← hk, sum_edgeTotal] at hM
  exact (Nat.not_even_iff_odd.2 hM (even_two_mul _)).elim

/-- **Partner recursion** (`wick:lem:ibp` on monomials):
`E_C[x^{M + eᵢ}] = ∑ⱼ C_ij M_j E_C[x^{M - e_j}]` for a symmetric `C`. -/
theorem moment_add_single {C : Matrix V V K} (hC : C.IsSymm) (M : V → ℕ) (i : V) :
    moment C (M + Pi.single i 1) = ∑ j, C i j * ((M j : K) * moment C (M - Pi.single j 1)) := by
  have step : moment C (M + Pi.single i 1) = ∑ j, ∑ k ∈ edgeFiber upperEnds (M + Pi.single i 1),
      if 0 < k (upper i j) then (M j : K) * wickNat upperEnds (k - Pi.single (upper i j) 1) *
        covMonomial C k else 0 := by
    rw [moment, Finset.sum_comm]
    refine sum_congr rfl fun k hk => ?_
    rw [wickNat_eq_sum i ((mem_edgeFiber upperEnds).1 hk), Nat.cast_sum, sum_mul]
    refine sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  rw [step]
  refine sum_congr rfl fun j _ => ?_
  rcases Nat.eq_zero_or_pos (M j) with h0 | hpos
  · simp [h0]
  rw [moment, mul_sum, mul_sum, ← sum_filter]
  refine sum_nbij' (fun k => k - Pi.single (upper i j) 1) (fun k => k + Pi.single (upper i j) 1)
    ?_ ?_ ?_ ?_ ?_
  · intro k hk
    rw [mem_filter, mem_edgeFiber] at hk
    rw [mem_edgeFiber]
    have h2 := hk.1
    rw [← sub_add_single hk.2, edgeTotal_add_upper] at h2
    funext l
    have := congrFun h2 l
    simp only [Pi.add_apply, Pi.sub_apply] at this ⊢
    omega
  · intro k hk
    rw [mem_edgeFiber] at hk
    rw [mem_filter, mem_edgeFiber, edgeTotal_add_upper, hk]
    refine ⟨funext fun l => ?_, by simp⟩
    have hle : (Pi.single j 1 : V → ℕ) l ≤ M l := by
      by_cases hl : l = j
      · subst hl
        rw [Pi.single_eq_same]
        exact hpos
      · rw [Pi.single_eq_of_ne hl]
        exact Nat.zero_le _
    simp only [Pi.add_apply, Pi.sub_apply]
    omega
  · intro k hk
    rw [mem_filter] at hk
    exact sub_add_single hk.2
  · intro k _
    exact add_single_sub k _
  · intro k hk
    rw [mem_filter] at hk
    have hcov : covMonomial C k = covMonomial C (k - Pi.single (upper i j) 1) * C i j := by
      rw [← cov_upper hC i j, ← covMonomial_add_single, sub_add_single hk.2]
    rw [hcov]
    ring

/-- The Wick expectation `E_C : K[x] → K`, the linear extension of `x^M ↦ E_C[x^M]`. -/
def expect (C : Matrix V V K) : MvPolynomial V K →ₗ[K] K :=
  Finsupp.linearCombination K (fun s : V →₀ ℕ => moment C s) ∘ₗ
    (AddMonoidAlgebra.coeffLinearEquiv K).toLinearMap

/-- `E_C[a x^s] = a E_C[x^s]`. -/
theorem expect_monomial (C : Matrix V V K) (s : V →₀ ℕ) (a : K) :
    expect C (MvPolynomial.monomial s a) = a * moment C s := by
  change Finsupp.linearCombination K (fun s : V →₀ ℕ => moment C s) (Finsupp.single s a) = _
  rw [Finsupp.linearCombination_single, smul_eq_mul]

/-- The expectation is normalized: `E_C[1] = 1`. -/
theorem expect_one (C : Matrix V V K) : expect C 1 = 1 := by
  rw [MvPolynomial.one_def, expect_monomial, Finsupp.coe_zero, moment_zero, one_mul]

/-- **Algebraic Gaussian integration by parts** (`wick:lem:ibp`): for a symmetric bilinear
covariance matrix `C`, with no invertibility or positivity assumption, and every polynomial `f`,
`E_C[xᵢ f] = ∑ⱼ C_ij E_C[∂ⱼ f]`, where `∂ⱼ` is formal differentiation in `xⱼ`. -/
theorem expect_X_mul {C : Matrix V V K} (hC : C.IsSymm) (i : V) (f : MvPolynomial V K) :
    expect C (MvPolynomial.X i * f) = ∑ j, C i j * expect C (MvPolynomial.pderiv j f) := by
  induction f using MvPolynomial.induction_on' with
  | monomial s a =>
    rw [MvPolynomial.X, MvPolynomial.monomial_mul, one_mul, expect_monomial, Finsupp.coe_add,
      Finsupp.single_eq_pi_single, add_comm, moment_add_single hC, mul_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [MvPolynomial.pderiv_monomial, expect_monomial, Finsupp.coe_tsub,
      Finsupp.single_eq_pi_single]
    ring
  | add p q hp hq =>
    rw [mul_add, map_add, hp, hq]
    simp only [map_add, mul_add, sum_add_distrib]

/-- **Uniqueness of the Wick expectation**: for a symmetric `C`, `E_C = expect C` is the only
`K`-linear functional `L` on `K[x]` with `L 1 = 1` satisfying the identity of `wick:lem:ibp`,
`L(xᵢ f) = ∑ⱼ C_ij L(∂ⱼ f)` for all `i` and `f`. -/
theorem eq_expect_of_ibp {C : Matrix V V K} (hC : C.IsSymm) (L : MvPolynomial V K →ₗ[K] K)
    (h1 : L 1 = 1)
    (hL : ∀ i f, L (MvPolynomial.X i * f) = ∑ j, C i j * L (MvPolynomial.pderiv j f)) :
    L = expect C := by
  have hmono : ∀ (L' : MvPolynomial V K →ₗ[K] K) (s : V →₀ ℕ) (a : K),
      L' (MvPolynomial.monomial s a) = a * L' (MvPolynomial.monomial s 1) := fun L' s a => by
    rw [← smul_eq_mul, ← map_smul, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  have key : ∀ n (s : V →₀ ℕ), ∑ l, s l ≤ n →
      L (MvPolynomial.monomial s 1) = expect C (MvPolynomial.monomial s 1) := by
    intro n
    induction n with
    | zero =>
      intro s hs
      have hs0 : s = 0 := by
        ext l
        exact (Finset.sum_eq_zero_iff.1 (Nat.le_zero.1 hs)) l (mem_univ l)
      rw [hs0, ← MvPolynomial.one_def, h1, expect_one]
    | succ n ih =>
      intro s hs
      by_cases hsn : ∑ l, s l ≤ n
      · exact ih s hsn
      obtain ⟨i, hi⟩ : ∃ i, s i ≠ 0 := by
        by_contra h
        push Not at h
        exact hsn (by simp [h])
      have hst : s = Finsupp.single i 1 + (s - Finsupp.single i 1) :=
        (add_tsub_cancel_of_le (Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hi))).symm
      have ht : ∑ l, (s - Finsupp.single i 1 : V →₀ ℕ) l ≤ n := by
        have hsum := congrArg (fun s : V →₀ ℕ => ∑ l, s l) hst
        simp only [Finsupp.coe_add, Pi.add_apply, sum_add_distrib, Finsupp.single_apply,
          sum_ite_eq, mem_univ, if_true] at hsum
        omega
      rw [hst, MvPolynomial.monomial_single_add, pow_one, hL, expect_X_mul hC]
      refine sum_congr rfl fun j _ => ?_
      rw [MvPolynomial.pderiv_monomial, hmono, hmono (expect C), ih]
      exact le_trans (sum_le_sum fun l _ => by simp) ht
  refine MvPolynomial.linearMap_ext fun s => LinearMap.ext fun a => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, hmono, hmono (expect C), key _ s le_rfl]

end Moment

/-! ### The source's edge set `{(i, j) : i ≤ j, C_ij ≠ 0}` and the rational form of `W` -/

section Restrict

variable {V K E' : Type*} [Fintype V] [LinearOrder V] [CommSemiring K] [Fintype E']
  {ι : E' → UpperEdge V}

/-- Extension by zero of an edge-count vector on a set `E'` of upper edges. -/
def extendCount (ι : E' → UpperEdge V) (k : E' → ℕ) : UpperEdge V → ℕ :=
  Function.extend ι k (0 : UpperEdge V → ℕ)

omit [Fintype V] [Fintype E'] in
theorem extendCount_apply (hι : Function.Injective ι) (k : E' → ℕ) (a : E') :
    extendCount ι k (ι a) = k a :=
  hι.extend_apply k 0 a

omit [Fintype V] [Fintype E'] in
theorem extendCount_apply_of_notMem {e : UpperEdge V} (he : e ∉ Set.range ι) (k : E' → ℕ) :
    extendCount ι k e = 0 :=
  Function.extend_apply' (f := ι) k (0 : UpperEdge V → ℕ) e he

theorem edgeTotal_extendCount (hι : Function.Injective ι) (k : E' → ℕ) :
    edgeTotal upperEnds (extendCount ι k) = edgeTotal (upperEnds ∘ ι) k := by
  funext i
  unfold edgeTotal
  symm
  exact Fintype.sum_of_injective ι hι _ _
    (fun e he => by rw [extendCount_apply_of_notMem he, zero_mul])
    (fun a => by rw [extendCount_apply hι]; rfl)

theorem edgeDen_extendCount (hι : Function.Injective ι) (k : E' → ℕ) :
    edgeDen upperEnds (extendCount ι k) = edgeDen (upperEnds ∘ ι) k := by
  unfold edgeDen
  symm
  exact Fintype.prod_of_injective ι hι _ _
    (fun e he => by simp [extendCount_apply_of_notMem he])
    (fun a => by rw [extendCount_apply hι]; rfl)

theorem wickNat_extendCount (hι : Function.Injective ι) (k : E' → ℕ) :
    wickNat upperEnds (extendCount ι k) = wickNat (upperEnds ∘ ι) k := by
  have h := factorialProd_edgeTotal upperEnds (extendCount ι k)
  rw [edgeTotal_extendCount hι, factorialProd_edgeTotal, edgeDen_extendCount hι] at h
  exact (Nat.eq_of_mul_eq_mul_right (edgeDen_pos _ k) h).symm

theorem covMonomial_extendCount (C : Matrix V V K) (hι : Function.Injective ι) (k : E' → ℕ) :
    covMonomial C (extendCount ι k) = ∏ a, C (ι a).1.1 (ι a).1.2 ^ k a := by
  unfold covMonomial
  symm
  exact Fintype.prod_of_injective ι hι _ _
    (fun e he => by rw [extendCount_apply_of_notMem he, pow_zero])
    (fun a => by rw [extendCount_apply hι])

theorem covMonomial_eq_zero (C : Matrix V V K) {k : UpperEdge V → ℕ} {e : UpperEdge V}
    (hCe : C e.1.1 e.1.2 = 0) (hk : k e ≠ 0) : covMonomial C k = 0 :=
  prod_eq_zero (mem_univ e) (by rw [hCe, zero_pow hk])

/-- **The moment over the source's edge set** (`wick:lem:wickcount`): if `ι` embeds an edge
set `E'` into the pairs `i ≤ j` and `C_ij = 0` off its range, for instance
`E' = {(i, j) : i ≤ j, C_ij ≠ 0}`, then `E_C[x^M] = ∑_{Dk = M} W(M, k) C^k` with `D` and `k`
taken over `E'`. -/
theorem moment_eq_sum_restrict (C : Matrix V V K) (hι : Function.Injective ι)
    (hC : ∀ e ∉ Set.range ι, C e.1.1 e.1.2 = 0) (M : V → ℕ) :
    moment C M = ∑ k ∈ edgeFiber (upperEnds ∘ ι) M,
      (wickNat (upperEnds ∘ ι) k : K) * ∏ a, C (ι a).1.1 (ι a).1.2 ^ k a := by
  have hinj : Function.Injective (extendCount ι) := fun k l h => funext fun a => by
    have := congrFun h (ι a)
    rwa [extendCount_apply hι, extendCount_apply hι] at this
  symm
  calc ∑ k ∈ edgeFiber (upperEnds ∘ ι) M,
        (wickNat (upperEnds ∘ ι) k : K) * ∏ a, C (ι a).1.1 (ι a).1.2 ^ k a
      = ∑ k ∈ edgeFiber (upperEnds ∘ ι) M,
          (wickNat upperEnds (extendCount ι k) : K) * covMonomial C (extendCount ι k) := by
        refine sum_congr rfl fun k _ => ?_
        rw [wickNat_extendCount hι, covMonomial_extendCount C hι]
    _ = ∑ k ∈ (edgeFiber (upperEnds ∘ ι) M).image (extendCount ι),
          (wickNat upperEnds k : K) * covMonomial C k :=
        (sum_image (f := fun k => (wickNat upperEnds k : K) * covMonomial C k)
          fun x _ y _ h => hinj h).symm
    _ = moment C M := by
        refine sum_subset (fun k hk => ?_) (fun k hk hnot => ?_)
        · obtain ⟨k', hk', rfl⟩ := mem_image.1 hk
          rw [mem_edgeFiber] at hk' ⊢
          rw [edgeTotal_extendCount hι, hk']
        · by_contra hne
          apply hnot
          have hsupp : ∀ e ∉ Set.range ι, k e = 0 := fun e he => by
            by_contra hke
            exact hne (by rw [covMonomial_eq_zero C (hC e he) hke, mul_zero])
          have hext : extendCount ι (k ∘ ι) = k := funext fun e => by
            by_cases he : e ∈ Set.range ι
            · obtain ⟨a, rfl⟩ := he
              exact extendCount_apply hι _ a
            · rw [extendCount_apply_of_notMem he, hsupp e he]
          refine mem_image.2 ⟨k ∘ ι, ?_, hext⟩
          rw [mem_edgeFiber, ← edgeTotal_extendCount hι, hext, ← mem_edgeFiber]
          exact hk

omit [Fintype E'] in
/-- The moment in the rational form of `wick:lem:wickcount`: over a field,
`E_C[x^M] = ∑_{Dk = M} W(M, k) C^k` with `W(M, k)` given by the closed formula `wick:eq:W`. -/
theorem moment_eq_sum_wickW {F : Type*} [Field F] (C : Matrix V V F) (M : V → ℕ) :
    moment C M = ∑ k ∈ edgeFiber upperEnds M,
      ((WickDomain.wickW upperEnds M k : ℚ) : F) * covMonomial C k := by
  refine sum_congr rfl fun k hk => ?_
  rw [wickW_eq_wickNat upperEnds ((mem_edgeFiber upperEnds).1 hk), Rat.cast_natCast]

/-- `moment_eq_sum_restrict` for the edge set `E = {(i, j) : i ≤ j, C_ij ≠ 0}` of a covariance
matrix over a Hahn field (`Surreal.WickDomain.MatrixEdge`), the setting of `wick:sec:wick`. -/
theorem moment_eq_sum_matrixEdge {Γ R : Type*} [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ] [Field R] (C : Matrix V V (HahnSeries Γ R)) (M : V → ℕ) :
    moment C M = ∑ k ∈ edgeFiber (Subtype.val : WickDomain.MatrixEdge C → V × V) M,
      (wickNat Subtype.val k : HahnSeries Γ R) * ∏ e, WickDomain.matrixCov C e ^ k e :=
  moment_eq_sum_restrict (ι := fun e : WickDomain.MatrixEdge C => (⟨e.1, e.2.1⟩ : UpperEdge V))
    C (fun _ _ h => Subtype.ext (congrArg (Subtype.val : UpperEdge V → V × V) h))
    (fun e he => by
      by_contra h
      exact he ⟨⟨e.1, e.2, h⟩, rfl⟩) M

/-- The moment formula of `wick:lem:wickcount` in the source's setting: over a Hahn field, with
the edge set `E = {(i, j) : i ≤ j, C_ij ≠ 0}` (`Surreal.WickDomain.MatrixEdge`),
`E_C[x^M] = ∑_{Dk = M} W(M, k) C^k` with `W(M, k)` given by the closed formula `wick:eq:W`. -/
theorem moment_eq_sum_matrixEdge_wickW {Γ R : Type*} [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ] [Field R] (C : Matrix V V (HahnSeries Γ R)) (M : V → ℕ) :
    moment C M = ∑ k ∈ edgeFiber (Subtype.val : WickDomain.MatrixEdge C → V × V) M,
      ((WickDomain.wickW (Subtype.val : WickDomain.MatrixEdge C → V × V) M k : ℚ) :
        HahnSeries Γ R) * ∏ e, WickDomain.matrixCov C e ^ k e := by
  rw [moment_eq_sum_matrixEdge]
  refine sum_congr rfl fun k hk => ?_
  rw [wickW_eq_wickNat _ ((mem_edgeFiber _).1 hk), Rat.cast_natCast]

end Restrict

end

end Surreal.WickIBP
