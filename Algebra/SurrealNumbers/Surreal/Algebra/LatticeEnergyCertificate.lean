import Mathlib.Algebra.Order.Group.PiLex
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.Order.WellFoundedSet
import Mathlib.Data.Fintype.BigOperators

/-!
# Finite minimum certificates for quadratic lattice energies

This file proves `tate:theta:thm:certificate` (with `tate:theta:eq:energydecomp` and
`tate:theta:eq:cert`; the equivalence and the incompatible-`b` clause outright, the termination
clause under the hypothesis that `𝓔(L)` is well ordered, see Pending), `tate:theta:cor:voronoi`
and `tate:theta:thm:minimizers` of `docs/surcomplex/hahn-tate-uniformization/article.tex`.
It also formalizes the definitions
`tate:theta:def:posgen`, `tate:theta:def:admissible`, `tate:theta:eq:flag`,
`tate:theta:eq:lexenergy` and `tate:theta:eq:linearcompatibility`, the consequence
`tate:theta:eq:firstlevel`, and the no-minimum half of the proof of `tate:theta:cor:domain`.

## Generic part

`L` is any abelian group and `Γ` any linearly ordered abelian group, for instance
`ℝ^r_lex = Lex (Fin r → ℝ)`. An energy `E : L → Γ` is quadratic with polar form
`B : L →+ L →+ Γ` if `E (x + y) = E x + E y + B x y` (`IsQuadraticEnergy`). The source energy
`E(n) = B(n,n)/2 + b(n)` is of this form; `isQuadraticEnergy_of_two_nsmul` states the halving
without division as `2 E(n) = B(n,n) + 2 b(n)`, which determines `E` since `Γ` is torsion
free. Write `I_m(h) = E(m + h) - E(m)` (`incr`). Proved:

* `IsQuadraticEnergy.incr_sum`: the exact decomposition `tate:theta:eq:energydecomp`, the pairs
  being ordered by any linear order of the index set.
* `IsQuadraticEnergy.isGlobalMin_iff`: for every positively generating finite set `S`, `m` is a
  global minimizer iff `I_m(s) ≥ 0` for all `s ∈ S`. No compatibility is assumed.
* `descentStep_wellFounded`: if `E(L)` is well ordered, every descent search by moves `s ∈ S`
  with `I_m(s) < 0` terminates. `IsQuadraticEnergy.isGlobalMin_of_not_descentStep`: any point
  admitting no descent step is a global minimizer, so a search that stops, however its moves
  were chosen, stops at a global minimizer (this part needs no well-ordering).
  `IsQuadraticEnergy.exists_descent_isGlobalMin`: under well-ordering, from every start some
  finite descent chain reaches a global minimizer.
* `mem_voronoiCell_iff`: `x ∈ Vor_L(0)` iff `2 B(x,s) ≤ B(s,s)` for every `s ∈ S`. The report
  does not define `Vor_L(0)`; `voronoiCell` follows Amini–Nicolussi,
  `Vor_L(0) = {x | B(x,x) ≤ B(x - l, x - l) for all l ∈ L}`.
* If `B(x,x) > 0` for `x ≠ 0` and `L` is free of finite rank `g`:
  `IsQuadraticEnergy.finite_minimizers` (at most `2^g` minimizers),
  `IsQuadraticEnergy.exists_orthogonal_decomposition` (`n - m` is the sum of at most `g`
  distinct pairwise orthogonal members of `S`, all partial sums added to `m` being minimizers)
  and `IsQuadraticEnergy.exists_zero_cost_path` (a path of at most `g` forward `S`-moves
  through minimizers, so the zero-cost graph is connected with diameter at most `g`).

## The higher-rank setting

`H` is a real vector space, `L ⊆ H` a subgroup and `B j` (`j : Fin r`) the real bilinear forms
`𝓑_{j+1}`. `flag` is the radical flag, `IsANAdmissible` the admissibility of
`tate:theta:def:admissible`, `lexForm` the form `𝓑 : H × H → ℝ^r_lex` and `lexEnergy` the
energy `𝓔_j(n) = 𝓑_j(n,n)/2 + b_j(n)`. Rationality is imposed for `0 ≤ j ≤ r`; the case
`j = 0` says `span_ℝ L = H`, the source's standing full-lattice assumption. Discreteness of `L`
is never assumed. Proved there: `exists_firstLevel`
(`tate:theta:eq:firstlevel`), hence `𝓑(x,x) > 0` for `x ≠ 0`; `certificate_iff` with the
explicit `I_m(s) = 𝓑(s,s)/2 + 𝓑(m,s) + b(s)`; `certificate_fails_of_not_compatible` (for an
incompatible `b` no lattice point passes the test, since some lattice vector lowers the energy
of every point); `certificate_descent` (well-foundedness of descent and a reachable global
minimizer, both assuming `𝓔(L)` well ordered, and minimality of every point admitting no
descent step); `mem_voronoiCell_iff_of_admissible`; and
`minimizers_finite_ncard_le`, `minimizers_orthogonal`, `minimizers_path` for `L ≅ ℤ^g`,
written as `Module.Free ℤ L`, `Module.Finite ℤ L` and `g = finrank ℤ L` (freeness is automatic
for a finitely generated subgroup of `H`, which is torsion free). The finiteness of the
minimizer set comes from the parity argument and does not use `tate:theta:thm:flag`.

## Pending

* The implication from compatibility to the well-ordering of `𝓔(L)` is
  `tate:theta:thm:flag` and is not proved here. Termination of the descent search is therefore
  proved under the hypothesis that `𝓔(L)` is well ordered.
* The finite positively generating set of `tate:theta:thm:positive` is a hypothesis. Every
  statement holds for any positively generating `S`.
* The algorithmic counts of `tate:theta:cor:BFS` and the sharpness example after
  `tate:theta:thm:minimizers` are not formalized.
-/

namespace Surreal.LatticeEnergy

open Finset

section Algebra

variable {L Γ : Type*} [AddCommGroup L] [AddCommGroup Γ]

/-- `E` is a quadratic energy with polar form `B`: `E (x + y) = E x + E y + B x y`. -/
def IsQuadraticEnergy (B : L →+ L →+ Γ) (E : L → Γ) : Prop :=
  ∀ x y, E (x + y) = E x + E y + B x y

/-- The energy difference `I_m(h) = E(m + h) - E(m)`. -/
def incr (E : L → Γ) (m h : L) : Γ := E (m + h) - E m

variable {B : L →+ L →+ Γ} {E : L → Γ}

namespace IsQuadraticEnergy

/-- A quadratic energy vanishes at `0`. -/
theorem energy_zero (hE : IsQuadraticEnergy B E) : E 0 = 0 := by
  simpa using hE 0 0

/-- The polar form of a quadratic energy is symmetric. -/
theorem symm (hE : IsQuadraticEnergy B E) (x y : L) : B x y = B y x := by
  have h1 := hE x y
  have h2 := hE y x
  rw [add_comm y x, h1, add_comm (E y) (E x)] at h2
  exact add_left_cancel h2

/-- `I_m(h) = E(h) + B(m,h)`. -/
theorem incr_eq (hE : IsQuadraticEnergy B E) (m h : L) : incr E m h = E h + B m h := by
  unfold incr
  rw [hE m h]
  abel

/-- `I_m(h₁ + h₂) = I_m(h₁) + I_m(h₂) + B(h₁,h₂)`. -/
theorem incr_add (hE : IsQuadraticEnergy B E) (m h₁ h₂ : L) :
    incr E m (h₁ + h₂) = incr E m h₁ + incr E m h₂ + B h₁ h₂ := by
  rw [hE.incr_eq, hE.incr_eq, hE.incr_eq, hE h₁ h₂, map_add]
  abel

/-- `I_m(a s) = a I_m(s) + binom(a,2) B(s,s)`. -/
theorem incr_nsmul (hE : IsQuadraticEnergy B E) (m s : L) (n : ℕ) :
    incr E m (n • s) = n • incr E m s + n.choose 2 • B s s := by
  induction n with
  | zero => simp [incr]
  | succ n ih =>
    rw [succ_nsmul, hE.incr_add, ih, Nat.choose_succ_succ, Nat.choose_one_right, map_nsmul,
      AddMonoidHom.nsmul_apply, succ_nsmul, add_nsmul]
    abel

/-- `tate:theta:eq:energydecomp`: for `h = ∑_{i ∈ A} a_i v_i`, with the pairs ordered by a
linear order on the index set,
`I_m(h) = ∑ a_i I_m(v_i) + ∑ binom(a_i,2) B(v_i,v_i) + ∑_{i<k} a_i a_k B(v_i,v_k)`. -/
theorem incr_sum {ι : Type*} [LinearOrder ι] (hE : IsQuadraticEnergy B E) (m : L)
    (A : Finset ι) (v : ι → L) (a : ι → ℕ) :
    incr E m (∑ i ∈ A, a i • v i) =
      ∑ i ∈ A, a i • incr E m (v i) + ∑ i ∈ A, (a i).choose 2 • B (v i) (v i) +
        ∑ i ∈ A, ∑ k ∈ A with i < k, (a i * a k) • B (v i) (v k) := by
  classical
  induction A using Finset.induction_on_max with
  | empty => simp [incr]
  | insert j A hj ih =>
    have hjA : j ∉ A := fun h => lt_irrefl j (hj j h)
    have hpair : ∑ i ∈ insert j A, ∑ k ∈ insert j A with i < k, (a i * a k) • B (v i) (v k) =
        ∑ i ∈ A, ∑ k ∈ A with i < k, (a i * a k) • B (v i) (v k) +
          ∑ i ∈ A, (a i * a j) • B (v i) (v j) := by
      rw [sum_insert hjA, filter_insert, if_neg (lt_irrefl j),
        filter_false_of_mem (fun x hx => not_lt.mpr (hj x hx).le), sum_empty, zero_add,
        ← sum_add_distrib]
      refine sum_congr rfl fun i hi => ?_
      rw [filter_insert, if_pos (hj i hi), sum_insert (fun h => hjA (mem_filter.mp h).1),
        add_comm]
    have hcross : B (a j • v j) (∑ i ∈ A, a i • v i) =
        ∑ i ∈ A, (a i * a j) • B (v i) (v j) := by
      rw [map_sum]
      refine sum_congr rfl fun i _ => ?_
      rw [map_nsmul, map_nsmul, AddMonoidHom.nsmul_apply, hE.symm (v j) (v i), mul_nsmul']
    rw [sum_insert hjA, hE.incr_add, ih, hE.incr_nsmul, hcross, hpair, sum_insert hjA,
      sum_insert hjA]
    abel

end IsQuadraticEnergy

end Algebra

section Order

variable {L Γ : Type*} [AddCommGroup L] [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]

/-- `tate:theta:def:posgen`: the finite set `S ⊆ L ∖ {0}` positively generates `L` for `B` if
every `x ∈ L` is `∑_{a ∈ A} c_a a` with `A ⊆ S`, positive integers `c_a` and `B(a,a') ≥ 0` for
all `a, a' ∈ A`. -/
def PositivelyGenerates (B : L →+ L →+ Γ) (S : Finset L) : Prop :=
  (0 : L) ∉ S ∧ ∀ x : L, ∃ A ⊆ S, ∃ c : L → ℕ, (∀ a ∈ A, 0 < c a) ∧
    (∀ a ∈ A, ∀ a' ∈ A, 0 ≤ B a a') ∧ x = ∑ a ∈ A, c a • a

variable {B : L →+ L →+ Γ} {E : L → Γ}

/-- One step of the descent search: move from `m` to `n = m + s` with `s ∈ S` and
`I_m(s) < 0`. -/
def DescentStep (E : L → Γ) (S : Finset L) (n m : L) : Prop :=
  ∃ s ∈ S, n = m + s ∧ incr E m s < 0

/-- If `E(L)` is well ordered, every descent search terminates. -/
theorem descentStep_wellFounded (hwf : (Set.range E).IsWF) (S : Finset L) :
    WellFounded (DescentStep E S) := by
  have h : WellFounded (Function.onFun (· < ·) E) := Set.wellFoundedOn_range.mp hwf
  refine Subrelation.wf (fun {n m} hnm => ?_) h
  obtain ⟨s, -, rfl, hs⟩ := hnm
  exact sub_neg.mp hs

namespace IsQuadraticEnergy

/-- For pairwise `B`-nonnegative vectors, `∑ c_a I_m(a) ≤ I_m(∑ c_a a)`. -/
theorem sum_nsmul_incr_le (hE : IsQuadraticEnergy B E) (m : L) (A : Finset L) (c : L → ℕ)
    (hA : ∀ a ∈ A, ∀ a' ∈ A, 0 ≤ B a a') :
    ∑ a ∈ A, c a • incr E m a ≤ incr E m (∑ a ∈ A, c a • a) := by
  letI : LinearOrder L := IsWellOrder.linearOrder WellOrderingRel
  rw [hE.incr_sum m A (fun a => a) c, add_assoc]
  refine le_add_of_nonneg_right (add_nonneg (sum_nonneg fun a ha => ?_)
    (sum_nonneg fun a ha => sum_nonneg fun a' ha' => ?_))
  · exact nsmul_nonneg (hA a ha a ha) _
  · exact nsmul_nonneg (hA a ha a' (mem_filter.mp ha').1) _

/-- `tate:theta:thm:certificate`, the equivalence: for any linear term, `m` is a global
minimizer exactly when it passes the finite test on a positively generating set. -/
theorem isGlobalMin_iff (hE : IsQuadraticEnergy B E) {S : Finset L}
    (hS : PositivelyGenerates B S) (m : L) :
    (∀ n, E m ≤ E n) ↔ ∀ s ∈ S, 0 ≤ incr E m s := by
  constructor
  · intro h s _
    exact sub_nonneg.mpr (h (m + s))
  · intro h n
    obtain ⟨A, hAS, c, -, hApos, hdec⟩ := hS.2 (n - m)
    have h1 := hE.sum_nsmul_incr_le m A c hApos
    rw [← hdec] at h1
    have h2 : 0 ≤ incr E m (n - m) :=
      (sum_nonneg fun a ha => nsmul_nonneg (h a (hAS ha)) _).trans h1
    unfold incr at h2
    rwa [add_sub_cancel, sub_nonneg] at h2

/-- `tate:theta:thm:certificate`, the end of the descent: a point from which no descent step is
possible is a global minimizer. No well-ordering is needed. -/
theorem isGlobalMin_of_not_descentStep (hE : IsQuadraticEnergy B E) {S : Finset L}
    (hS : PositivelyGenerates B S) {m : L} (hm : ∀ n, ¬ DescentStep E S n m) :
    ∀ n, E m ≤ E n :=
  (hE.isGlobalMin_iff hS m).mpr fun s hs => not_lt.mp fun h => hm _ ⟨s, hs, rfl, h⟩

/-- `tate:theta:thm:certificate`, descent: if `E(L)` is well ordered, then from every start some
descent chain reaches a global minimizer after finitely many steps. -/
theorem exists_descent_isGlobalMin (hE : IsQuadraticEnergy B E) {S : Finset L}
    (hS : PositivelyGenerates B S) (hwf : (Set.range E).IsWF) (m₀ : L) :
    ∃ m, Relation.ReflTransGen (DescentStep E S) m m₀ ∧ ∀ n, E m ≤ E n := by
  induction m₀ using (descentStep_wellFounded hwf S).induction with
  | _ m₀ ih =>
    by_cases h : ∃ n, DescentStep E S n m₀
    · obtain ⟨n, hn⟩ := h
      obtain ⟨m, hmn, hm⟩ := ih n hn
      exact ⟨m, hmn.tail hn, hm⟩
    · push Not at h
      exact ⟨m₀, .refl, hE.isGlobalMin_of_not_descentStep hS h⟩

/-- The midpoint argument: two global minimizers congruent modulo `2L` coincide, when
`B(x,x) > 0` for every nonzero `x`. -/
theorem eq_of_sub_eq_two_nsmul (hE : IsQuadraticEnergy B E) (hpos : ∀ x ≠ 0, 0 < B x x)
    {m n w : L} (hm : ∀ l, E m ≤ E l) (hn : ∀ l, E n ≤ E l) (hw : n - m = 2 • w) : m = n := by
  by_contra hne
  have hw0 : w ≠ 0 := by
    rintro rfl
    rw [smul_zero, sub_eq_zero] at hw
    exact hne hw.symm
  have h0 : incr E m (2 • w) = 0 := by
    rw [← hw]
    unfold incr
    rw [add_sub_cancel]
    exact sub_eq_zero.mpr (le_antisymm (hn m) (hm n))
  rw [hE.incr_nsmul, Nat.choose_self, one_smul] at h0
  have h1 : 0 ≤ incr E m w := sub_nonneg.mpr (hm (m + w))
  have h2 : 0 < 2 • incr E m w + B w w := add_pos_of_nonneg_of_pos (nsmul_nonneg h1 2) (hpos w hw0)
  exact h2.ne' h0

section Minimizers

variable [Module.Free ℤ L] [Module.Finite ℤ L]

/-- Reduction modulo `2L`, in the coordinates of a basis, is injective on the minimizers. -/
theorem injOn_parity (hE : IsQuadraticEnergy B E) (hpos : ∀ x ≠ 0, 0 < B x x) :
    Set.InjOn (fun m i => ((Module.Free.chooseBasis ℤ L).equivFun m i : ZMod 2))
      {m | ∀ l, E m ≤ E l} := by
  intro m hm n hn hmn
  set bL := Module.Free.chooseBasis ℤ L
  have hdvd : ∀ i, (2 : ℤ) ∣ bL.equivFun (n - m) i := by
    intro i
    have h := congrFun hmn i
    simp only at h
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h
    simpa [map_sub] using h
  refine hE.eq_of_sub_eq_two_nsmul hpos hm hn
    (w := bL.equivFun.symm fun i => bL.equivFun (n - m) i / 2) ?_
  apply bL.equivFun.injective
  ext i
  rw [map_nsmul, LinearEquiv.apply_symm_apply, Pi.smul_apply, nsmul_eq_mul, Nat.cast_ofNat,
    Int.mul_ediv_cancel' (hdvd i)]

/-- `tate:theta:thm:minimizers`, the count: any finite set of global minimizers of an energy
on `L ≅ ℤ^g` has at most `2^g` elements. -/
theorem card_le_two_pow_finrank (hE : IsQuadraticEnergy B E) (hpos : ∀ x ≠ 0, 0 < B x x)
    (M : Finset L) (hM : ∀ m ∈ M, ∀ l, E m ≤ E l) : M.card ≤ 2 ^ Module.finrank ℤ L := by
  classical
  calc M.card ≤ (univ : Finset (Module.Free.ChooseBasisIndex ℤ L → ZMod 2)).card :=
        card_le_card_of_injOn _ (fun _ _ => mem_univ _)
          ((hE.injOn_parity hpos).mono fun m hm => hM m hm)
    _ = 2 ^ Module.finrank ℤ L := by
        rw [card_univ, Fintype.card_fun, ZMod.card, Module.finrank_eq_card_chooseBasisIndex]

/-- `tate:theta:thm:minimizers`, the count: the set of global minimizers is finite with at most
`2^g` elements. -/
theorem finite_minimizers (hE : IsQuadraticEnergy B E) (hpos : ∀ x ≠ 0, 0 < B x x) :
    {m | ∀ l, E m ≤ E l}.Finite ∧ {m | ∀ l, E m ≤ E l}.ncard ≤ 2 ^ Module.finrank ℤ L := by
  have hfin : {m | ∀ l, E m ≤ E l}.Finite :=
    Set.Finite.of_finite_image (Set.toFinite _) (hE.injOn_parity hpos)
  refine ⟨hfin, ?_⟩
  rw [Set.ncard_eq_toFinset_card _ hfin]
  exact hE.card_le_two_pow_finrank hpos _ fun m hm => (hfin.mem_toFinset.mp hm)

omit [Module.Free ℤ L] in
/-- `tate:theta:thm:minimizers`, the geometry: for global minimizers `m, n`, the displacement
`n - m` is the sum of a set of at most `g` pairwise `B`-orthogonal members of `S`, and every
partial sum, added to `m`, is a global minimizer. -/
theorem exists_orthogonal_decomposition (hE : IsQuadraticEnergy B E) {S : Finset L}
    (hS : PositivelyGenerates B S) (hpos : ∀ x ≠ 0, 0 < B x x) {m n : L}
    (hm : ∀ l, E m ≤ E l) (hn : ∀ l, E n ≤ E l) :
    ∃ A ⊆ S, A.card ≤ Module.finrank ℤ L ∧ (∀ a ∈ A, ∀ a' ∈ A, a ≠ a' → B a a' = 0) ∧
      n - m = ∑ a ∈ A, a ∧ ∀ A' ⊆ A, ∀ l, E (m + ∑ a ∈ A', a) ≤ E l := by
  classical
  letI : LinearOrder L := IsWellOrder.linearOrder WellOrderingRel
  obtain ⟨A, hAS, c, hcpos, hApos, hdec⟩ := hS.2 (n - m)
  have hdecomp := hE.incr_sum m A (fun a => a) c
  rw [← hdec] at hdecomp
  have hLHS : incr E m (n - m) = 0 := by
    unfold incr
    rw [add_sub_cancel, sub_eq_zero]
    exact le_antisymm (hn m) (hm n)
  have h1 : 0 ≤ ∑ a ∈ A, c a • incr E m a :=
    sum_nonneg fun a _ => nsmul_nonneg (sub_nonneg.mpr (hm _)) _
  have h2 : 0 ≤ ∑ a ∈ A, (c a).choose 2 • B a a :=
    sum_nonneg fun a ha => nsmul_nonneg (hApos a ha a ha) _
  have h3 : 0 ≤ ∑ a ∈ A, ∑ a' ∈ A with a < a', (c a * c a') • B a a' :=
    sum_nonneg fun a ha => sum_nonneg fun a' ha' =>
      nsmul_nonneg (hApos a ha a' (mem_filter.mp ha').1) _
  rw [hLHS] at hdecomp
  obtain ⟨h12, h3z⟩ := (add_eq_zero_iff_of_nonneg (add_nonneg h1 h2) h3).mp hdecomp.symm
  obtain ⟨h1z, h2z⟩ := (add_eq_zero_iff_of_nonneg h1 h2).mp h12
  have hne0 : ∀ a ∈ A, a ≠ 0 := fun a ha h => hS.1 (h ▸ hAS ha)
  have hc1 : ∀ a ∈ A, c a = 1 := by
    intro a ha
    have h := (sum_eq_zero_iff_of_nonneg fun a ha => nsmul_nonneg (hApos a ha a ha) _).mp
      h2z a ha
    rw [nsmul_eq_zero_iff_left (hpos a (hne0 a ha)).ne', Nat.choose_eq_zero_iff] at h
    have := hcpos a ha
    omega
  have horth : ∀ a ∈ A, ∀ a' ∈ A, a ≠ a' → B a a' = 0 := by
    have key : ∀ a ∈ A, ∀ a' ∈ A, a < a' → B a a' = 0 := by
      intro a ha a' ha' hlt
      have hin := (sum_eq_zero_iff_of_nonneg fun a ha => sum_nonneg fun a' ha' =>
        nsmul_nonneg (hApos a ha a' (mem_filter.mp ha').1) _).mp h3z a ha
      have h := (sum_eq_zero_iff_of_nonneg fun a' ha' =>
        nsmul_nonneg (hApos a ha a' (mem_filter.mp ha').1) _).mp hin a'
          (mem_filter.mpr ⟨ha', hlt⟩)
      rwa [hc1 a ha, hc1 a' ha', one_mul, one_smul] at h
    intro a ha a' ha' hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact key a ha a' ha' h
    · rw [hE.symm]
      exact key a' ha' a ha h
  have hI0 : ∀ a ∈ A, incr E m a = 0 := by
    intro a ha
    have h := (sum_eq_zero_iff_of_nonneg fun a _ => nsmul_nonneg (sub_nonneg.mpr (hm _)) _).mp
      h1z a ha
    rwa [hc1 a ha, one_smul] at h
  refine ⟨A, hAS, ?_, horth, ?_, ?_⟩
  · have hli : LinearIndependent ℤ (fun x => x : A → L) := by
      rw [linearIndependent_iff']
      intro s g hg i hi
      have hBi := congrArg (B (i : L)) hg
      simp only [map_sum, map_zsmul] at hBi
      rw [map_zero (B (i : L))] at hBi
      rw [sum_eq_single i (fun j _ hji => by
          rw [horth i i.2 j j.2 (fun h => hji (Subtype.ext h.symm)), smul_zero])
        (fun h => absurd hi h)] at hBi
      exact (IsAddTorsionFree.zsmul_eq_zero_iff_left (hpos i (hne0 i i.2)).ne').mp hBi
    exact LinearIndependent.finset_card_le_finrank hli
  · rw [hdec]
    exact sum_congr rfl fun a ha => by rw [hc1 a ha, one_smul]
  · intro A' hA' l
    have hz : incr E m (∑ a ∈ A', a) = 0 := by
      have e : ∑ a ∈ A', a = ∑ a ∈ A', (fun _ => 1) a • (fun a => a) a := by simp
      rw [e, hE.incr_sum, sum_eq_zero fun a ha => by rw [hI0 a (hA' ha), smul_zero],
        sum_eq_zero fun a _ => by rw [Nat.choose_eq_zero_of_lt one_lt_two, zero_smul],
        sum_eq_zero fun a ha => sum_eq_zero fun a' ha' => by
          rw [horth a (hA' ha) a' (hA' (mem_filter.mp ha').1) (mem_filter.mp ha').2.ne,
            smul_zero]]
      simp
    unfold incr at hz
    rw [sub_eq_zero] at hz
    rw [hz]
    exact hm l

omit [Module.Free ℤ L] in
/-- `tate:theta:thm:minimizers`, connectivity and diameter: two global minimizers are joined by
a path of at most `g` forward `S`-moves all of whose vertices are global minimizers. -/
theorem exists_zero_cost_path (hE : IsQuadraticEnergy B E) {S : Finset L}
    (hS : PositivelyGenerates B S) (hpos : ∀ x ≠ 0, 0 < B x x) {m n : L}
    (hm : ∀ l, E m ≤ E l) (hn : ∀ l, E n ≤ E l) :
    ∃ p : List L, p.length ≤ Module.finrank ℤ L ∧ (∀ s ∈ p, s ∈ S) ∧ n = m + p.sum ∧
      ∀ k, ∀ l, E (m + (p.take k).sum) ≤ E l := by
  classical
  obtain ⟨A, hAS, hcard, -, hsum, hpart⟩ :=
    hE.exists_orthogonal_decomposition hS hpos hm hn
  refine ⟨A.toList, by rwa [length_toList], fun s hs => hAS (mem_toList.mp hs), ?_, ?_⟩
  · rw [sum_toList, ← hsum, add_sub_cancel]
  · intro k l
    have hnd : (A.toList.take k).Nodup := (nodup_toList A).sublist (List.take_sublist k _)
    have hsub : (A.toList.take k).toFinset ⊆ A := fun x hx =>
      mem_toList.mp (List.mem_of_mem_take (List.mem_toFinset.mp hx))
    have := hpart _ hsub l
    rwa [List.sum_toFinset _ hnd, List.map_id'] at this

end Minimizers

end IsQuadraticEnergy

/-- For `E(n) = B(n,n)/2 + b(n)`, written without division as `2 • E(n) = B(n,n) + 2 • b(n)`
(which determines `E`, since `Γ` is torsion free), the energy is quadratic with polar form
`B`. -/
theorem isQuadraticEnergy_of_two_nsmul (hB : ∀ x y, B x y = B y x) (b : L →+ Γ)
    (h2 : ∀ n, 2 • E n = B n n + 2 • b n) : IsQuadraticEnergy B E := by
  intro x y
  apply nsmul_right_injective (two_ne_zero : (2 : ℕ) ≠ 0)
  simp only [smul_add, h2, map_add, AddMonoidHom.add_apply, hB y x]
  abel

/-- The certificate quantity `tate:theta:eq:cert`, `I_m(s) = B(s,s)/2 + B(m,s) + b(s)`,
doubled. -/
theorem two_nsmul_incr (hB : ∀ x y, B x y = B y x) (b : L →+ Γ)
    (h2 : ∀ n, 2 • E n = B n n + 2 • b n) (m s : L) :
    2 • incr E m s = B s s + 2 • B m s + 2 • b s := by
  rw [(isQuadraticEnergy_of_two_nsmul hB b h2).incr_eq, smul_add, h2]
  abel

section Voronoi

variable {H : Type*} [AddCommGroup H]

/-- The higher-rank Voronoi cell `Vor_L(0)`: the points `x` with `B(x,x) ≤ B(x - l, x - l)`
for every lattice vector `l`, where `ι : L →+ H` is the inclusion of the lattice. The report
uses `Vor_L(0)` without defining it; this is the Amini–Nicolussi definition. -/
def voronoiCell (ι : L →+ H) (B : H →+ H →+ Γ) : Set H :=
  {x | ∀ l : L, B x x ≤ B (x - ι l) (x - ι l)}

/-- `tate:theta:cor:voronoi`: with `S` positively generating `L` for the restriction of `B`,
`x ∈ Vor_L(0)` if and only if `2 B(x,s) ≤ B(s,s)` for every `s ∈ S`. -/
theorem mem_voronoiCell_iff (ι : L →+ H) (B : H →+ H →+ Γ) (hB : ∀ x y, B x y = B y x)
    {S : Finset L} (hS : PositivelyGenerates ((B.compl₂ ι).comp ι) S) (x : H) :
    x ∈ voronoiCell ι B ↔ ∀ s ∈ S, 2 • B x (ι s) ≤ B (ι s) (ι s) := by
  set R : L →+ L →+ Γ := (B.compl₂ ι).comp ι with hR
  have hRapp : ∀ a a', R a a' = B (ι a) (ι a') := fun _ _ => rfl
  set F : L → Γ := fun l => B (ι l) (ι l) - 2 • B x (ι l) with hF
  have hF2 : IsQuadraticEnergy (2 • R) F := by
    intro a a'
    simp only [hF, AddMonoidHom.nsmul_apply, hRapp, map_add, AddMonoidHom.add_apply,
      hB (ι a') (ι a)]
    abel
  have hS2 : PositivelyGenerates (2 • R) S := by
    refine ⟨hS.1, fun y => ?_⟩
    obtain ⟨A, hAS, c, hc, hApos, hy⟩ := hS.2 y
    exact ⟨A, hAS, c, hc, fun a ha a' ha' => by
      simpa only [AddMonoidHom.nsmul_apply] using nsmul_nonneg (hApos a ha a' ha') 2, hy⟩
  have hF0 : F 0 = 0 := hF2.energy_zero
  have key : ∀ l, B (x - ι l) (x - ι l) = B x x + F l := by
    intro l
    simp only [hF, map_sub, AddMonoidHom.sub_apply, hB (ι l) x, two_nsmul]
    abel
  have hcert := hF2.isGlobalMin_iff hS2 0
  simp only [hF0, incr, zero_add, sub_zero] at hcert
  simp only [voronoiCell, Set.mem_setOf_eq, key, le_add_iff_nonneg_right]
  rw [hcert]
  simp only [hF, sub_nonneg]

end Voronoi

end Order

section HigherRank

variable {r : ℕ} {H : Type*} [AddCommGroup H] [Module ℝ H]

/-- The radical `{x ∈ W | β(x, W) = 0}` of the restriction of `β` to `W`. -/
def radical (β : H →ₗ[ℝ] H →ₗ[ℝ] ℝ) (W : Submodule ℝ H) : Submodule ℝ H where
  carrier := {x | x ∈ W ∧ ∀ y ∈ W, β x y = 0}
  add_mem' := fun {a b} ha hb =>
    ⟨W.add_mem ha.1 hb.1, fun y hy => by simp [ha.2 y hy, hb.2 y hy]⟩
  zero_mem' := ⟨W.zero_mem, fun y _ => by simp⟩
  smul_mem' := fun c x hx => ⟨W.smul_mem c hx.1, fun y hy => by simp [hx.2 y hy]⟩

/-- The radical flag `tate:theta:eq:flag` of a higher-rank form `(𝓑₁, …, 𝓑ᵣ)`, where
`𝓑_{j+1}` is written `B j` for `j : Fin r`: `V₀ = H` and `V_{j+1} = rad(𝓑_{j+1}|V_j)`.
Stages past `r` repeat `V_r`. -/
def flag (B : Fin r → H →ₗ[ℝ] H →ₗ[ℝ] ℝ) : ℕ → Submodule ℝ H
  | 0 => ⊤
  | j + 1 => if h : j < r then radical (B ⟨j, h⟩) (flag B j) else flag B j

/-- `tate:theta:def:admissible`: `𝓑` is a symmetric real-bilinear map to `ℝ^r_lex`, each
`𝓑_{j+1}` is positive semidefinite on `V_j`, satisfies the global radical condition
`𝓑_{j+1}(V_{j+1}, H) = 0` (`tate:theta:eq:globalradical`), every `V_j` with `0 ≤ j ≤ r` is
rational with respect to `L` (`span_ℝ (L ∩ V_j) = V_j`; for `j = 0` this is the standing
full-lattice assumption `span_ℝ L = H`), and `V_r = 0`. -/
structure IsANAdmissible (B : Fin r → H →ₗ[ℝ] H →ₗ[ℝ] ℝ) (L : AddSubgroup H) : Prop where
  symm : ∀ j x y, B j x y = B j y x
  psd : ∀ j : Fin r, ∀ x ∈ flag B j, 0 ≤ B j x x
  global_radical : ∀ j : Fin r, ∀ x ∈ flag B (j + 1), ∀ y, B j x y = 0
  rational : ∀ j ≤ r, Submodule.span ℝ {x | x ∈ L ∧ x ∈ flag B j} = flag B j
  terminal : flag B r = ⊥

/-- The lexicographic form `𝓑 : H × H → ℝ^r_lex`. -/
def lexForm (B : Fin r → H →ₗ[ℝ] H →ₗ[ℝ] ℝ) : H →+ H →+ Lex (Fin r → ℝ) :=
  AddMonoidHom.mk'
    (fun x => AddMonoidHom.mk' (fun y => toLex fun j => B j x y) fun y y' => by
      simp only [map_add]
      rfl)
    fun x x' => by
      ext y
      simp only [map_add, LinearMap.add_apply, AddMonoidHom.mk'_apply, AddMonoidHom.add_apply]
      rfl

/-- The coordinates of `𝓑(x,y)` are `𝓑_j(x,y)`. -/
theorem lexForm_apply (B : Fin r → H →ₗ[ℝ] H →ₗ[ℝ] ℝ) (x y : H) :
    lexForm B x y = toLex fun j => B j x y := rfl

/-- The lexicographic quadratic energy `tate:theta:eq:lexenergy`,
`𝓔_j(n) = 𝓑_j(n,n)/2 + b_j(n)`. -/
noncomputable def lexEnergy (B : Fin r → H →ₗ[ℝ] H →ₗ[ℝ] ℝ) (b : Fin r → H →ₗ[ℝ] ℝ) (n : H) :
    Lex (Fin r → ℝ) :=
  toLex fun j => B j n n / 2 + b j n

/-- The restriction of the lexicographic form to the lattice `L`. -/
def latticeForm (B : Fin r → H →ₗ[ℝ] H →ₗ[ℝ] ℝ) (L : AddSubgroup H) :
    L →+ L →+ Lex (Fin r → ℝ) :=
  ((lexForm B).compl₂ L.subtype).comp L.subtype

/-- The compatibility condition `tate:theta:eq:linearcompatibility`, `b_j(V_j) = 0`. -/
def IsCompatible (B : Fin r → H →ₗ[ℝ] H →ₗ[ℝ] ℝ) (b : Fin r → H →ₗ[ℝ] ℝ) : Prop :=
  ∀ j : Fin r, ∀ x ∈ flag B (j + 1), b j x = 0

variable {B : Fin r → H →ₗ[ℝ] H →ₗ[ℝ] ℝ} {L : AddSubgroup H}

/-- The flag is decreasing. -/
theorem flag_succ_le (j : ℕ) : flag B (j + 1) ≤ flag B j := by
  intro x hx
  simp only [flag] at hx
  split_ifs at hx with h
  · exact hx.1
  · exact hx

/-- Later stages of the flag are contained in earlier ones. -/
theorem flag_antitone {i j : ℕ} (hij : i ≤ j) : flag B j ≤ flag B i := by
  induction hij with
  | refl => exact le_rfl
  | step _ ih => exact (flag_succ_le _).trans ih

/-- A positive semidefinite symmetric form vanishes against any isotropic vector. -/
theorem apply_eq_zero_of_psd (β : H →ₗ[ℝ] H →ₗ[ℝ] ℝ) (hsymm : ∀ x y, β x y = β y x)
    (W : Submodule ℝ H) (hpsd : ∀ z ∈ W, 0 ≤ β z z) {x y : H} (hx : x ∈ W) (hy : y ∈ W)
    (hxx : β x x = 0) : β x y = 0 := by
  have h : ∀ t : ℝ, 0 ≤ β y y * (t * t) + (2 * β x y) * t + 0 := by
    intro t
    have := hpsd (x + t • y) (W.add_mem hx (W.smul_mem t hy))
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      hxx, hsymm y x] at this
    linarith
  have hd := discrim_le_zero h
  rw [discrim] at hd
  have hsq : β x y ^ 2 ≤ 0 := by nlinarith
  exact pow_eq_zero_iff two_ne_zero |>.mp (le_antisymm hsq (sq_nonneg _))

/-- `tate:theta:eq:firstlevel`: for an AN-admissible form and `x ≠ 0` with first active level
`j`, `𝓑_i(x, H) = 0` for `i < j` and `𝓑_j(x,x) > 0`. -/
theorem exists_firstLevel (hB : IsANAdmissible B L) {x : H} (hx : x ≠ 0) :
    ∃ j : Fin r, (∀ i < j, ∀ y, B i x y = 0) ∧ 0 < B j x x := by
  classical
  have hex : ∃ k, x ∉ flag B k := ⟨r, by rw [hB.terminal]; exact hx⟩
  set k := Nat.find hex with hk
  have hkx : x ∉ flag B k := Nat.find_spec hex
  have hk0 : k ≠ 0 := by
    intro h
    rw [h] at hkx
    exact hkx (by simp [flag])
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  have hxj : x ∈ flag B j := by
    by_contra h
    exact Nat.find_min hex (by omega : j < k) h
  rw [hj] at hkx
  have hjr : j < r := by
    by_contra h
    simp only [flag, dif_neg h] at hkx
    exact hkx hxj
  set jj : Fin r := ⟨j, hjr⟩
  have hkx' : ¬ (x ∈ flag B j ∧ ∀ y ∈ flag B j, B jj x y = 0) := by
    simpa [flag, dif_pos hjr, radical] using hkx
  have hpos : 0 < B jj x x := by
    refine lt_of_le_of_ne (hB.psd jj x hxj) (fun h => hkx' ⟨hxj, fun y hy => ?_⟩)
    exact apply_eq_zero_of_psd (B jj) (hB.symm jj) _ (hB.psd jj) hxj hy h.symm
  refine ⟨jj, fun i hi y => ?_, hpos⟩
  have hxi : x ∈ flag B (i + 1) := flag_antitone (show (i : ℕ) + 1 ≤ j from hi) hxj
  exact hB.global_radical i x hxi y

/-- The consequence of `tate:theta:eq:firstlevel`: `𝓑(x,x) > 0` lexicographically for every
nonzero `x`. -/
theorem lexForm_pos (hB : IsANAdmissible B L) {x : H} (hx : x ≠ 0) : 0 < lexForm B x x := by
  obtain ⟨j, hlow, hpos⟩ := exists_firstLevel hB hx
  exact ⟨j, fun i hi => (hlow i hi x).symm, hpos⟩

/-- The quadratic energy `n ↦ 𝓔(n)` on the lattice `L`. -/
noncomputable def latticeEnergy (B : Fin r → H →ₗ[ℝ] H →ₗ[ℝ] ℝ) (b : Fin r → H →ₗ[ℝ] ℝ)
    (L : AddSubgroup H) (n : L) : Lex (Fin r → ℝ) :=
  lexEnergy B b n

/-- The lattice form is the restriction of `𝓑`. -/
theorem latticeForm_apply (x y : L) : latticeForm B L x y = lexForm B x y := rfl

/-- The lattice energy `𝓔(n) = 𝓑(n,n)/2 + b(n)` is quadratic with polar form `𝓑`. -/
theorem isQuadraticEnergy_latticeEnergy (hsymm : ∀ j x y, B j x y = B j y x)
    (b : Fin r → H →ₗ[ℝ] ℝ) : IsQuadraticEnergy (latticeForm B L) (latticeEnergy B b L) := by
  intro x y
  show (toLex fun j => B j ↑(x + y) ↑(x + y) / 2 + b j ↑(x + y)) =
    (toLex fun j => B j x x / 2 + b j x) + (toLex fun j => B j y y / 2 + b j y) +
      toLex fun j => B j x y
  rw [← toLex_add, ← toLex_add]
  congr 1
  funext j
  simp only [AddSubgroup.coe_add, map_add, LinearMap.add_apply, Pi.add_apply, hsymm j y x]
  ring

/-- `𝓑(x,x) > 0` for every nonzero lattice vector. -/
theorem latticeForm_pos (hB : IsANAdmissible B L) {x : L} (hx : x ≠ 0) :
    0 < latticeForm B L x x :=
  lexForm_pos hB fun h => hx (Subtype.ext h)

/-- The certificate quantity `tate:theta:eq:cert`,
`I_m(s) = 𝓑(s,s)/2 + 𝓑(m,s) + b(s)`, coordinatewise in `ℝ^r_lex`. -/
theorem incr_latticeEnergy (hsymm : ∀ j x y, B j x y = B j y x) (b : Fin r → H →ₗ[ℝ] ℝ)
    (m s : L) :
    incr (latticeEnergy B b L) m s = toLex fun j => B j s s / 2 + B j m s + b j s := by
  rw [(isQuadraticEnergy_latticeEnergy hsymm b).incr_eq]
  show (toLex fun j => B j s s / 2 + b j s) + (toLex fun j => B j m s) = _
  rw [← toLex_add]
  congr 1
  funext j
  simp only [Pi.add_apply]
  ring

/-- `tate:theta:eq:energydecomp` for the lexicographic lattice energy. -/
theorem incr_latticeEnergy_sum (hsymm : ∀ j x y, B j x y = B j y x) (b : Fin r → H →ₗ[ℝ] ℝ)
    {ι : Type*} [LinearOrder ι] (m : L) (A : Finset ι) (v : ι → L) (a : ι → ℕ) :
    incr (latticeEnergy B b L) m (∑ i ∈ A, a i • v i) =
      ∑ i ∈ A, a i • incr (latticeEnergy B b L) m (v i) +
        ∑ i ∈ A, (a i).choose 2 • latticeForm B L (v i) (v i) +
          ∑ i ∈ A, ∑ k ∈ A with i < k, (a i * a k) • latticeForm B L (v i) (v k) :=
  (isQuadraticEnergy_latticeEnergy hsymm b).incr_sum m A v a

/-- The proof of `tate:theta:cor:domain`: if the compatibility condition fails, some lattice
vector `a` lowers the energy of every point, `𝓔(n + a) < 𝓔(n)`. -/
theorem exists_forall_lexEnergy_lt (hB : IsANAdmissible B L) {b : Fin r → H →ₗ[ℝ] ℝ}
    (hb : ¬ IsCompatible B b) : ∃ a ∈ L, ∀ n : H, lexEnergy B b (n + a) < lexEnergy B b n := by
  classical
  have hne : (univ.filter fun j : Fin r => ∃ x ∈ flag B (j + 1), b j x ≠ 0).Nonempty := by
    unfold IsCompatible at hb
    push Not at hb
    obtain ⟨j, x, hx, hbx⟩ := hb
    exact ⟨j, mem_filter.mpr ⟨mem_univ _, x, hx, hbx⟩⟩
  set j := (univ.filter fun j : Fin r => ∃ x ∈ flag B (j + 1), b j x ≠ 0).min' hne with hj
  have hjmem := (mem_filter.mp (min'_mem _ hne)).2
  rw [← hj] at hjmem
  have hmin : ∀ i : Fin r, i < j → ∀ x ∈ flag B (i + 1), b i x = 0 := by
    intro i hi x hx
    by_contra h
    exact absurd (min'_le _ i (mem_filter.mpr ⟨mem_univ _, x, hx, h⟩)) (not_le.mpr hi)
  have hlat : ∃ a ∈ L, a ∈ flag B (j + 1) ∧ b j a ≠ 0 := by
    by_contra h
    push Not at h
    obtain ⟨x, hx, hbx⟩ := hjmem
    have hle : Submodule.span ℝ {x | x ∈ L ∧ x ∈ flag B (j + 1)} ≤ LinearMap.ker (b j) :=
      Submodule.span_le.mpr fun y hy => h y hy.1 hy.2
    rw [hB.rational (j + 1) j.2] at hle
    exact hbx (hle hx)
  obtain ⟨a₀, ha₀L, ha₀V, hba₀⟩ := hlat
  obtain ⟨a, haL, haV, hba⟩ : ∃ a ∈ L, a ∈ flag B (j + 1) ∧ b j a < 0 := by
    rcases lt_or_gt_of_ne hba₀ with h | h
    · exact ⟨a₀, ha₀L, ha₀V, h⟩
    · exact ⟨-a₀, L.neg_mem ha₀L, (flag B _).neg_mem ha₀V, by simpa using h⟩
  refine ⟨a, haL, fun n => ?_⟩
  have hsub : ∀ i : Fin r, i ≤ j → a ∈ flag B (i + 1) := fun i hi =>
    flag_antitone (show (i : ℕ) + 1 ≤ j + 1 from Nat.succ_le_succ hi) haV
  have hcoord : ∀ i : Fin r, i ≤ j →
      B i (n + a) (n + a) / 2 + b i (n + a) = (B i n n / 2 + b i n) + b i a := by
    intro i hi
    have h1 := hB.global_radical i a (hsub i hi) a
    have h2 := hB.global_radical i a (hsub i hi) n
    have h3 : B i n a = 0 := by rw [hB.symm]; exact h2
    simp only [map_add, LinearMap.add_apply, h1, h2, h3]
    ring
  refine ⟨j, fun i hi => ?_, ?_⟩
  · show B i (n + a) (n + a) / 2 + b i (n + a) = B i n n / 2 + b i n
    rw [hcoord i hi.le, hmin i hi a (hsub i hi.le), add_zero]
  · show B j (n + a) (n + a) / 2 + b j (n + a) < B j n n / 2 + b j n
    rw [hcoord j le_rfl]
    linarith

/-- `tate:theta:thm:certificate`, the finite test: for an AN-admissible form, any linear term
and any positively generating set `S`, a lattice vector is a global minimizer of `𝓔` if and
only if `I_m(s) ≥ 0` for every `s ∈ S`. -/
theorem certificate_iff (hB : IsANAdmissible B L) (b : Fin r → H →ₗ[ℝ] ℝ) {S : Finset L}
    (hS : PositivelyGenerates (latticeForm B L) S) (m : L) :
    (∀ n, latticeEnergy B b L m ≤ latticeEnergy B b L n) ↔
      ∀ s ∈ S, (0 : Lex (Fin r → ℝ)) ≤ toLex fun j => B j s s / 2 + B j m s + b j s := by
  rw [(isQuadraticEnergy_latticeEnergy hB.symm b).isGlobalMin_iff hS m]
  simp only [incr_latticeEnergy hB.symm]

/-- `tate:theta:thm:certificate`, incompatible linear terms: then no lattice vector passes
the finite test (and there is no global minimum). -/
theorem certificate_fails_of_not_compatible (hB : IsANAdmissible B L)
    {b : Fin r → H →ₗ[ℝ] ℝ} (hb : ¬ IsCompatible B b) {S : Finset L}
    (hS : PositivelyGenerates (latticeForm B L) S) (m : L) :
    (¬ ∀ n, latticeEnergy B b L m ≤ latticeEnergy B b L n) ∧
      ∃ s ∈ S, incr (latticeEnergy B b L) m s < 0 := by
  obtain ⟨a, haL, ha⟩ := exists_forall_lexEnergy_lt hB hb
  have hnot : ¬ ∀ n, latticeEnergy B b L m ≤ latticeEnergy B b L n := by
    intro h
    have h' : lexEnergy B b m ≤ lexEnergy B b (m + a) := h (m + (⟨a, haL⟩ : L))
    exact (ha m).not_ge h'
  refine ⟨hnot, ?_⟩
  rw [(isQuadraticEnergy_latticeEnergy hB.symm b).isGlobalMin_iff hS m] at hnot
  by_contra hcon
  exact hnot fun s hs => not_lt.mp fun hlt => hcon ⟨s, hs, hlt⟩

/-- `tate:theta:thm:certificate`, termination of the descent search: whenever `𝓔(L)` is well
ordered (which `tate:theta:thm:flag`, not formalized here, derives from compatibility), every
descent search terminates, from every start some descent chain reaches a global minimum in
finitely many steps, and every point admitting no descent step is a global minimum, so a
search ends at a global minimum however its moves are chosen. -/
theorem certificate_descent (hB : IsANAdmissible B L) (b : Fin r → H →ₗ[ℝ] ℝ) {S : Finset L}
    (hS : PositivelyGenerates (latticeForm B L) S)
    (hwf : (Set.range (latticeEnergy B b L)).IsWF) :
    WellFounded (DescentStep (latticeEnergy B b L) S) ∧
      (∀ m₀, ∃ m, Relation.ReflTransGen (DescentStep (latticeEnergy B b L) S) m m₀ ∧
        ∀ n, latticeEnergy B b L m ≤ latticeEnergy B b L n) ∧
      ∀ m, (∀ n, ¬ DescentStep (latticeEnergy B b L) S n m) →
        ∀ n, latticeEnergy B b L m ≤ latticeEnergy B b L n :=
  ⟨descentStep_wellFounded hwf S,
    (isQuadraticEnergy_latticeEnergy hB.symm b).exists_descent_isGlobalMin hS hwf,
    fun _ hm => (isQuadraticEnergy_latticeEnergy hB.symm b).isGlobalMin_of_not_descentStep hS hm⟩

/-- `tate:theta:cor:voronoi`: `x ∈ Vor_L(0)` if and only if `2𝓑(x,s) ≤ 𝓑(s,s)`
lexicographically for every `s ∈ S`. -/
theorem mem_voronoiCell_iff_of_admissible (hB : IsANAdmissible B L) {S : Finset L}
    (hS : PositivelyGenerates (latticeForm B L) S) (x : H) :
    x ∈ voronoiCell L.subtype (lexForm B) ↔
      ∀ s ∈ S, 2 • lexForm B x s ≤ lexForm B s s :=
  mem_voronoiCell_iff L.subtype (lexForm B)
    (fun x y => by rw [lexForm_apply, lexForm_apply]; congr 1; funext j; exact hB.symm j x y)
    hS x

section Minimizers

variable [Module.Free ℤ L] [Module.Finite ℤ L]

/-- `tate:theta:thm:minimizers`, the count: with `L ≅ ℤ^g`, the set of global minimizers of
`𝓔` is finite with at most `2^g` elements. -/
theorem minimizers_finite_ncard_le (hB : IsANAdmissible B L) (b : Fin r → H →ₗ[ℝ] ℝ) :
    {m | ∀ n, latticeEnergy B b L m ≤ latticeEnergy B b L n}.Finite ∧
      {m | ∀ n, latticeEnergy B b L m ≤ latticeEnergy B b L n}.ncard ≤
        2 ^ Module.finrank ℤ L :=
  (isQuadraticEnergy_latticeEnergy hB.symm b).finite_minimizers fun _ hx =>
    latticeForm_pos hB hx

omit [Module.Free ℤ L] in
/-- `tate:theta:thm:minimizers`, the geometry: for minimizers `m, n`, the displacement `n - m`
is a sum of at most `g` distinct pairwise `𝓑`-orthogonal members of `S`, every partial sum of
which, added to `m`, is a minimizer. -/
theorem minimizers_orthogonal (hB : IsANAdmissible B L) (b : Fin r → H →ₗ[ℝ] ℝ)
    {S : Finset L} (hS : PositivelyGenerates (latticeForm B L) S) {m n : L}
    (hm : ∀ l, latticeEnergy B b L m ≤ latticeEnergy B b L l)
    (hn : ∀ l, latticeEnergy B b L n ≤ latticeEnergy B b L l) :
    ∃ A ⊆ S, A.card ≤ Module.finrank ℤ L ∧
      (∀ a ∈ A, ∀ a' ∈ A, a ≠ a' → latticeForm B L a a' = 0) ∧ n - m = ∑ a ∈ A, a ∧
        ∀ A' ⊆ A, ∀ l, latticeEnergy B b L (m + ∑ a ∈ A', a) ≤ latticeEnergy B b L l :=
  (isQuadraticEnergy_latticeEnergy hB.symm b).exists_orthogonal_decomposition hS
    (fun _ hx => latticeForm_pos hB hx) hm hn

omit [Module.Free ℤ L] in
/-- `tate:theta:thm:minimizers`, connectivity and diameter: any two minimizers are joined by a
path of at most `g` forward `S`-moves through minimizers. -/
theorem minimizers_path (hB : IsANAdmissible B L) (b : Fin r → H →ₗ[ℝ] ℝ)
    {S : Finset L} (hS : PositivelyGenerates (latticeForm B L) S) {m n : L}
    (hm : ∀ l, latticeEnergy B b L m ≤ latticeEnergy B b L l)
    (hn : ∀ l, latticeEnergy B b L n ≤ latticeEnergy B b L l) :
    ∃ p : List L, p.length ≤ Module.finrank ℤ L ∧ (∀ s ∈ p, s ∈ S) ∧ n = m + p.sum ∧
      ∀ k, ∀ l, latticeEnergy B b L (m + (p.take k).sum) ≤ latticeEnergy B b L l :=
  (isQuadraticEnergy_latticeEnergy hB.symm b).exists_zero_cost_path hS
    (fun _ hx => latticeForm_pos hB hx) hm hn

end Minimizers

end HigherRank

end Surreal.LatticeEnergy
