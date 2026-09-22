import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Order.Disjointed
import Mathlib.Algebra.BigOperators.Finprod
import Surreal.HahnSeries.StrongMeasure

/-!
# Disjoint-finite scalar measures are finitely point-atomic

This file proves `lem:scalar` and `prop:coefficients` in
`docs/surreal/hahn-valued-measures-and-probability/article.tex`.

A scalar set function on a measurable space is *finsum-additive* if every
pairwise disjoint measurable sequence has only finitely many nonzero values, and
the value of the union is their finite sum. No topology on the scalars is used,
matching the source's disjoint-finiteness hypothesis. On a countably separated
space such a set function is a finite combination of point masses: it equals
`A ↦ ∑_{x ∈ F ∩ A} λ({x})` for the finite set `F` of points of nonzero mass, and
this representation is unique.

The proof replaces the quotient Boolean algebra of the source by a direct
bisection. After subtracting the finitely many point masses, a nonzero value
would give a set that is not hereditarily null. Splitting it successively along
the separating sets and keeping a non-hereditarily-null half sets aside disjoint
pieces; only finitely many can fail to be hereditarily null, so beyond some
stage the remaining set differs from the at most one-point intersection of the
chain by a hereditarily null set, a contradiction.

Every coefficient of a strong Hahn measure is finsum-additive, which gives
`prop:coefficients` on countably separated spaces.
-/

namespace Surreal.HahnSeries

open _root_.HahnSeries

noncomputable section

variable {X k : Type*} [MeasurableSpace X] [AddCommGroup k]

/-- Countable separation by measurable sets, as defined in the source. -/
def IsCountablySeparated (X : Type*) [MeasurableSpace X] : Prop :=
  ∃ E : ℕ → Set X, (∀ n, MeasurableSet (E n)) ∧ ∀ x y, (∀ n, x ∈ E n ↔ y ∈ E n) → x = y

/-- Countable additivity for disjoint-finite scalar set functions: a disjoint
measurable sequence has finitely many nonzero values, summing to the union. -/
def IsFinsumAdditive (lam : Set X → k) : Prop :=
  ∀ A : ℕ → Set X, (∀ n, MeasurableSet (A n)) → Pairwise (Function.onFun Disjoint A) →
    {n | lam (A n) ≠ 0}.Finite ∧ lam (⋃ n, A n) = ∑ᶠ n, lam (A n)

namespace IsFinsumAdditive

variable {lam mu : Set X → k}

theorem empty (h : IsFinsumAdditive lam) : lam ∅ = 0 := by
  by_contra h0
  have := (h (fun _ => ∅) (fun _ => MeasurableSet.empty) (fun _ _ _ => disjoint_bot_left)).1
  exact Set.infinite_univ (this.subset fun n _ => h0)

theorem union (h : IsFinsumAdditive lam) {A B : Set X} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hAB : Disjoint A B) : lam (A ∪ B) = lam A + lam B := by
  classical
  set s : ℕ → Set X := fun n => if n = 0 then A else if n = 1 then B else ∅ with hs
  have hmeas : ∀ n, MeasurableSet (s n) := fun n => by
    simp only [hs]
    split_ifs
    exacts [hA, hB, MeasurableSet.empty]
  have hdisj : Pairwise (Function.onFun Disjoint s) := by
    intro m n hmn
    simp only [Function.onFun, hs]
    split_ifs <;> first | omega | exact hAB | exact hAB.symm | simp
  have hU : (⋃ n, s n) = A ∪ B := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_union, hs]
    constructor
    · rintro ⟨n, hn⟩
      split_ifs at hn
      exacts [Or.inl hn, Or.inr hn, absurd hn (Set.notMem_empty x)]
    · rintro (hx | hx)
      · exact ⟨0, by simpa using hx⟩
      · exact ⟨1, by simpa using hx⟩
  have hsum := (h s hmeas hdisj).2
  rw [hU] at hsum
  rw [hsum, finsum_eq_sum_of_support_subset (s := {0, 1}) _ fun n hn => ?_]
  · simp [hs]
  · simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    by_contra hn'
    push Not at hn'
    simp only [Function.mem_support, hs, if_neg hn'.1, if_neg hn'.2] at hn
    exact hn h.empty

theorem diff (h : IsFinsumAdditive lam) {A B : Set X} (hA : MeasurableSet A)
    (hB : MeasurableSet B) : lam A = lam (A ∩ B) + lam (A \ B) := by
  rw [← h.union (hA.inter hB) (hA.diff hB) Set.disjoint_sdiff_inter.symm,
    Set.inter_union_sdiff]

theorem sub (hl : IsFinsumAdditive lam) (hm : IsFinsumAdditive mu) :
    IsFinsumAdditive (lam - mu) := by
  intro A hA hdisj
  obtain ⟨hl1, hl2⟩ := hl A hA hdisj
  obtain ⟨hm1, hm2⟩ := hm A hA hdisj
  refine ⟨(hl1.union hm1).subset fun n hn => ?_, ?_⟩
  · by_contra hnot
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hnot
    exact hn (by simp [hnot.1, hnot.2])
  · simp only [Pi.sub_apply, hl2, hm2]
    exact (finsum_sub_distrib hl1 hm1).symm

end IsFinsumAdditive

variable {lam : Set X → k}

/-- Singletons are measurable in a countably separated space. -/
theorem measurableSet_singleton_of_separated {E : ℕ → Set X} (hE : ∀ n, MeasurableSet (E n))
    (hsep : ∀ x y, (∀ n, x ∈ E n ↔ y ∈ E n) → x = y) (x : X) : MeasurableSet ({x} : Set X) := by
  classical
  have : ({x} : Set X) = ⋂ n, if x ∈ E n then E n else (E n)ᶜ := by
    ext y
    simp only [Set.mem_singleton_iff, Set.mem_iInter]
    constructor
    · rintro rfl n
      split_ifs with h
      exacts [h, h]
    · intro hy
      refine hsep y x fun n => ?_
      have := hy n
      split_ifs at this with h
      · exact ⟨fun _ => h, fun _ => this⟩
      · exact ⟨fun hy' => absurd hy' this, fun hx => absurd hx h⟩
  rw [this]
  exact MeasurableSet.iInter fun n => by split_ifs; exacts [hE n, (hE n).compl]

/-- Only finitely many points carry a nonzero mass. -/
theorem finite_setOf_singleton_ne_zero (h : IsFinsumAdditive lam)
    (hsing : ∀ x : X, MeasurableSet ({x} : Set X)) : {x | lam {x} ≠ 0}.Finite := by
  by_contra hinf
  let e := Set.Infinite.natEmbedding _ hinf
  have hdisj : Pairwise (Function.onFun Disjoint fun n => ({(e n).1} : Set X)) := by
    intro m n hmn
    exact Set.disjoint_singleton.mpr fun h => hmn (e.injective (Subtype.ext h))
  have := (h (fun n => {(e n).1}) (fun n => hsing _) hdisj).1
  exact Set.infinite_univ (this.subset fun n _ => (e n).2)

/-- The finite atomic set function with prescribed masses. -/
def finiteAtomic (F : Finset X) (c : X → k) (A : Set X) : k := by
  classical
  exact ∑ x ∈ F.filter (· ∈ A), c x

theorem isFinsumAdditive_finiteAtomic (F : Finset X) (c : X → k) :
    IsFinsumAdditive (finiteAtomic F c) := by
  classical
  intro A _ hdisj
  have hsub : ∀ x : X, {n | x ∈ A n}.Subsingleton := fun x m hm n hn => by
    by_contra hmn
    exact Set.disjoint_left.mp (hdisj hmn) hm hn
  refine ⟨((F.finite_toSet.biUnion fun x _ => (hsub x).finite)).subset fun n hn => ?_, ?_⟩
  · by_contra hnot
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Finset.mem_coe, exists_prop, not_exists,
      not_and] at hnot
    apply hn
    simp only [finiteAtomic]
    exact Finset.sum_eq_zero fun x hx => absurd (Finset.mem_filter.mp hx).2
      (hnot x (Finset.mem_filter.mp hx).1)
  · simp only [finiteAtomic, Finset.sum_filter]
    rw [finsum_sum_comm]
    · refine Finset.sum_congr rfl fun x _ => ?_
      by_cases hx : x ∈ ⋃ n, A n
      · obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
        rw [if_pos hx, finsum_eq_single (fun a => if x ∈ A a then c x else 0) n
          fun m hm => if_neg fun hm' => hm (hsub x hm' hn), if_pos hn]
      · rw [if_neg hx]
        exact (finsum_eq_zero_of_forall_eq_zero fun n => if_neg fun hn =>
          hx (Set.mem_iUnion.mpr ⟨n, hn⟩)).symm
    · intro x _
      exact (hsub x).finite.subset fun n hn => by
        by_contra h'
        exact hn (if_neg h')

/-- A set is hereditarily null if every measurable subset has value zero. -/
def HereditarilyNull (lam : Set X → k) (B : Set X) : Prop :=
  ∀ C, MeasurableSet C → C ⊆ B → lam C = 0

/-- Hereditarily null measurable sets form a σ-ideal. -/
theorem hereditarilyNull_iUnion (h : IsFinsumAdditive lam) {B : ℕ → Set X}
    (hB : ∀ n, MeasurableSet (B n)) (hnull : ∀ n, HereditarilyNull lam (B n)) :
    HereditarilyNull lam (⋃ n, B n) := by
  intro C hC hCB
  have hpieces : ∀ n, MeasurableSet (C ∩ disjointed B n) := fun n =>
    hC.inter (MeasurableSet.disjointed hB n)
  have hdisj : Pairwise (Function.onFun Disjoint fun n => C ∩ disjointed B n) :=
    fun m n hmn => ((disjoint_disjointed B hmn).mono inf_le_right inf_le_right)
  have hU : (⋃ n, C ∩ disjointed B n) = C := by
    rw [← Set.inter_iUnion, iUnion_disjointed, Set.inter_eq_left.mpr hCB]
  have := (h _ hpieces hdisj).2
  rw [hU] at this
  rw [this]
  exact finsum_eq_zero_of_forall_eq_zero fun n =>
    hnull n _ (hpieces n) (Set.inter_subset_right.trans (disjointed_subset B n))

/-- The core of `lem:scalar`: a finsum-additive set function vanishing on points of
a countably separated space vanishes on every measurable set. -/
theorem eq_zero_of_singleton_eq_zero (h : IsFinsumAdditive lam) (hX : IsCountablySeparated X)
    (hpt : ∀ x, lam {x} = 0) {A : Set X} (hA : MeasurableSet A) : lam A = 0 := by
  classical
  obtain ⟨E, hE, hsep⟩ := hX
  have hsing := measurableSet_singleton_of_separated hE hsep
  by_contra hA0
  -- Sets that are measurable and not hereditarily null.
  let G := {B : Set X // MeasurableSet B ∧ ¬ HereditarilyNull lam B}
  have hstep : ∀ (B : G) (n : ℕ), ∃ B' : G, (B'.1 = B.1 ∩ E n ∨ B'.1 = B.1 \ E n) := by
    intro B n
    by_cases h1 : HereditarilyNull lam (B.1 ∩ E n)
    · refine ⟨⟨B.1 \ E n, B.2.1.diff (hE n), fun h2 => B.2.2 ?_⟩, Or.inr rfl⟩
      have hU := hereditarilyNull_iUnion h (B := fun m => if m = 0 then B.1 ∩ E n else B.1 \ E n)
        (fun m => by split_ifs; exacts [B.2.1.inter (hE n), B.2.1.diff (hE n)])
        (fun m => by split_ifs; exacts [h1, h2])
      intro C hC hCB
      refine hU C hC fun x hx => ?_
      by_cases hxE : x ∈ E n
      · exact Set.mem_iUnion.mpr ⟨0, by simp [hCB hx, hxE]⟩
      · exact Set.mem_iUnion.mpr ⟨1, by simp [hCB hx, hxE]⟩
    · exact ⟨⟨B.1 ∩ E n, B.2.1.inter (hE n), h1⟩, Or.inl rfl⟩
  choose step hstep using hstep
  let chain : ℕ → G := fun n => Nat.rec ⟨A, hA, fun hn => hA0 (hn A hA le_rfl)⟩
    (fun m B => step B m) n
  have hchain : ∀ n, (chain (n + 1)).1 = (chain n).1 ∩ E n ∨
      (chain (n + 1)).1 = (chain n).1 \ E n := fun n => hstep (chain n) n
  have hdec : ∀ n, (chain (n + 1)).1 ⊆ (chain n).1 := fun n => by
    rcases hchain n with h' | h' <;> rw [h']
    exacts [Set.inter_subset_left, Set.sdiff_subset]
  have hanti : ∀ m n, m ≤ n → (chain n).1 ⊆ (chain m).1 := by
    intro m n hmn
    induction hmn with
    | refl => exact le_rfl
    | step _ ih => exact (hdec _).trans ih
  -- The pieces set aside at each stage.
  let S : ℕ → Set X := fun n => (chain n).1 \ (chain (n + 1)).1
  have hSmeas : ∀ n, MeasurableSet (S n) := fun n => (chain n).2.1.diff (chain (n + 1)).2.1
  have hSdisj : Pairwise (Function.onFun Disjoint S) := by
    intro m n hmn
    wlog hlt : m < n generalizing m n
    · exact (this (m := n) (n := m) (Ne.symm hmn)
        (lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hmn))).symm
    refine Set.disjoint_left.mpr fun x hxm hxn => hxm.2 ?_
    exact hanti (m + 1) n hlt hxn.1
  -- Only finitely many pieces fail to be hereditarily null.
  have hfinS : {n | ¬ HereditarilyNull lam (S n)}.Finite := by
    have hchoice : ∀ n, ¬ HereditarilyNull lam (S n) →
        ∃ C, MeasurableSet C ∧ C ⊆ S n ∧ lam C ≠ 0 := fun n hn => by
      simpa [HereditarilyNull] using hn
    let C : ℕ → Set X := fun n => if hn : HereditarilyNull lam (S n) then ∅ else
      (hchoice n hn).choose
    have hCmeas : ∀ n, MeasurableSet (C n) := fun n => by
      simp only [C]
      split_ifs with hn
      exacts [MeasurableSet.empty, (hchoice n hn).choose_spec.1]
    have hCsub : ∀ n, C n ⊆ S n := fun n => by
      simp only [C]
      split_ifs with hn
      exacts [Set.empty_subset _, (hchoice n hn).choose_spec.2.1]
    have hCdisj : Pairwise (Function.onFun Disjoint C) := fun m n hmn =>
      (hSdisj hmn).mono (hCsub m) (hCsub n)
    refine (h C hCmeas hCdisj).1.subset fun n hn => ?_
    simp only [Set.mem_setOf_eq, C]
    rw [dif_neg hn]
    exact (hchoice n hn).choose_spec.2.2
  obtain ⟨N, hN⟩ := hfinS.bddAbove
  have hnullS : ∀ n, HereditarilyNull lam (S (n + (N + 1))) := fun n => by
    by_contra hn
    have := hN (show n + (N + 1) ∈ {n | ¬ HereditarilyNull lam (S n)} from hn)
    omega
  -- The intersection of the chain has at most one point.
  let I := ⋂ n, (chain n).1
  have hImeas : MeasurableSet I := MeasurableSet.iInter fun n => (chain n).2.1
  have hIsub : I.Subsingleton := by
    intro x hx y hy
    refine hsep x y fun n => ?_
    have hx' : x ∈ (chain (n + 1)).1 := Set.mem_iInter.mp hx (n + 1)
    have hy' : y ∈ (chain (n + 1)).1 := Set.mem_iInter.mp hy (n + 1)
    rcases hchain n with h' | h' <;> rw [h'] at hx' hy'
    · exact ⟨fun _ => hy'.2, fun _ => hx'.2⟩
    · exact ⟨fun hxE => absurd hxE hx'.2, fun hyE => absurd hyE hy'.2⟩
  -- Beyond stage `N + 1` the chain is hereditarily null outside its intersection.
  apply (chain (N + 1)).2.2
  intro C hC hCsub
  have htail : HereditarilyNull lam (⋃ n, S (n + (N + 1))) :=
    hereditarilyNull_iUnion h (B := fun n => S (n + (N + 1))) (fun n => hSmeas (n + (N + 1))) hnullS
  have hdiff : C \ I ⊆ ⋃ n, S (n + (N + 1)) := by
    intro z hz
    have hzm : ∃ m, z ∉ (chain m).1 := by
      by_contra hall
      push Not at hall
      exact hz.2 (Set.mem_iInter.mpr hall)
    let m := Nat.find hzm
    have hmN : N + 1 < m := by
      by_contra hle
      exact Nat.find_spec hzm (hanti m (N + 1) (not_lt.mp hle) (hCsub hz.1))
    have hprev : z ∈ (chain (m - 1)).1 := by
      by_contra hno
      exact Nat.find_min hzm (by omega : m - 1 < m) hno
    refine Set.mem_iUnion.mpr ⟨m - 1 - (N + 1), ?_⟩
    rw [show m - 1 - (N + 1) + (N + 1) = m - 1 by omega]
    refine ⟨hprev, ?_⟩
    rw [show m - 1 + 1 = m by omega]
    exact Nat.find_spec hzm
  rw [h.diff hC hImeas, htail _ (hC.diff hImeas) hdiff, add_zero]
  rcases (hIsub.anti Set.inter_subset_right : (C ∩ I).Subsingleton).eq_empty_or_singleton with
    he | ⟨x, hx⟩
  · rw [he, h.empty]
  · rw [hx, hpt]

omit [MeasurableSpace X] in
open Classical in
/-- The value of a finite atomic set function on a point. -/
theorem finiteAtomic_singleton (F : Finset X) (c : X → k) (x : X) :
    finiteAtomic F c {x} = if x ∈ F then c x else 0 := by
  simp only [finiteAtomic, Finset.sum_filter, Set.mem_singleton_iff]
  convert Finset.sum_ite_eq' F x c

/-- `lem:scalar`: a disjoint-finite, countably additive scalar set function on a
countably separated space is the finite combination of its nonzero point masses. -/
theorem eq_finiteAtomic (h : IsFinsumAdditive lam) (hX : IsCountablySeparated X) :
    ∃ F : Finset X, (∀ x ∈ F, lam {x} ≠ 0) ∧
      ∀ A, MeasurableSet A → lam A = finiteAtomic F (fun x => lam {x}) A := by
  classical
  obtain ⟨E, hE, hsep⟩ := hX
  have hsing := measurableSet_singleton_of_separated hE hsep
  have hfin := finite_setOf_singleton_ne_zero h hsing
  refine ⟨hfin.toFinset, fun x hx => hfin.mem_toFinset.mp hx, fun A hA => ?_⟩
  have hsub := h.sub (isFinsumAdditive_finiteAtomic hfin.toFinset fun x => lam {x})
  have hzero := eq_zero_of_singleton_eq_zero hsub ⟨E, hE, hsep⟩ (fun x => ?_) hA
  · exact sub_eq_zero.mp hzero
  · rw [Pi.sub_apply, finiteAtomic_singleton]
    split_ifs with hxF
    · exact sub_self _
    · rw [sub_zero]
      by_contra hne
      exact hxF (hfin.mem_toFinset.mpr hne)

/-- `lem:scalar`, uniqueness: a representation with nonzero coefficients has exactly
the points of nonzero mass as its support, and the point masses as coefficients. -/
theorem finiteAtomic_unique {G : Finset X} {d : X → k} (hd : ∀ x ∈ G, d x ≠ 0)
    (hsing : ∀ x : X, MeasurableSet ({x} : Set X))
    (hrep : ∀ A, MeasurableSet A → lam A = finiteAtomic G d A) :
    (∀ x, x ∈ G ↔ lam {x} ≠ 0) ∧ ∀ x ∈ G, d x = lam {x} := by
  classical
  have hpt : ∀ x, lam {x} = if x ∈ G then d x else 0 := fun x => by
    rw [hrep _ (hsing x), finiteAtomic_singleton]
  refine ⟨fun x => ⟨fun hx => by rw [hpt, if_pos hx]; exact hd x hx, fun hx => ?_⟩,
    fun x hx => by rw [hpt, if_pos hx]⟩
  by_contra hxG
  rw [hpt, if_neg hxG] at hx
  exact hx rfl

section Coefficients

variable {Γ R : Type*} [PartialOrder Γ] [AddCommGroup R]

/-- Every coefficient of a strong Hahn measure is disjoint-finite and countably
additive, as in the proof of `prop:coefficients`. -/
theorem isFinsumAdditive_coeff {μ : Set X → R⟦Γ⟧} (hμ : IsStrongHahnMeasure μ) (γ : Γ) :
    IsFinsumAdditive fun A => (μ A).coeff γ := by
  intro A hA hdisj
  obtain ⟨s, hs, hsum⟩ := hμ.iUnion A hA hdisj
  refine ⟨(s.finite_co_support γ).subset fun n hn => ?_, ?_⟩
  · simpa [hs n] using hn
  · simp only [hsum, SummableFamily.coeff_hsum, hs]

/-- `prop:coefficients`: on a countably separated space, every coefficient of a
strong Hahn measure is a finite linear combination of point masses. -/
theorem coeff_eq_finiteAtomic {μ : Set X → R⟦Γ⟧} (hμ : IsStrongHahnMeasure μ)
    (hX : IsCountablySeparated X) (γ : Γ) :
    ∃ F : Finset X, (∀ x ∈ F, (μ {x}).coeff γ ≠ 0) ∧
      ∀ A, MeasurableSet A → (μ A).coeff γ = finiteAtomic F (fun x => (μ {x}).coeff γ) A :=
  eq_finiteAtomic (isFinsumAdditive_coeff hμ γ) hX

end Coefficients

end

end Surreal.HahnSeries
