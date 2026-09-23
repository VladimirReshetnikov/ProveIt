import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.RingTheory.HahnSeries.Multiplication
import Surreal.HahnSeries.StrongMeasureShadow

/-!
# Invariant strong Hahn measures live on finite orbits

This file formalizes `meas:thm:orbits` (with `meas:eq:orbit-law`), `meas:cor:transitive` and
`meas:cor:exchangeable` (with `meas:eq:exchangeable`) of
`docs/surreal/hahn-valued-measures-and-probability/article.tex`, section `meas:sec:orbits`, on
top of the atomicity theorem `meas:thm:atomic` of `StrongMeasure.lean`,
`MeasureAtomicity.lean` and `StrongMeasureShadow.lean`.

Weights and orbit laws (no measure involved). A strongly summable family takes a nonzero value
at only finitely many points. Hence weights invariant under a group action vanish on infinite
orbits; the orbit weights `w_O = ∑ˢ_{x ∈ O} w_x`, the regrouping of the point weights by the
orbit map, equal `|O| w_x`; and splitting `w_O` equally among the points of `O` recovers the
weights over a division ring of characteristic zero. For every strongly summable family
`(w_O)_{O ∈ S}` indexed by a set `S` of orbits, over any division ring, the orbit law
`A ↦ ∑ˢ_{O ∈ S} w_O |A ∩ O| / |O|` (`orbitLawOn`) is the atomic measure of the split weights.

`meas:thm:orbits`. Let a group `G` act on a countably separated measurable space `X`, and let
`μ` be a strong Hahn measure with `μ (g • A) = μ A` for measurable `A`.
* The point weights are constant on orbits, and every point with `w_x ≠ 0` has a finite orbit
  (`singleton_smul_eq_of_invariant`, `finite_orbit_of_invariant`); no coefficient structure
  beyond an additive group is used.
* Signed and complex versions, over any division ring of characteristic zero:
  `μ A = ∑ˢ_{O ∈ 𝒪_f} w_O |A ∩ O| / |O|` on measurable sets, where `𝒪_f` is the set of finite
  orbits and `w_O = ∑ˢ_{x ∈ O} w_x` (`exists_orbitLawOn_of_invariant`).
* For a strong Hahn probability over a linearly ordered division ring, moreover `w_O ≥ 0` and
  `∑ˢ_O w_O = 1` (`IsStrongHahnProbability.exists_orbitLawOn_of_invariant`).
* Converse: for every set `S` of orbits and every strongly summable family on it, the orbit law
  is a strong Hahn measure for every measurable structure, in particular on all subsets, it is
  additive on arbitrary disjoint families and `G`-invariant on all subsets; when the orbits are
  finite and the weights are nonnegative with strong sum `1`, it is a strong Hahn probability
  (`isStrongHahnProbability_orbitLawOn`, `isStrongHahnProbability_top_orbitLawOn`).

`meas:cor:transitive`: under a transitive action on an infinite countably separated space an
invariant strong Hahn measure vanishes on events, so no invariant strong Hahn probability exists
for any coefficients with `1 ≠ 0`.

`meas:cor:exchangeable`: `E^ℕ` is countably separated for a countable alphabet with measurable
singletons. For a finite alphabet, a strong Hahn measure invariant under transpositions of
coordinates, in particular an exchangeable one (`IsExchangeable`: invariance under every
permutation moving finitely many coordinates), is `∑_{a ∈ E} μ({(a,a,…)}) δ_{(a,a,…)}` on
events; for a strong Hahn probability the weights are nonnegative with sum `1`. The i.i.d.
clause is proved in a stronger form: for `0 < p < 1` in `R⟦Γ⟧`, with `R` a linearly ordered
commutative ring and `Γ` a linearly ordered cancellative monoid, no strong Hahn measure on
`Bool^ℕ` has the independent Bernoulli(`p`) cylinder masses, in particular for an ordinary
constant bias.

Deviations from the source. The invariance hypothesis is `μ (g • A) = μ A` for measurable `A`,
and measurability of `g(A)` and `g⁻¹(A)` is not assumed; outside the source's setting the
hypothesis therefore also constrains values of `μ` on non-events. The proofs use it only on
singletons, where `g • {x} = {g • x}` is measurable by countable separation: only the invariance
`μ {g • x} = μ {x}` of the singleton masses is used (`singleton_smul_eq_of_invariant`). When
every `g` maps events to events, the hypothesis is exactly the source's. The exchangeable
corollary needs only invariance under transpositions. The i.i.d. clause is proved directly, not
through exchangeability (which would require knowing that the i.i.d. law is determined by its
cylinder masses): one of `p` and `1 - p` has order `0`, and the disjoint cylinders "`b` up to
time `n - 1`, then `!b`" have masses `r_b^n r_{!b}`, all with a nonzero coefficient at
`v(r_{!b})`, which violates `(SH)`. Orbit cardinalities are `Set.ncard`, which is `0` on
infinite orbits, where all weights vanish.
-/

namespace Surreal.HahnSeries

open _root_.HahnSeries MulAction
open scoped Pointwise

noncomputable section

section ConstantWeights

variable {Γ R X : Type*} [PartialOrder Γ] [AddCommMonoid R]

/-- A strongly summable family takes a given nonzero value at only finitely many points: at an
exponent where the value has a nonzero coefficient, every such point contributes. -/
theorem eq_zero_of_infinite_of_forall_eq (w : SummableFamily Γ R X) {T : Set X}
    (hT : T.Infinite) {c : R⟦Γ⟧} (hc : ∀ x ∈ T, w x = c) : c = 0 := by
  by_contra hc0
  obtain ⟨γ, hγ⟩ : ∃ γ, c.coeff γ ≠ 0 := by
    by_contra h
    push Not at h
    exact hc0 (HahnSeries.ext (funext h))
  refine hT ((w.finite_co_support γ).subset fun x hx => Function.mem_support.mpr ?_)
  rw [hc x hx]
  exact hγ

/-- The atomic mass of a set on which the weights are constant is its cardinality times the
common weight. For an infinite set both sides vanish. -/
theorem atomicMeasure_eq_ncard_smul (w : SummableFamily Γ R X) {B : Set X} {c : R⟦Γ⟧}
    (hc : ∀ x ∈ B, w x = c) : atomicMeasure w B = B.ncard • c := by
  by_cases hB : B.Finite
  · ext γ
    have h : ∑ᶠ x ∈ B, (w x).coeff γ = ∑ᶠ _x ∈ B, c.coeff γ :=
      finsum_mem_congr rfl fun x hx => by rw [hc x hx]
    rw [coeff_atomicMeasure, h, finsum_mem_eq_finite_toFinset_sum _ hB, Finset.sum_const,
      Set.ncard_eq_toFinset_card B hB, coeff_nsmul, Pi.smul_apply]
  · obtain rfl := eq_zero_of_infinite_of_forall_eq w hB hc
    rw [Set.Infinite.ncard hB, zero_smul]
    ext γ
    rw [coeff_atomicMeasure, coeff_zero]
    exact finsum_mem_eq_zero_of_forall_eq_zero fun x hx => by rw [hc x hx, coeff_zero]

end ConstantWeights

section OrbitClass

variable (G : Type*) {X : Type*} [Group G] [MulAction G X]

/-- The orbit of a point, as an element of the orbit space `X / G`. -/
def orbitClass (x : X) : orbitRel.Quotient G X :=
  Quotient.mk'' x

variable {G}

theorem mem_orbit_iff_orbitClass_eq {x : X} {O : orbitRel.Quotient G X} :
    x ∈ O.orbit ↔ orbitClass G x = O :=
  orbitRel.Quotient.mem_orbit

theorem mem_orbit_orbitClass (x : X) : x ∈ (orbitClass G x).orbit :=
  mem_orbit_iff_orbitClass_eq.mpr rfl

@[simp]
theorem orbit_orbitClass (x : X) : (orbitClass G x).orbit = orbit G x :=
  rfl

@[simp]
theorem orbitClass_smul (g : G) (x : X) : orbitClass G (g • x) = orbitClass G x :=
  Quotient.sound' (mem_orbit x g)

/-- Distinct orbits are disjoint. -/
theorem pairwise_disjoint_inter_orbit (A : Set X) :
    Pairwise (Function.onFun Disjoint fun O : orbitRel.Quotient G X => A ∩ O.orbit) := by
  intro O O' hne
  refine Set.disjoint_left.mpr fun x hx hx' => hne ?_
  exact (mem_orbit_iff_orbitClass_eq.mp hx.2).symm.trans (mem_orbit_iff_orbitClass_eq.mp hx'.2)

/-- The orbits partition every set. -/
theorem iUnion_inter_orbit (A : Set X) :
    (⋃ O : orbitRel.Quotient G X, A ∩ O.orbit) = A := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_inter_iff]
  exact ⟨fun ⟨_, h, _⟩ => h, fun h => ⟨orbitClass G x, h, mem_orbit_orbitClass x⟩⟩

end OrbitClass

section InvariantWeights

variable {G Γ R X : Type*} [Group G] [MulAction G X] [PartialOrder Γ] [AddCommMonoid R]
  {w : SummableFamily Γ R X}

/-- Invariant strongly summable weights vanish on infinite orbits. -/
theorem eq_zero_of_infinite_orbit (hw : ∀ (g : G) (x : X), w (g • x) = w x) {x : X}
    (hx : (orbit G x).Infinite) : w x = 0 :=
  eq_zero_of_infinite_of_forall_eq w hx (by rintro _ ⟨g, rfl⟩; exact hw g x)

/-- A point of nonzero invariant weight has a finite orbit. -/
theorem finite_orbit_of_ne_zero (hw : ∀ (g : G) (x : X), w (g • x) = w x) {x : X}
    (hx : w x ≠ 0) : (orbit G x).Finite := by
  by_contra h
  exact hx (eq_zero_of_infinite_orbit hw h)

/-- The total weight of an orbit is its cardinality times the weight of any of its points. -/
theorem atomicMeasure_orbit (hw : ∀ (g : G) (x : X), w (g • x) = w x) (x : X) :
    atomicMeasure w (orbit G x) = (orbit G x).ncard • w x :=
  atomicMeasure_eq_ncard_smul w (by rintro _ ⟨g, rfl⟩; exact hw g x)

variable (w) in
/-- The orbit weights `w_O = ∑ˢ_{x ∈ O} w_x`, the regrouping of the point weights by orbits. -/
def orbitWeights : SummableFamily Γ R (orbitRel.Quotient G X) :=
  regroup w (orbitClass G)

theorem orbitWeights_apply (O : orbitRel.Quotient G X) :
    orbitWeights w O = atomicMeasure w O.orbit := by
  have h : {x | orbitClass G x = O} = O.orbit := by
    ext x
    exact mem_orbit_iff_orbitClass_eq.symm
  rw [orbitWeights, regroup_apply, h]
  rfl

theorem hsum_orbitWeights : (orbitWeights (G := G) w).hsum = w.hsum :=
  hsum_regroup _ _

theorem orbitWeights_orbitClass (hw : ∀ (g : G) (x : X), w (g • x) = w x) (x : X) :
    orbitWeights w (orbitClass G x) = (orbit G x).ncard • w x := by
  rw [orbitWeights_apply, orbit_orbitClass, atomicMeasure_orbit hw]

theorem orbitWeights_eq_zero (hw : ∀ (g : G) (x : X), w (g • x) = w x)
    {O : orbitRel.Quotient G X} (hO : O.orbit.Infinite) : orbitWeights w O = 0 := by
  obtain ⟨x, hx⟩ := O.nonempty_orbit
  obtain rfl := mem_orbit_iff_orbitClass_eq.mp hx
  rw [orbitWeights_orbitClass hw, ← orbit_orbitClass, Set.Infinite.ncard hO, zero_smul]

/-- Invariant weights give an invariant atomic measure, on arbitrary subsets. -/
theorem atomicMeasure_smul_set (hw : ∀ (g : G) (x : X), w (g • x) = w x) (g : G)
    (A : Set X) : atomicMeasure w (g • A) = atomicMeasure w A := by
  ext γ
  rw [coeff_atomicMeasure, coeff_atomicMeasure, ← Set.image_smul,
    finsum_mem_image (MulAction.injective g).injOn]
  simp only [hw]

end InvariantWeights

section Spread

variable {G Γ R X : Type*} [Group G] [MulAction G X] [PartialOrder Γ] [DivisionRing R]

/-- Splitting orbit weights equally among the points of each orbit: `v_x = w_O / |O|` for
`x ∈ O`. On an infinite orbit `ncard` is `0`, and the split weights vanish there. -/
def orbitSpread (W : SummableFamily Γ R (orbitRel.Quotient G X)) : SummableFamily Γ R X where
  toFun x := ((orbitClass G x).orbit.ncard : R)⁻¹ • W (orbitClass G x)
  isPWO_iUnion_support' := by
    refine W.isPWO_iUnion_support.mono (Set.iUnion_subset fun x γ hγ => ?_)
    simp only [mem_support, coeff_smul, smul_eq_mul] at hγ
    exact Set.mem_iUnion.mpr ⟨orbitClass G x, (mem_support _ _).mpr (right_ne_zero_of_mul hγ)⟩
  finite_co_support' γ := by
    refine (((W.finite_co_support γ).inter_of_left {O | O.orbit.Finite}).biUnion
      fun O hO => hO.2).subset fun x hx => ?_
    have hx' := Function.mem_support.mp hx
    simp only [coeff_smul, smul_eq_mul] at hx'
    refine Set.mem_iUnion₂.mpr ⟨orbitClass G x, ⟨right_ne_zero_of_mul hx', ?_⟩,
      mem_orbit_orbitClass x⟩
    by_contra hinf
    rw [Set.Infinite.ncard hinf, Nat.cast_zero, inv_zero, zero_mul] at hx'
    exact hx' rfl

/-- The split weight at `x` is `w_{O_x} / |O_x|`. -/
theorem orbitSpread_apply (W : SummableFamily Γ R (orbitRel.Quotient G X)) (x : X) :
    orbitSpread W x = ((orbit G x).ncard : R)⁻¹ • W (orbitClass G x) :=
  rfl

theorem orbitSpread_of_mem (W : SummableFamily Γ R (orbitRel.Quotient G X))
    {O : orbitRel.Quotient G X} {x : X} (hx : x ∈ O.orbit) :
    orbitSpread W x = (O.orbit.ncard : R)⁻¹ • W O := by
  obtain rfl := mem_orbit_iff_orbitClass_eq.mp hx
  rfl

/-- The split weights are constant on orbits. -/
theorem orbitSpread_smul (W : SummableFamily Γ R (orbitRel.Quotient G X)) (g : G) (x : X) :
    orbitSpread W (g • x) = orbitSpread W x :=
  orbitSpread_of_mem W (mem_orbit_iff_orbitClass_eq.mpr (orbitClass_smul g x))

/-- The orbit law `A ↦ ∑ˢ_O w_O |A ∩ O| / |O|` of `meas:eq:orbit-law`, for weights indexed
by all orbits. -/
def orbitLaw (W : SummableFamily Γ R (orbitRel.Quotient G X)) (A : Set X) : R⟦Γ⟧ :=
  (SummableFamily.smulFamily (fun O => ((A ∩ O.orbit).ncard : R) / (O.orbit.ncard : R))
    W).hsum

/-- The orbit law is the atomic measure of the split weights. -/
theorem atomicMeasure_orbitSpread (W : SummableFamily Γ R (orbitRel.Quotient G X))
    (A : Set X) : atomicMeasure (orbitSpread W) A = orbitLaw W A := by
  conv_lhs => rw [← iUnion_inter_orbit (G := G) A]
  rw [← hsum_disjointFamily, orbitLaw]
  congr 1
  ext O : 1
  rw [disjointFamily_apply _ (pairwise_disjoint_inter_orbit A),
    atomicMeasure_eq_ncard_smul _ (c := (O.orbit.ncard : R)⁻¹ • W O)
      fun x hx => orbitSpread_of_mem W hx.2,
    SummableFamily.smulFamily_toFun, ← Nat.cast_smul_eq_nsmul R, smul_smul, div_eq_mul_inv]

/-- The orbit law is invariant on all subsets. -/
theorem orbitLaw_smul_set (W : SummableFamily Γ R (orbitRel.Quotient G X)) (g : G)
    (A : Set X) : orbitLaw W (g • A) = orbitLaw W A := by
  rw [← atomicMeasure_orbitSpread, ← atomicMeasure_orbitSpread,
    atomicMeasure_smul_set (orbitSpread_smul W) g A]

variable [CharZero R]

/-- Splitting the orbit weights of invariant weights recovers the weights. -/
theorem orbitSpread_orbitWeights {w : SummableFamily Γ R X}
    (hw : ∀ (g : G) (x : X), w (g • x) = w x) : orbitSpread (orbitWeights (G := G) w) = w := by
  ext x : 1
  rw [orbitSpread_apply, orbitWeights_orbitClass hw]
  by_cases hfin : (orbit G x).Finite
  · have hne : ((orbit G x).ncard : R) ≠ 0 :=
      Nat.cast_ne_zero.mpr ((Set.ncard_pos hfin).mpr ⟨x, mem_orbit_self x⟩).ne'
    rw [← Nat.cast_smul_eq_nsmul R, smul_smul, inv_mul_cancel₀ hne, one_smul]
  · rw [Set.Infinite.ncard hfin, zero_smul, smul_zero, eq_zero_of_infinite_orbit hw hfin]

/-- For invariant weights, the orbit law of the orbit weights is the atomic measure. -/
theorem orbitLaw_orbitWeights {w : SummableFamily Γ R X}
    (hw : ∀ (g : G) (x : X), w (g • x) = w x) (A : Set X) :
    orbitLaw (orbitWeights (G := G) w) A = atomicMeasure w A := by
  rw [← atomicMeasure_orbitSpread, orbitSpread_orbitWeights hw]

end Spread

section OrbitSets

variable {G Γ R X : Type*} [Group G] [MulAction G X] [PartialOrder Γ] [DivisionRing R]

/-- `meas:eq:orbit-law`: the set function `A ↦ ∑ˢ_{O ∈ S} w_O |A ∩ O| / |O|` of a strongly
summable family `(w_O)_{O ∈ S}` indexed by a set `S` of orbits. -/
def orbitLawOn (S : Set (orbitRel.Quotient G X)) (w : SummableFamily Γ R S) (A : Set X) :
    R⟦Γ⟧ :=
  (SummableFamily.smulFamily
    (fun O : S => ((A ∩ O.1.orbit).ncard : R) / (O.1.orbit.ncard : R)) w).hsum

/-- The orbit law of a family indexed by a set of orbits is the orbit law of its extension by
zero to all orbits. -/
theorem orbitLawOn_eq_orbitLaw (S : Set (orbitRel.Quotient G X)) (w : SummableFamily Γ R S)
    (A : Set X) :
    orbitLawOn S w A = orbitLaw (w.embDomain (Function.Embedding.subtype (· ∈ S))) A := by
  rw [orbitLaw, orbitLawOn,
    ← SummableFamily.hsum_embDomain _ (Function.Embedding.subtype (· ∈ S))]
  congr 1
  ext O : 1
  by_cases hO : O ∈ S
  · have h := SummableFamily.embDomain_image w (Function.Embedding.subtype (· ∈ S))
      (a := ⟨O, hO⟩)
    have h' := SummableFamily.embDomain_image (SummableFamily.smulFamily
      (fun O : S => ((A ∩ O.1.orbit).ncard : R) / (O.1.orbit.ncard : R)) w)
      (Function.Embedding.subtype (· ∈ S)) (a := ⟨O, hO⟩)
    simp only [Function.Embedding.coe_subtype] at h h'
    rw [h', SummableFamily.smulFamily_toFun, SummableFamily.smulFamily_toFun, h]
  · have hr : O ∉ Set.range (Function.Embedding.subtype (· ∈ S)) := by simpa using hO
    rw [SummableFamily.embDomain_notin_range _ _ hr, SummableFamily.smulFamily_toFun,
      SummableFamily.embDomain_notin_range _ _ hr, smul_zero]

/-- The orbit law is the atomic measure `meas:eq:atomic` of the weights `w_O / |O|` spread
over the points of each orbit. -/
theorem orbitLawOn_eq_atomicMeasure (S : Set (orbitRel.Quotient G X))
    (w : SummableFamily Γ R S) :
    orbitLawOn S w =
      atomicMeasure (orbitSpread (w.embDomain (Function.Embedding.subtype (· ∈ S)))) := by
  funext A
  rw [orbitLawOn_eq_orbitLaw, atomicMeasure_orbitSpread]

/-- `meas:thm:orbits`, converse: every orbit law is a strong Hahn measure, for every measurable
structure on `X`. -/
theorem isStrongHahnMeasure_orbitLawOn [MeasurableSpace X] (S : Set (orbitRel.Quotient G X))
    (w : SummableFamily Γ R S) : IsStrongHahnMeasure (orbitLawOn S w) := by
  rw [orbitLawOn_eq_atomicMeasure]
  exact isStrongHahnMeasure_atomicMeasure _

/-- `meas:thm:orbits`, converse on all subsets: the orbit law is a strong Hahn measure on the
power set of `X`. -/
theorem isStrongHahnMeasure_top_orbitLawOn (S : Set (orbitRel.Quotient G X))
    (w : SummableFamily Γ R S) : @IsStrongHahnMeasure Γ R X _ _ ⊤ (orbitLawOn S w) :=
  @isStrongHahnMeasure_orbitLawOn G Γ R X _ _ _ _ ⊤ S w

/-- `meas:thm:orbits`, converse: the orbit law is additive on every pairwise disjoint family of
subsets, indexed by an arbitrary type, with the sum interpreted strongly. -/
theorem orbitLawOn_iUnion {ι : Type*} (S : Set (orbitRel.Quotient G X))
    (w : SummableFamily Γ R S) {A : ι → Set X} (hA : Pairwise (Function.onFun Disjoint A)) :
    ∃ s : SummableFamily Γ R ι, (∀ i, s i = orbitLawOn S w (A i)) ∧
      orbitLawOn S w (⋃ i, A i) = s.hsum := by
  rw [orbitLawOn_eq_atomicMeasure]
  exact atomicMeasure_iUnion _ hA

/-- `meas:thm:orbits`, converse: the orbit law is `G`-invariant on all subsets. -/
theorem orbitLawOn_smul_set (S : Set (orbitRel.Quotient G X)) (w : SummableFamily Γ R S)
    (g : G) (A : Set X) : orbitLawOn S w (g • A) = orbitLawOn S w A := by
  rw [orbitLawOn_eq_orbitLaw, orbitLawOn_eq_orbitLaw, orbitLaw_smul_set]

/-- On a set of finite orbits the total mass of the orbit law is `∑ˢ_O w_O`. -/
theorem orbitLawOn_univ [CharZero R] {S : Set (orbitRel.Quotient G X)}
    (hS : ∀ O ∈ S, O.orbit.Finite) (w : SummableFamily Γ R S) :
    orbitLawOn S w Set.univ = w.hsum := by
  rw [orbitLawOn]
  congr 1
  ext O : 1
  rw [SummableFamily.smulFamily_toFun, Set.univ_inter, div_self, one_smul]
  exact Nat.cast_ne_zero.mpr ((Set.ncard_pos (hS O.1 O.2)).mpr O.1.nonempty_orbit).ne'

end OrbitSets

section OrbitSetsPositive

variable {G Γ R X : Type*} [Group G] [MulAction G X] [LinearOrder Γ] [DivisionRing R]
  [LinearOrder R] [IsStrictOrderedRing R] {S : Set (orbitRel.Quotient G X)}
  {w : SummableFamily Γ R S}

/-- `meas:thm:orbits`, converse: nonnegative orbit weights give an orbit law that is
nonnegative on all subsets. -/
theorem orbitLawOn_nonneg (hw : ∀ O, 0 ≤ toLex (w O)) (A : Set X) :
    0 ≤ toLex (orbitLawOn S w A) :=
  hsum_nonneg _ fun O =>
    smul_nonneg_toLex (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (hw O)

/-- `meas:thm:orbits`, converse: for a set of finite orbits and nonnegative orbit weights of
total mass `1`, the orbit law is a strong Hahn probability, for every measurable structure on `X`
(on all subsets: `isStrongHahnProbability_top_orbitLawOn`). Its `G`-invariance on all subsets is
`orbitLawOn_smul_set`. -/
theorem isStrongHahnProbability_orbitLawOn [Zero Γ] [MeasurableSpace X]
    (hS : ∀ O ∈ S, O.orbit.Finite) (hw : ∀ O, 0 ≤ toLex (w O)) (hw1 : w.hsum = 1) :
    IsStrongHahnProbability (orbitLawOn S w) where
  toIsStrongHahnMeasure := isStrongHahnMeasure_orbitLawOn S w
  nonneg A _ := orbitLawOn_nonneg hw A
  univ := (orbitLawOn_univ hS w).trans hw1

/-- `meas:thm:orbits`, converse on all subsets: the orbit law is a strong Hahn probability on the
power set of `X`. -/
theorem isStrongHahnProbability_top_orbitLawOn [Zero Γ] (hS : ∀ O ∈ S, O.orbit.Finite)
    (hw : ∀ O, 0 ≤ toLex (w O)) (hw1 : w.hsum = 1) :
    @IsStrongHahnProbability Γ R X _ _ _ _ _ ⊤ (orbitLawOn S w) :=
  @isStrongHahnProbability_orbitLawOn G Γ R X _ _ _ _ _ _ S w _ ⊤ hS hw hw1

end OrbitSetsPositive

section Measures

variable {G Γ R X : Type*} [Group G] [MulAction G X] [MeasurableSpace X] [LinearOrder Γ]

section AddCommGroup

variable [AddCommGroup R] {μ : Set X → R⟦Γ⟧}

/-- `meas:thm:orbits`: invariance applied to singletons gives `w_{gx} = w_x`, so the point
weights are constant on orbits. -/
theorem singleton_smul_eq_of_invariant (hX : IsCountablySeparated X)
    (hinv : ∀ (g : G) (A : Set X), MeasurableSet A → μ (g • A) = μ A) (g : G) (x : X) :
    μ {g • x} = μ {x} := by
  rw [← Set.smul_set_singleton, hinv g _ (hX.measurableSet_singleton x)]

/-- The point weights `w_x = μ({x})` of an invariant strong Hahn measure are invariant. -/
theorem strongWeights_smul_of_invariant (hμ : IsStrongHahnMeasure μ)
    (hX : IsCountablySeparated X)
    (hinv : ∀ (g : G) (A : Set X), MeasurableSet A → μ (g • A) = μ A) (g : G) (x : X) :
    strongWeights hμ hX (g • x) = strongWeights hμ hX x :=
  singleton_smul_eq_of_invariant hX hinv g x

/-- `meas:thm:orbits`: for a `G`-invariant strong Hahn measure on a countably separated space,
every point with `w_x ≠ 0` has a finite orbit. -/
theorem finite_orbit_of_invariant (hμ : IsStrongHahnMeasure μ) (hX : IsCountablySeparated X)
    (hinv : ∀ (g : G) (A : Set X), MeasurableSet A → μ (g • A) = μ A) {x : X}
    (hx : μ {x} ≠ 0) : (orbit G x).Finite :=
  finite_orbit_of_ne_zero (strongWeights_smul_of_invariant hμ hX hinv) hx

/-- `meas:cor:transitive`, signed and complex form: a strong Hahn measure on an infinite
countably separated space that is invariant under a transitive group vanishes on every event. -/
theorem eq_zero_of_invariant_of_isPretransitive [IsPretransitive G X] [Infinite X]
    (hμ : IsStrongHahnMeasure μ) (hX : IsCountablySeparated X)
    (hinv : ∀ (g : G) (A : Set X), MeasurableSet A → μ (g • A) = μ A) {A : Set X}
    (hA : MeasurableSet A) : μ A = 0 := by
  have h0 : ∀ x, strongWeights hμ hX x = 0 := fun x =>
    eq_zero_of_infinite_orbit (strongWeights_smul_of_invariant hμ hX hinv)
      (by rw [orbit_eq_univ]; exact Set.infinite_univ)
  rw [eq_atomicMeasure_strongWeights hμ hX hA]
  ext γ
  rw [coeff_atomicMeasure, coeff_zero]
  exact finsum_mem_eq_zero_of_forall_eq_zero fun x _ => by rw [h0 x, coeff_zero]

/-- `meas:cor:transitive`: an infinite countably separated space admits no strong Hahn
probability that is invariant (on events) under a transitive group action; the permutations need
not be measurable. -/
theorem not_isStrongHahnProbability_of_isPretransitive [Zero Γ] [One R] [LinearOrder R]
    [NeZero (1 : R)] [IsPretransitive G X] [Infinite X] (hX : IsCountablySeparated X)
    (hinv : ∀ (g : G) (A : Set X), MeasurableSet A → μ (g • A) = μ A) :
    ¬ IsStrongHahnProbability μ := by
  intro hP
  have h := eq_zero_of_invariant_of_isPretransitive hP.toIsStrongHahnMeasure hX hinv
    MeasurableSet.univ
  rw [hP.univ] at h
  have h0 := congrArg (fun x : R⟦Γ⟧ => x.coeff 0) h
  simp only [coeff_one, coeff_zero] at h0
  exact one_ne_zero h0

end AddCommGroup

section DivisionRing

variable [DivisionRing R] [CharZero R] {μ : Set X → R⟦Γ⟧}

/-- `meas:eq:orbit-law` with the orbit weights `w_O = ∑ˢ_{x ∈ O} w_x` indexed by all orbits: a
`G`-invariant strong Hahn measure on a countably separated space is, on every event, the orbit
law of its orbit weights. -/
theorem eq_orbitLaw_of_invariant (hμ : IsStrongHahnMeasure μ) (hX : IsCountablySeparated X)
    (hinv : ∀ (g : G) (A : Set X), MeasurableSet A → μ (g • A) = μ A) {A : Set X}
    (hA : MeasurableSet A) : μ A = orbitLaw (orbitWeights (G := G) (strongWeights hμ hX)) A := by
  rw [orbitLaw_orbitWeights (strongWeights_smul_of_invariant hμ hX hinv),
    eq_atomicMeasure_strongWeights hμ hX hA]

/-- `meas:thm:orbits`, signed and complex version: a `G`-invariant strong Hahn measure on a
countably separated space agrees on events with the orbit law
`A ↦ ∑ˢ_{O ∈ 𝒪_f} w_O |A ∩ O| / |O|` of a strongly summable family indexed by a set `𝒪_f` of
finite orbits, with `w_O = ∑ˢ_{x ∈ O} w_x`. -/
theorem exists_orbitLawOn_of_invariant (hμ : IsStrongHahnMeasure μ)
    (hX : IsCountablySeparated X)
    (hinv : ∀ (g : G) (A : Set X), MeasurableSet A → μ (g • A) = μ A) :
    ∃ (S : Set (orbitRel.Quotient G X)) (w : SummableFamily Γ R S),
      (∀ O ∈ S, O.orbit.Finite) ∧
      (∀ O : S, w O = atomicMeasure (strongWeights hμ hX) O.1.orbit) ∧
      ∀ A, MeasurableSet A → μ A = orbitLawOn S w A := by
  refine ⟨{O | O.orbit.Finite}, restrict (orbitWeights (G := G) (strongWeights hμ hX)) _,
    fun O hO => hO, fun O => orbitWeights_apply O.1, fun A hA => ?_⟩
  rw [orbitLawOn_eq_orbitLaw, eq_orbitLaw_of_invariant hμ hX hinv hA]
  congr 1
  ext O : 1
  by_cases hO : O.orbit.Finite
  · exact (SummableFamily.embDomain_image
      (restrict (orbitWeights (G := G) (strongWeights hμ hX)) {O | O.orbit.Finite})
      (Function.Embedding.subtype _) (a := ⟨O, hO⟩)).symm
  · have hr : O ∉ Set.range
        (Function.Embedding.subtype (· ∈ {O : orbitRel.Quotient G X | O.orbit.Finite})) := by
      rintro ⟨O', rfl⟩
      exact hO O'.2
    rw [SummableFamily.embDomain_notin_range _ _ hr]
    exact orbitWeights_eq_zero (strongWeights_smul_of_invariant hμ hX hinv) hO

end DivisionRing

section Probability

variable [Zero Γ] [DivisionRing R] [LinearOrder R] [IsStrictOrderedRing R]
  {μ : Set X → R⟦Γ⟧}

/-- `meas:thm:orbits`: a `G`-invariant strong Hahn probability on a countably separated space
satisfies `meas:eq:orbit-law`: `μ(A) = ∑ˢ_{O ∈ 𝒪_f} w_O |A ∩ O| / |O|` for every event `A`, with
`𝒪_f` a set of finite orbits, `(w_O)` strongly summable, `w_O = ∑ˢ_{x ∈ O} w_x ≥ 0` and
`∑ˢ_O w_O = 1`. -/
theorem IsStrongHahnProbability.exists_orbitLawOn_of_invariant
    (hμ : IsStrongHahnProbability μ) (hX : IsCountablySeparated X)
    (hinv : ∀ (g : G) (A : Set X), MeasurableSet A → μ (g • A) = μ A) :
    ∃ (S : Set (orbitRel.Quotient G X)) (w : SummableFamily Γ R S),
      (∀ O ∈ S, O.orbit.Finite) ∧
      (∀ O : S, w O = atomicMeasure (strongWeights hμ.toIsStrongHahnMeasure hX) O.1.orbit) ∧
      (∀ O, 0 ≤ toLex (w O)) ∧ w.hsum = 1 ∧
      ∀ A, MeasurableSet A → μ A = orbitLawOn S w A := by
  obtain ⟨S, w, hS, hw, hrep⟩ :=
    Surreal.HahnSeries.exists_orbitLawOn_of_invariant hμ.toIsStrongHahnMeasure hX hinv
  refine ⟨S, w, hS, hw, fun O => ?_, ?_, hrep⟩
  · rw [hw O]
    exact (atomicMeasure_nonneg_iff _).mpr
      (fun x => hμ.nonneg _ (hX.measurableSet_singleton x)) _
  · rw [← orbitLawOn_univ hS, ← hrep _ MeasurableSet.univ, hμ.univ]

end Probability

end Measures

section Exchangeable

variable {Γ R E : Type*} [LinearOrder Γ] [MeasurableSpace E] [MeasurableSingletonClass E]

/-- The sequence space `E^ℕ` over a countable alphabet with measurable singletons is countably
separated by the coordinate events `{x | x k = a}`. -/
theorem isCountablySeparated_nat_pi [Countable E] : IsCountablySeparated (ℕ → E) := by
  obtain ⟨f, hf⟩ := exists_surjective_nat (Option (ℕ × E))
  refine ⟨fun n => {x | ∀ p ∈ f n, x p.1 = p.2}, fun n => ?_, fun x y hxy => funext fun k => ?_⟩
  · show MeasurableSet {x : ℕ → E | ∀ p ∈ f n, x p.1 = p.2}
    rcases f n with _ | ⟨k, a⟩
    · have h : {x : ℕ → E | ∀ p ∈ (none : Option (ℕ × E)), x p.1 = p.2} = Set.univ := by
        ext x
        simp
      rw [h]
      exact MeasurableSet.univ
    · have h : {x : ℕ → E | ∀ p ∈ some (k, a), x p.1 = p.2} = (fun x : ℕ → E => x k) ⁻¹' {a} := by
        ext x
        simp
      rw [h]
      exact (measurableSet_singleton a).preimage (measurable_pi_apply k)
  · obtain ⟨n, hn⟩ := hf (some (k, x k))
    have h := hxy n
    simp only [Set.mem_setOf_eq, hn, Option.mem_def, Option.some.injEq, forall_eq'] at h
    exact (h.mp trivial).symm

variable [AddCommGroup R] {μ : Set (ℕ → E) → R⟦Γ⟧}

/-- Exchangeability of a set function on `E^ℕ`: invariance under every permutation of the
coordinates that moves only finitely many of them. -/
def IsExchangeable (μ : Set (ℕ → E) → R⟦Γ⟧) : Prop :=
  ∀ σ : Equiv.Perm ℕ, {i | σ i ≠ i}.Finite → ∀ A : Set (ℕ → E), MeasurableSet A →
    μ ((fun x => x ∘ σ) ⁻¹' A) = μ A

omit [MeasurableSingletonClass E] in
/-- An exchangeable set function is invariant under every transposition of two coordinates. -/
theorem IsExchangeable.swap (h : IsExchangeable μ) (i j : ℕ) (A : Set (ℕ → E))
    (hA : MeasurableSet A) : μ ((fun x => x ∘ Equiv.swap i j) ⁻¹' A) = μ A := by
  refine h _ ((Set.toFinite {i, j}).subset fun k hk => ?_) A hA
  have hk' : Equiv.swap i j k ≠ k := hk
  by_contra hkij
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hkij
  exact hk' (Equiv.swap_apply_of_ne_of_ne hkij.1 hkij.2)

/-- Invariance under transpositions, read on singletons. -/
theorem singleton_comp_swap_eq [Countable E]
    (hswap : ∀ (i j : ℕ) (A : Set (ℕ → E)), MeasurableSet A →
      μ ((fun x => x ∘ Equiv.swap i j) ⁻¹' A) = μ A) (i j : ℕ) (y : ℕ → E) :
    μ {y ∘ Equiv.swap i j} = μ {y} := by
  have h : (fun x : ℕ → E => x ∘ Equiv.swap i j) ⁻¹' {y} = {y ∘ Equiv.swap i j} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · rintro rfl
      funext k
      simp [Equiv.swap_apply_self]
    · rintro rfl
      funext k
      simp [Equiv.swap_apply_self]
  rw [← h, hswap i j _ ((isCountablySeparated_nat_pi (E := E)).measurableSet_singleton y)]

/-- For a finite alphabet `E`, a strong Hahn measure on `E^ℕ` that is invariant under
transpositions of coordinates gives nonzero weight only to constant sequences. Proof idea (the
finite orbits of the finitary permutations are the constant sequences): a nonconstant sequence
has a symbol `b` occurring infinitely often and a position `i` carrying another symbol; swapping
`i` with the positions of `b` gives infinitely many distinct sequences of the same weight. -/
theorem exists_eq_const_of_singleton_ne_zero [Finite E] (hμ : IsStrongHahnMeasure μ)
    (hswap : ∀ (i j : ℕ) (A : Set (ℕ → E)), MeasurableSet A →
      μ ((fun x => x ∘ Equiv.swap i j) ⁻¹' A) = μ A) {x : ℕ → E} (hx : μ {x} ≠ 0) :
    ∃ a, x = fun _ => a := by
  have hX : IsCountablySeparated (ℕ → E) := isCountablySeparated_nat_pi
  obtain ⟨b, hb⟩ := Finite.exists_infinite_fiber x
  by_contra hconst
  push Not at hconst
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ b := by
    by_contra h
    push Not at h
    exact hconst b (funext h)
  have hinj : Set.InjOn (fun j => x ∘ Equiv.swap i j) (x ⁻¹' {b}) := by
    intro j hj j' _ h
    by_contra hne
    have hj0 : x j = b := hj
    have hji : j ≠ i := fun h' => hi (h' ▸ hj0)
    have h1 := congrFun h j
    simp only [Function.comp_apply, Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne hji hne] at h1
    exact hi (h1.trans hj0)
  refine hx (eq_zero_of_infinite_of_forall_eq (strongWeights hμ hX)
    (Set.Infinite.image hinj (Set.infinite_coe_iff.mp hb)) ?_)
  rintro _ ⟨j, -, rfl⟩
  exact singleton_comp_swap_eq hswap i j x

open Classical in
/-- `meas:eq:exchangeable`, signed and complex form, under invariance by transpositions only: a
strong Hahn measure on `E^ℕ` for a finite alphabet `E` that is invariant under transpositions of
coordinates agrees on events with the finite combination `∑_{a ∈ E} μ({(a,a,…)}) δ_{(a,a,…)}`
of Dirac masses at the constant sequences. -/
theorem eq_sum_const_of_swap_invariant [Fintype E] (hμ : IsStrongHahnMeasure μ)
    (hswap : ∀ (i j : ℕ) (A : Set (ℕ → E)), MeasurableSet A →
      μ ((fun x => x ∘ Equiv.swap i j) ⁻¹' A) = μ A) {A : Set (ℕ → E)}
    (hA : MeasurableSet A) :
    μ A = ∑ a ∈ Finset.univ with (fun _ : ℕ => a) ∈ A, μ {fun _ => a} := by
  have hX : IsCountablySeparated (ℕ → E) := isCountablySeparated_nat_pi
  have hc : Function.Injective fun (a : E) (_ : ℕ) => a := Function.const_injective
  rw [eq_atomicMeasure_strongWeights hμ hX hA]
  ext γ
  rw [coeff_atomicMeasure, coeff_sum, finsum_mem_eq_sum_of_subset _
    (t := (Finset.univ.filter fun a : E => (fun _ : ℕ => a) ∈ A).image fun a _ => a) ?_ ?_,
    Finset.sum_image fun a _ b _ h => hc h]
  · rfl
  · rintro x ⟨hxA, hx0⟩
    have hx : μ {x} ≠ 0 := fun h => (Function.mem_support.mp hx0) (by
      change (μ {x}).coeff γ = 0
      rw [h, coeff_zero])
    obtain ⟨a, rfl⟩ := exists_eq_const_of_singleton_ne_zero hμ hswap hx
    exact Finset.mem_coe.mpr
      (Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, hxA⟩, rfl⟩)
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
    exact (Finset.mem_filter.mp ha).2

open Classical in
/-- `meas:cor:exchangeable`, `meas:eq:exchangeable`, signed and complex form: an exchangeable
strong Hahn measure on `E^ℕ` for a finite alphabet `E` agrees on events with
`∑_{a ∈ E} q_a δ_{(a,a,…)}`, where `q_a = μ({(a,a,…)})`. -/
theorem IsExchangeable.eq_sum_const [Fintype E] (hμ : IsStrongHahnMeasure μ)
    (hex : IsExchangeable μ) {A : Set (ℕ → E)} (hA : MeasurableSet A) :
    μ A = ∑ a ∈ Finset.univ with (fun _ : ℕ => a) ∈ A, μ {fun _ => a} :=
  eq_sum_const_of_swap_invariant hμ hex.swap hA

open Classical in
/-- `meas:cor:exchangeable` under invariance by transpositions only: a strong Hahn probability
on `E^ℕ` for a finite alphabet `E` that is invariant under transpositions of coordinates agrees
on events with a mixture `∑_{a ∈ E} q_a δ_{(a,a,…)}` of constant sequences with `q_a ≥ 0` and
`∑_a q_a = 1`. -/
theorem IsStrongHahnProbability.exists_mixture_const_of_swap_invariant [Fintype E] [Zero Γ]
    [One R] [LinearOrder R] (hμ : IsStrongHahnProbability μ)
    (hswap : ∀ (i j : ℕ) (A : Set (ℕ → E)), MeasurableSet A →
      μ ((fun x => x ∘ Equiv.swap i j) ⁻¹' A) = μ A) :
    ∃ q : E → R⟦Γ⟧, (∀ a, 0 ≤ toLex (q a)) ∧ ∑ a, q a = 1 ∧
      ∀ A, MeasurableSet A → μ A = ∑ a ∈ Finset.univ with (fun _ : ℕ => a) ∈ A, q a := by
  have hX : IsCountablySeparated (ℕ → E) := isCountablySeparated_nat_pi
  refine ⟨fun a => μ {fun _ => a}, fun a => hμ.nonneg _ (hX.measurableSet_singleton _), ?_,
    fun A hA => eq_sum_const_of_swap_invariant hμ.toIsStrongHahnMeasure hswap hA⟩
  have h := eq_sum_const_of_swap_invariant hμ.toIsStrongHahnMeasure hswap MeasurableSet.univ
  rw [hμ.univ] at h
  simpa using h.symm

open Classical in
/-- `meas:cor:exchangeable`: every exchangeable strong Hahn probability on `E^ℕ` for a finite
alphabet `E` agrees on events with a mixture `∑_{a ∈ E} q_a δ_{(a,a,…)}` of constant sequences
with `q_a ≥ 0` and `∑_a q_a = 1`. -/
theorem IsStrongHahnProbability.exists_mixture_const [Fintype E] [Zero Γ] [One R]
    [LinearOrder R] (hμ : IsStrongHahnProbability μ) (hex : IsExchangeable μ) :
    ∃ q : E → R⟦Γ⟧, (∀ a, 0 ≤ toLex (q a)) ∧ ∑ a, q a = 1 ∧
      ∀ A, MeasurableSet A → μ A = ∑ a ∈ Finset.univ with (fun _ : ℕ => a) ∈ A, q a :=
  hμ.exists_mixture_const_of_swap_invariant hex.swap

end Exchangeable

section Bernoulli

variable {Γ R : Type*} [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]
  [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

omit [IsOrderedCancelAddMonoid Γ] [LinearOrder R] [IsStrictOrderedRing R] in
/-- A Hahn series with a nonzero constant coefficient and no negative exponent has order `0`. -/
theorem order_eq_zero_of_coeff_zero_ne_zero {a : R⟦Γ⟧} (h0 : a.coeff 0 ≠ 0)
    (hneg : ∀ g < 0, a.coeff g = 0) : a.order = 0 := by
  refine le_antisymm (order_le_of_coeff_ne_zero h0) (not_lt.mp fun hlt => ?_)
  exact coeff_order_eq_zero.not.mpr (ne_zero_of_coeff_ne_zero h0) (hneg _ hlt)

/-- For `a` of order `0` and `c ≠ 0`, every product `a^n c` has a nonzero coefficient at the
order of `c`. -/
theorem coeff_pow_mul_order_ne_zero {a c : R⟦Γ⟧} (ha : a ≠ 0) (ha0 : a.order = 0) (hc : c ≠ 0)
    (n : ℕ) : (a ^ n * c).coeff c.order ≠ 0 := by
  have han : a ^ n ≠ 0 := pow_ne_zero n ha
  have h := order_mul han hc
  rw [order_pow, ha0, smul_zero, zero_add] at h
  rw [← h]
  exact coeff_order_eq_zero.not.mpr (mul_ne_zero han hc)

/-- A strong Hahn measure cannot give pairwise disjoint events the masses `a^n c` with `a` of
order `0` and `c ≠ 0`: all of them contribute at the exponent `v(c)`, violating `(SH)`. -/
theorem not_forall_eq_pow_mul {X : Type*} [MeasurableSpace X] {μ : Set X → R⟦Γ⟧}
    (hμ : IsStrongHahnMeasure μ) {A : ℕ → Set X} (hA : ∀ n, MeasurableSet (A n))
    (hdisj : Pairwise (Function.onFun Disjoint A)) {a c : R⟦Γ⟧} (ha : a ≠ 0) (ha0 : a.order = 0)
    (hc : c ≠ 0) : ¬ ∀ n, μ (A n) = a ^ n * c := by
  intro hmass
  obtain ⟨s, hs, -⟩ := hμ.iUnion A hA hdisj
  refine Set.infinite_univ ((s.finite_co_support c.order).subset fun n _ => ?_)
  rw [Function.mem_support, hs n, hmass n]
  exact coeff_pow_mul_order_ne_zero ha ha0 hc n

/-- The cylinder of binary sequences equal to `b` before time `n` and to `!b` at time `n`. -/
def switchCylinder (b : Bool) (n : ℕ) : Set (ℕ → Bool) :=
  {x | ∀ i : Fin (n + 1), x i = if (i : ℕ) < n then b else !b}

/-- The switch cylinders are events of the product σ-algebra. -/
theorem measurableSet_switchCylinder (b : Bool) (n : ℕ) :
    MeasurableSet (switchCylinder b n) := by
  have h : switchCylinder b n = ⋂ i : Fin (n + 1),
      (fun x : ℕ → Bool => x i) ⁻¹' {if (i : ℕ) < n then b else !b} := by
    ext x
    simp [switchCylinder]
  rw [h]
  exact MeasurableSet.iInter fun i => measurable_pi_apply _ (measurableSet_singleton _)

/-- The switch cylinders with a fixed symbol are pairwise disjoint. -/
theorem pairwise_disjoint_switchCylinder (b : Bool) :
    Pairwise (Function.onFun Disjoint (switchCylinder b)) := by
  have key : ∀ m n, m < n → Disjoint (switchCylinder b m) (switchCylinder b n) := by
    intro m n hmn
    refine Set.disjoint_left.mpr fun x hm hn => ?_
    have h1 := hm ⟨m, Nat.lt_succ_self m⟩
    have h2 := hn ⟨m, by omega⟩
    simp only [lt_irrefl, if_false, hmn, if_true] at h1 h2
    rw [h1] at h2
    cases b <;> simp at h2
  intro m n hmn
  rcases lt_or_gt_of_ne hmn with h | h
  · exact key m n h
  · exact (key n m h).symm

/-- `meas:cor:exchangeable`, i.i.d. clause: no nondegenerate i.i.d. Bernoulli law on `{0,1}^ℕ`
with bias `0 < p < 1` in the lexicographically ordered Hahn series ring `R⟦Γ⟧` is a strong Hahn
measure (a fortiori not a strong Hahn probability); the ordinary bias case is
`not_isStrongHahnMeasure_of_bernoulli_C`. The cylinder hypothesis prescribes the masses of the
initial cylinders, `P(x_0 = s_0, …, x_{n-1} = s_{n-1}) = ∏ p^{s_i} (1 - p)^{1 - s_i}`. The proof
is direct: one of `p` and `1 - p` has order `0`, and the disjoint cylinders `b^n (!b)` have
masses `r_b^n r_{!b}`. -/
theorem not_isStrongHahnMeasure_of_bernoulli {p : R⟦Γ⟧} (hp0 : 0 < toLex p)
    (hp1 : toLex p < toLex (1 : R⟦Γ⟧)) {μ : Set (ℕ → Bool) → R⟦Γ⟧}
    (hcyl : ∀ (n : ℕ) (s : Fin n → Bool),
      μ {x | ∀ i : Fin n, x i = s i} = ∏ i, if s i then p else 1 - p) :
    ¬ IsStrongHahnMeasure μ := by
  intro hμ
  have hsub : toLex (1 - p) = toLex 1 - toLex p := rfl
  have hr : ∀ b : Bool, 0 < toLex (if b then p else 1 - p) ∧
      toLex (if b then p else 1 - p) ≤ toLex (1 : R⟦Γ⟧) := by
    intro b
    cases b
    · simp only [Bool.false_eq_true, if_false]
      rw [hsub]
      exact ⟨sub_pos.mpr hp1, sub_le_self _ hp0.le⟩
    · simp only [if_true]
      exact ⟨hp0, hp1.le⟩
  have hne : ∀ b : Bool, (if b then p else 1 - p) ≠ 0 := fun b h => by
    have h' := (hr b).1
    rw [h] at h'
    exact lt_irrefl _ h'
  have hneg : ∀ b : Bool, ∀ g < 0, (if b then p else 1 - p).coeff g = 0 := fun b _ hg =>
    coeff_eq_zero_of_neg_of_le_one (hr b).1.le (hr b).2 hg
  obtain ⟨b, hb⟩ : ∃ b : Bool, (if b then p else 1 - p).coeff 0 ≠ 0 := by
    by_contra h
    push Not at h
    have h1 := h true
    have h2 := h false
    simp only [if_true, Bool.false_eq_true, if_false, coeff_sub, coeff_one] at h1 h2
    rw [h1, sub_zero] at h2
    exact one_ne_zero h2
  refine not_forall_eq_pow_mul hμ (measurableSet_switchCylinder b)
    (pairwise_disjoint_switchCylinder b) (hne b)
    (order_eq_zero_of_coeff_zero_ne_zero hb (hneg b)) (hne !b) fun n => ?_
  have h : μ (switchCylinder b n) = _ := hcyl (n + 1) fun i => if (i : ℕ) < n then b else !b
  rw [h, Fin.prod_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.is_lt, if_true, Fin.val_last, lt_irrefl, if_false,
    Fin.prod_const]

/-- `meas:cor:exchangeable`, i.i.d. clause with an ordinary bias: for `0 < r < 1` in the
coefficient ring (for instance a real bias), the i.i.d. Bernoulli law with constant parameter
`C r` is not a strong Hahn measure. -/
theorem not_isStrongHahnMeasure_of_bernoulli_C {r : R} (hr0 : 0 < r) (hr1 : r < 1)
    {μ : Set (ℕ → Bool) → R⟦Γ⟧}
    (hcyl : ∀ (n : ℕ) (s : Fin n → Bool),
      μ {x | ∀ i : Fin n, x i = s i} = ∏ i, if s i then C r else 1 - C r) :
    ¬ IsStrongHahnMeasure μ := by
  have hpos : ∀ {t : R}, 0 < t → 0 < toLex (C t : R⟦Γ⟧) := fun {t} ht =>
    pos_of_coeff (i := 0) (fun j hj => by rw [C_apply, coeff_single_of_ne hj.ne])
      (by rwa [C_apply, coeff_single_same])
  have h : (C (1 - r) : R⟦Γ⟧) = 1 - C r := by rw [map_sub, map_one]
  have h1 : 0 < toLex (1 : R⟦Γ⟧) - toLex (C r) := by
    have h2 := hpos (sub_pos.mpr hr1)
    rw [h] at h2
    exact h2
  exact not_isStrongHahnMeasure_of_bernoulli (hpos hr0) (sub_pos.mp h1) hcyl

end Bernoulli

end

end Surreal.HahnSeries
