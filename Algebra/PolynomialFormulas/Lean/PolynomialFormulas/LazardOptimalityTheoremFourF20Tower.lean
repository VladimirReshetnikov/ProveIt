import PolynomialFormulas.LazardOptimalityTheoremFourDegree
import PolynomialFormulas.QuinticScalarGaloisBridge
import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Sylow

/-!
# The `F₂₀` subgroup chain behind Lazard's Theorem 4

This file closes the group-to-field gap in the corrected radical-presentation
part of Lazard's Theorem 4.  It does not assume an index-two field tower.
Instead it starts with the subgroup information furnished by the quintic
Galois representation:

* the root-permutation group is transitive;
* it is contained in a conjugate of the standard Frobenius group `F₂₀`.

Those facts force its order to be `5 * 2^e` for `e ≤ 2`.  Sylow's theorems
then give a unique normal subgroup of order five.  For order twenty, Cauchy's
theorem in the order-four quotient supplies the intermediate subgroup of
index two.  Thus one obtains an honest exact chain of `e` index-two
subgroups, not merely the numerical equality `|G| = 5 * 2^e`.

The finite Galois correspondence reverses this chain.  Every resulting field
step has degree two; separability inherited from the ambient Galois extension
makes it a quadratic Galois extension.  Consequently the output is precisely
the `IsIndexTwoGaloisTower` input consumed by
`LazardOptimalityTheoremFourDegree`'s Kummer construction.
-/

open scoped Polynomial

namespace LeanProofs.PolynomialFormulas.LazardOptimalityTheoremFourF20Tower

open LeanProofs.PolynomialFormulas
open LazardOptimalityTheoremFourDegree
open QuinticScalarGaloisBridge
open Fin5Solvable Fin5TransitiveC5

/-! ## Exact index-two subgroup chains -/

/-- A decreasing exact-length chain of subgroups, starting at `K`, in which
each new subgroup has relative index two in the preceding subgroup.  Under
Galois correspondence this becomes an increasing tower of quadratic fields. -/
inductive IsIndexTwoSubgroupTower
    (G : Type*) [Group G] (K : Subgroup G) : ℕ → Subgroup G → Prop
  | zero : IsIndexTwoSubgroupTower G K 0 K
  | succ {n : ℕ} {H J : Subgroup G}
      (tower : IsIndexTwoSubgroupTower G K n H)
      (hJH : J ≤ H) (index_two : J.relIndex H = 2) :
      IsIndexTwoSubgroupTower G K (n + 1) J

namespace IsIndexTwoSubgroupTower

theorem terminal_le_start
    {G : Type*} [Group G] {K H : Subgroup G} {n : ℕ}
    (h : IsIndexTwoSubgroupTower G K n H) : H ≤ K := by
  induction h with
  | zero => exact le_rfl
  | succ _ hJH _ ih => exact hJH.trans ih

/-- Transport an exact index-two subgroup tower across a group equivalence. -/
theorem map_equiv
    {G G' : Type*} [Group G] [Group G']
    {K H : Subgroup G} {n : ℕ}
    (h : IsIndexTwoSubgroupTower G K n H) (e : G ≃* G') :
    IsIndexTwoSubgroupTower G'
      (K.map e.toMonoidHom) n (H.map e.toMonoidHom) := by
  induction h with
  | zero => exact IsIndexTwoSubgroupTower.zero
  | succ tower hJH hindex ih =>
      exact IsIndexTwoSubgroupTower.succ ih
        (Subgroup.map_mono hJH)
        ((Subgroup.relIndex_map_map_of_injective _ _ e.injective).trans hindex)

end IsIndexTwoSubgroupTower

/-! ## Fixed-field transport -/

section FixedField

variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]

/-- The relative degree between two nested fixed fields is the relative index
of the corresponding subgroups.  This is Artin's fixed-field degree theorem
combined with the tower law; no normality assumption is needed. -/
theorem finrank_extendScalars_fixedField_eq_relIndex
    [FiniteDimensional F Ω]
    {H K : Subgroup Gal(Ω/F)} (hHK : H ≤ K) :
    Module.finrank (IntermediateField.fixedField K)
        (IntermediateField.extendScalars
          (IntermediateField.fixedField_le hHK)) =
      H.relIndex K := by
  let A : IntermediateField F Ω := IntermediateField.fixedField K
  let B : IntermediateField F Ω := IntermediateField.fixedField H
  let hAB : A ≤ B := IntermediateField.fixedField_le hHK
  let E : IntermediateField A Ω := IntermediateField.extendScalars hAB
  have htower := Module.finrank_mul_finrank A E Ω
  change Module.finrank A E * Module.finrank B Ω = Module.finrank A Ω at htower
  rw [IntermediateField.finrank_fixedField_eq_card H,
    IntermediateField.finrank_fixedField_eq_card K] at htower
  have hcard : Nat.card H * H.relIndex K = Nat.card K := by
    have h := (H.subgroupOf K).card_mul_index
    change Nat.card (H.subgroupOf K) * H.relIndex K = Nat.card K at h
    rw [Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe hHK).toEquiv] at h
    exact h
  apply Nat.mul_right_cancel (Nat.card_pos (α := H))
  calc
    Module.finrank A E * Nat.card H = Nat.card K := htower
    _ = H.relIndex K * Nat.card H := by simpa [mul_comm] using hcard.symm

/-- Galois correspondence sends an exact index-two subgroup chain to an exact
index-two Galois field tower.  The Galois property of each field step is
proved from its derived degree two and ambient separability, rather than
being smuggled in as a tower hypothesis. -/
theorem IsIndexTwoSubgroupTower.fixedField
    [FiniteDimensional F Ω] [IsGalois F Ω]
    {K H : Subgroup Gal(Ω/F)} {n : ℕ}
    (h : IsIndexTwoSubgroupTower Gal(Ω/F) K n H) :
    IsIndexTwoGaloisTower F Ω
      (IntermediateField.fixedField K) n
      (IntermediateField.fixedField H) := by
  induction h with
  | zero => exact IsIndexTwoGaloisTower.zero
  | @succ n H J tower hJH hindex ih =>
      let A : IntermediateField F Ω := IntermediateField.fixedField H
      let B : IntermediateField F Ω := IntermediateField.fixedField J
      let hAB : A ≤ B := IntermediateField.fixedField_le hJH
      let E : IntermediateField A Ω := IntermediateField.extendScalars hAB
      letI : FiniteDimensional A E := inferInstance
      have hdegree : Module.finrank A E = 2 := by
        exact (finrank_extendScalars_fixedField_eq_relIndex hJH).trans hindex
      letI : Algebra.IsQuadraticExtension A E :=
        { finrank_eq_two' := hdegree }
      have hgalois : IsGalois A E := inferInstance
      exact IsIndexTwoGaloisTower.succ ih hAB inferInstance hgalois hdegree

end FixedField

/-! ## The order-`5 * 2^e` group calculation -/

section FiniteGroup

variable {G : Type*} [Group G] [Finite G]

/-- A normal subgroup of index four has an intermediate subgroup at which
both relative indices are two.  Passing to the order-four quotient isolates
the only group-theoretic construction needed by the `e = 2` case below. -/
theorem exists_intermediate_indexTwo_of_normal_index_four
    (P : Subgroup G) [P.Normal] (hPindex : P.index = 4) :
    ∃ M : Subgroup G,
      P ≤ M ∧ M.index = 2 ∧ P.relIndex M = 2 := by
  classical
  let Q := G ⧸ P
  have hQcard : Nat.card Q = 4 := by
    change P.index = 4
    exact hPindex
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ :=
    exists_prime_orderOf_dvd_card' (G := Q) 2 (by
      rw [hQcard]
      norm_num)
  let R : Subgroup Q := Subgroup.zpowers x
  have hRcard : Nat.card R = 2 := by
    rw [Nat.card_zpowers, hx]
  let q : G →* Q := QuotientGroup.mk' P
  have hq_surjective : Function.Surjective q :=
    QuotientGroup.mk'_surjective P
  let M : Subgroup G := R.comap q
  have hPM : P ≤ M := by
    intro g hg
    change q g ∈ R
    have hq : q g = 1 := (QuotientGroup.eq_one_iff g).mpr hg
    rw [hq]
    exact R.one_mem
  have hRindex : R.index = 2 := by
    have hmul := R.index_mul_card
    rw [hRcard, hQcard] at hmul
    omega
  have hMindex : M.index = 2 := by
    change (R.comap q).index = 2
    rw [R.index_comap_of_surjective hq_surjective, hRindex]
  have hPrelM : P.relIndex M = 2 := by
    have hmul :=
      Subgroup.relIndex_mul_relIndex P M ⊤ hPM le_top
    rw [Subgroup.relIndex_top_right, Subgroup.relIndex_top_right,
      hMindex, hPindex] at hmul
    omega
  exact ⟨M, hPM, hMindex, hPrelM⟩

/-- A finite group of order `5 * 2^e`, with `e ≤ 2`, has a unique normal
Sylow-five subgroup and an exact `e`-step index-two chain from the whole group
to that subgroup. -/
theorem exists_normal_sylowFive_and_indexTwoSubgroupTower
    {e : ℕ} (he : e ≤ 2) (hcard : Nat.card G = 5 * 2 ^ e) :
    ∃ P : Subgroup G,
      Nat.card P = 5 ∧ P.Normal ∧
        IsIndexTwoSubgroupTower G ⊤ e P := by
  classical
  letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let P : Sylow 5 G := default
  have hPcard : Nat.card P = 5 := by
    rw [P.card_eq_multiplicity, hcard]
    rw [Nat.factorization_mul (by norm_num)
      (pow_ne_zero e (by norm_num : (2 : ℕ) ≠ 0))]
    rw [Nat.factorization_pow, Finsupp.add_apply, Finsupp.smul_apply,
      Nat.Prime.factorization_self Nat.prime_five,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬5 ∣ 2)]
    simp
  have hPindex : P.index = 2 ^ e := by
    have hmul := P.index_mul_card
    rw [hPcard, hcard] at hmul
    exact Nat.mul_right_cancel (by norm_num : 0 < 5)
      (by simpa [mul_comm] using hmul)
  have hn_dvd : Nat.card (Sylow 5 G) ∣ 2 ^ e := by
    simpa only [hPindex] using P.card_dvd_index
  have hn_le_pow : Nat.card (Sylow 5 G) ≤ 2 ^ e :=
    Nat.le_of_dvd (by positivity) hn_dvd
  have hpow_le : 2 ^ e ≤ 4 := by
    interval_cases e <;> norm_num
  have hn_lt_five : Nat.card (Sylow 5 G) < 5 :=
    (hn_le_pow.trans hpow_le).trans_lt (by norm_num)
  have hn_eq_one : Nat.card (Sylow 5 G) = 1 :=
    (card_sylow_modEq_one 5 G).eq_of_lt_of_lt hn_lt_five (by norm_num)
  letI : Subsingleton (Sylow 5 G) :=
    Finite.card_le_one_iff_subsingleton.mp hn_eq_one.le
  have hPnormal : (P : Subgroup G).Normal := P.normal_of_subsingleton
  letI : (P : Subgroup G).Normal := hPnormal
  interval_cases e
  · have hGcard : Nat.card G = 5 := by simpa using hcard
    have hPtop : (P : Subgroup G) = ⊤ :=
      Subgroup.eq_top_of_card_eq
        (H := (P : Subgroup G)) (hPcard.trans hGcard.symm)
    refine ⟨P, hPcard, hPnormal, ?_⟩
    simpa only [hPtop] using
      (IsIndexTwoSubgroupTower.zero (G := G) (K := (⊤ : Subgroup G)))
  · have hPindexTwo : P.index = 2 := by simpa using hPindex
    refine ⟨P, hPcard, hPnormal, ?_⟩
    simpa only [Nat.zero_add] using
      (IsIndexTwoSubgroupTower.succ
        (IsIndexTwoSubgroupTower.zero (G := G) (K := (⊤ : Subgroup G)))
        (show (P : Subgroup G) ≤ ⊤ from le_top)
        (by simpa only [Subgroup.relIndex_top_right] using hPindexTwo))
  · have hPindexFour : P.index = 4 := by simpa using hPindex
    obtain ⟨M, hPM, hMindex, hPrelM⟩ :=
      exists_intermediate_indexTwo_of_normal_index_four
        (P : Subgroup G) hPindexFour
    have htowerM : IsIndexTwoSubgroupTower G ⊤ 1 M := by
      simpa only [Nat.zero_add] using
        (IsIndexTwoSubgroupTower.succ
          (IsIndexTwoSubgroupTower.zero (G := G) (K := (⊤ : Subgroup G)))
          (show M ≤ (⊤ : Subgroup G) from le_top)
          (by simpa only [Subgroup.relIndex_top_right] using hMindex))
    refine ⟨P, hPcard, hPnormal, ?_⟩
    simpa using
      (IsIndexTwoSubgroupTower.succ htowerM hPM hPrelM)

end FiniteGroup

/-! ## Adapter from the actual quintic permutation representation -/

/-- The polynomial Galois-group wrapper and the ordinary automorphism group
have the same elements but intentionally carry separately generated group
instances.  This explicit identity equivalence is the safe transport between
them; relying on instance-level definitional equality is brittle. -/
def polynomialGalMulEquiv (p : ℚ[X]) :
    p.Gal ≃* Gal(p.SplittingField/ℚ) where
  toFun := fun σ => σ
  invFun := fun σ => σ
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_mul' := fun _ _ => rfl

/-- Transitivity and containment in a conjugate of `F₂₀` force the order of
the permutation group to be exactly `5`, `10`, or `20`, expressed uniformly
as `5 * 2^e` with `e ≤ 2`. -/
theorem exists_twoExponent_of_pretransitive_le_conjugate_standardF20
    (H : Subgroup S5) [MulAction.IsPretransitive H (Fin 5)]
    (g : S5)
    (hH : H ≤ standardF20.map (MulAut.conj g).toMonoidHom) :
    ∃ e : ℕ, e ≤ 2 ∧ Nat.card H = 5 * 2 ^ e := by
  have hfive : 5 ∣ Nat.card H := five_dvd_natCard_of_pretransitive H
  have hcontainer :
      Nat.card (standardF20.map (MulAut.conj g).toMonoidHom) = 20 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective,
      natCard_standardF20]
  have hdvd : Nat.card H ∣ 20 := by
    simpa only [hcontainer] using Subgroup.card_dvd_of_le hH
  let n := Nat.card H
  change 5 ∣ n at hfive
  change n ∣ 20 at hdvd
  have hnle : n ≤ 20 := Nat.le_of_dvd (by norm_num) hdvd
  have hnpos : 0 < n := by
    by_contra hn
    have hnzero : n = 0 := Nat.eq_zero_of_not_pos hn
    rw [hnzero] at hdvd
    norm_num at hdvd
  have hcases : n = 5 ∨ n = 10 ∨ n = 20 := by
    obtain ⟨k, hk⟩ := hfive
    have hkpos : 0 < k := by omega
    have hkle : k ≤ 4 := by omega
    have hkcases : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
    rcases hkcases with rfl | rfl | rfl | rfl
    · exact Or.inl (by omega)
    · exact Or.inr (Or.inl (by omega))
    · have hn15 : n = 15 := by omega
      rw [hn15] at hdvd
      norm_num at hdvd
    · exact Or.inr (Or.inr (by omega))
  rcases hcases with hfiveOrder | htenOrder | htwentyOrder
  · exact ⟨0, by norm_num, by simp [n, hfiveOrder]⟩
  · exact ⟨1, by norm_num, by simp [n, htenOrder]⟩
  · exact ⟨2, by norm_num, by simp [n, htwentyOrder]⟩

/-- Paper-shaped fixed-field output from the actual faithful quintic Galois
representation.  The hypothesis is exactly the `Gal ≤ conjugate(F₂₀)` datum
returned by `QuinticScalarGaloisBridge`, not a preselected radical tower.

The terminal subgroup has order five.  Therefore the remaining top extension
has degree five and is Galois; only the primitive-fifth-root hypothesis still
has to be supplied before applying the Kummer theorem. -/
theorem exists_fixedField_indexTwoTower_of_le_conjugate_standardF20
    (p : ℚ[X]) (hp : Irreducible p) (hdeg : p.natDegree = 5)
    (g : S5)
    (hcontain : rootPermutationGroup p hp hdeg ≤
      standardF20.map (MulAut.conj g).toMonoidHom) :
    ∃ (e : ℕ) (P : Subgroup Gal(p.SplittingField/ℚ)),
      e ≤ 2 ∧ Nat.card p.Gal = 5 * 2 ^ e ∧
      Nat.card P = 5 ∧ P.Normal ∧
      IsIndexTwoGaloisTower ℚ p.SplittingField
        (⊥ : IntermediateField ℚ p.SplittingField) e
        (IntermediateField.fixedField P) ∧
      FiniteDimensional (IntermediateField.fixedField P) p.SplittingField ∧
      IsGalois (IntermediateField.fixedField P) p.SplittingField ∧
      Module.finrank (IntermediateField.fixedField P) p.SplittingField = 5 := by
  classical
  letI : p.IsSplittingField ℚ p.SplittingField :=
    Polynomial.IsSplittingField.splittingField p
  letI : FiniteDimensional ℚ p.SplittingField :=
    Polynomial.IsSplittingField.finiteDimensional p.SplittingField p
  haveI : IsGalois ℚ p.SplittingField :=
    IsGalois.of_separable_splitting_field (p := p) hp.separable
  let H := rootPermutationGroup p hp hdeg
  letI : MulAction.IsPretransitive H (Fin 5) :=
    rootPermutationGroup_isPretransitive p hp hdeg
  obtain ⟨e, he, hHcard⟩ :=
    exists_twoExponent_of_pretransitive_le_conjugate_standardF20 H g hcontain
  have hGalCard : Nat.card p.Gal = 5 * 2 ^ e := by
    calc
      Nat.card p.Gal = Nat.card H :=
        Nat.card_congr (galEquivRootPermutationGroup p hp hdeg).toEquiv
      _ = 5 * 2 ^ e := hHcard
  obtain ⟨P₀, hP₀card, hP₀normal, hP₀tower⟩ :=
    exists_normal_sylowFive_and_indexTwoSubgroupTower he hGalCard
  let galEquiv := polynomialGalMulEquiv p
  let P : Subgroup Gal(p.SplittingField/ℚ) :=
    P₀.map galEquiv.toMonoidHom
  have hPcard : Nat.card P = 5 := by
    dsimp only [P]
    rw [Subgroup.card_map_of_injective galEquiv.injective, hP₀card]
  have hPnormal : P.Normal := by
    dsimp only [P]
    exact hP₀normal.map galEquiv.toMonoidHom galEquiv.surjective
  have hsubgroupTower :
      IsIndexTwoSubgroupTower Gal(p.SplittingField/ℚ) ⊤ e P := by
    have hmapped := hP₀tower.map_equiv galEquiv
    simpa only [P,
      Subgroup.map_top_of_surjective galEquiv.toMonoidHom
        galEquiv.surjective] using hmapped
  letI : P.Normal := hPnormal
  have hfieldTower :=
    hsubgroupTower.fixedField (F := ℚ) (Ω := p.SplittingField)
  have hfieldTower' :
      IsIndexTwoGaloisTower ℚ p.SplittingField
        (⊥ : IntermediateField ℚ p.SplittingField) e
        (IntermediateField.fixedField P) := by
    simpa only [IsGalois.fixedField_top] using hfieldTower
  have hfinalDegree :
      Module.finrank (IntermediateField.fixedField P) p.SplittingField = 5 := by
    rw [IntermediateField.finrank_fixedField_eq_card, hPcard]
  exact ⟨e, P, he, hGalCard, hPcard, hPnormal, hfieldTower', inferInstance,
    inferInstance, hfinalDegree⟩

/-- The same adapter with the paper's solvability premise.  The existing
quintic Galois bridge first turns solvability into containment in a conjugate
of `F₂₀`; the preceding theorem then derives the subgroup and fixed-field
towers. -/
theorem exists_fixedField_indexTwoTower_of_isSolvable
    (p : ℚ[X]) (hp : Irreducible p) (hdeg : p.natDegree = 5)
    (hsolvable : IsSolvable p.Gal) :
    ∃ (e : ℕ) (P : Subgroup Gal(p.SplittingField/ℚ)),
      e ≤ 2 ∧ Nat.card p.Gal = 5 * 2 ^ e ∧
      Nat.card P = 5 ∧ P.Normal ∧
      IsIndexTwoGaloisTower ℚ p.SplittingField
        (⊥ : IntermediateField ℚ p.SplittingField) e
        (IntermediateField.fixedField P) ∧
      FiniteDimensional (IntermediateField.fixedField P) p.SplittingField ∧
      IsGalois (IntermediateField.fixedField P) p.SplittingField ∧
      Module.finrank (IntermediateField.fixedField P) p.SplittingField = 5 := by
  obtain ⟨g, hcontain⟩ :=
    (gal_isSolvable_iff_le_conjugate_standardF20 p hp hdeg).mp hsolvable
  exact exists_fixedField_indexTwoTower_of_le_conjugate_standardF20
    p hp hdeg g hcontain

end LeanProofs.PolynomialFormulas.LazardOptimalityTheoremFourF20Tower
