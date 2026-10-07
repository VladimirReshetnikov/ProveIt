/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.CommonIntegralModelEquivalences
import OAI.Combinatorics.Progressions.Estimates.NativeEqualDimension

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.NativeModelEquiv

open Module CircleFourier
open scoped TensorProduct NNReal

variable {σ L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {E : RationalFilteredNilmanifold M s d}
  (e : NativeModelEquiv D E) {w : σ → ℕ}

noncomputable def transport (T : D.Niltest w) : E.Niltest w where
  orbit := e.mapOrbit T.orbit
  observable := T.observable ∘ e.symm.spaceMap
  normBound := T.normBound
  lipBound := T.lipBound * coordinateLipschitzBound d d 1
  norm_le x := T.norm_le _
  lipschitz := by
    let := D.metricSpace
    let := E.metricSpace
    exact T.lipschitz.comp e.symm.spaceMap_lipschitz

theorem transport_orbit (T : D.Niltest w) : (e.transport T).orbit = e.mapOrbit T.orbit := rfl

theorem transport_normBound (T : D.Niltest w) : (e.transport T).normBound = T.normBound := rfl

theorem transport_eval (T : D.Niltest w) (x : σ → ℤ) : (e.transport T).eval x = T.eval x := by
  change T.observable (e.symm.spaceMap
    (QuotientGroup.mk (E.filtration.realification.polynomialOrbitEval w x (e.mapOrbit T.orbit)))) = _
  rw [e.mapOrbit_eval, ← e.spaceMap_mk, e.symm_spaceMap_apply]
  rfl

theorem transport_evalCyclic (T : D.Niltest w) (N : ℕ) [NeZero N] (x : σ → ZMod N) :
    (e.transport T).evalCyclic N x = T.evalCyclic N x := e.transport_eval T _

theorem transport_unit_interval (T : D.Niltest w) (hT : T.UnitIntervalValued) :
    (e.transport T).UnitIntervalValued := fun x => hT (e.symm.spaceMap x)

theorem transport_complexity (T : D.Niltest w) {p : ℝ} (hp : 0 ≤ p)
    (hT : T.ComplexityLE p) (hE : E.GeometryComplexityLE p) :
    (e.transport T).ComplexityLE (p + (p + 2) ^ 2) := by
  have hK : (coordinateLipschitzBound d d 1 : ℝ) ≤ Real.exp ((p + 2) ^ 2) :=
    coordinateLipschitzBound_le_exp d d 1 hp hT.1.1 hE.1 (Real.one_le_exp_iff.mpr hp)
  have h1 : 1 ≤ Real.exp ((p + 2) ^ 2) := Real.one_le_exp_iff.mpr (sq_nonneg _)
  refine ⟨hE.mono E (le_add_of_nonneg_right (sq_nonneg _)), ?_⟩
  change Real.log (2 + (T.normBound : ℝ) +
    (T.lipBound : ℝ) * coordinateLipschitzBound d d 1) ≤ p + (p + 2) ^ 2
  apply (Real.log_le_iff_le_exp (by positivity)).mpr
  calc
    2 + (T.normBound : ℝ) + (T.lipBound : ℝ) * coordinateLipschitzBound d d 1 ≤
        (2 + (T.normBound : ℝ)) * Real.exp ((p + 2) ^ 2) +
          (T.lipBound : ℝ) * Real.exp ((p + 2) ^ 2) :=
      add_le_add (le_mul_of_one_le_right (by positivity) h1)
        (mul_le_mul_of_nonneg_left hK T.lipBound.coe_nonneg)
    _ = (2 + (T.normBound : ℝ) + (T.lipBound : ℝ)) * Real.exp ((p + 2) ^ 2) := by ring
    _ ≤ Real.exp p * Real.exp ((p + 2) ^ 2) :=
      mul_le_mul_of_nonneg_right (Niltest.observable_budget hT) (Real.exp_pos _).le
    _ = Real.exp (p + (p + 2) ^ 2) := (Real.exp_add _ _).symm

omit [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)] in
theorem transported_frequency_basis (eta : L →ₗ[ℚ] ℚ) (i : Fin d) :
    (eta.comp e.toLieEquiv.symm.toLieHom.toLinearMap) (E.basis i) = eta (D.basis i) := by
  change eta (e.symm.toLieEquiv (E.basis i)) = _
  rw [e.symm.map_basis]

theorem transport_vertical (T : D.Niltest w) (eta : L →ₗ[ℚ] ℚ)
    (hT : ∀ z, z ∈ D.filtration.realification.subgroup s → ∀ x,
      T.observable (z • x) = character ((realifyFunctional eta z.coord : ℝ) : CircleFourier.Circle) * T.observable x)
    (z : E.RealGroup) (hz : z ∈ E.filtration.realification.subgroup s) (x : E.Space) :
    (e.transport T).observable (z • x) =
      character ((realifyFunctional (eta.comp e.toLieEquiv.symm.toLieHom.toLinearMap) z.coord : ℝ) : CircleFourier.Circle) *
        (e.transport T).observable x := by
  change T.observable (e.symm.spaceMap (z • x)) = _
  rw [e.symm.spaceMap_smul]
  have heq : realifyFunctional (eta.comp e.toLieEquiv.symm.toLieHom.toLinearMap) z.coord =
      realifyFunctional eta (e.symm.realGroupEquiv z).coord := by
    calc
      _ = realifyFunctional eta
          (e.toLieEquiv.symm.toLieHom.toLinearMap.baseChange ℝ z.coord) :=
        realifyFunctional_comp eta e.toLieEquiv.symm.toLieHom.toLinearMap z.coord
      _ = _ := rfl
  rw [heq]
  exact hT _ (e.symm.map_real_layer s z hz) _

theorem transport_kernel_invariant (T : D.Niltest w) {J : Type*} (eta : J → L →ₗ[ℚ] ℚ)
    (hT : ∀ z, z ∈ D.filtration.realification.subgroup s →
      (∀ j, realifyFunctional (eta j) z.coord = 0) → ∀ x, T.observable (z • x) = T.observable x)
    (z : E.RealGroup) (hz : z ∈ E.filtration.realification.subgroup s)
    (hzero : ∀ j, realifyFunctional ((eta j).comp e.toLieEquiv.symm.toLieHom.toLinearMap) z.coord = 0)
    (x : E.Space) : (e.transport T).observable (z • x) = (e.transport T).observable x := by
  change T.observable (e.symm.spaceMap (z • x)) = T.observable (e.symm.spaceMap x)
  rw [e.symm.spaceMap_smul]
  apply hT _ (e.symm.map_real_layer s z hz) _ _
  intro j
  calc
    _ = realifyFunctional (eta j)
        (e.toLieEquiv.symm.toLieHom.toLinearMap.baseChange ℝ z.coord) := rfl
    _ = realifyFunctional ((eta j).comp e.toLieEquiv.symm.toLieHom.toLinearMap) z.coord :=
      (realifyFunctional_comp (eta j) e.toLieEquiv.symm.toLieHom.toLinearMap z.coord).symm
    _ = 0 := hzero j

end Erdos3.RationalFilteredNilmanifold.NativeModelEquiv

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

theorem exists_common_native_niltest_model (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {G σ : Type*} {L : G → Type*}
      [∀ h, LieRing (L h)] [∀ h, LieAlgebra ℚ (L h)]
      [∀ h, TopologicalSpace (ℝ ⊗[ℚ] L h)] [∀ h, IsTopologicalAddGroup (ℝ ⊗[ℚ] L h)]
      [∀ h, ContinuousSMul ℝ (ℝ ⊗[ℚ] L h)] [∀ h, T2Space (ℝ ⊗[ℚ] L h)] {d : ℕ}
      (D : ∀ h, RationalFilteredNilmanifold (L h) s d) {w : σ → ℕ}
      (T : ∀ h, (D h).Niltest w) (H : Finset G), H.Nonempty →
      ∀ {p : ℝ}, 0 ≤ p → (∀ h, (T h).ComplexityLE p) →
      ∃ h₀ ∈ H, ∃ E : RationalFilteredNilmanifold (L h₀) s d,
        E.GeometryComplexityLE ((p + C) ^ C) ∧
        ∃ (H' : Finset G) (S : G → E.Niltest w),
          H' ⊆ H ∧ h₀ ∈ H' ∧ Real.exp (-((p + C) ^ C)) * H.card ≤ (H'.card : ℝ) ∧
          ∀ h ∈ H', (S h).ComplexityLE ((p + C) ^ C) ∧ (S h).normBound = (T h).normBound ∧
            (∀ x : σ → ℤ, (S h).eval x = (T h).eval x) ∧
            ((T h).UnitIntervalValued → (S h).UnitIntervalValued) := by
  classical
  obtain ⟨c, _, hmodels⟩ := exists_common_integral_models s
  let X : Polynomial ℕ := Polynomial.X
  let Q := X + (X + Polynomial.C c) ^ c
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (Q + (Q + 2) ^ 2)
  refine ⟨C, hC, ?_⟩
  intro G σ L _ _ _ _ _ _ d D w T H hH p hp hT
  let q := p + (p + c) ^ c
  have hc0 : 0 ≤ (p + c) ^ c := by positivity
  have hpq : p ≤ q := le_add_of_nonneg_right hc0
  have hcq : (p + c) ^ c ≤ q := le_add_of_nonneg_left hp
  have hq0 : 0 ≤ q := hp.trans hpq
  have hbud : q + (q + 2) ^ 2 ≤ (p + C) ^ C := by
    simpa [Q, X, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := (le_add_of_nonneg_right (sq_nonneg _)).trans hbud
  obtain ⟨B, Λ, hB, hin, hout, hcover, h₀, hh₀, H', hsub, hh₀', hsame, hlarge⟩ :=
    hmodels D H hH hp (fun h => (hT h).1)
  let E₀ := (D h₀).withLattice (Λ h₀) (B h₀) (hB h₀) (hin h₀) (hout h₀)
  have hE₀ : E₀.GeometryComplexityLE q := (hcover h₀).2.2.2.mono E₀ hcq
  have hbuild (h : {h // h ∈ H'}) : ∃ S : E₀.Niltest w,
      S.ComplexityLE ((p + C) ^ C) ∧ S.normBound = (T h.val).normBound ∧
      (∀ x : σ → ℤ, S.eval x = (T h.val).eval x) ∧
      ((T h.val).UnitIntervalValued → S.UnitIntervalValued) := by
    let E₁ := (D h.val).withLattice (Λ h.val) (B h.val) (hB h.val) (hin h.val) (hout h.val)
    have hE₁ : E₁.GeometryComplexityLE q := (hcover h.val).2.2.2.mono E₁ hcq
    have hcode : E₁.rationalModelCoordinates = E₀.rationalModelCoordinates := (hsame h.val h.property).2
    have hcoords₁ : bchSubgroupCoordinates E₁.basis E₁.lattice = scaledIntegerGrid (B h₀) := by
      change bchSubgroupCoordinates (D h.val).basis (Λ h.val) = _
      rw [(hcover h.val).2.2.1, (hsame h.val h.property).1]
    let e := nativeModelEquivOfCoordinates E₁ E₀ hcode (B h₀) hcoords₁ (hcover h₀).2.2.1
    let T₁ := (T h.val).onSublattice (Λ h.val) (B h.val) (hB h.val)
      (hin h.val) (hout h.val) (hcover h.val).2.1
    have hT₁ : T₁.ComplexityLE q := (T h.val).onSublattice_complexity
      (Λ h.val) (B h.val) (hB h.val) (hin h.val) (hout h.val) (hcover h.val).2.1
      ((hT h.val).mono hpq) hE₁
    refine ⟨e.transport T₁, (e.transport_complexity T₁ hq0 hT₁ hE₀).mono hbud, rfl, ?_, ?_⟩
    · intro x
      exact e.transport_eval T₁ x
    · intro ht
      apply e.transport_unit_interval
      exact (T h.val).onSublattice_unit_interval (Λ h.val) (B h.val) (hB h.val)
        (hin h.val) (hout h.val) (hcover h.val).2.1 ht
  choose S hS using hbuild
  let S₀ : G → E₀.Niltest w := fun h =>
    if hh : h ∈ H' then S ⟨h, hh⟩ else Niltest.const E₀ w 0
  refine ⟨h₀, hh₀, E₀, hE₀.mono E₀ hqC, H', S₀, hsub, hh₀', ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg (hcq.trans hqC)))
      (Nat.cast_nonneg _)).trans hlarge
  · intro h hh
    simpa only [S₀, dite_eq_left hh] using hS ⟨h, hh⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

theorem exists_common_variable_dimension_niltest_model (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {G σ : Type*} {L : G → Type*}
      [∀ h, LieRing (L h)] [∀ h, LieAlgebra ℚ (L h)]
      [∀ h, TopologicalSpace (ℝ ⊗[ℚ] L h)] [∀ h, IsTopologicalAddGroup (ℝ ⊗[ℚ] L h)]
      [∀ h, ContinuousSMul ℝ (ℝ ⊗[ℚ] L h)] [∀ h, T2Space (ℝ ⊗[ℚ] L h)] {d : G → ℕ}
      (D : ∀ h, RationalFilteredNilmanifold (L h) s (d h)) {w : σ → ℕ}
      (T : ∀ h, (D h).Niltest w) (H : Finset G), H.Nonempty →
      ∀ {p : ℝ}, 0 ≤ p → (∀ h, (T h).ComplexityLE p) →
      ∃ h₀ ∈ H, ∃ E : RationalFilteredNilmanifold (L h₀) s (d h₀),
        E.GeometryComplexityLE ((p + C) ^ C) ∧
        ∃ (H' : Finset G) (S : G → E.Niltest w),
          H' ⊆ H ∧ h₀ ∈ H' ∧ Real.exp (-((p + C) ^ C)) * H.card ≤ (H'.card : ℝ) ∧
          ∀ h ∈ H', (S h).ComplexityLE ((p + C) ^ C) ∧ (S h).normBound = (T h).normBound ∧
            (∀ x : σ → ℤ, (S h).eval x = (T h).eval x) ∧
            ((T h).UnitIntervalValued → (S h).UnitIntervalValued) := by
  classical
  obtain ⟨c, _, hmodels⟩ := exists_common_native_niltest_model s
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C c) ^ c + X + 1)
  refine ⟨C, hC, ?_⟩
  intro G σ L _ _ _ _ _ _ d D w T H hH p hp hT
  let q := (p + c) ^ c
  have hbud : q + p + 1 ≤ (p + C) ^ C := by
    simpa [X, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith
  have hpexp : p ≤ Real.exp p := by linarith [Real.add_one_le_exp p]
  obtain ⟨hbase, _, H₀, hsub₀, hhbase, hsame, hlarge₀⟩ :=
    exists_common_bounded_moduli H hH (fun h (_ : Unit) => d h) hp
      (fun h _ _ => (hT h).1.1.trans hpexp)
  have hdim (h : {h // h ∈ H₀}) : d h.val = d hbase := congrFun (hsame h.val h.property) ()
  let D₀ := fun h : {h // h ∈ H₀} => (D h.val).castDimension (hdim h)
  let T₀ := fun h : {h // h ∈ H₀} => (T h.val).castDimension (hdim h)
  have hT₀ (h : {h // h ∈ H₀}) : (T₀ h).ComplexityLE p :=
    ((T h.val).castDimension_complexity (hdim h) p).mpr (hT h.val)
  obtain ⟨a, _, E₀, hE₀, H₁, S₁, _, ha, hlarge₁, hS₁⟩ :=
    hmodels D₀ T₀ Finset.univ ⟨⟨hbase, hhbase⟩, Finset.mem_univ _⟩ hp hT₀
  let E := E₀.castDimension (hdim a).symm
  let H' := H₁.image Subtype.val
  let S : G → E.Niltest w := fun h => if hh : h ∈ H₀ then
    (S₁ ⟨h, hh⟩).castDimension (hdim a).symm else Niltest.const E w 0
  have hcard : H'.card = H₁.card := Finset.card_image_of_injective _ Subtype.val_injective
  have hcard₀ : (Finset.univ : Finset {h // h ∈ H₀}).card = H₀.card := by simp
  have hlarge₀' : Real.exp (-(p + 1)) * H.card ≤ (H₀.card : ℝ) := by
    simpa only [Fintype.card_unit, Nat.cast_one, mul_one] using hlarge₀
  have hlarge₁' : Real.exp (-q) * H₀.card ≤ (H'.card : ℝ) := by
    rw [hcard]
    simpa only [hcard₀] using hlarge₁
  refine ⟨a.val, hsub₀ a.property, E,
    (E₀.castDimension_geometry (hdim a).symm _).mpr (hE₀.mono E₀ hqC), H', S, ?_, ?_, ?_, ?_⟩
  · intro h hh
    obtain ⟨g, _, rfl⟩ := Finset.mem_image.mp hh
    exact hsub₀ g.property
  · exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
  · calc
      Real.exp (-((p + C) ^ C)) * H.card ≤ Real.exp (-(q + (p + 1))) * H.card :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg (by linarith))) (Nat.cast_nonneg _)
      _ = Real.exp (-q) * (Real.exp (-(p + 1)) * H.card) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-q) * H₀.card := mul_le_mul_of_nonneg_left hlarge₀' (Real.exp_pos _).le
      _ ≤ H'.card := hlarge₁'
  · intro h hh
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hh
    have hSg := hS₁ g hg
    dsimp only [S]
    rw [dite_eq_left g.property]
    refine ⟨((S₁ g).castDimension_complexity (hdim a).symm _).mpr (hSg.1.mono hqC), ?_, ?_, ?_⟩
    · calc
        _ = (S₁ g).normBound := (S₁ g).castDimension_normBound _
        _ = (T₀ g).normBound := hSg.2.1
        _ = (T g.val).normBound := (T g.val).castDimension_normBound _
    · intro x
      calc
        _ = (S₁ g).eval x := (S₁ g).castDimension_eval _ x
        _ = (T₀ g).eval x := hSg.2.2.1 x
        _ = (T g.val).eval x := (T g.val).castDimension_eval _ x
    · intro ht
      apply ((S₁ g).castDimension_unit_interval (hdim a).symm).mpr
      apply hSg.2.2.2
      exact ((T g.val).castDimension_unit_interval (hdim g)).mpr ht

end Erdos3.RationalFilteredNilmanifold

end

end OAI
