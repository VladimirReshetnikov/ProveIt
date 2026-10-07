/- Modified for ProveIt: Use IsModuleTopology.topologicalAddGroup on Lean 4.32; statements unchanged. -/
import OAI.Combinatorics.Progressions.Lattices.ControlledRefilteredResidueExpansion
import OAI.Combinatorics.Progressions.Lattices.SlowResidueRecovery

namespace OAI

section

namespace Erdos3

theorem positive_cell_residue_recovery
    {I J X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {P N : ℕ} [NeZero N] (A : I → ZMod N → ℝ) (B : J → ZMod N → ℝ)
    (label : I → ZMod P) (f : ℤ → X) (b : ℤ → Y) {R K ρ : ℝ}
    (hR : 0 ≤ R) (hρ : 0 < ρ)
    (hA : ∀ i x, 0 ≤ A i x)
    (hres : ∀ i x, 0 < A i x → (x.val : ZMod P) = label i)
    (hcircle : ∀ i x y, 0 < A i x → 0 < A i y →
      dist (ZMod.toAddCircle x) (ZMod.toAddCircle y) ≤ ρ)
    (hrecover : ∀ n m : ℤ, (n : ZMod P) = (m : ZMod P) →
      ∀ δ : ℝ, 0 ≤ δ → |(n : ℝ)| ≤ N → |(m : ℝ)| ≤ N →
        |(n : ℝ) - m| ≤ (N : ℝ) * δ →
        dist (b n) (b m) ≤ R * (dist (f n) (f m) + δ))
    (h : ZMod N) (i : I) (j : J) (x y : ZMod N)
    (hx : x ∉ cyclicWrapExceptional h ρ) (hy : y ∉ cyclicWrapExceptional h ρ)
    (hxy : 0 < A i x * B j (x + h)) (hyy : 0 < A i y * B j (y + h))
    (hinput : dist (f x.val) (f y.val) ≤ K * ρ) :
    dist (b x.val) (b y.val) ≤ R * (K + 1) * ρ := by
  have hpositive (z : ZMod N) (hz : 0 < A i z * B j (z + h)) : 0 < A i z := by
    rcases mul_pos_iff.mp hz with hz | hz
    · exact hz.1
    · linarith [hA i z]
  have hAx := hpositive x hxy
  have hAy := hpositive y hyy
  have hmod : ((x.val : ℤ) : ZMod P) = ((y.val : ℤ) : ZMod P) := by
    simpa only [Int.cast_natCast] using (hres i x hAx).trans (hres i y hAy).symm
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have hbound (z : ZMod N) : |((z.val : ℤ) : ℝ)| ≤ (N : ℝ) := by
    rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast (Nat.le_of_lt (ZMod.val_lt z))
  have hdiff := good_circle_observations_control_representatives h x y hρ hx hy
    (hcircle i x y hAx hAy)
  rw [← sub_div, abs_div, abs_of_pos hN] at hdiff
  have hdiff' : |((x.val : ℤ) : ℝ) - ((y.val : ℤ) : ℝ)| ≤ (N : ℝ) * ρ := by
    simpa only [Int.cast_natCast, mul_comm ρ (N : ℝ)] using (div_le_iff₀ hN).mp hdiff
  calc
    _ ≤ R * (dist (f x.val) (f y.val) + ρ) :=
      hrecover x.val y.val hmod ρ hρ.le (hbound x) (hbound y) hdiff'
    _ ≤ R * (K * ρ + ρ) := mul_le_mul_of_nonneg_left
      (by linarith : dist (f x.val) (f y.val) + ρ ≤ K * ρ + ρ) hR
    _ = _ := by ring

end Erdos3

end

section

universe u v w

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct

def NativeCyclicRecoverySpec (s k C : ℕ) : Prop :=
    ∀ {L : Type u} {M : Type v} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)] {d e : ℕ}
      (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
      (φ : L →ₗ⁅ℚ⁆ M) {p : ℝ}, 1 ≤ p → D.GeometryComplexityLE p → E.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis j)) i) ≤ p) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ P m : ℕ, 0 < P ∧ 0 < m ∧
        (P : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ Λ : Subgroup D.filtration.Group, Λ ≤ D.lattice ∧
          (Λ.subgroupOf D.lattice).Characteristic ∧ (Λ.subgroupOf D.lattice).Normal ∧
          (Λ.subgroupOf D.lattice).FiniteIndex ∧ (Λ.relIndex D.lattice : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
          ∃ (l : ℕ) (hl : 0 < l)
            (hin : scaledIntegerGrid l ⊆ bchSubgroupCoordinates D.basis Λ)
            (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid l),
            let Q := D.withLattice Λ l hl hin hout
            Q.GeometryComplexityLE ((p + C) ^ C) ∧
            letI := Q.metricSpace
            letI := E.metricSpace
            let ψ := realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
              (hM := E.filtration.lowerCentralSeries_eq_bot) φ
            ∀ R : (E.filtration.realification.adaptedPolynomialFiltration (fun _ : Unit => 1)).Group,
              E.filtration.PolynomialRationalGrid E.basis (fun _ : Unit => 1) q R →
              ∃ z : (Unit → ZMod P) → E.RealGroup,
                (∀ c, (∀ i, |(E.basis.baseChange ℝ).repr (z c).coord i| ≤ Real.exp ((p + C) ^ C)) ∧
                  (E.basis.baseChange ℝ).equivFun (z c).coord ∈ realDenominatorGrid m) ∧
                ∀ κ : D.RealGroup, κ ∈ D.realLattice →
                  ∀ a b r f : (Unit → ℤ) → D.RealGroup,
                    (∀ x, a x * b x * r x * κ = f x) →
                    (∀ x, ψ (r x) = E.filtration.adaptedPolynomialRealValueHom (fun _ : Unit => 1)
                      (fun i => (x i : ℝ)) R) →
                    (∀ x, (QuotientGroup.mk (ψ (b x)) : E.Space) =
                      QuotientGroup.mk ((ψ (a x))⁻¹ * ψ (f x) * (ψ κ)⁻¹ *
                        (z (fun i => (x i : ZMod P)))⁻¹)) ∧
                    ∀ (N : ℕ) [NeZero N]
                      (S : (E.filtration.realification.adaptedPolynomialFiltration (fun _ : Unit => 1)).Group),
                      E.filtration.PolynomialSlowBound E.basis (fun _ : Unit => 1)
                        (fun _ => (N : ℝ)) (Real.exp ((p + 2) ^ k)) S →
                      (∀ x, ψ (a x) = E.filtration.adaptedPolynomialRealValueHom (fun _ : Unit => 1)
                        (fun i => (x i : ℝ)) S) →
                      ∀ {I J : Type w} (A : I → ZMod N → ℝ) (B : J → ZMod N → ℝ)
                        (label : I → ZMod P) {ρ K : ℝ}, 0 < ρ →
                        (∀ i x, 0 ≤ A i x) →
                        (∀ i x, 0 < A i x → (x.val : ZMod P) = label i) →
                        (∀ i x y, 0 < A i x → 0 < A i y →
                          dist (ZMod.toAddCircle x) (ZMod.toAddCircle y) ≤ ρ) →
                        ∀ (h : ZMod N) i j x y,
                          x ∉ cyclicWrapExceptional h ρ → y ∉ cyclicWrapExceptional h ρ →
                          0 < A i x * B j (x + h) → 0 < A i y * B j (y + h) →
                          dist (QuotientGroup.mk (f (fun _ => (x.val : ℤ))) : Q.Space)
                            (QuotientGroup.mk (f (fun _ => (y.val : ℤ)))) ≤ K * ρ →
                          dist (QuotientGroup.mk (ψ (b (fun _ => (x.val : ℤ)))) : E.Space)
                            (QuotientGroup.mk (ψ (b (fun _ => (y.val : ℤ))))) ≤
                              Real.exp ((p + C) ^ C) * (K + 1) * ρ

theorem exists_native_cyclic_recovery (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ NativeCyclicRecoverySpec.{u, v, w} s k C := by
  obtain ⟨C, hC, hrec⟩ := exists_slow_residue_recovery s k
  refine ⟨C, hC, ?_⟩
  dsimp only [NativeCyclicRecoverySpec]
  intro L M _ _ _ _ _ _ _ _ _ _ _ _ d e D E φ p hp hD hE hφ q hq hqp
  have hp0 : 0 ≤ p := by linarith
  obtain ⟨P, m, hP, hm, hPb, hmb, Λ, hΛ, hchar, hnormal, hfinite, hindex,
      l, hl, hin, hout, hQ, hrecover⟩ :=
    hrec D E φ (fun _ : Unit => 1) (fun _ => Nat.zero_lt_one) hp0
      (by simpa only [Fintype.card_unit, Nat.cast_one] using hp) hD hE hφ q hq hqp
  let Q := D.withLattice Λ l hl hin hout
  let ψ := realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
    (hM := E.filtration.lowerCentralSeries_eq_bot) φ
  refine ⟨P, m, hP, hm, hPb, hmb, Λ, hΛ, hchar, hnormal, hfinite, hindex,
    l, hl, hin, hout, hQ, ?_⟩
  let := Q.metricSpace
  let := E.metricSpace
  intro R hR
  obtain ⟨z, hz, heval⟩ := hrecover R hR
  refine ⟨z, hz, ?_⟩
  intro κ hκ a b r f hfactor hvalue
  obtain ⟨hexact, hmove⟩ := heval κ hκ a b r f hfactor hvalue
  refine ⟨hexact, ?_⟩
  intro N _ S hS hSvalue I J A B label ρ K hρ hA hres hcircle h i j x y hx hy hxy hyy hinput
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  apply positive_cell_residue_recovery A B label
    (fun n => (QuotientGroup.mk (f (fun _ => n)) : Q.Space))
    (fun n => (QuotientGroup.mk (ψ (b (fun _ => n))) : E.Space))
    (Real.exp_pos _).le hρ hA hres hcircle ?_ h i j x y hx hy hxy hyy hinput
  intro n m hmod δ hδ hn hm hdiff
  exact hmove (fun _ : Unit => (N : ℝ)) (fun _ => hN) S hS hSvalue
    (fun _ => n) (fun _ => m) (funext (fun _ => hmod)) δ hδ
    (fun _ => hn) (fun _ => hm) (fun _ => hdiff)

end Erdos3.RationalFilteredNilmanifold

end

section

universe u v w z

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct BigOperators NNReal

def NativeRecoveredApproximationSpec (s k C : ℕ) : Prop :=
    ∀ {L : Type u} {M : Type v} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)] {d e : ℕ}
      (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
      (φ : L →ₗ⁅ℚ⁆ M) {p : ℝ}, 1 ≤ p → D.GeometryComplexityLE p → E.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis j)) i) ≤ p) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ P : ℕ, 0 < P ∧ (P : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ Λ : Subgroup D.filtration.Group, Λ ≤ D.lattice ∧
          (Λ.subgroupOf D.lattice).Characteristic ∧ (Λ.subgroupOf D.lattice).Normal ∧
          (Λ.subgroupOf D.lattice).FiniteIndex ∧ (Λ.relIndex D.lattice : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
          ∃ (l : ℕ) (hl : 0 < l)
            (hin : scaledIntegerGrid l ⊆ bchSubgroupCoordinates D.basis Λ)
            (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid l),
            let Q := D.withLattice Λ l hl hin hout
            Q.GeometryComplexityLE ((p + C) ^ C) ∧
            letI := Q.metricSpace
            letI := E.metricSpace
            let ψ := realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
              (hM := E.filtration.lowerCentralSeries_eq_bot) φ
            ∀ (N : ℕ) [NeZero N]
              (R : ZMod N → (E.filtration.realification.adaptedPolynomialFiltration (fun _ : Unit => 1)).Group)
              (κ : ZMod N → D.RealGroup)
              (a b r f : ZMod N → (Unit → ℤ) → D.RealGroup)
              (S : ZMod N → (E.filtration.realification.adaptedPolynomialFiltration (fun _ : Unit => 1)).Group),
              (∀ h, E.filtration.PolynomialRationalGrid E.basis (fun _ : Unit => 1) q (R h)) →
              (∀ h, κ h ∈ D.realLattice) →
              (∀ h x, a h x * b h x * r h x * κ h = f h x) →
              (∀ h x, ψ (r h x) = E.filtration.adaptedPolynomialRealValueHom (fun _ : Unit => 1)
                (fun i => (x i : ℝ)) (R h)) →
              (∀ h, E.filtration.PolynomialSlowBound E.basis (fun _ : Unit => 1)
                (fun _ => (N : ℝ)) (Real.exp ((p + 2) ^ k)) (S h)) →
              (∀ h x, ψ (a h x) = E.filtration.adaptedPolynomialRealValueHom (fun _ : Unit => 1)
                (fun i => (x i : ℝ)) (S h)) →
              ∀ {I J : Type z} [Fintype I] [Fintype J]
                (A : I → ZMod N → ℝ) (B : J → ZMod N → ℝ) (label : I → ZMod P)
                {ρ δ K : ℝ}, 0 < ρ → 0 ≤ δ → 0 ≤ K →
                (∀ i n, 0 ≤ A i n) → (∀ j n, 0 ≤ B j n) →
                (∀ n, ∑ i, A i n = 1) → (∀ n, ∑ j, B j n = 1) →
                (∀ i n, 0 < A i n → (n.val : ZMod P) = label i) →
                (∀ i n n', 0 < A i n → 0 < A i n' →
                  dist (ZMod.toAddCircle n) (ZMod.toAddCircle n') ≤ ρ) →
                (∀ h i j n n', n ∉ cyclicWrapExceptional h ρ → n' ∉ cyclicWrapExceptional h ρ →
                  0 < A i n * B j (n + h) → 0 < A i n' * B j (n' + h) →
                  dist (QuotientGroup.mk (f h (fun _ => (n.val : ℤ))) : Q.Space)
                    (QuotientGroup.mk (f h (fun _ => (n'.val : ℤ)))) ≤ K * ρ) →
                ∀ {L₀ : ZMod N → Type w} [∀ h, LieRing (L₀ h)] [∀ h, LieAlgebra ℚ (L₀ h)]
                  [∀ h, TopologicalSpace (ℝ ⊗[ℚ] L₀ h)] [∀ h, IsTopologicalAddGroup (ℝ ⊗[ℚ] L₀ h)]
                  [∀ h, ContinuousSMul ℝ (ℝ ⊗[ℚ] L₀ h)] [∀ h, T2Space (ℝ ⊗[ℚ] L₀ h)]
                  {s₀ : ℕ} {d₀ : ZMod N → ℕ} (D₀ : ∀ h, RationalFilteredNilmanifold (L₀ h) s₀ (d₀ h))
                  (g : ∀ h, (D₀ h).filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
                  (F : I → ∀ h, (D₀ h).Space → E.Space → ℝ) (T : ZMod N → ZMod N → ℝ)
                  {Lx Lz : ℝ≥0} {p₀ : ℝ},
                  (∀ i h z a, 0 ≤ F i h z a ∧ F i h z a ≤ 1) →
                  (∀ i h, letI := (D₀ h).metricSpace; ∀ a, LipschitzWith Lz (fun z => F i h z a)) →
                  (∀ i h z, LipschitzWith Lx (F i h z)) →
                  (∀ h, (D₀ h).GeometryComplexityLE p₀) → Real.log (3 + (Lz : ℝ)) ≤ p₀ →
                  (∀ h n, 0 ≤ T h n ∧ T h n ≤ 1) →
                  (∀ i h n, n ∉ cyclicWrapExceptional h ρ → 0 < A i n →
                    |T h n - F i h ((D₀ h).cyclicOrbitPoint (g h) N (fun _ : Unit => n))
                      (QuotientGroup.mk (ψ (b h (fun _ => (n.val : ℤ)))))| ≤ δ) →
                  ∃ U : I → J → (h : ZMod N) → (D₀ h).Niltest (fun _ : Unit => 1),
                    (∀ i j h, (U i j h).UnitIntervalValued) ∧
                    (∀ i j h, (U i j h).ComplexityLE p₀) ∧
                    (∀ i j h, (¬∃ n, n ∉ cyclicWrapExceptional h ρ ∧ 0 < A i n * B j (n + h)) →
                      ∀ x, (U i j h).eval x = 0) ∧
                    ∃ err : ZMod N → ZMod N → ℝ,
                      (∀ h n, T h n = (∑ i, ∑ j, A i n * B j (n + h) *
                        ((U i j h).evalCyclic N (fun _ : Unit => n)).re) + err h n) ∧
                      ∀ h, (𝔼 n, |err h n|) ≤
                        δ + Lx * (Real.exp ((p + C) ^ C) * (K + 1) * ρ) + 6 * ρ + 3 / N

end Erdos3.RationalFilteredNilmanifold

end

section

universe u v w z

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct BigOperators NNReal

theorem exists_native_recovered_approximation (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ NativeRecoveredApproximationSpec.{u, v, w, z} s k C := by
  obtain ⟨C, hC, hrecovery⟩ := exists_native_cyclic_recovery.{u, v, z} s k
  refine ⟨C, hC, ?_⟩
  dsimp only [NativeRecoveredApproximationSpec]
  intro L M _ _ _ _ _ _ _ _ _ _ _ _ d e D E φ p hp hD hE hφ q hq hqp
  obtain ⟨P, _, hP, _, hPb, _, Λ, hΛ, hchar, hnormal, hfinite, hindex,
      l, hl, hin, hout, hQ, hrec⟩ := hrecovery D E φ hp hD hE hφ q hq hqp
  let Q := D.withLattice Λ l hl hin hout
  let ψ := realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
    (hM := E.filtration.lowerCentralSeries_eq_bot) φ
  refine ⟨P, hP, hPb, Λ, hΛ, hchar, hnormal, hfinite, hindex, l, hl, hin, hout, hQ, ?_⟩
  let := Q.metricSpace
  let := E.metricSpace
  intro N _ R κ a b r f S hR hκ hfactor hvalue hS hSvalue
    I J _ _ A B label ρ δ K hρ hδ hK hA hB hAsum hBsum hres hcircle hinput
    L₀ _ _ _ _ _ _ s₀ d₀ D₀ g F T Lx Lz p₀ hF hFirstLip hSecondLip hGeometry hBudget hT happrox
  let xi : ZMod N → ZMod N → E.Space := fun h n =>
    QuotientGroup.mk (ψ (b h (fun _ => (n.val : ℤ))))
  have hdiam (i : I) (j : J) (h n n' : ZMod N)
      (hn : n ∉ cyclicWrapExceptional h ρ) (hn' : n' ∉ cyclicWrapExceptional h ρ)
      (hij : 0 < A i n * B j (n + h)) (hij' : 0 < A i n' * B j (n' + h)) :
      dist (xi h n) (xi h n') ≤ Real.exp ((p + C) ^ C) * (K + 1) * ρ := by
    obtain ⟨_, _, hmove⟩ := hrec (R h) (hR h)
    obtain ⟨_, hcell⟩ := hmove (κ h) (hκ h) (a h) (b h) (r h) (f h) (hfactor h) (hvalue h)
    exact hcell N (S h) (hS h) (hSvalue h) A B label hρ hA hres hcircle h i j n n'
      hn hn' hij hij' (hinput h i j n n' hn hn' hij hij')
  have hη : 0 ≤ Real.exp ((p + C) ^ C) * (K + 1) * ρ := by positivity
  obtain ⟨U, hU, hUcomplexity, hUempty, _, err, heval, hmean⟩ :=
    exists_cyclic_cellwise_niltest_approximation N D₀ g F A B xi T hρ hδ hη
      hA hB hAsum hBsum hF hFirstLip hSecondLip hGeometry hBudget hT happrox hdiam
  exact ⟨U, hU, hUcomplexity, hUempty, err, heval, hmean⟩

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct BigOperators NNReal

variable {ι : Type u} [Fintype ι] [DecidableEq ι] {L : ι → Type u}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i)) (a : ι)
  (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded) {e n : ℕ}
  (E : RationalFilteredNilmanifold ((pi D).filtration.gradedRefiltrationSubalgebra W) (s + 1) e)
  (Q : RationalFilteredNilmanifold
    (((pi D).filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n)
  [TopologicalSpace (ℝ ⊗[ℚ] L a)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L a)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L a)] [T2Space (ℝ ⊗[ℚ] L a)]

noncomputable def RefilteredRecoveredExpansionSpec (p : ℝ) (q r : ℕ) (cost : ℝ) : Prop :=
  let H := (pi D).filtration.gradedRefiltrationSubalgebra W
  let I₀ := {i : ι // i ≠ a}
  let Z₀ := pi (fun i : I₀ => D i.val)
  letI := moduleTopology ℝ (ℝ ⊗[ℚ] (H ⧸ E.filtration.layerIdeal (s + 1)))
  letI := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] (H ⧸ E.filtration.layerIdeal (s + 1)))
  letI := realification_moduleTopology_t2 Q.basis
  letI := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i : I₀, L i.val))
  letI := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] (∀ i : I₀, L i.val))
  letI := realification_moduleTopology_t2 Z₀.basis
  ∃ P : ℕ, 0 < P ∧ (P : ℝ) ≤ Real.exp cost ∧
    ∃ Q' : RationalFilteredNilmanifold (H ⧸ E.filtration.layerIdeal (s + 1)) s n,
      Q'.filtration = Q.filtration ∧ Q'.basis = Q.basis ∧ Q'.lattice ≤ Q.lattice ∧
      Q'.GeometryComplexityLE cost ∧
      ∃ Z : RationalFilteredNilmanifold (∀ i : I₀, L i.val) (s + 1)
          (Fintype.card (Σ i : I₀, Fin (d i.val))),
        Z.filtration = Z₀.filtration ∧ Z.basis = Z₀.basis ∧ Z.lattice ≤ Z₀.lattice ∧
        Z.GeometryComplexityLE cost ∧
        ∃ Λ : Subgroup Z₀.filtration.Group, Λ ≤ Z₀.lattice ∧
          (Λ.subgroupOf Z₀.lattice).Characteristic ∧ (Λ.subgroupOf Z₀.lattice).Normal ∧
          (Λ.subgroupOf Z₀.lattice).FiniteIndex ∧ (Λ.relIndex Z₀.lattice : ℝ) ≤ Real.exp cost ∧
          ∃ (l : ℕ) (hl : 0 < l)
            (hin : scaledIntegerGrid l ⊆ bchSubgroupCoordinates Z₀.basis Λ)
            (hout : bchSubgroupCoordinates Z₀.basis Λ ⊆ denominatorGrid l),
            let V := Z₀.withLattice Λ l hl hin hout
            V.GeometryComplexityLE cost ∧
            letI := V.metricSpace
            let w := fun _ : Unit => 1
            let φ := realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
              (hM := (D a).filtration.lowerCentralSeries_eq_bot) (refilteredComponentMap D W a)
            let ψ := realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
              (hM := Z.filtration.lowerCentralSeries_eq_bot)
              (liePiMap (fun i : I₀ => refilteredComponentMap D W i.val))
            ∀ {J₀ : Type u} (freq : J₀ → ∀ i, L i →ₗ[ℚ] ℚ),
              (∀ j x, x ∈ (pi D).filtration.realGradedRefiltrationLayer W (s + 1) →
                realifyFunctional (piFrequency (freq j)) x = 0) →
              ∀ (N : ℕ) [NeZero N] {I J : Type u} [Fintype I] [Fintype J]
                (A : I → ZMod N → ℝ) (B : J → ZMod N → ℝ) (label : I → ZMod P) {ρ K : ℝ},
                0 < ρ → 0 ≤ K →
                (∀ i x, 0 ≤ A i x) → (∀ j x, 0 ≤ B j x) →
                (∀ x, ∑ i, A i x = 1) → (∀ x, ∑ j, B j x = 1) →
                (∀ i x, 0 < A i x → (x.val : ZMod P) = label i) →
                (∀ i x y, 0 < A i x → 0 < A i y →
                  dist (ZMod.toAddCircle x) (ZMod.toAddCircle y) ≤ ρ) →
                ∀ (S : ZMod N → (D a).Niltest w),
                  (∀ h, (S h).ComplexityLE p) → (∀ h, (S h).UnitIntervalValued) →
                  (∀ h z, z ∈ (D a).filtration.realification.subgroup (s + 1) →
                    (∀ j, realifyFunctional (freq j a) z.coord = 0) →
                    ∀ x, (S h).observable (z • x) = (S h).observable x) →
                  ∀ (slow middle rat : ZMod N → ((D a).filtration.realification.adaptedPolynomialFiltration w).Group)
                    (κ : ZMod N → (D a).RealGroup)
                    (g : ZMod N → E.filtration.realification.PolynomialOrbit w),
                    (∀ h, κ h ∈ (D a).realLattice) →
                    (∀ h, slow h * middle h * rat h * (D a).filtration.realification.adaptedConstantGroupHom w (κ h) =
                      ⟨⟨(S h).orbit.log, (S h).orbit.property⟩⟩) →
                    (∀ h, (D a).filtration.PolynomialSlowBound (D a).basis w
                      (fun _ => (N : ℝ)) (Real.exp ((p + 2) ^ r)) (slow h)) →
                    (∀ h, (D a).filtration.PolynomialRationalGrid (D a).basis w q (rat h)) →
                    (∀ h x, (D a).filtration.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ)) (middle h) =
                      φ (E.filtration.realification.polynomialOrbitEval w x (g h))) →
                    ∀ (slowZ ratZ : ZMod N → (Z.filtration.realification.adaptedPolynomialFiltration w).Group)
                      (κZ : ZMod N → Z₀.RealGroup) (fZ : ZMod N → (Unit → ℤ) → Z₀.RealGroup),
                      (∀ h, κZ h ∈ Z₀.realLattice) →
                      (∀ h x, Z.filtration.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ)) (slowZ h) *
                        ψ (E.filtration.realification.polynomialOrbitEval w x (g h)) *
                        Z.filtration.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ)) (ratZ h) * κZ h = fZ h x) →
                      (∀ h, Z.filtration.PolynomialSlowBound Z.basis w (fun _ => (N : ℝ))
                        (Real.exp ((p + 2) ^ r)) (slowZ h)) →
                      (∀ h, Z.filtration.PolynomialRationalGrid Z.basis w q (ratZ h)) →
                      (∀ i j h x y, x ∉ cyclicWrapExceptional h ρ → y ∉ cyclicWrapExceptional h ρ →
                        0 < A i x * B j (x + h) → 0 < A i y * B j (y + h) →
                        dist (QuotientGroup.mk (fZ h (fun _ => (x.val : ℤ))) : V.Space)
                          (QuotientGroup.mk (fZ h (fun _ => (y.val : ℤ)))) ≤ K * ρ) →
                      ∃ U : I → J → ZMod N → Q'.Niltest w,
                        (∀ i j h, (U i j h).UnitIntervalValued) ∧
                        (∀ i j h, (U i j h).ComplexityLE (cost + 2)) ∧
                        (∀ i j h, (¬∃ x, x ∉ cyclicWrapExceptional h ρ ∧ 0 < A i x * B j (x + h)) →
                          ∀ x, (U i j h).eval x = 0) ∧
                        ∃ err : ZMod N → ZMod N → ℝ,
                          (∀ h x, ((S h).evalCyclic N (fun _ => x)).re =
                            (∑ i, ∑ j, A i x * B j (x + h) * ((U i j h).evalCyclic N (fun _ => x)).re) + err h x) ∧
                          ∀ h, (𝔼 x, |err h x|) ≤ Real.exp cost * (K + 2) * ρ + 6 * ρ + 3 / N

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct BigOperators NNReal

variable {ι : Type u} [Fintype ι] [DecidableEq ι] {L : ι → Type u}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i)) (a : ι)
  (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded) {e n : ℕ}
  (E : RationalFilteredNilmanifold ((pi D).filtration.gradedRefiltrationSubalgebra W) (s + 1) e)
  (Q : RationalFilteredNilmanifold
    (((pi D).filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n)
  [TopologicalSpace (ℝ ⊗[ℚ] L a)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L a)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L a)] [T2Space (ℝ ⊗[ℚ] L a)]

noncomputable def RefilteredProductExpansionSpec (p : ℝ) (q r : ℕ) (cost : ℝ) : Prop :=
  let H := (pi D).filtration.gradedRefiltrationSubalgebra W
  let I₀ := {i : ι // i ≠ a}
  let Z₀ := pi (fun i : I₀ => D i.val)
  letI := moduleTopology ℝ (ℝ ⊗[ℚ] (H ⧸ E.filtration.layerIdeal (s + 1)))
  letI := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] (H ⧸ E.filtration.layerIdeal (s + 1)))
  letI := realification_moduleTopology_t2 Q.basis
  letI := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i : I₀, L i.val))
  letI := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] (∀ i : I₀, L i.val))
  letI := realification_moduleTopology_t2 Z₀.basis
  ∃ P : ℕ, 0 < P ∧ (P : ℝ) ≤ Real.exp cost ∧
    ∃ Q' : RationalFilteredNilmanifold (H ⧸ E.filtration.layerIdeal (s + 1)) s n,
      Q'.filtration = Q.filtration ∧ Q'.basis = Q.basis ∧ Q'.lattice ≤ Q.lattice ∧
      Q'.GeometryComplexityLE cost ∧
        ∃ Λ : Subgroup Z₀.filtration.Group, Λ ≤ Z₀.lattice ∧
          (Λ.subgroupOf Z₀.lattice).Characteristic ∧ (Λ.subgroupOf Z₀.lattice).Normal ∧
          (Λ.subgroupOf Z₀.lattice).FiniteIndex ∧ (Λ.relIndex Z₀.lattice : ℝ) ≤ Real.exp cost ∧
          ∃ (l : ℕ) (hl : 0 < l)
            (hin : scaledIntegerGrid l ⊆ bchSubgroupCoordinates Z₀.basis Λ)
            (hout : bchSubgroupCoordinates Z₀.basis Λ ⊆ denominatorGrid l),
            let V := Z₀.withLattice Λ l hl hin hout
            V.GeometryComplexityLE cost ∧
            letI := V.metricSpace
            let w := fun _ : Unit => 1
            ∀ {J₀ : Type u} (freq : J₀ → ∀ i, L i →ₗ[ℚ] ℚ),
              (∀ j x, x ∈ (pi D).filtration.realGradedRefiltrationLayer W (s + 1) →
                realifyFunctional (piFrequency (freq j)) x = 0) →
              ∀ (N : ℕ) [NeZero N] {I J : Type u} [Fintype I] [Fintype J]
                (A : I → ZMod N → ℝ) (B : J → ZMod N → ℝ) (label : I → ZMod P) {ρ K : ℝ},
                0 < ρ → 0 ≤ K →
                (∀ i x, 0 ≤ A i x) → (∀ j x, 0 ≤ B j x) →
                (∀ x, ∑ i, A i x = 1) → (∀ x, ∑ j, B j x = 1) →
                (∀ i x, 0 < A i x → (x.val : ZMod P) = label i) →
                (∀ i x y, 0 < A i x → 0 < A i y →
                  dist (ZMod.toAddCircle x) (ZMod.toAddCircle y) ≤ ρ) →
                ∀ (S : ZMod N → (D a).Niltest w),
                  (∀ h, (S h).ComplexityLE p) → (∀ h, (S h).UnitIntervalValued) →
                  (∀ h z, z ∈ (D a).filtration.realification.subgroup (s + 1) →
                    (∀ j, realifyFunctional (freq j a) z.coord = 0) →
                    ∀ x, (S h).observable (z • x) = (S h).observable x) →
                  ∀ (g : ZMod N → ∀ i, (D i).filtration.realification.PolynomialOrbit w),
                    (∀ h, g h a = (S h).orbit) →
                    ∀ (slow middle rat : ZMod N → ((pi D).filtration.realification.adaptedPolynomialFiltration w).Group)
                      (κ : ZMod N → (pi D).RealGroup),
                      (∀ h, κ h ∈ (pi D).realLattice) →
                      (∀ h, slow h * middle h * rat h * (pi D).filtration.realification.adaptedConstantGroupHom w (κ h) =
                        ⟨⟨(NilpotentLieFiltration.piRealOrbit (fun i => (D i).filtration) (g h)).log,
                          (NilpotentLieFiltration.piRealOrbit (fun i => (D i).filtration) (g h)).property⟩⟩) →
                      (∀ h, (pi D).filtration.PolynomialSlowBound (pi D).basis w
                        (fun _ => (N : ℝ)) (Real.exp ((p + 2) ^ r)) (slow h)) →
                      (∀ h, (pi D).filtration.PolynomialRationalGrid (pi D).basis w q (rat h)) →
                      (∀ h α, VectorPolynomial.coefficients
                        ((middle h).coord : VectorPolynomial Unit ℚ (ℝ ⊗[ℚ] (∀ i, L i))) α ∈
                          (pi D).filtration.realGradedRefiltrationLayer W (Finsupp.weight w α)) →
                      (∀ h, VectorPolynomial.coefficients
                        ((middle h).coord : VectorPolynomial Unit ℚ (ℝ ⊗[ℚ] (∀ i, L i))) 0 = 0) →
                      (∀ i j h x y, x ∉ cyclicWrapExceptional h ρ → y ∉ cyclicWrapExceptional h ρ →
                        0 < A i x * B j (x + h) → 0 < A i y * B j (y + h) →
                        dist (V.cyclicOrbitPoint
                          (NilpotentLieFiltration.piRealOrbit (fun i : I₀ => (D i.val).filtration)
                            (fun i : I₀ => g h i.val)) N (fun _ : Unit => x))
                          (V.cyclicOrbitPoint
                            (NilpotentLieFiltration.piRealOrbit (fun i : I₀ => (D i.val).filtration)
                              (fun i : I₀ => g h i.val)) N (fun _ : Unit => y)) ≤ K * ρ) →
                      ∃ U : I → J → ZMod N → Q'.Niltest w,
                        (∀ i j h, (U i j h).UnitIntervalValued) ∧
                        (∀ i j h, (U i j h).ComplexityLE (cost + 2)) ∧
                        (∀ i j h, (¬∃ x, x ∉ cyclicWrapExceptional h ρ ∧ 0 < A i x * B j (x + h)) →
                          ∀ x, (U i j h).eval x = 0) ∧
                        ∃ err : ZMod N → ZMod N → ℝ,
                          (∀ h x, ((S h).evalCyclic N (fun _ => x)).re =
                            (∑ i, ∑ j, A i x * B j (x + h) * ((U i j h).evalCyclic N (fun _ => x)).re) + err h x) ∧
                          ∀ h, (𝔼 x, |err h x|) ≤ Real.exp cost * (K + 2) * ρ + 6 * ρ + 3 / N

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

theorem exists_refiltered_recovered_expansion (s r : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] {L : ι → Type u}
      [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {d : ι → ℕ}
      (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i)) (a : ι)
      (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded) {e n : ℕ}
      (E : RationalFilteredNilmanifold ((pi D).filtration.gradedRefiltrationSubalgebra W) (s + 1) e)
      (Q : RationalFilteredNilmanifold
        (((pi D).filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n)
      [TopologicalSpace (ℝ ⊗[ℚ] L a)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L a)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L a)] [T2Space (ℝ ⊗[ℚ] L a)]
      {p b : ℝ} {q P₀ : ℕ}, 1 ≤ p → p ≤ b → (Fintype.card ι : ℝ) ≤ b →
      (∀ i, (D i).GeometryComplexityLE b) → 0 < q → (q : ℝ) ≤ Real.exp b →
      0 < P₀ → (P₀ : ℝ) ≤ Real.exp b →
      RefilteredResidueExpansionSpec D a W E Q p q r P₀ b →
      RefilteredRecoveredExpansionSpec D a W E Q p q r ((b + C) ^ C) := by
  obtain ⟨a₀, _, hrecover⟩ := exists_native_cyclic_recovery.{u, u, u} (s + 1) r
  let X : Polynomial ℕ := Polynomial.X
  let T := (X + 2) ^ 2 + X + 1
  let R := (T + Polynomial.C a₀) ^ a₀
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (T + X + R)
  refine ⟨C, hC, ?_⟩
  intro ι _ _ L _ _ d D a W e n E Q _ _ _ _ p b q P₀ hp hpb hι hD hq hqb hP₀ hP₀b hbase
  classical
  let H := (pi D).filtration.gradedRefiltrationSubalgebra W
  let I₀ := {i : ι // i ≠ a}
  let Z₀ := pi (fun i : I₀ => D i.val)
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (H ⧸ E.filtration.layerIdeal (s + 1)))
  let := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] (H ⧸ E.filtration.layerIdeal (s + 1)))
  let := realification_moduleTopology_t2 Q.basis
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i : I₀, L i.val))
  let := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] (∀ i : I₀, L i.val))
  let := realification_moduleTopology_t2 Z₀.basis
  obtain ⟨Q', hQF, hQb, hQle, hQ, Z, hZF, hZb, hZle, hZ, hbase⟩ := hbase
  let t := (b + 2) ^ 2 + b + 1
  let cost := (b + C) ^ C
  have hb : 0 ≤ b := by linarith
  have hbt : b ≤ t := by dsimp [t]; nlinarith [sq_nonneg (b + 2)]
  have ht : 0 ≤ t := hb.trans hbt
  have hsum : t + b + (t + a₀) ^ a₀ ≤ cost := by
    simpa [T, R, X, t, cost, Polynomial.eval₂_pow] using hbudget b hb
  have hrecpos : 0 ≤ (t + a₀) ^ a₀ := pow_nonneg (by positivity) _
  have hbCost : b ≤ cost := by linarith
  have hrecCost : (t + a₀) ^ a₀ ≤ cost := by linarith
  have hbothCost : b + (t + a₀) ^ a₀ ≤ cost := by linarith
  have hI₀ : (Fintype.card I₀ : ℝ) ≤ b :=
    (Nat.cast_le.mpr (Fintype.card_subtype_le _)).trans hι
  have hZ₀ : Z₀.GeometryComplexityLE t :=
    (pi_geometry (fun i : I₀ => D i.val) hb hI₀ (fun i => hD i.val)).mono Z₀
      (by dsimp [t]; linarith)
  let idLie : (∀ i : I₀, L i.val) →ₗ⁅ℚ⁆ (∀ i : I₀, L i.val) := LieHom.id
  have hheight (i j : Fin (Fintype.card (Σ i : I₀, Fin (d i.val)))) :
      rationalLogHeight (Z.basis.repr (idLie (Z₀.basis j)) i) ≤ t := by
    rw [hZb]
    change rationalLogHeight (Z₀.basis.repr (Z₀.basis j) i) ≤ t
    rw [Basis.repr_self]
    by_cases h : j = i <;> simp [h, rationalLogHeight, ht]
  obtain ⟨P₁, _, hP₁, _, hP₁b, _, Λ, hΛ, hchar, hnormal, hfinite, hindex,
      l, hl, hin, hout, hV, hrec⟩ := hrecover Z₀ Z idLie (hp.trans (hpb.trans hbt))
        hZ₀ (hZ.mono Z hbt) hheight q hq (hqb.trans (Real.exp_le_exp.mpr hbt))
  have hP : ((P₀ * P₁ : ℕ) : ℝ) ≤ Real.exp cost := by
    rw [Nat.cast_mul]
    calc
      _ ≤ Real.exp b * Real.exp ((t + a₀) ^ a₀) :=
        mul_le_mul hP₀b hP₁b (Nat.cast_nonneg _) (Real.exp_pos _).le
      _ = Real.exp (b + (t + a₀) ^ a₀) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr hbothCost
  refine ⟨P₀ * P₁, Nat.mul_pos hP₀ hP₁, hP, Q', hQF, hQb, hQle, hQ.mono Q' hbCost,
    Z, hZF, hZb, hZle, hZ.mono Z hbCost, Λ, hΛ, hchar, hnormal, hfinite,
    hindex.trans (Real.exp_le_exp.mpr hrecCost), l, hl, hin, hout, hV.mono _ hrecCost, ?_⟩
  let V := Z₀.withLattice Λ l hl hin hout
  let := V.metricSpace
  let := Z.metricSpace
  let Ψ := realificationMap (hnil := Z₀.filtration.lowerCentralSeries_eq_bot)
    (hM := Z.filtration.lowerCentralSeries_eq_bot) idLie
  have hΨ (x : Z₀.RealGroup) : Ψ x = x := by
    apply NilpotentLieBCHGroup.ext
    exact realificationLieHom_id_apply x.coord
  dsimp only [Ψ] at hΨ
  dsimp only
  intro J₀ freq hfreq N _ I J _ _ A B label ρ K hρ hK hA hB hAsum hBsum hres hcircle
    S hS hpositive hinvariant slow middle rat κ g hκ hfactor hslow hrat hmiddle
    slowZ ratZ κZ fZ hκZ hfactorZ hslowZ hratZ hinput
  let w := fun _ : Unit => 1
  let ψ := realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
    (hM := Z.filtration.lowerCentralSeries_eq_bot)
    (liePiMap (fun i : I₀ => refilteredComponentMap D W i.val))
  let π₀ := ZMod.castHom (dvd_mul_right P₀ P₁) (ZMod P₀)
  let π₁ := ZMod.castHom (dvd_mul_left P₁ P₀) (ZMod P₁)
  let label₀ := fun i => π₀ (label i)
  let label₁ := fun i => π₁ (label i)
  have hres₀ (i : I) (x : ZMod N) (hx : 0 < A i x) : (x.val : ZMod P₀) = label₀ i := by
    simpa only [map_natCast] using congrArg π₀ (hres i x hx)
  have hres₁ (i : I) (x : ZMod N) (hx : 0 < A i x) : (x.val : ZMod P₁) = label₁ i := by
    simpa only [map_natCast] using congrArg π₁ (hres i x hx)
  have hslowZ' (h : ZMod N) : Z.filtration.PolynomialSlowBound Z.basis w
      (fun _ => (N : ℝ)) (Real.exp ((t + 2) ^ r)) (slowZ h) :=
    Z.filtration.polynomialSlowBound_mono Z.basis w (fun _ => (N : ℝ))
      (fun _ => Nat.cast_pos.mpr (NeZero.pos N))
      (Real.exp_le_exp.mpr (pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ p + 2)
        (by linarith : p + 2 ≤ t + 2) r)) (slowZ h) (hslowZ h)
  let η := Real.exp ((t + a₀) ^ a₀) * (K + 1) * ρ
  have hη : 0 ≤ η := by dsimp [η]; positivity
  have hdiam (i : I) (j : J) (h x y : ZMod N)
      (hx : x ∉ cyclicWrapExceptional h ρ) (hy : y ∉ cyclicWrapExceptional h ρ)
      (hxy : 0 < A i x * B j (x + h)) (hyy : 0 < A i y * B j (y + h)) :
      dist (QuotientGroup.mk (ψ (E.filtration.realification.polynomialOrbitEval w
        (fun _ => (x.val : ℤ)) (g h))) : Z.Space)
        (QuotientGroup.mk (ψ (E.filtration.realification.polynomialOrbitEval w
          (fun _ => (y.val : ℤ)) (g h)))) ≤ η := by
    obtain ⟨_, _, hmove⟩ := hrec (ratZ h) (hratZ h)
    obtain ⟨_, hcell⟩ := hmove (κZ h) (hκZ h)
      (fun x => Z.filtration.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ)) (slowZ h))
      (fun x => ψ (E.filtration.realification.polynomialOrbitEval w x (g h)))
      (fun x => Z.filtration.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ)) (ratZ h))
      (fZ h) (hfactorZ h) (fun _ => hΨ _)
    have hd := hcell N (slowZ h) (hslowZ' h) (fun _ => hΨ _)
      A B label₁ hρ hA hres₁ hcircle h i j x y hx hy hxy hyy (hinput i j h x y hx hy hxy hyy)
    simpa only [hΨ] using hd
  obtain ⟨U, hU, hUcomplexity, hUempty, err, herr, hmean⟩ :=
    hbase freq hfreq N A B label₀ hρ hη hA hB hAsum hBsum hres₀ hcircle
      S hS hpositive hinvariant slow middle rat κ g hκ hfactor hslow hrat hmiddle hdiam
  refine ⟨U, hU, fun i j h => (hUcomplexity i j h).mono (by linarith), hUempty, err, herr, ?_⟩
  intro h
  have hρR : ρ ≤ Real.exp ((t + a₀) ^ a₀) * ρ := by
    nlinarith [Real.one_le_exp hrecpos]
  have hprod := mul_le_mul_of_nonneg_left
    (show ρ + η ≤ Real.exp ((t + a₀) ^ a₀) * ρ + η by linarith) (Real.exp_pos b).le
  calc
    _ ≤ Real.exp b * (ρ + η) + 6 * ρ + 3 / N := hmean h
    _ ≤ Real.exp b * (Real.exp ((t + a₀) ^ a₀) * ρ + η) + 6 * ρ + 3 / N := by linarith
    _ = Real.exp (b + (t + a₀) ^ a₀) * (K + 2) * ρ + 6 * ρ + 3 / N := by
      rw [Real.exp_add]
      dsimp [η]
      ring
    _ ≤ Real.exp cost * (K + 2) * ρ + 6 * ρ + 3 / N := by
      have hh := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hbothCost)
        (show 0 ≤ (K + 2) * ρ by positivity)
      nlinarith

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_controlled_refiltered_recovered_expansion (s r : ℕ) :
    ∃ A B : ℕ, 2 ≤ A ∧ 2 ≤ B ∧ ∀ {ι : Type u} [Fintype ι] [DecidableEq ι]
      {L : ι → Type u} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      {κ : Type*} [Fintype κ] {d : ι → ℕ}
      (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i)) (a : ι)
      (w : ∀ i, Fin (d i) → ℕ)
      (hF : ∀ i j, (D i).filtration.layer j =
        Submodule.span ℚ ((D i).basis '' {b | j ≤ w i b}))
      (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded)
      (v₀ : κ → (pi D).filtration.AssociatedGraded)
      (_hspan : Submodule.span ℚ (Set.range v₀) = W.toSubmodule) {p : ℝ},
      1 ≤ p → (Fintype.card ι : ℝ) ≤ p → (∀ i, (D i).GeometryComplexityLE p) →
      (Fintype.card κ : ℝ) ≤ p →
      (∀ i b, rationalLogHeight (((pi D).filtration.associatedGradedBasis (pi D).basis
        (productBasisWeight w) (pi_layer_span D w hF)).repr (v₀ i) b) ≤ p) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ E : RationalFilteredNilmanifold ((pi D).filtration.gradedRefiltrationSubalgebra W)
          (s + 1) (finrank ℚ ((pi D).filtration.gradedRefiltrationSubalgebra W)),
        E.filtration = (pi D).filtration.gradedRefiltration W ∧
        E.lattice = (pi D).lattice.comap
          (NilpotentLieBCHGroup.map
            (hnil := ((pi D).filtration.gradedRefiltration W).lowerCentralSeries_eq_bot)
            ((pi D).filtration.gradedRefiltrationSubalgebra W).incl) ∧
        E.GeometryComplexityLE ((p + A) ^ A) ∧
        ∃ n : ℕ, n ≤ finrank ℚ ((pi D).filtration.gradedRefiltrationSubalgebra W) ∧
          ∃ Q : RationalFilteredNilmanifold
              (((pi D).filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n,
            Q.filtration = E.filtration.quotientTop ∧
            Q.lattice = E.lattice.map
              (E.filtration.quotientStepHom (E.filtration.layerIdeal (s + 1)) le_rfl) ∧
            Q.GeometryComplexityLE ((p + A) ^ A) ∧
            (nativeRefilteredTarget D a W E Q).GeometryComplexityLE ((p + A) ^ A) ∧
            RefilteredRecoveredExpansionSpec D a W E Q p q r (((p + A) ^ A + B) ^ B) := by
  obtain ⟨A, hA, hmodels⟩ := exists_controlled_refiltered_residue_expansion s r
  obtain ⟨B, hB, hrecover⟩ := exists_refiltered_recovered_expansion s r
  refine ⟨A, B, hA, hB, ?_⟩
  intro ι _ _ L _ _ _ _ _ _ κ _ d D a w hF W v₀ hspan p hp hι hD hκ hv q hq hqp
  obtain ⟨P, hP, hPb, E, hEF, hEL, hE, n, hn, Q, hQF, hQL, hQ, htarget, hbase⟩ :=
    hmodels D a w hF W v₀ hspan hp hι hD hκ hv q hq hqp
  have hAℝ : (2 : ℝ) ≤ A := by exact_mod_cast hA
  have hpA : p ≤ (p + A) ^ A :=
    (le_power_budget (by linarith) (by omega : 1 ≤ A)).trans
      (pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ p + 2) (by linarith) A)
  refine ⟨E, hEF, hEL, hE, n, hn, Q, hQF, hQL, hQ, htarget, ?_⟩
  exact hrecover D a W E Q hp hpA (hι.trans hpA) (fun i => (hD i).mono (D i) hpA)
    hq (hqp.trans (Real.exp_le_exp.mpr hpA)) hP hPb hbase

end Erdos3.RationalFilteredNilmanifold

end

end OAI
