import OAI.Combinatorics.Progressions.Dynamics.SquareImagePathRecovery

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct

def AnchoredSquareImagePartitionSpec (s t a C : ℕ) : Prop :=
    ∀ {L M : Type} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)] {d dV dQ : ℕ}
      (D : RationalFilteredNilmanifold L s d)
      [TopologicalSpace (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      [T2Space (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      (V : RationalFilteredNilmanifold D.filtration.squareLieSubalgebra s dV)
      (Q : RationalFilteredNilmanifold M t dQ)
      (φ : D.filtration.squareLieSubalgebra →ₗ⁅ℚ⁆ M)
      (g : D.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
      (c : ℤ) (q N : ℕ) [NeZero q] [NeZero N] {p ε : ℝ},
      1 ≤ s → 2 ≤ p → D.GeometryComplexityLE p → V.GeometryComplexityLE p →
      Q.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight ((pi (fun _ : Bool => D)).basis.repr
        (D.filtration.squarePairMap (V.basis j)) i) ≤ p) →
      (∀ i j, rationalLogHeight (Q.basis.repr (φ (V.basis j)) i) ≤ p) →
      (q : ℝ) ≤ Real.exp p → 0 < ε → ε ≤ 1 → 1 / ε ≤ Real.exp ((p + 2) ^ a) →
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ ε ∧ 1 / δ ≤ Real.exp ((p + C) ^ C) ∧
        ∃ n k : ℕ, 0 < n ∧ 0 < k ∧
          (Fintype.card ((Fin n × ZMod q) × Fin k) : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
          ∃ A : ((Fin n × ZMod q) × Fin k) → ZMod N → ℝ,
            (∀ j, PositiveCyclicNiltest.{0} s N ((p + C) ^ C) (A j)) ∧
            (∀ x, ∑ j, A j x = 1) ∧
            (∀ j x, 0 < A j x → (x.val : ZMod q) = j.1.2) ∧
            (∀ j x y, 0 < A j x → 0 < A j y →
              dist (ZMod.toAddCircle x) (ZMod.toAddCircle y) ≤ δ) ∧
            (∀ h : ZMod N, ((cyclicWrapExceptional h δ).card : ℝ) / N ≤ 6 * δ + 3 / N) ∧
            letI := Q.metricSpace
            let ψ := realificationMap (hnil := D.filtration.squareFiltration.lowerCentralSeries_eq_bot)
              (hM := Q.filtration.lowerCentralSeries_eq_bot) φ
            ∀ (h : ZMod N) (branch : Fin 2),
              ∃ (η γ : D.RealGroup)
                (rSq : D.filtration.squareFiltration.realification.PolynomialOrbit (fun _ : Unit => 1)),
                γ ∈ D.realLattice ∧
                (∀ i, |(D.basis.baseChange ℝ).repr η.coord i| ≤ Real.exp ((p + C) ^ C)) ∧
                (∀ z : Unit → ℤ,
                  D.filtration.realSquareFstHom
                    (D.filtration.squareFiltration.realification.polynomialOrbitEval
                      (fun _ : Unit => 1) z rSq) =
                      η⁻¹ * D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
                        (z + fun _ => (h.val : ℤ) - (branch.val : ℤ) * N) g * γ⁻¹ ∧
                  D.filtration.realSquareSndHom
                    (D.filtration.squareFiltration.realification.polynomialOrbitEval
                      (fun _ : Unit => 1) z rSq) =
                      D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
                        (z + fun _ => c) g) ∧
                ∀ i j x y,
                  x ∉ cyclicWrapExceptional h δ → y ∉ cyclicWrapExceptional h δ →
                  0 < A i x * A j (x + h) → 0 < A i y * A j (y + h) →
                  dist (QuotientGroup.mk (ψ
                      (D.filtration.squareFiltration.realification.polynomialOrbitEval
                        (fun _ : Unit => 1) (fun _ => (x.val : ℤ)) rSq)) : Q.Space)
                    (QuotientGroup.mk (ψ
                      (D.filtration.squareFiltration.realification.polynomialOrbitEval
                        (fun _ : Unit => 1) (fun _ => (y.val : ℤ)) rSq))) ≤ ε

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_anchored_square_image_partition (s t a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ AnchoredSquareImagePartitionSpec s t a C := by
  obtain ⟨R, _, hrec⟩ := exists_square_image_path_recovery.{0, 0, 0} s t
  let B : ℕ := Classical.choose (exists_anchored_observation_partition s 1)
  have hpartition := @(Classical.choose_spec (exists_anchored_observation_partition s 1)).2
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C R) ^ R
  let T := X + U + (X + 2) ^ a + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (T + (T + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  dsimp only [AnchoredSquareImagePartitionSpec]
  intro L M _ _ _ _ _ _ _ _ _ _ _ _ d dV dQ D _ _ _ _ V Q φ g c q N _ _ p ε
    hs hp hD hV hQ hpair hφ hq hε hε1 hεinv
  have hp0 : 0 ≤ p := by linarith
  obtain ⟨Δ, l, hl, hlin, hlout, _, hE, hpaths⟩ := hrec D V Q φ hp hD hV hQ hpair hφ
  let E := fun i => D.withLattice (Δ i) (l i) (hl i) (hlin i) (hlout i)
  let r := (p + R) ^ R
  let K := (p + 2) ^ a
  let u := p + r + K + 2
  let δ := ε * Real.exp (-r)
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hpu : p ≤ u := by dsimp [u]; linarith
  have hru : r ≤ u := by dsimp [u]; linarith
  have hku : K + r ≤ u := by dsimp [u]; linarith
  have hu : 0 ≤ u := hp0.trans hpu
  obtain ⟨hδ, hδε, hδsmall, hδerror, hδinv⟩ := recovery_precision_bounds hr hε hε1 hεinv
  have htotal : u + (u + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, U, T, r, K, u, Polynomial.eval₂_pow] using hbudget p hp0
  have hcost : (u + B) ^ B ≤ (p + C) ^ C := (le_add_of_nonneg_left hu).trans htotal
  have huC : u ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (pow_nonneg (by positivity) _)).trans htotal
  have hrC : r ≤ (p + C) ^ C := hru.trans huC
  let E' : Unit → Bool → RationalFilteredNilmanifold L s d := fun _ => E
  let g' : ∀ i b, (E' i b).filtration.realification.PolynomialOrbit (fun _ : Unit => 1) :=
    fun _ _ => g
  have hδinverse : 1 / δ ≤ Real.exp ((u + 2) ^ 1) := by
    apply hδinv.trans (Real.exp_le_exp.mpr _)
    rw [pow_one]
    linarith
  obtain ⟨n, k, hn, hk, hcount, A, hA, hsum, hres, hcircle, hexception, hanchor, hmove⟩ :=
    hpartition E' g' (fun _ => c) q N hs hu
      (by simpa only [Fintype.card_unit, Nat.cast_one] using
        ((by linarith : 1 ≤ p).trans hpu))
      (fun _ b => (hE b).mono (E b) hru)
      (hq.trans (Real.exp_le_exp.mpr hpu)) hδ hδinverse
  refine ⟨δ, hδ, hδε, hδinv.trans (Real.exp_le_exp.mpr (hku.trans huC)),
    n, k, hn, hk, hcount.trans (Real.exp_le_exp.mpr hcost), A,
    fun j => (hA j).mono le_rfl hcost, hsum, hres, hcircle, hexception, ?_⟩
  let : ∀ b, MetricSpace (E b).Space := fun b => (E b).metricSpace
  let := Q.metricSpace
  intro h branch
  obtain ⟨η, γ, rSq, hγ, hη, hnorm, hrecover⟩ := hpaths (fun _ : Unit => 1)
    (fun _ => Nat.zero_lt_one) g (fun _ => (h.val : ℤ) - (branch.val : ℤ) * N) (fun _ => c)
  refine ⟨η, γ, rSq, hγ, fun i => (hη i).trans (Real.exp_le_exp.mpr hrC), hnorm, ?_⟩
  intro i j x y hx hy hxy hyy
  have hpositive (z : ZMod N) (hz : 0 < A i z * A j (z + h)) : 0 < A i z := by
    rcases mul_pos_iff.mp hz with hz | hz
    · exact hz.1
    · linarith [((hA i).unit_interval z).1]
  have hfirst := hmove h branch i j x y hx hy hxy hyy ()
  change dist ((E true).integerOrbitPoint g ((x.val : ℤ) + h.val - (branch.val : ℤ) * N))
    ((E true).integerOrbitPoint g ((y.val : ℤ) + h.val - (branch.val : ℤ) * N)) ≤ δ at hfirst
  have hsecond := hanchor i x y (hpositive x hxy) (hpositive y hyy) ()
  change dist ((E false).integerOrbitPoint g ((x.val : ℤ) + c))
    ((E false).integerOrbitPoint g ((y.val : ℤ) + c)) ≤ δ at hsecond
  have hbound := hrecover (fun _ => (x.val : ℤ)) (fun _ => (y.val : ℤ)) δ hδ.le hδsmall
    (by
      change dist ((E true).integerOrbitPoint g ((x.val : ℤ) + ((h.val : ℤ) - (branch.val : ℤ) * N)))
        ((E true).integerOrbitPoint g ((y.val : ℤ) + ((h.val : ℤ) - (branch.val : ℤ) * N))) ≤ δ
      simpa only [add_sub_assoc] using hfirst)
    hsecond
  exact hδerror ▸ hbound

end Erdos3.RationalFilteredNilmanifold

end

end OAI
