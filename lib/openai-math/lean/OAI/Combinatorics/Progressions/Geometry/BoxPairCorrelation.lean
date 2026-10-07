import OAI.Combinatorics.Progressions.Estimates.SmoothPairErrorLogBounds

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem box_smooth_pair_correlation {J I A B : Type*}
    [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (t u : J → ℤ) (k : J) (hne : u k - t k ≠ 0)
    (H : I → ℝ) {L C κ δ : ℝ} (Q : ℕ) (hH : ∀ i, 0 < H i)
    (hL : 1 ≤ L) (hC : 1 ≤ C) (hκ : 0 < κ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (ht : ∀ j, |(t j : ℝ) / L| ≤ C) (hu : ∀ j, |(u j : ℝ) / L| ≤ C)
    (hgap : κ ≤ |((u k - t k : ℤ) : ℝ) / L|)
    (hQ : affinePairModulus t u ≤ Q)
    (hmesh : ∀ i, ((u k - t k).natAbs : ℝ) * L / H i ≤ δ)
    (hsmall : (4 : ℝ) ^ (2 + Fintype.card {j : J // j ≠ k}) * smoothPairRowLipschitz k * δ ≤ 1 / 2)
    (b : Option J × I → ℤ)
    (hZ : 0 < shiftedSmoothProductMass (fun z => (b z : ℝ))
      (fun z : Option J × I => smoothPairCoefficientScale (H z.2) L z.1))
    (loT hiT loU hiU : I → ℤ)
    (hlenT : ∀ i, loT i < hiT i) (hlenU : ∀ i, loU i < hiU i)
    (hwidthT : ∀ i, (affinePairModulus t u : ℝ) ≤ ((hiT i - loT i : ℤ) : ℝ))
    (hwidthU : ∀ i, (affinePairModulus t u : ℝ) ≤ ((hiU i - loU i : ℤ) : ℝ))
    (T U : Finset (I → ℤ)) [Nonempty T] [Nonempty U]
    (hT : T = Fintype.piFinset (fun i => Finset.Ico (loT i) (hiT i)))
    (hU : U = Fintype.piFinset (fun i => Finset.Ico (loU i) (hiU i)))
    (e d : (I → ℤ) → ℝ) (heoff : ∀ x ∉ T, e x = 0) (hdoff : ∀ y ∉ U, d y = 0)
    (P : T → A) (R : U → B) (cell : A → B → (I → ZMod (affinePairModulus t u)) → ℝ)
    {alpha beta cap zeta : ℝ} (halpha : 0 ≤ alpha) (hcap : 0 ≤ cap) (hzeta : 0 ≤ zeta)
    (he : ∀ c r, |finiteCellResidueMean (FiniteProbabilityWeights.uniform T) P
      (fun x => integerVectorResidue (affinePairModulus t u) x.val) (fun x => e x.val) c r| ≤
      (finiteCellWeights (FiniteProbabilityWeights.uniform T) P).weight c * alpha /
        (affinePairModulus t u : ℝ) ^ Fintype.card I)
    (hd : ∀ c r, |finiteCellResidueMean (FiniteProbabilityWeights.uniform U) R
      (fun y => integerVectorResidue (affinePairModulus t u) y.val) (fun y => d y.val) c r| ≤
      (finiteCellWeights (FiniteProbabilityWeights.uniform U) R).weight c * beta /
        (affinePairModulus t u : ℝ) ^ Fintype.card I)
    (hcell : ∀ c c' r, |cell c c' r| ≤ cap)
    (hgrid : ∀ x : T, ∀ y : U,
      integerVectorResidue (affinePairModulus t u) x.val = integerVectorResidue (affinePairModulus t u) y.val →
      |shiftedPairLocationKernel t u k hne H L hH (zero_lt_one.trans_le hL) b x.val y.val -
        cell (P x) (R y) (integerVectorResidue (affinePairModulus t u) x.val)| ≤ zeta) :
    |(smoothSourceFiniteWeights (fun z => (b z : ℝ))
      (fun z : Option J × I => smoothPairCoefficientScale (H z.2) L z.1)
      (fun z => smoothPairCoefficientScale_pos (hH z.2) (zero_lt_one.trans_le hL) z.1) hZ).mean
      (fun z => e (smoothAffineSample t z.val) * d (smoothAffineSample u z.val))| ≤
      ((T.card : ℝ) * U.card / ∏ i, H i ^ 2) *
        (cap * alpha * beta + (fullSmoothPairError (Fintype.card I) k Q C κ δ + zeta) * ((2 : ℝ) ^ Fintype.card I / 2 *
          ((FiniteProbabilityWeights.uniform T).mean (fun x => e x.val ^ 2) +
           (FiniteProbabilityWeights.uniform U).mean (fun y => d y.val ^ 2)))) := by
  subst T
  subst U
  refine canonical_smooth_pair_correlation t u k hne H Q hH hL hC hκ hδ hδ1
    ht hu hgap hQ hmesh hsmall b hZ _ _ e d heoff hdoff P R cell halpha hcap hzeta
    ?_ ?_ he hd hcell hgrid
  · exact uniform_interval_box_residue_bound loT hiT hlenT (affinePairModulus t u)
      (affinePairModulus_pos t u k hne) hwidthT
  · exact uniform_interval_box_residue_bound loU hiU hlenU (affinePairModulus t u)
      (affinePairModulus_pos t u k hne) hwidthU

end Erdos3

end

end OAI
