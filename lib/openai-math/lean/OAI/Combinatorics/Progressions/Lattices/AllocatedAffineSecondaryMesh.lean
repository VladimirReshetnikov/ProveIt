import OAI.Combinatorics.Progressions.Dynamics.SecondaryMeshLogBudget
import OAI.Combinatorics.Progressions.Lattices.ConcreteAffineMeshBoundary

namespace OAI

section

namespace Erdos3

open scoped Classical

theorem exists_allocated_affine_secondary_mesh {J I : Type*}
    [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (sourceLo sourceHi : Option J × I → ℤ) (hsource : ∀ z, sourceLo z < sourceHi z)
    (parLo parHi anchor : J → ℤ) (hpar : ∀ j, parLo j < parHi j) (D : ℕ) (hD : 0 < D)
    (lo : I → ℤ) (N : I → ℕ) (H : I → ℝ) {L C B A c rho sourceRatio parameterRatio U lengthLog beta : ℝ}
    (hL : 0 < L) (hH : ∀ i, 0 < H i) (hC : 0 ≤ C) (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hc : 0 < c) (hrho : 0 < rho) (hsRatio : 0 ≤ sourceRatio) (hpRatio : 0 ≤ parameterRatio)
    (hU : 0 ≤ U) (hlength : 0 ≤ lengthLog) (hbeta : 0 < beta)
    (hsiteLarge : ∀ i, 4 ≤ rho * H i) (hsiteWhole : ∀ i, rho * H i ≤ 2 * (N i : ℝ))
    (hsiteRatio : ∀ i, (N i : ℝ) ≤ A * H i)
    (hbaseWidth : ∀ i, c * H i ≤ ((sourceHi (none, i) - sourceLo (none, i) : ℤ) : ℝ))
    (hparamLo : ∀ j, |((anchor j + (D : ℤ) * parLo j : ℤ) : ℝ) / L| ≤ C)
    (hparamHi : ∀ j, |((anchor j + (D : ℤ) * parHi j : ℤ) : ℝ) / L| ≤ C)
    (hsourceLo : ∀ j i, |(sourceLo (some j, i) : ℝ)| ≤ B * H i / L)
    (hsourceHi : ∀ j i, |(sourceHi (some j, i) : ℝ)| ≤ B * H i / L)
    (hboundaryU : 40 * (Fintype.card I : ℝ) * A / (rho * c) ≤ Real.exp U)
    (hmovementU : 1 + (Fintype.card J : ℝ) * (C + B) ≤ Real.exp U)
    (hsourceU : sourceRatio ≤ Real.exp U) (hparameterU : parameterRatio ≤ Real.exp U)
    (hbetaU : beta⁻¹ ≤ Real.exp U)
    (hsourceWidth : ∀ z : Option J × I, smoothPairCoefficientScale (H z.2) L z.1 ≤
      sourceRatio * ((sourceHi z - sourceLo z).toNat : ℝ))
    (hparameterWidth : ∀ j, L / (D : ℝ) ≤ parameterRatio * ((parHi j - parLo j).toNat : ℝ))
    (hsourceScale : ∀ z : Option J × I, 4 * Real.exp (4 * U + 18 + lengthLog) ≤
      smoothPairCoefficientScale (H z.2) L z.1)
    (hparameterScale : 4 * Real.exp (4 * U + 18 + lengthLog) ≤ L / (D : ℝ)) :
    let P := normalizedBoxPartitions N H rho hsiteLarge hsiteWhole
    ∃ (S : ∀ z, FiniteProgressionPartition (sourceHi z - sourceLo z).toNat)
      (T : ∀ j, FiniteProgressionPartition (parHi j - parLo j).toNat),
    (∀ z cs, (S z).step cs = 1) ∧ (∀ z cs, 0 < (S z).length cs) ∧
    (∀ j ct, (T j).step ct = 1) ∧ (∀ j ct, 0 < (T j).length ct) ∧
    (∀ z cs, Real.exp lengthLog ≤ ((S z).length cs : ℝ)) ∧
    (∀ j ct, Real.exp lengthLog ≤ ((T j).length ct : ℝ)) ∧
    ((integerBoxUniformWeights parLo parHi hpar).prod
      (integerBoxUniformWeights sourceLo sourceHi hsource)).eventProbability
      (physicalMeshCrossing lo N P
        (fun tz => (integerBoxMesh sourceLo sourceHi S tz.2, integerBoxMesh parLo parHi T tz.1))
        (fun tz => smoothAffineSample (fun j => anchor j + (D : ℤ) * (tz.1 j).val)
          (fun i => (tz.2 i).val))) ≤ beta := by
  intro P
  let boundary := 40 * (Fintype.card I : ℝ) * A / (rho * c)
  let movement := 1 + (Fintype.card J : ℝ) * (C + B)
  let M := secondaryMovementBudget movement sourceRatio parameterRatio
  let margin := secondaryBoundaryMargin boundary beta
  let delta := secondaryMeshDelta boundary M beta
  have hb : 0 ≤ boundary := by dsimp only [boundary]; positivity
  have hm : 0 ≤ movement := by dsimp only [movement]; positivity
  obtain ⟨hmargin, _, hpay, hdelta, _, hmove, hsw, hpw⟩ :=
    secondaryMesh_geometry hb hm hsRatio hpRatio hbeta
  have hinv := secondaryMesh_geometry_inverse hb hm hsRatio hpRatio hbeta hU
    hboundaryU hmovementU hsourceU hparameterU hbetaU
  change 0 < margin at hmargin
  change 0 < delta at hdelta
  change delta * movement ≤ margin at hmove
  change delta * sourceRatio ≤ 1 at hsw
  change delta * parameterRatio ≤ 1 at hpw
  have hsLarge (z : Option J × I) : 4 ≤ delta * smoothPairCoefficientScale (H z.2) L z.1 :=
    normalizedMesh_scale_large hdelta hinv.2 hlength (hsourceScale z)
  have hsWhole (z : Option J × I) : delta * smoothPairCoefficientScale (H z.2) L z.1 ≤
      2 * ((sourceHi z - sourceLo z).toNat : ℝ) :=
    normalizedMesh_upper_of_ratio _ hdelta.le hsw (hsourceWidth z)
  have htLarge (_j : J) : 4 ≤ delta * (L / (D : ℝ)) :=
    normalizedMesh_scale_large hdelta hinv.2 hlength hparameterScale
  have htWhole (j : J) : delta * (L / (D : ℝ)) ≤ 2 * ((parHi j - parLo j).toNat : ℝ) :=
    normalizedMesh_upper_of_ratio _ hdelta.le hpw (hparameterWidth j)
  let S := normalizedBoxPartitions (fun z => (sourceHi z - sourceLo z).toNat)
    (fun z => smoothPairCoefficientScale (H z.2) L z.1) delta hsLarge hsWhole
  let T := normalizedBoxPartitions (fun j => (parHi j - parLo j).toNat)
    (fun _ => L / (D : ℝ)) delta htLarge htWhole
  refine ⟨S, T, normalizedBoxPartitions_step _ _ _ _ _, normalizedBoxPartitions_positive _ _ _ _ _,
    normalizedBoxPartitions_step _ _ _ _ _, normalizedBoxPartitions_positive _ _ _ _ _, ?_, ?_, ?_⟩
  · exact normalizedBoxPartitions_exp_lengths _ _ delta (4 * U + 18) lengthLog hdelta hinv.2
      hsourceScale hsLarge hsWhole
  · exact normalizedBoxPartitions_exp_lengths _ _ delta (4 * U + 18) lengthLog hdelta hinv.2
      (fun _ => hparameterScale) htLarge htWhole
  · have hround (i : I) : 1 ≤ margin * H i :=
      secondaryMesh_rounding_of_scale hmargin hinv.1 hU hlength (hsourceScale (none,i))
    have hbad := concrete_affine_mesh_boundary_probability sourceLo sourceHi hsource
      parLo parHi anchor hpar D hD lo N H hL hH hC hB hA hc hrho hmargin
      hsiteLarge hsiteWhole hsiteRatio hbaseWidth hround hparamLo hparamHi hsourceLo hsourceHi
      hsLarge hsWhole htLarge htWhole hmove
    apply hbad.trans
    change 40 * (Fintype.card I : ℝ) * A * margin / (rho * c) ≤ beta
    calc
      _ = boundary * margin := by dsimp only [boundary]; ring
      _ ≤ beta := hpay

end Erdos3

end

end OAI
