import OAI.Combinatorics.Progressions.Estimates.FiniteRetainedCellMean
import OAI.Combinatorics.Progressions.Estimates.PhysicalZeroExtension
import OAI.Combinatorics.Progressions.Estimates.RetainedPhysicalDifference
import OAI.Combinatorics.Progressions.Lattices.ConcreteAffineMeshBoundary

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem affine_mesh_truncation_bound
    {ι I J : Type*} [Fintype ι] [DecidableEq ι] [Fintype I] [Fintype J]
    (lo : I → ℤ) (N : I → ℕ) (P : ∀ i, FiniteProgressionPartition (N i))
    (hPstep : ∀ i c, (P i).step c = 1) (hPpos : ∀ i c, 0 < (P i).length c)
    (sourceLo sourceHi : Option J × I → ℤ) (hsource : ∀ i, sourceLo i < sourceHi i)
    (S : ∀ i, FiniteProgressionPartition (sourceHi i - sourceLo i).toNat)
    (hSstep : ∀ i c, (S i).step c = 1) (hSpos : ∀ i c, 0 < (S i).length c)
    (paramLo paramHi : J → ℤ) (hparam : ∀ j, paramLo j < paramHi j)
    (T : ∀ j, FiniteProgressionPartition (paramHi j - paramLo j).toNat)
    (hTstep : ∀ j c, (T j).step c = 1) (hTpos : ∀ j c, 0 < (T j).length c)
    (D : ℕ) (a : J → ℤ) (q : ι → ℕ) [∀ i, NeZero (q i)] (b : ℕ)
    (w : (Option J × I → ℤ) → ℝ) (h g : (I → ℤ) → ℝ)
    (hw : ∀ z : (∀ i, Finset.Ico (sourceLo i) (sourceHi i)),
      0 ≤ w (fun i => (z i).val) ∧ w (fun i => (z i).val) ≤ 1)
    (hh : ∀ x ∈ translatedIntegerBox lo N, 0 ≤ h x ∧ h x ≤ 1)
    (hg : ∀ x ∈ translatedIntegerBox lo N, 0 ≤ g x ∧ g x ≤ 1)
    {etaParam etaSite r R beta : ℝ} (hetaParam : 0 ≤ etaParam) (hetaSite : 0 ≤ etaSite)
    (hr : 0 ≤ r) (hR : 0 ≤ R)
    (hcloseParam : ∀ ct : (∀ j, (T j).Label),
      ProductMarginalsClose (primeCoordinateReference (σ := J) q)
        (residuePrimeCoordinateDensity (fun j => intervalCellLower (paramLo j) (T j) (ct j))
          (fun j => (T j).length (ct j)) 1 (fun _ => 0)
          (physicalBoxCell_nonempty paramLo (fun j => (paramHi j - paramLo j).toNat) T hTpos ct)
          q (fun _ => 1)) etaParam b)
    (hcloseSite : ∀ c : (∀ i, (P i).Label),
      ProductMarginalsClose (primeCoordinateReference (σ := I) q)
        (residuePrimeCoordinateDensity (fun i => intervalCellLower (lo i) (P i) (c i))
          (fun i => (P i).length (c i)) 1 (fun _ => 0) (physicalBoxCell_nonempty lo N P hPpos c)
          q (fun _ => 1)) etaSite b)
    (hreference : ∀ cs : (∀ i, (S i).Label), ∀ c : (∀ i, (P i).Label),
      productTruncatedPairing (affinePeriodProductCoupling (σ := I) q D a) (lowDegreeCoordinateSets ι b)
        (residuePrimeCoordinateDensity (fun i => intervalCellLower (sourceLo i) (S i) (cs i))
          (fun i => (S i).length (cs i)) 1 (fun _ => 0)
          (physicalBoxCell_nonempty sourceLo (fun i => (sourceHi i - sourceLo i).toNat) S hSpos cs) q w)
        (fun x => residuePrimeCoordinateDensity (fun i => intervalCellLower (lo i) (P i) (c i))
            (fun i => (P i).length (c i)) 1 (fun _ => 0) (physicalBoxCell_nonempty lo N P hPpos c) q h x -
          r * residuePrimeCoordinateDensity (fun i => intervalCellLower (lo i) (P i) (c i))
            (fun i => (P i).length (c i)) 1 (fun _ => 0) (physicalBoxCell_nonempty lo N P hPpos c) q g x) ≤ R)
    (hbad : ((integerBoxUniformWeights paramLo paramHi hparam).prod
        (integerBoxUniformWeights sourceLo sourceHi hsource)).eventProbability
      (physicalMeshCrossing lo N P
        (fun tz => (integerBoxMesh sourceLo sourceHi S tz.2, integerBoxMesh paramLo paramHi T tz.1))
        (fun tz => smoothAffineSample (fun j => a j + (D : ℤ) * (tz.1 j).val) (fun i => (tz.2 i).val))) ≤ beta) :
    ((integerBoxUniformWeights paramLo paramHi hparam).prod
      (integerBoxUniformWeights sourceLo sourceHi hsource)).mean
      (fun tz => w (fun i => (tz.2 i).val) *
        (physicalBoxTruncation lo N P hPpos q b h
            (smoothAffineSample (fun j => a j + (D : ℤ) * (tz.1 j).val) (fun i => (tz.2 i).val)) -
          r * physicalBoxTruncation lo N P hPpos q b g
            (smoothAffineSample (fun j => a j + (D : ℤ) * (tz.1 j).val) (fun i => (tz.2 i).val)))) ≤
      R + (1 + r) * (etaParam + beta) * residueTruncationCap ι b etaSite := by
  let : Nonempty (∀ i, Finset.Ico (sourceLo i) (sourceHi i)) :=
    ⟨fun i => ⟨sourceLo i, Finset.mem_Ico.mpr ⟨le_rfl, hsource i⟩⟩⟩
  let : Nonempty (∀ j, Finset.Ico (paramLo j) (paramHi j)) :=
    ⟨fun j => ⟨paramLo j, Finset.mem_Ico.mpr ⟨le_rfl, hparam j⟩⟩⟩
  let ps := FiniteProbabilityWeights.uniform (∀ i, Finset.Ico (sourceLo i) (sourceHi i))
  let pt := FiniteProbabilityWeights.uniform (∀ j, Finset.Ico (paramLo j) (paramHi j))
  let p := pt.prod ps
  let ms := integerBoxMesh sourceLo sourceHi S
  let mt := integerBoxMesh paramLo paramHi T
  let mesh := fun tz : (∀ j, Finset.Ico (paramLo j) (paramHi j)) ×
      (∀ i, Finset.Ico (sourceLo i) (sourceHi i)) => (ms tz.2, mt tz.1)
  let location := fun tz : (∀ j, Finset.Ico (paramLo j) (paramHi j)) ×
      (∀ i, Finset.Ico (sourceLo i) (sourceHi i)) =>
    smoothAffineSample (fun j => a j + (D : ℤ) * (tz.1 j).val) (fun i => (tz.2 i).val)
  let bad := physicalMeshCrossing lo N P mesh location
  let value := fun (z : Option J × I → ℤ) (t : J → ℤ) => w z *
    (physicalBoxTruncation lo N P hPpos q b h (smoothAffineSample (fun j => a j + (D : ℤ) * t j) z) -
      r * physicalBoxTruncation lo N P hPpos q b g (smoothAffineSample (fun j => a j + (D : ℤ) * t j) z))
  let F := fun tz : (∀ j, Finset.Ico (paramLo j) (paramHi j)) ×
      (∀ i, Finset.Ico (sourceLo i) (sourceHi i)) => value (fun i => (tz.2 i).val) (fun j => (tz.1 j).val)
  let cap := residueTruncationCap ι b etaSite
  let K := R + (1 + r) * etaParam * cap
  have hcap0 : 0 ≤ cap := residueTruncationCap_nonneg ι b hetaSite
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hsLaw : integerBoxUniformWeights sourceLo sourceHi hsource = ps :=
    integerBoxUniformWeights_eq_uniform sourceLo sourceHi hsource
  have htLaw : integerBoxUniformWeights paramLo paramHi hparam = pt :=
    integerBoxUniformWeights_eq_uniform paramLo paramHi hparam
  rw [hsLaw, htLaw] at hbad ⊢
  change p.eventProbability bad ≤ beta at hbad
  change p.mean F ≤ R + (1 + r) * (etaParam + beta) * cap
  have hlocal (x) (hx : ¬ bad x) : finiteCellMean p mesh F (mesh x) ≤ K * (finiteCellWeights p mesh).weight (mesh x) := by
    let cs := ms x.2
    let ct := mt x.1
    have hclass := retained_integer_mesh_boxes_classify lo N P sourceLo sourceHi S hSstep hSpos
      paramLo paramHi T hTstep hTpos D a x hx
    have hwcell (z) (hz : z ∈ translatedIntegerBox
        (fun i => intervalCellLower (sourceLo i) (S i) (cs i)) (fun i => (S i).length (cs i))) :
        0 ≤ w z ∧ w z ≤ 1 := by
      obtain ⟨y, _, hy⟩ := integerBoxMesh_cell_realize sourceLo sourceHi S hSstep hSpos cs z hz
      simpa only [hy] using hw y
    have havg : (𝔼 z : IntegerResidueBox (fun i => intervalCellLower (sourceLo i) (S i) (cs i))
        (fun i => intervalCellLower (sourceLo i) (S i) (cs i) + (S i).length (cs i)) (fun _ => 1) (fun _ => 0),
      𝔼 t : IntegerResidueBox (fun j => intervalCellLower (paramLo j) (T j) (ct j))
        (fun j => intervalCellLower (paramLo j) (T j) (ct j) + (T j).length (ct j)) (fun _ => 1) (fun _ => 0),
        value (fun i => (z i).val) (fun j => (t j).val)) ≤ K := by
      cases hc : physicalBoxClassify lo N P (location x) with
      | some c =>
          have ht := retained_physical_truncation_difference_le lo N P hPstep hPpos c q
            (fun i => intervalCellLower (sourceLo i) (S i) (cs i)) (fun i => (S i).length (cs i))
            (physicalBoxCell_nonempty sourceLo (fun i => (sourceHi i - sourceLo i).toNat) S hSpos cs)
            (fun j => intervalCellLower (paramLo j) (T j) (ct j)) (fun j => (T j).length (ct j))
            (physicalBoxCell_nonempty paramLo (fun j => (paramHi j - paramLo j).toNat) T hTpos ct)
            D a b w h g hwcell hh hg
            (fun z hz t ht => (hclass z hz t ht).trans hc) hetaParam hetaSite hr
            (hcloseParam ct) (hcloseSite c) (hreference cs c)
          simpa only [value, K, cap, ← Finset.mul_expect] using ht
      | none =>
          have he (z : IntegerResidueBox (fun i => intervalCellLower (sourceLo i) (S i) (cs i))
              (fun i => intervalCellLower (sourceLo i) (S i) (cs i) + (S i).length (cs i)) (fun _ => 1) (fun _ => 0))
              (t : IntegerResidueBox (fun j => intervalCellLower (paramLo j) (T j) (ct j))
              (fun j => intervalCellLower (paramLo j) (T j) (ct j) + (T j).length (ct j)) (fun _ => 1) (fun _ => 0)) :
              value (fun i => (z i).val) (fun j => (t j).val) = 0 := by
            have hnone := (hclass (fun i => (z i).val)
              ((mem_translatedIntegerBox _ _ _).mpr (fun i => Finset.mem_Ico.mp (Finset.mem_filter.mp (z i).property).1))
              (fun j => (t j).val)
              ((mem_translatedIntegerBox _ _ _).mpr (fun j => Finset.mem_Ico.mp (Finset.mem_filter.mp (t j).property).1))).trans hc
            dsimp only [value]
            rw [physicalBoxTruncation_of_classify_none lo N P hPpos q b h _ hnone,
              physicalBoxTruncation_of_classify_none lo N P hPpos q b g _ hnone]
            ring
          simpa only [he, Finset.expect_const_zero] using hK
    have hm := integerBoxMesh_pair_cell_mean sourceLo sourceHi S hSstep hSpos
      paramLo paramHi T hTstep hTpos cs ct value
    have hwgt := finiteCellWeights_product ps pt ms mt cs ct
    change finiteCellMean p mesh F (cs,ct) ≤ K * (finiteCellWeights p mesh).weight (cs,ct)
    rw [hm, hwgt]
    exact (mul_le_mul_of_nonneg_left havg
      (mul_nonneg ((finiteCellWeights ps ms).nonneg cs) ((finiteCellWeights pt mt).nonneg ct))).trans_eq (mul_comm _ _)
  have hbound (x) (_ : bad x) : |F x| ≤ (1 + r) * cap := by
    have hhc := physicalBoxTruncation_cap lo N P hPstep hPpos q b h hh hetaSite hcloseSite (location x)
    have hgc := physicalBoxTruncation_cap lo N P hPstep hPpos q b g hg hetaSite hcloseSite (location x)
    have hd : |physicalBoxTruncation lo N P hPpos q b h (location x) -
        r * physicalBoxTruncation lo N P hPpos q b g (location x)| ≤ (1 + r) * cap := by
      apply (abs_sub _ _).trans
      rw [abs_mul, abs_of_nonneg hr]
      exact (add_le_add hhc (mul_le_mul_of_nonneg_left hgc hr)).trans_eq (by dsimp only [cap]; ring)
    change |w (fun i => (x.2 i).val) *
      (physicalBoxTruncation lo N P hPpos q b h (location x) -
        r * physicalBoxTruncation lo N P hPpos q b g (location x))| ≤ _
    rw [abs_mul, abs_of_nonneg (hw x.2).1]
    exact (mul_le_mul (hw x.2).2 hd (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hall := finite_mean_le_of_retained_cells p mesh bad F
    (fun x y hxy => physicalMeshCrossing_congr lo N P mesh location hxy)
    hK (by positivity : 0 ≤ (1 + r) * cap) hbad hbound hlocal
  exact hall.trans_eq (by dsimp only [K]; ring)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem affine_mesh_zero_extension_bound
    {ι I J : Type*} [Fintype ι] [DecidableEq ι] [Fintype I] [Fintype J]
    (lo : I → ℤ) (N : I → ℕ) (P : ∀ i, FiniteProgressionPartition (N i))
    (hPstep : ∀ i c, (P i).step c = 1) (hPpos : ∀ i c, 0 < (P i).length c)
    (sourceLo sourceHi : Option J × I → ℤ) (hsource : ∀ i, sourceLo i < sourceHi i)
    (S : ∀ i, FiniteProgressionPartition (sourceHi i - sourceLo i).toNat)
    (hSstep : ∀ i c, (S i).step c = 1) (hSpos : ∀ i c, 0 < (S i).length c)
    (paramLo paramHi : J → ℤ) (hparam : ∀ j, paramLo j < paramHi j)
    (T : ∀ j, FiniteProgressionPartition (paramHi j - paramLo j).toNat)
    (hTstep : ∀ j c, (T j).step c = 1) (hTpos : ∀ j c, 0 < (T j).length c)
    (D : ℕ) (a : J → ℤ) (q : ι → ℕ) [∀ i, NeZero (q i)] (b : ℕ)
    (w : (Option J × I → ℤ) → ℝ) (h g : (I → ℤ) → ℝ)
    (hw : ∀ z : (∀ i, Finset.Ico (sourceLo i) (sourceHi i)),
      0 ≤ w (fun i => (z i).val) ∧ w (fun i => (z i).val) ≤ 1)
    (hh : ∀ x ∈ translatedIntegerBox lo N, 0 ≤ h x ∧ h x ≤ 1)
    (hg : ∀ x ∈ translatedIntegerBox lo N, 0 ≤ g x ∧ g x ≤ 1)
    {etaParam etaSite r R beta accuracy : ℝ} (hetaParam : 0 ≤ etaParam) (hetaSite : 0 ≤ etaSite)
    (hr : 0 ≤ r) (hR : 0 ≤ R)
    (hcloseParam : ∀ ct : (∀ j, (T j).Label),
      ProductMarginalsClose (primeCoordinateReference (σ := J) q)
        (residuePrimeCoordinateDensity (fun j => intervalCellLower (paramLo j) (T j) (ct j))
          (fun j => (T j).length (ct j)) 1 (fun _ => 0)
          (physicalBoxCell_nonempty paramLo (fun j => (paramHi j - paramLo j).toNat) T hTpos ct)
          q (fun _ => 1)) etaParam b)
    (hcloseSite : ∀ c : (∀ i, (P i).Label),
      ProductMarginalsClose (primeCoordinateReference (σ := I) q)
        (residuePrimeCoordinateDensity (fun i => intervalCellLower (lo i) (P i) (c i))
          (fun i => (P i).length (c i)) 1 (fun _ => 0) (physicalBoxCell_nonempty lo N P hPpos c)
          q (fun _ => 1)) etaSite b)
    (hreference : ∀ cs : (∀ i, (S i).Label), ∀ c : (∀ i, (P i).Label),
      productTruncatedPairing (affinePeriodProductCoupling (σ := I) q D a) (lowDegreeCoordinateSets ι b)
        (residuePrimeCoordinateDensity (fun i => intervalCellLower (sourceLo i) (S i) (cs i))
          (fun i => (S i).length (cs i)) 1 (fun _ => 0)
          (physicalBoxCell_nonempty sourceLo (fun i => (sourceHi i - sourceLo i).toNat) S hSpos cs) q w)
        (fun x => residuePrimeCoordinateDensity (fun i => intervalCellLower (lo i) (P i) (c i))
            (fun i => (P i).length (c i)) 1 (fun _ => 0) (physicalBoxCell_nonempty lo N P hPpos c) q h x -
          r * residuePrimeCoordinateDensity (fun i => intervalCellLower (lo i) (P i) (c i))
            (fun i => (P i).length (c i)) 1 (fun _ => 0) (physicalBoxCell_nonempty lo N P hPpos c) q g x) ≤ R)
    (hbad : ((integerBoxUniformWeights paramLo paramHi hparam).prod
        (integerBoxUniformWeights sourceLo sourceHi hsource)).eventProbability
      (physicalMeshCrossing lo N P
        (fun tz => (integerBoxMesh sourceLo sourceHi S tz.2, integerBoxMesh paramLo paramHi T tz.1))
        (fun tz => smoothAffineSample (fun j => a j + (D : ℤ) * (tz.1 j).val) (fun i => (tz.2 i).val))) ≤ beta)
    (heh : |((integerBoxUniformWeights paramLo paramHi hparam).prod
        (integerBoxUniformWeights sourceLo sourceHi hsource)).mean
      (fun tz => w (fun i => (tz.2 i).val) * physicalBoxResidual lo N P hPpos q b h
        (smoothAffineSample (fun j => a j + (D : ℤ) * (tz.1 j).val) (fun i => (tz.2 i).val)))| ≤ accuracy)
    (heg : |((integerBoxUniformWeights paramLo paramHi hparam).prod
        (integerBoxUniformWeights sourceLo sourceHi hsource)).mean
      (fun tz => w (fun i => (tz.2 i).val) * physicalBoxResidual lo N P hPpos q b g
        (smoothAffineSample (fun j => a j + (D : ℤ) * (tz.1 j).val) (fun i => (tz.2 i).val)))| ≤ accuracy) :
    ((integerBoxUniformWeights paramLo paramHi hparam).prod
      (integerBoxUniformWeights sourceLo sourceHi hsource)).mean
      (fun tz => w (fun i => (tz.2 i).val) *
        (realZeroExtendFinset (translatedIntegerBox lo N) h
            (smoothAffineSample (fun j => a j + (D : ℤ) * (tz.1 j).val) (fun i => (tz.2 i).val)) -
          r * realZeroExtendFinset (translatedIntegerBox lo N) g
            (smoothAffineSample (fun j => a j + (D : ℤ) * (tz.1 j).val) (fun i => (tz.2 i).val)))) ≤
      R + (1 + r) * ((etaParam + beta) * residueTruncationCap ι b etaSite + accuracy) := by
  have hlow := affine_mesh_truncation_bound lo N P hPstep hPpos
    sourceLo sourceHi hsource S hSstep hSpos paramLo paramHi hparam T hTstep hTpos
    D a q b w h g hw hh hg hetaParam hetaSite hr hR hcloseParam hcloseSite hreference hbad
  have hrestore := physical_zero_extension_restore_difference
    ((integerBoxUniformWeights paramLo paramHi hparam).prod
      (integerBoxUniformWeights sourceLo sourceHi hsource))
    (fun tz => smoothAffineSample (fun j => a j + (D : ℤ) * (tz.1 j).val) (fun i => (tz.2 i).val))
    (fun tz => w (fun i => (tz.2 i).val)) lo N P hPstep hPpos q b h g hr heh heg hlow
  exact hrestore.trans_eq (by ring)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem affine_mesh_scalar_tail
    {ι I J : Type*} [Fintype ι] [DecidableEq ι] [Fintype I] [Fintype J]
    (lo : I → ℤ) (N : I → ℕ) (P : ∀ i, FiniteProgressionPartition (N i))
    (hPstep : ∀ i c, (P i).step c = 1) (hPpos : ∀ i c, 0 < (P i).length c)
    (sourceLo sourceHi : Option J × I → ℤ) (hsource : ∀ i, sourceLo i < sourceHi i)
    (S : ∀ i, FiniteProgressionPartition (sourceHi i - sourceLo i).toNat)
    (hSstep : ∀ i c, (S i).step c = 1) (hSpos : ∀ i c, 0 < (S i).length c)
    (paramLo paramHi : J → ℤ) (hparam : ∀ j, paramLo j < paramHi j)
    (T : ∀ j, FiniteProgressionPartition (paramHi j - paramLo j).toNat)
    (hTstep : ∀ j c, (T j).step c = 1) (hTpos : ∀ j c, 0 < (T j).length c)
    (D : ℕ) (a : J → ℤ) (q : ι → ℕ) [∀ i, NeZero (q i)] (b : ℕ)
    (h g : (I → ℤ) → ℝ)
    (hh : ∀ x ∈ translatedIntegerBox lo N, 0 ≤ h x ∧ h x ≤ 1)
    (hg : ∀ x ∈ translatedIntegerBox lo N, 0 ≤ g x ∧ g x ≤ 1)
    {etaParam etaSite r R beta accuracy : ℝ} (hetaParam : 0 ≤ etaParam) (hetaSite : 0 ≤ etaSite)
    (hr : 0 ≤ r) (hR : 0 ≤ R)
    (hcloseParam : ∀ ct : (∀ j, (T j).Label),
      ProductMarginalsClose (primeCoordinateReference (σ := J) q)
        (residuePrimeCoordinateDensity (fun j => intervalCellLower (paramLo j) (T j) (ct j))
          (fun j => (T j).length (ct j)) 1 (fun _ => 0)
          (physicalBoxCell_nonempty paramLo (fun j => (paramHi j - paramLo j).toNat) T hTpos ct)
          q (fun _ => 1)) etaParam b)
    (hcloseSite : ∀ c : (∀ i, (P i).Label),
      ProductMarginalsClose (primeCoordinateReference (σ := I) q)
        (residuePrimeCoordinateDensity (fun i => intervalCellLower (lo i) (P i) (c i))
          (fun i => (P i).length (c i)) 1 (fun _ => 0) (physicalBoxCell_nonempty lo N P hPpos c)
          q (fun _ => 1)) etaSite b)
    (hreference : ∀ w : (Option J × I → ℤ) → ℝ, (∀ z : (∀ i, Finset.Ico (sourceLo i) (sourceHi i)),
      0 ≤ w (fun i => (z i).val) ∧ w (fun i => (z i).val) ≤ 1) →
      ∀ cs : (∀ i, (S i).Label), ∀ c : (∀ i, (P i).Label),
      productTruncatedPairing (affinePeriodProductCoupling (σ := I) q D a) (lowDegreeCoordinateSets ι b)
        (residuePrimeCoordinateDensity (fun i => intervalCellLower (sourceLo i) (S i) (cs i))
          (fun i => (S i).length (cs i)) 1 (fun _ => 0)
          (physicalBoxCell_nonempty sourceLo (fun i => (sourceHi i - sourceLo i).toNat) S hSpos cs) q w)
        (fun x => residuePrimeCoordinateDensity (fun i => intervalCellLower (lo i) (P i) (c i))
            (fun i => (P i).length (c i)) 1 (fun _ => 0) (physicalBoxCell_nonempty lo N P hPpos c) q h x -
          r * residuePrimeCoordinateDensity (fun i => intervalCellLower (lo i) (P i) (c i))
            (fun i => (P i).length (c i)) 1 (fun _ => 0) (physicalBoxCell_nonempty lo N P hPpos c) q g x) ≤ R)
    (hbad : ((integerBoxUniformWeights paramLo paramHi hparam).prod
        (integerBoxUniformWeights sourceLo sourceHi hsource)).eventProbability
      (physicalMeshCrossing lo N P
        (fun tz => (integerBoxMesh sourceLo sourceHi S tz.2, integerBoxMesh paramLo paramHi T tz.1))
        (fun tz => smoothAffineSample (fun j => a j + (D : ℤ) * (tz.1 j).val) (fun i => (tz.2 i).val))) ≤ beta)
    (heh : ∀ w : (Option J × I → ℤ) → ℝ, (∀ z : (∀ i, Finset.Ico (sourceLo i) (sourceHi i)),
      0 ≤ w (fun i => (z i).val) ∧ w (fun i => (z i).val) ≤ 1) →
      |((integerBoxUniformWeights paramLo paramHi hparam).prod
        (integerBoxUniformWeights sourceLo sourceHi hsource)).mean
      (fun tz => w (fun i => (tz.2 i).val) * physicalBoxResidual lo N P hPpos q b h
        (smoothAffineSample (fun j => a j + (D : ℤ) * (tz.1 j).val) (fun i => (tz.2 i).val)))| ≤ accuracy)
    (heg : ∀ w : (Option J × I → ℤ) → ℝ, (∀ z : (∀ i, Finset.Ico (sourceLo i) (sourceHi i)),
      0 ≤ w (fun i => (z i).val) ∧ w (fun i => (z i).val) ≤ 1) →
      |((integerBoxUniformWeights paramLo paramHi hparam).prod
        (integerBoxUniformWeights sourceLo sourceHi hsource)).mean
      (fun tz => w (fun i => (tz.2 i).val) * physicalBoxResidual lo N P hPpos q b g
        (smoothAffineSample (fun j => a j + (D : ℤ) * (tz.1 j).val) (fun i => (tz.2 i).val)))| ≤ accuracy)
    (p dominationLog : ℝ)
    (outer : FiniteProbabilityWeights (∀ i, Finset.Ico (sourceLo i) (sourceHi i)))
    (hdom : ∀ z, outer.weight z ≤ Real.exp dominationLog *
      (integerBoxUniformWeights sourceLo sourceHi hsource).weight z)
    (herror : R + (1 + r) * ((etaParam + beta) * residueTruncationCap ι b etaSite + accuracy) ≤
      Real.exp (-(2 * p + dominationLog)) / 2) :
    outer.eventProbability (fun z => Real.exp (-p) <
      (integerBoxUniformWeights paramLo paramHi hparam).mean (fun t =>
        realZeroExtendFinset (translatedIntegerBox lo N) h
          (smoothAffineSample (fun j => a j + (D : ℤ) * (t j).val) (fun i => (z i).val)) -
        r * realZeroExtendFinset (translatedIntegerBox lo N) g
          (smoothAffineSample (fun j => a j + (D : ℤ) * (t j).val) (fun i => (z i).val)))) ≤
      Real.exp (-p) := by
  apply fixedParameter_observed_tail_dominated
    (integerBoxUniformWeights sourceLo sourceHi hsource) outer
    (integerBoxUniformWeights paramLo paramHi hparam) (fun z i => (z i).val)
    (fun t z => realZeroExtendFinset (translatedIntegerBox lo N) h
        (smoothAffineSample (fun j => a j + (D : ℤ) * (t j).val) z) -
      r * realZeroExtendFinset (translatedIntegerBox lo N) g
        (smoothAffineSample (fun j => a j + (D : ℤ) * (t j).val) z)) p dominationLog hdom
  intro w hw
  exact (affine_mesh_zero_extension_bound lo N P hPstep hPpos sourceLo sourceHi hsource
    S hSstep hSpos paramLo paramHi hparam T hTstep hTpos D a q b w h g hw hh hg
    hetaParam hetaSite hr hR hcloseParam hcloseSite (hreference w hw) hbad
    (heh w hw) (heg w hw)).trans herror

end Erdos3

end

end OAI
