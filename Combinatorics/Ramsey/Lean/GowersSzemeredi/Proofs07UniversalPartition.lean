import GowersSzemeredi.Proofs07NinePointLinearity

/-! A single domain-dependent affine partition works for every Freiman map.
This gives simultaneous affine formulas for vector-valued maps without
charging one spectrum or one exponent loss for each coordinate. -/

set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The constant-radius partition can be chosen before any map is specified. -/
theorem corollary_7_11_universal_modular (N : Nat) [Fact N.Prime]
    (R : ModAP N) (A : Finset (ZMod N)) (alpha : Real)
    (hR : R.IsProper) (hl : 0 < R.length) (hα : 0 < alpha) (hαone : alpha ≤ 1)
    (hA : A ⊆ R.carrier) (hdensity : alpha * R.length ≤ A.card)
    (hlarge : 8 ≤ (R.length : Real) ^ cor711Exponent alpha 1) :
    ∃ M : Nat, ∃ Q : Fin M → ModAP N,
      IsPartition (fun j ↦ (Q j).carrier) R.carrier ∧
      (∀ j, (Q j).step != 0 ∧ (Q j).IsProper ∧
        (R.length : Real) ^ cor711Exponent alpha 1 ≤ (Q j).length ∧
        ∀ phi : ZMod N → ZMod N, FreimanHom 8 A phi →
          LinearOn ((Q j).carrier.filter fun x ↦ x ∈ A) phi) := by
  classical
  let P := R.asBox
  let B := liftScalarDomain A
  let U := BaseCase.boxOneIndexAP P
  let C := BaseCase.boxOneIndexDomain P B
  have hP : P.IsProper := fun _ ↦ hR
  have hwidth : P.width = R.length := BaseCase.boxOne_width P
  have hUlength : U.length = R.length := hwidth
  have hBsub : B ⊆ P.carrier := by
    intro x hx
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro i
    fin_cases i
    exact hA ((mem_liftScalarDomain A x).mp hx)
  have hCcard : C.card = A.card := by
    rw [BaseCase.boxOneIndexDomain_card P hP B, Finset.inter_eq_left.mpr hBsub]
    simp [B, liftScalarDomain]
  have hBdomain : BaseCase.pointOneDomain B = A := by
    ext x
    rw [BaseCase.mem_pointOneDomain]
    simp [B, BaseCase.pointOneEquiv]
  have hCfreiman (phi : ZMod N → ZMod N) (hfreiman : FreimanHom 8 A phi) :
      FreimanHom 8 C (BaseCase.boxOneIndexMap P (fun x ↦ phi (x 0))) := by
    apply BaseCase.boxOneIndex_freiman
    change FreimanHom 8 (BaseCase.pointOneDomain B) phi
    rw [hBdomain]
    exact hfreiman
  obtain ⟨M, T, hTpart, hTcell, hTstep, hTlinear⟩ :=
    corollary_7_11_universal_real_lower_bound N 1 U (fun _ ↦ C) alpha
      (by norm_num) hα (by simpa only [hUlength] using hl)
      (BaseCase.boxOneIndexAP_proper P)
      (fun _ ↦ ⟨BaseCase.boxOneIndexDomain_subset P B,
        by simpa only [hUlength, hCcard] using hdensity⟩)
      (by simpa only [hUlength] using hlarge)
  let Q : Fin M → ModAP N := fun j ↦ (BaseCase.indexCellBox P (T j)).axis 0
  have hQproper (j : Fin M) : (Q j).IsProper :=
    BaseCase.indexCellBox_proper P hP (T j) (hTcell j).1 (hTpart.cell_subset j) 0
  have hXtwo : (2 : Real) < (R.length : Real) ^ cor711Exponent alpha 1 := by
    linarith only [hlarge]
  have hQstep (j : Fin M) : (Q j).step ≠ 0 :=
    BaseCase.proper_modAP_step_ne_zero_of_two_le (Q j) (hQproper j) (by
      have hlen : (2 : Real) < (T j).length :=
        hXtwo.trans_le (by simpa only [hUlength] using (hTcell j).2)
      have hlenNat : 2 < (T j).length := by exact_mod_cast hlen
      change 2 ≤ (T j).length
      omega)
  refine ⟨M, Q, ?_, ?_⟩
  · exact box_one_partition_axes P (fun j ↦ BaseCase.indexCellBox P (T j))
      (BaseCase.indexCells_partition P hP T hTpart)
  · intro j
    refine ⟨bne_iff_ne.mpr (hQstep j), hQproper j, ?_, ?_⟩
    · exact (show (R.length : Real) ^ cor711Exponent alpha 1 ≤ (T j).length by
        simpa only [hUlength] using (hTcell j).2)
    · intro phi hfreiman
      exact indexCell_scalar_linear P (T j) A phi (hTpart.cell_subset j) (hQstep j)
        (hTlinear (fun _ ↦ BaseCase.boxOneIndexMap P (fun x ↦ phi (x 0)))
          (fun _ ↦ hCfreiman phi hfreiman) (0 : Fin 1) j)

/-- A short-cell partition works for every Freiman map on the same domain. -/
theorem short_universal_modular_partition {N : Nat} [Fact N.Prime]
    (R : ModAP N) (A : Finset (ZMod N)) (m : Nat)
    (hR : R.IsProper) (hstep : R.step != 0) (hm : 0 < m) (hmEight : m ≤ 8)
    (hlen : m * m ≤ R.length) {t : Real} (ht : t ≤ m) :
    ∃ M : Nat, ∃ Q : Fin M → ModAP N,
      IsPartition (fun j ↦ (Q j).carrier) R.carrier ∧
      ∀ j, (Q j).step != 0 ∧ (Q j).IsProper ∧ t ≤ (Q j).length ∧
        ∀ phi : ZMod N → ZMod N, FreimanHom 8 A phi →
          LinearOn ((Q j).carrier.filter fun x ↦ x ∈ A) phi := by
  classical
  let P := R.asBox
  have hP : P.IsProper := fun _ ↦ hR
  have hwidth : P.width = R.length := BaseCase.boxOne_width P
  have hLm : m * m ≤ P.width := by rwa [hwidth]
  let Q : Fin (P.width / m) → ModAP N :=
    fun j ↦ (BaseCase.coarseChildBox P m j).axis 0
  have hproper (j : Fin (P.width / m)) : (Q j).IsProper :=
    BaseCase.coarseChildBox_proper P hP m hm hLm j 0
  have hlength (j : Fin (P.width / m)) : m ≤ (Q j).length ∧ (Q j).length ≤ 9 := by
    dsimp only [Q, BaseCase.coarseChildBox, BaseCase.coarseChunkLength]
    split_ifs <;> omega
  refine ⟨P.width / m, Q, ?_, ?_⟩
  · exact box_one_partition_axes P (fun j ↦ BaseCase.coarseChildBox P m j)
      (BaseCase.coarseChildBox_partition P hP m hm hLm)
  · intro j
    refine ⟨hstep, hproper j, ht.trans (by exact_mod_cast (hlength j).1), ?_⟩
    intro phi hphi
    apply linearOn_nine_point_progression (Q j) _ phi (hproper j) (hlength j).2
      (Finset.filter_subset _ _)
    exact IsAddFreimanHom.subset
      (fun x hx ↦ (Finset.mem_filter.mp hx).2) hphi (Set.mapsTo_univ _ _)

/-- At every scale, one partition of a proper prime-field progression makes
all order-eight Freiman maps on the given dense domain affine on every cell. -/
theorem corollary_7_11_all_scales_universal (N : Nat) [Fact N.Prime]
    (R : ModAP N) (A : Finset (ZMod N)) (alpha : Real)
    (hR : R.IsProper) (hstep : R.step != 0) (hl : 0 < R.length)
    (hα : 0 < alpha) (hαone : alpha ≤ 1)
    (hA : A ⊆ R.carrier) (hdensity : alpha * R.length ≤ A.card) :
    ∃ M : Nat, ∃ Q : Fin M → ModAP N,
      IsPartition (fun j ↦ (Q j).carrier) R.carrier ∧
      (∀ j, (Q j).step != 0 ∧ (Q j).IsProper ∧
        (R.length : Real) ^ cor711Exponent alpha 1 ≤ (Q j).length ∧
        ∀ phi : ZMod N → ZMod N, FreimanHom 8 A phi →
          LinearOn ((Q j).carrier.filter fun x ↦ x ∈ A) phi) := by
  classical
  have he := cor711_single_exponent_bounds hα hαone
  by_cases hlarge : 8 ≤ (R.length : Real) ^ cor711Exponent alpha 1
  · exact corollary_7_11_universal_modular N R A alpha hR hl hα hαone hA hdensity hlarge
  by_cases hlen : 64 ≤ R.length
  · exact short_universal_modular_partition R A 8 hR hstep (by norm_num) (by norm_num)
      hlen (le_of_not_ge hlarge)
  have hsmall : (R.length : Real) ^ cor711Exponent alpha 1 ≤ 2 := by
    calc
      _ ≤ (64 : Real) ^ cor711Exponent alpha 1 :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast (show R.length ≤ 64 by omega)) he.1.le
      _ = (2 : Real) ^ (6 * cor711Exponent alpha 1) := by
        rw [Real.rpow_mul (by norm_num)]
        norm_num
      _ ≤ (2 : Real) ^ (1 : Real) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [he.2])
      _ = 2 := Real.rpow_one _
  by_cases hfour : 4 ≤ R.length
  · exact short_universal_modular_partition R A 2 hR hstep (by norm_num) (by norm_num)
      hfour hsmall
  have htR : (R.length : Real) ^ cor711Exponent alpha 1 ≤ R.length :=
    Real.rpow_le_self_of_one_le (by exact_mod_cast hl) (by linarith [he.2])
  refine ⟨1, fun _ ↦ R, ?_, fun _ ↦ ⟨hstep, hR, htR, ?_⟩⟩
  · constructor
    · intro x
      exact ⟨fun hx ↦ ⟨0, hx⟩, fun ⟨_, hx⟩ ↦ hx⟩
    · intro i j hij
      exact (bne_iff_ne.mp hij (Subsingleton.elim i j)).elim
  · intro phi hphi
    apply linearOn_nine_point_progression R _ phi hR (by omega) (Finset.filter_subset _ _)
    exact IsAddFreimanHom.subset
      (fun x hx ↦ (Finset.mem_filter.mp hx).2) hphi (Set.mapsTo_univ _ _)

/-- Two coefficient maps share the single-domain exponent, rather than
losing a factor two from treating them as two independent spectra. -/
theorem corollary_7_11_pair_modular (N : Nat) [Fact N.Prime]
    (R : ModAP N) (A : Finset (ZMod N)) (a c : ZMod N → ZMod N) (alpha : Real)
    (hR : R.IsProper) (hstep : R.step != 0) (hl : 0 < R.length)
    (hα : 0 < alpha) (hαone : alpha ≤ 1)
    (hA : A ⊆ R.carrier) (hdensity : alpha * R.length ≤ A.card)
    (ha : FreimanHom 8 A a) (hc : FreimanHom 8 A c) :
    ∃ M : Nat, ∃ Q : Fin M → ModAP N,
      IsPartition (fun j ↦ (Q j).carrier) R.carrier ∧
      ∀ j, (Q j).step != 0 ∧ (Q j).IsProper ∧
        (R.length : Real) ^ cor711Exponent alpha 1 ≤ (Q j).length ∧
        LinearOn ((Q j).carrier.filter fun x ↦ x ∈ A) a ∧
        LinearOn ((Q j).carrier.filter fun x ↦ x ∈ A) c := by
  obtain ⟨M, Q, hp, hcell⟩ :=
    corollary_7_11_all_scales_universal N R A alpha hR hstep hl hα hαone hA hdensity
  exact ⟨M, Q, hp, fun j ↦ ⟨(hcell j).1, (hcell j).2.1, (hcell j).2.2.1,
    (hcell j).2.2.2 a ha, (hcell j).2.2.2 c hc⟩⟩

end LeanProofs.GowersSzemeredi
