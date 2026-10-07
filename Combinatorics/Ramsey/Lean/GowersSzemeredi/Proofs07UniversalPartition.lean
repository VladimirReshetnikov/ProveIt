import GowersSzemeredi.Proofs07IndexedPartition

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
  obtain ⟨M, Q, hpart, hcell, _⟩ := corollary_7_11_universal_modular_with_step_span
    N R A alpha hR hl hα hαone hA hdensity hlarge
  exact ⟨M, Q, hpart, hcell⟩

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
