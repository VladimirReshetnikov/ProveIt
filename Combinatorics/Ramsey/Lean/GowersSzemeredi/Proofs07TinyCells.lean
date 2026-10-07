import GowersSzemeredi.Proofs07UniversalPartition

/-! Universal affine partitions with explicit small upper lengths. -/

set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- A short-cell partition works for every Freiman map on the same domain. -/
theorem short_universal_modular_partition_bounded {N : Nat} [Fact N.Prime]
    (R : ModAP N) (A : Finset (ZMod N)) (m : Nat)
    (hR : R.IsProper) (hstep : R.step != 0) (hm : 0 < m) (hmEight : m ≤ 8)
    (hlen : m * m ≤ R.length) {t : Real} (ht : t ≤ m) :
    ∃ M : Nat, ∃ Q : Fin M → ModAP N,
      IsPartition (fun j ↦ (Q j).carrier) R.carrier ∧
      ∀ j, (Q j).step != 0 ∧ (Q j).IsProper ∧ t ≤ (Q j).length ∧ (Q j).length ≤ m + 1 ∧
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
  have hlength (j : Fin (P.width / m)) : m ≤ (Q j).length ∧ (Q j).length ≤ m + 1 := by
    dsimp only [Q, BaseCase.coarseChildBox, BaseCase.coarseChunkLength]
    split_ifs <;> omega
  refine ⟨P.width / m, Q, ?_, ?_⟩
  · exact box_one_partition_axes P (fun j ↦ BaseCase.coarseChildBox P m j)
      (BaseCase.coarseChildBox_partition P hP m hm hLm)
  · intro j
    refine ⟨hstep, hproper j, ht.trans (by exact_mod_cast (hlength j).1), (hlength j).2, ?_⟩
    intro phi hphi
    apply linearOn_nine_point_progression (Q j) _ phi (hproper j) ((hlength j).2.trans (by omega))
      (Finset.filter_subset _ _)
    exact IsAddFreimanHom.subset
      (fun x hx ↦ (Finset.mem_filter.mp hx).2) hphi (Set.mapsTo_univ _ _)

/-- Any target at most two and no larger than the parent is realized by
cells of length at most three, simultaneously for every order-eight map. -/
theorem universal_partition_at_most_three {N : Nat} [Fact N.Prime]
    (R : ModAP N) (A : Finset (ZMod N)) (t : Real)
    (hR : R.IsProper) (hstep : R.step != 0) (ht : t ≤ 2) (htR : t ≤ R.length) :
    ∃ M : Nat, ∃ Q : Fin M → ModAP N,
      IsPartition (fun j ↦ (Q j).carrier) R.carrier ∧
      ∀ j, (Q j).step != 0 ∧ (Q j).IsProper ∧ t ≤ (Q j).length ∧
        (Q j).length ≤ 3 ∧
        ∀ phi : ZMod N → ZMod N, FreimanHom 8 A phi →
          LinearOn ((Q j).carrier.filter fun x ↦ x ∈ A) phi := by
  classical
  by_cases hfour : 4 ≤ R.length
  · exact short_universal_modular_partition_bounded R A 2 hR hstep
      (by norm_num) (by norm_num) hfour ht
  refine ⟨1, fun _ ↦ R, ?_, fun _ ↦ ⟨hstep, hR, htR, by change R.length ≤ 3; omega, ?_⟩⟩
  · constructor
    · intro x
      exact ⟨fun hx ↦ ⟨0, hx⟩, fun ⟨_, hx⟩ ↦ hx⟩
    · intro i j hij
      exact (bne_iff_ne.mp hij (Subsingleton.elim i j)).elim
  · intro phi hphi
    apply linearOn_nine_point_progression R _ phi hR (by omega) (Finset.filter_subset _ _)
    exact IsAddFreimanHom.subset
      (fun x hx ↦ (Finset.mem_filter.mp hx).2) hphi (Set.mapsTo_univ _ _)

end LeanProofs.GowersSzemeredi
