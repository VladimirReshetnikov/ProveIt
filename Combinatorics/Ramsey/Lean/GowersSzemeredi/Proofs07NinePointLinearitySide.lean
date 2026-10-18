import GowersSzemeredi.Proofs07NinePointLinearity
import GowersSzemeredi.Proofs07ModularPartitionSide
import GowersSzemeredi.Proofs07ShortLinearitySide

/-! Declarations of `Proofs07NinePointLinearity` that the final route does not use (moved here so
that the route keeps only what it uses). -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

/-- Eight- or nine-point affine cells cover every proper progression of
length at least sixty-four, retaining its nonzero step. -/
theorem eight_modular_affine_partition {N : Nat} [Fact N.Prime]
    (R : ModAP N) (A : Finset (ZMod N)) (phi : ZMod N → ZMod N)
    (hR : R.IsProper) (hstep : R.step != 0) (hlen : 64 ≤ R.length)
    (hphi : FreimanHom 8 A phi) {t : Real} (ht : t ≤ 8) :
    ∃ M : Nat, ∃ Q : Fin M → ModAP N,
      IsPartition (fun j ↦ (Q j).carrier) R.carrier ∧
      ∀ j, (Q j).step != 0 ∧ (Q j).IsProper ∧ t ≤ (Q j).length ∧
        LinearOn ((Q j).carrier.filter fun x ↦ x ∈ A) phi := by
  have hlinear (P : ModAP N) (hp : P.IsProper) (hlen : P.length ≤ 9) :
      LinearOn (P.carrier.filter fun x ↦ x ∈ A) phi := by
    apply linearOn_nine_point_progression P _ phi hp hlen (Finset.filter_subset _ _)
    exact IsAddFreimanHom.subset
      (fun x hx ↦ (Finset.mem_filter.mp hx).2) hphi (Set.mapsTo_univ _ _)
  let P := R.asBox
  have hP : P.IsProper := fun _ ↦ hR
  have hwidth : P.width = R.length := BaseCase.boxOne_width P
  have hLm : 8 * 8 ≤ P.width := by rw [hwidth]; omega
  let Q : Fin (P.width / 8) → ModAP N :=
    fun j ↦ (BaseCase.coarseChildBox P 8 j).axis 0
  have hproper (j : Fin (P.width / 8)) : (Q j).IsProper :=
    BaseCase.coarseChildBox_proper P hP 8 (by norm_num) hLm j 0
  have hlength (j : Fin (P.width / 8)) : 8 ≤ (Q j).length ∧ (Q j).length ≤ 9 := by
    dsimp only [Q, BaseCase.coarseChildBox, BaseCase.coarseChunkLength]
    split_ifs <;> omega
  refine ⟨P.width / 8, Q, ?_, ?_⟩
  · exact box_one_partition_axes P (fun j ↦ BaseCase.coarseChildBox P 8 j)
      (BaseCase.coarseChildBox_partition P hP 8 (by norm_num) hLm)
  · intro j
    refine ⟨hstep, hproper j, ?_, hlinear (Q j) (hproper j) (hlength j).2⟩
    exact ht.trans (by exact_mod_cast (hlength j).1)

/-- The original real-power cell length is attainable at every scale over
a prime field. The proof combines the constant-radius construction with
short affine partitions, including missing points in each domain. -/
theorem corollary_7_11_all_scales_modular (N : Nat) [Fact N.Prime]
    (R : ModAP N) (A : Finset (ZMod N)) (phi : ZMod N → ZMod N) (alpha : Real)
    (hR : R.IsProper) (hstep : R.step != 0) (hl : 0 < R.length)
    (hα : 0 < alpha) (hαone : alpha ≤ 1)
    (hA : A ⊆ R.carrier) (hdensity : alpha * R.length ≤ A.card)
    (hfreiman : FreimanHom 8 A phi) :
    ∃ M : Nat, ∃ Q : Fin M → ModAP N,
      IsPartition (fun j ↦ (Q j).carrier) R.carrier ∧
      (∀ j, (Q j).step != 0 ∧ (Q j).IsProper ∧
        (R.length : Real) ^ cor711Exponent alpha 1 ≤ (Q j).length ∧
        LinearOn ((Q j).carrier.filter fun x ↦ x ∈ A) phi) := by
  have he := cor711_single_exponent_bounds hα hαone
  by_cases hlarge : 8 ≤ (R.length : Real) ^ cor711Exponent alpha 1
  · exact corollary_7_11_constant_modular N R A phi alpha hR hl hα hA hdensity
      hfreiman hlarge
  by_cases hlen : 64 ≤ R.length
  · exact eight_modular_affine_partition R A phi hR hstep hlen hfreiman (le_of_not_ge hlarge)
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
  exact short_modular_affine_partition R A phi hR hstep hfreiman hsmall
    (Real.rpow_le_self_of_one_le (by exact_mod_cast hl) (by linarith [he.2]))

end LeanProofs.GowersSzemeredi
