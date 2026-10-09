import GowersSzemeredi.Proofs16PopularCoherentAnchorRows

/-! Sixteen coordinate cells per progression direction make every
matched eight-term relation lift to an exact integer-coordinate relation.
This supplies finite rectification without intersecting unrelated translates. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical
open OAI.Erdos3.BohrProgression

def progressionCellCode {N : Nat} (P : CyclicCenteredGAP N) (u : P.Param) : Fin P.rank → Fin 16 :=
  fun i => ⟨(u i : Nat)/(P.radius i/8+1),by
    apply (Nat.div_lt_iff_lt_mul (by omega : 0 < P.radius i/8+1)).mpr
    have hu := (u i).isLt
    omega⟩

theorem progressionCellCode_diff_le {N : Nat} (P : CyclicCenteredGAP N) (u v : P.Param)
    (h : progressionCellCode P u = progressionCellCode P v) (i : Fin P.rank) :
    |(u i : Int)-(v i : Int)| ≤ (P.radius i/8 : Nat) := by
  have he := congrArg Fin.val (congrFun h i)
  change (u i : Nat)/(P.radius i/8+1) = (v i : Nat)/(P.radius i/8+1) at he
  have hu := Nat.mod_add_div (u i : Nat) (P.radius i/8+1)
  have hv := Nat.mod_add_div (v i : Nat) (P.radius i/8+1)
  have hru := Nat.mod_lt (u i : Nat) (by omega : 0 < P.radius i/8+1)
  have hrv := Nat.mod_lt (v i : Nat) (by omega : 0 < P.radius i/8+1)
  rw [he] at hu
  rw [abs_le]
  constructor <;> omega

theorem progression_cell_relation_lifts {N : Nat} [NeZero N]
    (P : CyclicCenteredGAP N) (hP : P.Proper) (u v : Fin 8 → P.Param)
    (hcell : ∀ j, progressionCellCode P (u j) = progressionCellCode P (v j))
    (he : ∑ j, P.eval (u j) = ∑ j, P.eval (v j)) :
    ∀ i, (∑ j, ((u j i : Nat) : Int)) = ∑ j, ((v j i : Nat) : Int) := by
  let d : Fin P.rank → Int := fun i => ∑ j, (((u j i : Nat) : Int)-((v j i : Nat) : Int))
  have hd (i : Fin P.rank) : |d i| ≤ (P.radius i : Int) := by
    calc |d i| ≤ ∑ j : Fin 8, |((u j i : Nat) : Int)-((v j i : Nat) : Int)| :=
           Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin 8, ((P.radius i/8 : Nat) : Int) :=
           Finset.sum_le_sum fun j _ => progressionCellCode_diff_le P (u j) (v j) (hcell j) i
      _ ≤ _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; omega
  let w : P.Param := fun i => ⟨(d i+(P.radius i : Int)).toNat,by
    have hb := abs_le.mp (hd i)
    omega⟩
  let o : P.Param := fun i => ⟨P.radius i,by omega⟩
  have hw (i : Fin P.rank) : P.coeff w i = d i := by
    have hb := abs_le.mp (hd i)
    change ((d i+(P.radius i : Int)).toNat : Int)-(P.radius i : Int) = d i
    rw [Int.toNat_of_nonneg (by omega)]
    ring
  have ho (i : Fin P.rank) : P.coeff o i = 0 := by simp [CyclicCenteredGAP.coeff,o]
  have hsum : ∑ i, (d i : ZMod N)*P.step i = 0 := by
    have hdiff : (∑ j : Fin 8, P.eval (u j))-(∑ j : Fin 8, P.eval (v j)) =
        ∑ i, (d i : ZMod N)*P.step i := by
      simp only [CyclicCenteredGAP.eval,CyclicCenteredGAP.coeff,d,Int.cast_sum,Int.cast_sub,Int.cast_natCast]
      rw [← Finset.sum_sub_distrib]
      simp_rw [← Finset.sum_sub_distrib,← sub_mul,sub_sub_sub_cancel_right]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_mul]
    rw [he,sub_self] at hdiff
    exact hdiff.symm
  have heval : P.eval w = P.eval o := by
    simp only [CyclicCenteredGAP.eval,hw,ho,Int.cast_zero,zero_mul,Finset.sum_const_zero]
    exact hsum
  have hwo := hP heval
  intro i
  have hz : d i = 0 := by rw [← hw i,hwo,ho]
  exact sub_eq_zero.mp (by simpa only [d,Finset.sum_sub_distrib] using hz)

end LeanProofs.GowersSzemeredi
