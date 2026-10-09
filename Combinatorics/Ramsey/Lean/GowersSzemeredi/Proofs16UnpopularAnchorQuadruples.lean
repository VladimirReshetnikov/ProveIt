import GowersSzemeredi.Proofs16UniformAnchorIndexDensity

/-! Quadruples whose shift has few supported column pairs have small
mass. Fixing the shift leaves exactly the two unshifted anchor bases. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def columnShiftBases {N : Nat} (P : Finset (ZMod N)) (a : ZMod N) : Finset (ZMod N) :=
  P.filter fun z => z+a ∈ P

def unpopularAnchorQuadruples {N : Nat} [NeZero N] (P : Finset (ZMod N)) (t : Real) :
    Finset (Fin 4 → ZMod N) :=
  (supportedAnchorQuadruples P).filter fun q => ((columnShiftBases P (q 0-q 1)).card : Real) < t*N

theorem supported_anchor_shift_fiber_card_le {N : Nat} [NeZero N]
    (P : Finset (ZMod N)) (E : Finset (Fin 4 → ZMod N)) (a : ZMod N)
    (hE : E ⊆ supportedAnchorQuadruples P) (hshift : ∀ q ∈ E, q 0-q 1 = a) :
    E.card ≤ (columnShiftBases P a).card^2 := by
  have hc : E.card ≤ ((columnShiftBases P a) ×ˢ (columnShiftBases P a)).card := by
    apply Finset.card_le_card_of_injOn (fun q : Fin 4 → ZMod N => (q 1,q 3))
    · intro q hq
      obtain ⟨hqP,hadd⟩ := Finset.mem_filter.mp (hE hq)
      have hP := Fintype.mem_piFinset.mp hqP
      have ha := hshift q hq
      have h0 : q 1+a = q 0 := by linear_combination -ha
      have h2 : q 3+a = q 2 := by linear_combination hadd-ha
      exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨hP 1,by rw [h0]; exact hP 0⟩,
        Finset.mem_filter.mpr ⟨hP 3,by rw [h2]; exact hP 2⟩⟩
    · intro q hq v hv he
      have h1 := congrArg Prod.fst he
      have h3 := congrArg Prod.snd he
      have hqshift := hshift q hq
      have hvshift := hshift v hv
      have hqadd := (Finset.mem_filter.mp (hE hq)).2
      have hvadd := (Finset.mem_filter.mp (hE hv)).2
      funext i
      fin_cases i
      · change q 0 = v 0
        linear_combination hqshift-hvshift+h1
      · exact h1
      · change q 2 = v 2
        linear_combination hqshift-hvshift-hqadd+hvadd+h3
      · exact h3
  simpa only [Finset.card_product,pow_two] using hc

theorem unpopular_anchor_quadruples_card_le {N : Nat} [NeZero N]
    (P : Finset (ZMod N)) {t : Real} :
    ((unpopularAnchorQuadruples P t).card : Real) ≤ t^2*(N : Real)^3 := by
  let E := unpopularAnchorQuadruples P t
  have hf (a : ZMod N) : ((E.filter fun q => q 0-q 1 = a).card : Real) ≤ t^2*(N : Real)^2 := by
    by_cases ha : ((columnShiftBases P a).card : Real) < t*N
    · have hc : ((E.filter fun q => q 0-q 1 = a).card : Real) ≤ ((columnShiftBases P a).card : Real)^2 := by
        exact_mod_cast supported_anchor_shift_fiber_card_le P (E.filter fun q => q 0-q 1 = a) a
          (fun q hq => (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1)
          (fun q hq => (Finset.mem_filter.mp hq).2)
      have hs := pow_le_pow_left₀ (Nat.cast_nonneg (columnShiftBases P a).card) ha.le 2
      exact hc.trans (by simpa only [mul_pow] using hs)
    · have he : (E.filter fun q => q 0-q 1 = a) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro q hq
        obtain ⟨hq,hqa⟩ := Finset.mem_filter.mp hq
        have hb := (Finset.mem_filter.mp hq).2
        exact ha (by simpa only [hqa] using hb)
      rw [he,Finset.card_empty,Nat.cast_zero]
      positivity
  have hsum : (∑ a : ZMod N, ((E.filter fun q => q 0-q 1 = a).card : Real)) = E.card := by
    have h := Finset.sum_card_fiberwise_eq_card_filter E Finset.univ (fun q => q 0-q 1)
    simp only [Finset.mem_univ,Finset.filter_true] at h
    exact_mod_cast h
  calc (E.card : Real) = ∑ a : ZMod N, ((E.filter fun q => q 0-q 1 = a).card : Real) := hsum.symm
    _ ≤ ∑ _a : ZMod N, t^2*(N : Real)^2 := Finset.sum_le_sum fun a _ => hf a
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,ZMod.card,nsmul_eq_mul]; ring

end LeanProofs.GowersSzemeredi
