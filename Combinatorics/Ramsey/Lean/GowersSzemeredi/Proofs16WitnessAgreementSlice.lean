import GowersSzemeredi.Proofs16SharedWitnessZeros
import GowersSzemeredi.Proofs16IndexPatternAveraging
import GowersSzemeredi.Proofs16BohrLowerBound

/-! Freeze three witness coordinates and one frequency-cell signature.
Differences of the remaining coordinates give exact original-map agreement. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem witness_agreement_slice {N Q : Nat} [NeZero N] [NeZero Q]
    (B T S : Finset (ZMod N)) (W : Finset (Fin 4 → ZMod N))
    (f L : ZMod N → ZMod N) {rho s : Real}
    (hrho : 0 ≤ rho) (hQ : 1 ≤ s*Q)
    (hdom : bohr S s ⊆ bohr T rho)
    (hL : IsFreimanLinearOn (bohr T rho) L) (hL0 : L 0 = 0)
    (hW : ∀ w ∈ W, (∀ i, w i ∈ B) ∧ fourSum w ∈ bohr T rho ∧ L (fourSum w) = repFourValue f w) :
    ∃ D ⊆ B, W.card ≤ N^3*Q^S.card*D.card ∧
      ∀ a ∈ D, ∀ b ∈ D, a-b ∈ bohr S s ∧ L (a-b) = f a-f b := by
  let label (w : Fin 4 → ZMod N) : (Fin 3 → ZMod N) × (S → Fin Q) :=
    (![w 1,w 2,w 3],fun z => dirichletCell Q (z.1*w 0))
  obtain ⟨c,hc⟩ := exists_large_label_fiber W label
  let F := W.filter (fun w => label w = c)
  let D := F.image (fun w => w 0)
  have hlabel : ∀ w ∈ F, label w = c := fun w hw => (Finset.mem_filter.mp hw).2
  have htail : ∀ w ∈ F, ∀ v ∈ F, w 1 = v 1 ∧ w 2 = v 2 ∧ w 3 = v 3 := by
    intro w hw v hv
    have h := congrArg Prod.fst ((hlabel w hw).trans (hlabel v hv).symm)
    exact ⟨congrFun h 0,congrFun h 1,congrFun h 2⟩
  have hcard : D.card = F.card := by
    apply Finset.card_image_of_injOn
    intro w hw v hv he
    have ht := htail w hw v hv
    funext i
    fin_cases i
    · exact he
    · exact ht.1
    · exact ht.2.1
    · exact ht.2.2
  refine ⟨D,?_,?_,?_⟩
  · intro a ha
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp ha
    exact (hW w (Finset.mem_filter.mp hw).1).1 0
  · rw [hcard]
    convert hc using 1
    simp [F,Fintype.card_prod,ZMod.card]
    left
    congr 1
    ext w
    simp
  · intro a ha b hb
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hb
    have ht := htail w hw v hv
    have hdiff : w 0-v 0 ∈ bohr S s := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      intro z hz
      have hsig := congrArg Prod.snd ((hlabel w hw).trans (hlabel v hv).symm)
      have hcell : dirichletCell Q (z*w 0) = dirichletCell Q (z*v 0) := congrFun hsig ⟨z,hz⟩
      have hd : (centeredAbs (z*w 0-z*v 0) : Real)*Q < N := by
        exact_mod_cast dirichletCell_close hcell
      have hq : (0 : Real) < Q := by exact_mod_cast NeZero.pos Q
      have hN : (0 : Real) ≤ N := Nat.cast_nonneg _
      rw [mul_sub]
      have hu : (N : Real) ≤ (s*N)*Q := by nlinarith [mul_le_mul_of_nonneg_right hQ hN]
      exact (le_of_lt ((mul_lt_mul_iff_left₀ hq).mp (by simpa only [mul_comm] using hd.trans_le hu)))
    refine ⟨hdiff,?_⟩
    have hw' := hW w (Finset.mem_filter.mp hw).1
    have hv' := hW v (Finset.mem_filter.mp hv).1
    have he : fourSum w+0 = fourSum v+(w 0-v 0) := by
      dsimp [fourSum]
      rw [ht.1,ht.2.1,ht.2.2]
      ring
    have hl := hL (fourSum w) 0 (fourSum v) (w 0-v 0)
      hw'.2.1 (zero_mem_bohr T hrho) hv'.2.1 (hdom hdiff) he
    rw [hL0,hw'.2.2,hv'.2.2] at hl
    dsimp [repFourValue] at hl
    rw [ht.1,ht.2.1,ht.2.2] at hl
    linear_combination -hl

/-- A uniform spectral rank bound turns witness mass into a dense
agreement slice. -/
theorem witness_agreement_slice_density {N Q R : Nat} [NeZero N] [NeZero Q]
    (B T S : Finset (ZMod N)) (W : Finset (Fin 4 → ZMod N))
    (f L : ZMod N → ZMod N) {rho s c : Real}
    (hrho : 0 ≤ rho) (hQ : 1 ≤ s*Q) (hS : S.card ≤ R)
    (hdom : bohr S s ⊆ bohr T rho)
    (hL : IsFreimanLinearOn (bohr T rho) L) (hL0 : L 0 = 0)
    (hW : ∀ w ∈ W, (∀ i, w i ∈ B) ∧ fourSum w ∈ bohr T rho ∧ L (fourSum w) = repFourValue f w)
    (hcount : c*(N : Real)^4 ≤ W.card) :
    ∃ D ⊆ B, (c/(Q : Real)^R)*N ≤ (D.card : Real) ∧
      ∀ a ∈ D, ∀ b ∈ D, a-b ∈ bohr S s ∧ L (a-b) = f a-f b := by
  obtain ⟨D,hDB,hD,hagree⟩ := witness_agreement_slice B T S W f L hrho hQ hdom hL hL0 hW
  refine ⟨D,hDB,?_,hagree⟩
  have hpow : Q^S.card ≤ Q^R := Nat.pow_le_pow_right (NeZero.pos Q) hS
  have hD' : W.card ≤ N^3*Q^R*D.card := hD.trans
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hpow))
  have hm : c*(N : Real)^4 ≤ (N : Real)^3*(Q : Real)^R*D.card :=
    hcount.trans (by exact_mod_cast hD')
  have hn : (0 : Real) < (N : Real)^3 := by exact_mod_cast pow_pos (NeZero.pos N) 3
  have hq : (0 : Real) < (Q : Real)^R := by exact_mod_cast pow_pos (NeZero.pos Q) R
  have hc : c*N ≤ (Q : Real)^R*D.card := by
    apply (mul_le_mul_iff_left₀ hn).mp
    nlinarith only [hm]
  rw [div_mul_eq_mul_div]
  exact (div_le_iff₀ hq).mpr (by simpa only [mul_comm] using hc)

end LeanProofs.GowersSzemeredi
