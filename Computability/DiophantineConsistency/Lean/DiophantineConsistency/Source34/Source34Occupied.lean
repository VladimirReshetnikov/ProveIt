import DiophantineConsistency.Source34.Source34Selected
import DiophantineConsistency.Mixed121.Mixed121Occupied

/-! # The origin tile is selected, and the anchors are occupied, at source34

`Mixed121Occupied` at the source34 tuple. The Start tile
`Mixed121Occupied.origin` (row `0`) is shared. Re-declared because they read
the source34 copy positions (`Source34Band.extraPosN`, `Source34Band.copyDigit`):
`Occupied`, `origin_selected`, `selected_origin_occupied`, `anchors_occupied`
and the chain link `graph_selected_occupied`.

Selector `0` of a clause band reads the native cell `0`, and `dig C 0 = 1`, so
the decoded selection at the clean target is the Start tile. Each of the 44
copy and anchor cells of `C` (now the stride-two tracks and the anchors) then
equals the Start tile's radix-four digit; the copy indices `40..43` still sit
at the anchors `1095, 1096, 2195, 3296`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
noncomputable section
namespace Source34Occupied
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open ArithmeticBinaryCarry ArithmeticRepunit ArithmeticWindowDigits ArithmeticCyclicWord
open Mixed121Occupied (origin)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The copy and anchor cells of `C` repeat the Start tile's digits. -/
def Occupied (C : V) : Prop :=
  ∀ j < 44, dig 121 C (Source34Band.extraPosN j : V) =
    (Mixed121Digits.digit (Compact943Data.row origin) j : V)

theorem origin_selected (n C : V) (T : ℕ) (ht : (T:V)<n) (h0 : dig 121 C 0=1)
    (hdecode : Source34Selected.Decoded n C T) :
    CompactSelectorSum.Selected (Mixed121Band.selDigit n C (T:V) T) origin ∧
      ∀ j < 44, Source34Band.copyDigit n C (T:V) T j =
        (Mixed121Digits.digit (Compact943Data.row origin) j : V) := by
  have hsel0 : Mixed121Band.selDigit n C (T:V) T origin = 1 := by
    unfold Mixed121Band.selDigit
    rw [Mixed121Selected.source_cell n T origin.val ht (Nat.zero_le _)]
    simpa [origin] using h0
  rcases hdecode with ⟨hz, _⟩ | ⟨i, hi, hcopy⟩
  · have := hz origin
    rw [hsel0] at this
    exact absurd this _root_.one_ne_zero
  · have hio : i = origin := by
      by_contra hne
      have := hi.2 origin (Ne.symm hne)
      rw [hsel0] at this
      exact _root_.one_ne_zero this
    subst hio
    exact ⟨hi, hcopy⟩

theorem selected_origin_occupied (n C : V) (T : ℕ) (ht : (T:V)<n) (hT : 3296≤T)
    (h0 : dig 121 C 0=1) (hdecode : Source34Selected.Decoded n C T) : Occupied C := by
  have hcopy := (origin_selected n C T ht h0 hdecode).2
  intro j hj
  have h := hcopy j hj
  unfold Source34Band.copyDigit at h
  have hmem := Source34Selected.extraPosN_mem j hj
  have hall := Source34Single.extra_allowed _ hmem
  have hle : Source34Band.extraPosN j ≤ T := by
    unfold Source34Single.Allowed at hall
    omega
  rw [Mixed121Selected.source_cell n T _ ht hle] at h
  exact h

/-- The anchors: the copy indices `40..43` sit at cells `1095, 1096, 2195,
3296`, and the Start tile's anchor digits are `1`. -/
theorem anchors_occupied (C : V) (h : Occupied C) :
    dig 121 C 1095 = 1 ∧ dig 121 C 1096 = 1 ∧ dig 121 C 2195 = 1 ∧ dig 121 C 3296 = 1 := by
  have e (j : ℕ) (hj : j < 44) (hj40 : 40 ≤ j) (c : ℕ) (hc : Source34Band.extraPosN j = c) :
      dig 121 C (c:V) = 1 := by
    have hd : Mixed121Digits.digit (Compact943Data.row origin) j = 1 := by
      unfold Mixed121Digits.digit
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    have := h j hj
    rw [hc, hd, Nat.cast_one] at this
    exact this
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [Nat.cast_ofNat] using e 40 (by norm_num) le_rfl 1095 rfl
  · simpa only [Nat.cast_ofNat] using e 41 (by norm_num) (by norm_num) 1096 rfl
  · simpa only [Nat.cast_ofNat] using e 42 (by norm_num) (by norm_num) 2195 rfl
  · simpa only [Nat.cast_ofNat] using e 43 (by norm_num) (by norm_num) 3296 rfl

attribute [local irreducible] Compact943Data.rows Mixed121Flatten.selectors Mixed121Flatten.copies
attribute [local irreducible] Source34Ports.betaNat Source34Ports.lowNat Source34Ports.highNat
  Source34Kernel.paramKernel Mixed121Kernel.rho

theorem graph_selected_occupied (v : Fin 12 → V) (hv : ∀ j, 0 < v j)
    (hz : CompactLeafFacts.LeafFacts Source34Ports.ports v) :
    let p := Source34Ports.ports
    let q : V := 1+v 0*(p 0:V)
    let C : V := q-v 1-v 2
    ∃ N : V, 0<N ∧ q=Exp.exp ((121*8801)*N) ∧ v 0=rep (121*8801) N ∧ Occupied C := by
  obtain ⟨N,t,hN,hq,hJ,hband⟩ := Source34Selected.graph_selected_decode v hv hz
  obtain ⟨N',w',hN',hq',hJ',hle',hw',hv5',hcarry',h0,hzero,hbool⟩ :=
    Source34Clean.graph_support_carry v hv hz
  dsimp only at *
  have hNN : N'=N := by
    apply mul_left_cancel₀ (by norm_num : ((121*8801):V)≠0)
    exact exp_inj (hq'.symm.trans hq)
  subst N'
  have hnge : (8801:V)≤8801*N := by
    have h := mul_le_mul_of_nonneg_left (pos_iff_one_le.mp hN) (by norm_num : (0:V)≤8801)
    simpa only [mul_one] using h
  have ht₁ : ((4393:ℕ):V)<8801*N := by
    simpa using lt_of_lt_of_le (by norm_num : (4393:V)<8801) hnge
  have ht₂ : ((5495:ℕ):V)<8801*N := by
    simpa using lt_of_lt_of_le (by norm_num : (5495:V)<8801) hnge
  refine ⟨N,hN,hq,hJ,?_⟩
  rcases hband with ⟨_, hd⟩ | ⟨_, hd⟩
  · exact selected_origin_occupied _ _ 4393 ht₁ (by norm_num) h0 hd
  · exact selected_origin_occupied _ _ 5495 ht₂ (by norm_num) h0 hd
end Source34Occupied
#print axioms Source34Occupied.origin_selected
#print axioms Source34Occupied.selected_origin_occupied
#print axioms Source34Occupied.anchors_occupied
#print axioms Source34Occupied.graph_selected_occupied
