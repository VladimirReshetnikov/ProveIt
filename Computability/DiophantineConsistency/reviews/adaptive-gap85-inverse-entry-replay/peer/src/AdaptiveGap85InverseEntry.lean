import DiophantineConsistency.AdaptiveGap85ForwardOrbitNoCross
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 12000000
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85InverseEntry
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveGap85JointResidue AdaptiveGap85ForwardOrbitNoCross
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A forward balance move whose positive source is already in the gap can
only be defined with amount zero. -/
theorem gap_source_balance_zero (p : Fin 4 → ℕ) (w : Fin 13 → V) (t : V)
    (hb : 0<w 0*(p 0:V))
    (hg : w 1+w 2<1+w 0*(p 0:V))
    (hC : let b := w 0*(p 0:V); let q := 1+b; q*b*t≤w 2) : t=0 := by
  let b : V := w 0*(p 0:V)
  let q : V := 1+b
  have hq : 0<q := by dsimp [q]; simp
  have hb1 : 1≤b := pos_iff_one_le.mp hb
  have hc : w 2<q := lt_of_le_of_lt (by simp : w 2≤w 1+w 2) hg
  change q*b*t≤w 2 at hC
  by_contra hn
  have ht1 : 1≤t := pos_iff_one_le.mp (pos_iff_ne_zero.mpr hn)
  have hbt : 1≤b*t := one_le_mul hb1 ht1
  have hqbt : q≤q*b*t := by
    have hh := le_mul_of_one_le_right (by simp : (0:V)≤q) hbt
    simpa only [mul_assoc] using hh
  exact (not_le_of_gt hc) (le_trans hqbt hC)

/-- A forward third move whose positive source is in the gap can only have
amount zero: its F decrement is at least q whenever the amount is positive. -/
theorem gap_source_third_zero (p : Fin 4 → ℕ) (w : Fin 13 → V) (s : V)
    (hw : ∀i,0<w i)
    (hg : w 1+w 2<1+w 0*(p 0:V))
    (hF : let b := w 0*(p 0:V); let q := 1+b; let A := w 6+(p 1:V)*q;
      let U := w 7*(q*q); let c := w 9+w 7*(w 9+w 10); A*(c*U*s)≤w 1) : s=0 := by
  let b : V := w 0*(p 0:V)
  let q : V := 1+b
  let A : V := w 6+(p 1:V)*q
  let U : V := w 7*(q*q)
  let c : V := w 9+w 7*(w 9+w 10)
  have hq : 0<q := by dsimp [q]; simp
  have hq1 : 1≤q := pos_iff_one_le.mp hq
  have hA1 : 1≤A := pos_iff_one_le.mp (add_pos_of_pos_of_nonneg (hw 6) (by simp))
  have hY1 : 1≤w 7 := pos_iff_one_le.mp (hw 7)
  have hcpos : 0<c := by
    dsimp [c]
    exact add_pos (hw 9) (mul_pos (hw 7) (add_pos (hw 9) (hw 10)))
  have hc1 : 1≤c := pos_iff_one_le.mp hcpos
  have hf : w 1<q := lt_of_le_of_lt (by simp : w 1≤w 1+w 2) hg
  change A*(c*U*s)≤w 1 at hF
  by_contra hn
  have hs1 : 1≤s := pos_iff_one_le.mp (pos_iff_ne_zero.mpr hn)
  have hlower : q≤A*(c*U*s) := calc
    q≤q*q := le_mul_of_one_le_right (by simp) hq1
    _≤U := le_mul_of_one_le_left (by simp) hY1
    _≤c*U := le_mul_of_one_le_left (by simp) hc1
    _≤c*U*s := le_mul_of_one_le_right (by simp) hs1
    _≤A*(c*U*s) := le_mul_of_one_le_left (by simp) hA1
  exact (not_le_of_gt hf) (le_trans hlower hF)

def PositiveBiStep (p : Fin 4 → ℕ) (v w : Fin 13 → V) : Prop :=
  PositiveStep p v w ∨ PositiveStep p w v

/-- If an allowed forward-or-inverse step first enters the positive gap at
b≥2, it is an inverse old shift. No such step is asserted to exist. -/
theorem entry_requires_inverse_old (p : Fin 4 → ℕ) (v w : Fin 13 → V)
    (hb : 2≤v 0*(p 0:V)) (h : PositiveBiStep p v w)
    (hnot : ¬v 1+v 2<1+v 0*(p 0:V))
    (hg : w 1+w 2<1+w 0*(p 0:V)) :
    v=AdaptiveGap85ShiftModel.shift p w := by
  rcases h with hfwd | hinv
  · exact False.elim (hnot (step_gap_backward p v w hb hfwd hg))
  · obtain ⟨hstep,hw,hv⟩ := hinv
    have h0 := (literal_step_joint p w v hstep).1
    have hbw : 2≤w 0*(p 0:V) := by rw [←h0]; exact hb
    have hbpos : 0<w 0*(p 0:V) := lt_of_lt_of_le (by simp : (0:V)<2) hbw
    rcases hstep with he | ⟨t,hC,he⟩ | ⟨s,hBA,hF,he⟩
    · exact he
    · have ht := gap_source_balance_zero p w t hbpos hg hC
      subst t
      have h1 : v 1=w 1 := by rw [he]; simp [AdaptiveGap85BalanceModel.shift]
      have h2 : v 2=w 2 := by rw [he]; simp [AdaptiveGap85BalanceModel.shift]
      exact False.elim (hnot (by rw [h0,h1,h2]; exact hg))
    · have hs := gap_source_third_zero p w s hw hg hF
      subst s
      have h1 : v 1=w 1 := by rw [he]; simp [AdaptiveGap85ThirdModel.shift]
      have h2 : v 2=w 2 := by rw [he]; simp [AdaptiveGap85ThirdModel.shift]
      exact False.elim (hnot (by rw [h0,h1,h2]; exact hg))
end DiophantineConsistency.AdaptiveGap85InverseEntry
