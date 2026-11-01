import DiophantineConsistency.AdaptiveGap85BalanceNoCross
import DiophantineConsistency.AdaptiveGap85JointResidue
import DiophantineConsistency.ArithmeticAdaptiveScaledNorms2011
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 12000000
set_option maxRecDepth 100000
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85ForwardOrbitNoCross
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveGap85JointResidue AdaptiveGap85BalanceNoCross ArithmeticAdaptiveScaledNorms2011
attribute [local irreducible] CurrentMasks2011.radix
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def PositiveStep (p : Fin 4 → ℕ) (v w : Fin 13 → V) : Prop :=
  LiteralStep p v w ∧ (∀i,0<v i) ∧ (∀i,0<w i)

theorem third_score_nondecreasing (p : Fin 4 → ℕ) (v : Fin 13 → V) (s : V)
    (hb : 2≤v 0*(p 0:V)) (hX : 0<v 6)
    (hF : let b := v 0*(p 0:V); let q := 1+b; let A := v 6+(p 1:V)*q;
      let U := v 7*(q*q); let c := v 9+v 7*(v 9+v 10); A*(c*U*s)≤v 1) :
    v 1+v 2≤AdaptiveGap85ThirdModel.shift p v s 1+AdaptiveGap85ThirdModel.shift p v s 2 := by
  let b : V := v 0*(p 0:V)
  let q : V := 1+b
  let A : V := v 6+(p 1:V)*q
  let U : V := v 7*(q*q)
  let c : V := v 9+v 7*(v 9+v 10)
  let d := c*U*s
  change 2≤b at hb
  change A*d≤v 1 at hF
  have hA : 1≤A := pos_iff_one_le.mp (add_pos_of_pos_of_nonneg hX (by simp))
  have hBA : 1≤b*A := le_trans (by simp : (1:V)≤2) (le_trans
    (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hA (by simp : (0:V)≤2))
    (mul_le_mul_of_nonneg_right hb (by simp)))
  have hba : (b*A-1)+1=b*A := tsub_add_cancel_of_le hBA
  have hf : (v 1-A*d)+A*d=v 1 := tsub_add_cancel_of_le hF
  have hd : d≤A*d := le_mul_of_one_le_left (by simp) hA
  have h2 : 2*A≤b*A := mul_le_mul_of_nonneg_right hb (by simp)
  have hneed : A*d+d≤b*A*d := calc
    _≤A*d+A*d := add_le_add (le_refl _) hd
    _=(2*A)*d := by ring
    _≤(b*A)*d := mul_le_mul_of_nonneg_right h2 (by simp)
  have hinc : A*d≤(b*A-1)*d := by
    apply (add_le_add_iff_right d).mp
    calc
      A*d+d≤b*A*d := hneed
      _=((b*A-1)+1)*d := by rw [hba]
      _=(b*A-1)*d+d := by ring
  change v 1+v 2≤(v 1-A*d)+(v 2+(b*A-1)*d)
  calc
    _ = ((v 1-A*d)+A*d)+v 2 := by rw [hf]
    _ = (v 1-A*d)+(A*d+v 2) := by ring
    _ ≤ (v 1-A*d)+((b*A-1)*d+v 2) := _root_.add_le_add (le_refl _) (_root_.add_le_add hinc (le_refl _))
    _ = _ := by ring

theorem step_gap_backward (p : Fin 4 → ℕ) (v w : Fin 13 → V)
    (hb : 2≤v 0*(p 0:V)) (h : PositiveStep p v w)
    (hg : w 1+w 2<1+w 0*(p 0:V)) :
    v 1+v 2<1+v 0*(p 0:V) := by
  obtain ⟨hstep,hv,hw⟩ := h
  have h0 := (literal_step_joint p v w hstep).1
  have hg' : w 1+w 2<1+v 0*(p 0:V) := by simpa only [h0] using hg
  rcases hstep with he | ⟨t,hC,he⟩ | ⟨s,hBA,hF,he⟩
  · subst w
    have hs : v 1+v 2≤AdaptiveGap85ShiftModel.shift p v 1+AdaptiveGap85ShiftModel.shift p v 2 := by
      dsimp [AdaptiveGap85ShiftModel.shift]
      simp
    exact lt_of_le_of_lt hs hg'
  · subst w
    have hbp : 0<v 0*(p 0:V) := lt_of_lt_of_le (by simp : (0:V)<2) hb
    have ht := gap_forces_t_zero p v t hbp (hv 1) hg'
    subst t
    simpa [AdaptiveGap85BalanceModel.shift] using hg'
  · subst w
    exact lt_of_le_of_lt (third_score_nondecreasing p v s hb (hv 6) hF) hg'

theorem positive_orbit_first (p : Fin 4 → ℕ) (v w : Fin 13 → V)
    (h : Relation.ReflTransGen (PositiveStep p) v w) : w 0=v 0 := by
  induction h with
  | refl => rfl
  | @tail x y hprev hstep ih => exact ((literal_step_joint p x y hstep.1).1).trans ih

/-- No finite sequence of the three forward shifts through positive tuples
can enter the reverse gap when b≥2. This does not cover inverse shifts. -/
theorem positive_forward_orbit_no_cross (p : Fin 4 → ℕ) (v w : Fin 13 → V)
    (hb : 2≤v 0*(p 0:V))
    (h : Relation.ReflTransGen (PositiveStep p) v w)
    (hg : w 1+w 2<1+w 0*(p 0:V)) :
    v 1+v 2<1+v 0*(p 0:V) := by
  induction h with
  | refl => exact hg
  | @tail x y hprev hstep ih =>
    have hx0 : x 0=v 0 := positive_orbit_first p v x hprev
    have hbx : 2≤x 0*(p 0:V) := by rw [hx0]; exact hb
    exact ih (step_gap_backward p x y hbx hstep hg)
private theorem nat_le_pow_general (r n : ℕ) (hn : 0<n) : r≤r^n := Nat.le_pow hn

/-- The no-cross result applies to the actual ZFC fixed ports. -/
theorem current_positive_forward_orbit_no_cross (v w : Fin 13 → V)
    (hv0 : 0<v 0)
    (h : Relation.ReflTransGen (PositiveStep currentPorts) v w)
    (hg : w 1+w 2<1+w 0*(currentPorts 0:V)) :
    v 1+v 2<1+v 0*(currentPorts 0:V) := by
  have hr : 3≤CurrentMasks2011.radix := by norm_num [CurrentMasks2011.radix]
  have hp : CurrentMasks2011.radix≤CurrentMasks2011.radix^2011 :=
    nat_le_pow_general _ _ (by decide)
  have hβ : 2≤CurrentMasks2011.beta := by
    unfold CurrentMasks2011.beta
    exact Nat.le_sub_of_add_le (by simpa only [show 2+1=3 by decide] using le_trans hr hp)
  have hport : (2:V)≤(currentPorts 0:V) := by
    have hn : 2≤currentPorts 0 := by change 2≤CurrentMasks2011.beta; exact hβ
    exact_mod_cast hn
  have hj : 1≤v 0 := pos_iff_one_le.mp hv0
  have hb : 2≤v 0*(currentPorts 0:V) := by
    have hh : (currentPorts 0:V)≤v 0*(currentPorts 0:V) := by
      simpa only [one_mul] using Arithmetic.mul_le_mul_right (a:=(currentPorts 0:V)) hj
    exact le_trans hport hh
  exact positive_forward_orbit_no_cross currentPorts v w hb h hg
end DiophantineConsistency.AdaptiveGap85ForwardOrbitNoCross
