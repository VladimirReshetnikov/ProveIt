import DiophantineConsistency.AdaptiveGap85InverseOneStep
import DiophantineConsistency.AdaptiveGap85StrongNorm
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 12000000
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85InverseExample
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 AdaptiveGap85Literal ArithmeticSignedPairs
open AdaptiveDirectOrdinate86Context AdaptiveGap85InverseEntry AdaptiveGap85ForwardOrbitNoCross
open AdaptiveGap85StrongNorm ArithmeticAdaptiveStrongNorm2011 ArithmeticAdaptiveScaledNorms2011
attribute [local irreducible] CurrentMasks2011.radix
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def seed (p : Fin 4 → ℕ) : Fin 13 → V :=
  let b : V := p 0
  let q := 1+b
  ![1,1,1,1,1,1+b*(q*q)*(q*q-1),1,1,1,1,1,1,1]

theorem generic_shift_positive (p : Fin 4 → ℕ) (w : Fin 13 → V)
    (hw : ∀i,0<w i)
    (ht : let b := w 0*(p 0:V); let q := 1+b; let U := w 7*(q*q)
      b*U*(q*q-1)<w 5) : ∀i,0<AdaptiveGap85ShiftModel.shift p w i := by
  have h8 : 0<w 8+(w 0*(p 0:V))*(w 9+w 7*(w 9+w 10))*(w 7*((1+w 0*(p 0:V))*(1+w 0*(p 0:V))))*
      (w 6+(p 1:V)*(1+w 0*(p 0:V)))*(w 9+w 10)+(w 9+w 7*(w 9+w 10))*
      (w 7*((1+w 0*(p 0:V))*(1+w 0*(p 0:V))))*(w 6+(p 1:V)*(1+w 0*(p 0:V))) :=
    add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (hw 8) (by simp)) (by simp)
  intro i
  fin_cases i <;> dsimp [AdaptiveGap85ShiftModel.shift] <;> first
    | exact hw 0 | exact hw 1 | exact hw 3 | exact hw 4 | exact hw 6
    | exact hw 7 | exact hw 9 | exact hw 10 | exact hw 11
    | exact tsub_pos_iff_lt.mpr ht
    | apply add_pos_of_pos_of_nonneg (hw 2); simp
    | exact h8
    | apply add_pos_of_pos_of_nonneg (hw 12); simp

/-- The inverse-old crossing condition is arithmetically realizable at any
ports with first port at least two, but both example tuples are nonzeros. -/
theorem inverse_crossing_nonzero_example (p : Fin 4 → ℕ) (hb : (2:V)≤(p 0:V)) :
    ∃ v w : Fin 13 → V, (∀i,0<v i) ∧ (∀i,0<w i) ∧
      ¬(v 1+v 2<1+v 0*(p 0:V)) ∧
      w 1+w 2<1+w 0*(p 0:V) ∧ PositiveBiStep p v w ∧
      ¬InternalZero (expressionAt85 (fun j => (p j:ℤ))) v ∧
      ¬InternalZero (expressionAt85 (fun j => (p j:ℤ))) w := by
  let w : Fin 13 → V := seed p
  let v : Fin 13 → V := AdaptiveGap85ShiftModel.shift p w
  let b : V := p 0
  let q : V := 1+b
  have hb0 : 0<b := lt_of_lt_of_le (by simp : (0:V)<2) hb
  have hb1 : 1≤b := le_trans (by simp : (1:V)≤2) hb
  have hq : 0<q := by dsimp [q]; simp
  have hq1 : 1≤q := pos_iff_one_le.mp hq
  have hw : ∀i,0<w i := by
    intro i
    fin_cases i <;> dsimp [w,seed] <;> simp
  have ht : let b := w 0*(p 0:V); let q := 1+b; let U := w 7*(q*q)
      b*U*(q*q-1)<w 5 := by
    dsimp [w,seed]
    simpa only [one_mul,add_comm] using
      (lt_add_of_pos_right (b*(q*q)*(q*q-1)) (by simp : (0:V)<1))
  have hv : ∀i,0<v i := generic_shift_positive p w hw ht
  have hgap : w 1+w 2<1+w 0*(p 0:V) := by
    have h3 : (3:V)≤1+b := by simpa only [show (1:V)+2=3 by ring] using add_le_add (le_refl (1:V)) hb
    have hh : (1:V)+1<1+b := lt_of_lt_of_le (by norm_num : (1:V)+1<3) h3
    simpa [w,seed,b] using hh
  have hd : b≤b*(3*(q*q)) := by
    have hsq : 1≤q*q := one_le_mul hq1 hq1
    have hscale : 1≤3*(q*q) := one_le_mul (by simp) hsq
    exact le_mul_of_one_le_right (by simp) hscale
  have hnot : ¬(v 1+v 2<1+v 0*(p 0:V)) := by
    apply not_lt_of_ge
    have hh : 1+b≤1+b*(3*(q*q)) := add_le_add (le_refl _) hd
    have he : 1+b≤1+(1+b*3*(q*q)) := by
      calc
        _≤1+b*(3*(q*q)) := hh
        _≤1+(1+b*3*(q*q)) := by simp [mul_assoc]
    simpa [v,w,AdaptiveGap85ShiftModel.shift,seed,b,q,mul_assoc,add_assoc,show (1:V)+(1+1)=3 by norm_num] using he
  have hnz : ¬InternalZero (expressionAt85 (fun j => (p j:ℤ))) w := by
    intro hz
    have hs := expressionAt_strong_norm85 p w hz
    dsimp [StrongNorm,w,seed] at hs
    norm_num at hs
  have hnzv : ¬InternalZero (expressionAt85 (fun j => (p j:ℤ))) v := by
    intro hz
    have he := AdaptiveGap85ShiftModel.literal_preserved p w (le_of_lt ht)
    exact hnz ((equivalent_zero_iff he).1 hz)
  exact ⟨v,w,hv,hw,hnot,hgap,Or.inr ⟨Or.inl rfl,hw,hv⟩,hnzv,hnz⟩
private theorem nat_le_pow_general (r n : ℕ) (hn : 0<n) : r≤r^n := Nat.le_pow hn

/-- The explicit nonzero crossing examples exist at the literal current ports. -/
theorem current_inverse_crossing_nonzero_example :
    ∃ v w : Fin 13 → V, (∀i,0<v i) ∧ (∀i,0<w i) ∧
      ¬(v 1+v 2<1+v 0*(currentPorts 0:V)) ∧
      w 1+w 2<1+w 0*(currentPorts 0:V) ∧ PositiveBiStep currentPorts v w ∧
      ¬InternalZero (expressionAt85 (fun j => (currentPorts j:ℤ))) v ∧
      ¬InternalZero (expressionAt85 (fun j => (currentPorts j:ℤ))) w := by
  have hr : 3≤CurrentMasks2011.radix := by norm_num [CurrentMasks2011.radix]
  have hp : CurrentMasks2011.radix≤CurrentMasks2011.radix^2011 :=
    nat_le_pow_general _ _ (by decide)
  have hβ : 2≤CurrentMasks2011.beta := by
    unfold CurrentMasks2011.beta
    exact Nat.le_sub_of_add_le (by simpa only [show 2+1=3 by decide] using le_trans hr hp)
  have hport : (2:V)≤(currentPorts 0:V) := by
    have hn : 2≤currentPorts 0 := by change 2≤CurrentMasks2011.beta; exact hβ
    exact_mod_cast hn
  exact inverse_crossing_nonzero_example currentPorts hport
end DiophantineConsistency.AdaptiveGap85InverseExample
