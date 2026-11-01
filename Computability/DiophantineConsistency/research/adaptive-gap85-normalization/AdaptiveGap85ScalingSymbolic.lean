import DiophantineConsistency.ArithmeticPellSquaredSeed
import DiophantineConsistency.ArithmeticPellHalfIndex
import DiophantineConsistency.AdaptiveGap85Quotients
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 12000000
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85ScalingSymbolic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPellRecurrence ArithmeticPellSquaredSeed ArithmeticPellHalfIndex
open AdaptiveEquationSyntax2011 AdaptiveGap85Literal AdaptiveGap85Quotients ArithmeticAdaptiveScaledNorms2011
attribute [local irreducible] CurrentMasks2011.radix
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- For any beta, use J=2, q=1+2beta, Y=q³, X=2, eta=4,
zeta=2. The main and strong norms admit positive solutions without
Δ-divisibility of i. This does not assert the remaining 85 factors. -/
theorem partial_norms_without_scaling (beta : V) :
    let q := 1+2*beta
    let Y := q^3
    let a := 2*Y+Y
    let c := 4+Y*(4+2)
    let deltaA := delta a
    ∃ main f i : V, 0<main ∧ 0<f ∧ 0 < i ∧
      main*main=1+deltaA*c*c ∧ (i*c*c)*(i*c*c)+deltaA=deltaA*(f*f) ∧
      ¬deltaA∣i := by
  let q : V := 1+2*beta
  let Y : V := q^3
  let h : V := 4*beta^3+6*beta^2+3*beta
  let a : V := 2*Y+Y
  let c : V := 4+Y*(4+2)
  let t : V := 3*h+2
  let d : V := t*(a+3)
  have hY : Y=2*h+1 := by dsimp [Y,q,h]; ring
  have hB : a+2=2*t+1 := by dsimp [a,t]; rw [hY]; ring
  have hc : c=2*(a+2) := by dsimp [c,a]; ring
  have hd : delta a=2*d := by
    have hh : a+1=2*t := by dsimp [a,t]; rw [hY]; ring
    dsimp [d,delta]
    rw [hh]
    ring
  have hy2 : ycoord 2 a=c := by rw [y_two,hc]
  have hidx : (2*t+1)*2=c := by rw [←hB,hc]; ring
  obtain ⟨s,hs⟩ := odd_quotient t 2 a
  rw [hidx,hy2] at hs
  have hyc : ycoord c a=(2*t+1)*c+c*c*s := hs
  let i : V := delta a*s+d
  let f : V := xcoord c a
  let main : V := xcoord 2 a
  have hdi : 0<d := mul_pos (by dsimp [t]; simp) (by simp)
  have hdelta : 0<delta a := by rw [hd]; exact mul_pos (by simp) hdi
  have hdlt : d<delta a := by rw [hd]; simpa only [two_mul] using lt_add_of_pos_right d hdi
  have hcpos : 0<c := by dsimp [c]; simp
  have hmainpos : 0<main := by dsimp [main]; exact lt_of_lt_of_le (by simp : (0:V)<1) (one_le_x _ _)
  have hfpos : 0<f := by dsimp [f]; exact lt_of_lt_of_le (by simp : (0:V)<1) (one_le_x _ _)
  have hipos : 0 < i := by dsimp [i]; exact add_pos_of_nonneg_of_pos (by simp) hdi
  have hprod : i*c*c=delta a*ycoord c a := by
    dsimp [i]
    rw [hyc,hd,hc,←hB]
    dsimp [d]
    ring
  have hmain : main*main=1+delta a*c*c := by
    dsimp [main]
    have hh := norm (2:V) a
    rw [hy2] at hh
    exact hh
  have hstrong : (i*c*c)*(i*c*c)+delta a=delta a*(f*f) := by
    rw [hprod]
    dsimp [f]
    rw [norm]
    ring
  have hmod : i%(delta a)=d := by
    dsimp [i]
    rw [add_comm,mod_add_mul' _ _ hdelta,mod_eq_self_of_lt hdlt]
  have hnot : ¬delta a∣i := by
    intro hdiv
    have hz := mod_eq_zero_iff_dvd.mpr hdiv
    rw [hmod] at hz
    exact (ne_of_gt hdi) hz
  exact ⟨main,f,i,hmainpos,hfpos,hipos,hmain,hstrong,hnot⟩
/-- With X=2 and eta+zeta=6 the first Pell norm is impossible for
any positive Y, so the partial configuration cannot extend to a full zero. -/
theorem first_norm_fails (Y : V) (hY : 1≤Y) :
    ¬∃ first : V, first*first=1+(2*Y*Y)*(2*Y*Y+1)*(4+2)*(4+2) := by
  let Q : V := 2*Y*Y
  let L : V := 6*Q+2
  let H : V := 6*Q+3
  have hQ : 1≤Q := by
    have h := one_le_mul (by norm_num : (1:V)≤2) (one_le_mul hY hY)
    change 1≤2*Y*Y
    simpa only [mul_assoc] using h
  have hQeq : Q-1+1=Q := tsub_add_cancel_of_le hQ
  have hlo : L*L<1+Q*(Q+1)*(4+2)*(4+2) := by
    have hp : 0<12*(Q-1)+9 := by simp
    calc
      L*L<L*L+(12*(Q-1)+9) := lt_add_of_pos_right _ hp
      _=36*Q*Q+24*Q+12*(Q-1+1)+1 := by dsimp [L]; ring
      _=1+Q*(Q+1)*(4+2)*(4+2) := by rw [hQeq]; ring
  have hhi : 1+Q*(Q+1)*(4+2)*(4+2)<H*H := by
    calc
      _<(1+Q*(Q+1)*(4+2)*(4+2))+8 := lt_add_of_pos_right _ (by simp)
      _=H*H := by dsimp [H]; ring
  rintro ⟨first,hfirst⟩
  change first*first=1+Q*(Q+1)*(4+2)*(4+2) at hfirst
  have hlt : L<first := lt_of_mul_self_lt_mul_self₀ (by simp) (by rw [hfirst]; exact hlo)
  have hgt : first<H := lt_of_mul_self_lt_mul_self₀ (by simp) (by rw [hfirst]; exact hhi)
  have hle : H≤first := by
    have he : L+1=H := by dsimp [L,H]; ring
    rw [←he]
    exact lt_iff_succ_le.mp hlt
  exact (not_le_of_gt hgt) hle

/-- No positive full 85-zero, at any positive first port, has these X,eta,
zeta values, even though the two remaining partial norms can hold. -/
theorem no_full_zero_fixed_split (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hX : v 6=2) (he : v 9=4) (hz : v 10=2) :
    ¬InternalZero (expressionAt85 (fun j => (p j:ℤ))) v := by
  intro hzero
  obtain ⟨first,main,_,_,_,hnorm,_,_⟩ := expressionAt_quotients85 p v hb hv hzero
  have hnorm' : first*first=1+(2*v 7*v 7)*(2*v 7*v 7+1)*(4+2)*(4+2) := by
    rw [hX,he,hz] at hnorm
    calc
      first*first=1+((2*v 7)*(v 7*(4+2)))*(((2*v 7)*(v 7*(4+2)))+(4+2)) := hnorm
      _=1+(2*v 7*v 7)*(2*v 7*v 7+1)*(4+2)*(4+2) := by ring
  exact first_norm_fails (v 7) (pos_iff_one_le.mp (hv 7)) ⟨first,hnorm'⟩
private theorem nat_le_pow_general (r n : ℕ) (hn : 0<n) : r≤r^n := Nat.le_pow hn

/-- The partial failure of seed scaling occurs for J=2 at the literal fixed
ports in every IΣ₁ model; it cannot extend to a full 85-zero. -/
theorem current_port_partial_norms_without_scaling :
    let beta : V := currentPorts 0
    let q := 1+2*beta
    let Y := q^3
    let a := 2*Y+Y
    let c := 4+Y*(4+2)
    let deltaA := delta a
    5≤q ∧ ∃ main f i : V, 0<main ∧ 0<f ∧ 0 < i ∧
      main*main=1+deltaA*c*c ∧ (i*c*c)*(i*c*c)+deltaA=deltaA*(f*f) ∧
      ¬deltaA∣i := by
  let beta : V := currentPorts 0
  let q : V := 1+2*beta
  have hr : 3≤CurrentMasks2011.radix := by norm_num [CurrentMasks2011.radix]
  have hp : CurrentMasks2011.radix≤CurrentMasks2011.radix^2011 := nat_le_pow_general _ _ (by decide)
  have hβ : 2≤CurrentMasks2011.beta := by
    unfold CurrentMasks2011.beta
    exact Nat.le_sub_of_add_le (by simpa only [show 2+1=3 by decide] using le_trans hr hp)
  have hport : (2:V)≤beta := by
    change (2:V)≤(currentPorts 0:V)
    have hn : 2≤currentPorts 0 := by change 2≤CurrentMasks2011.beta; exact hβ
    exact_mod_cast hn
  have h4 : (4:V)≤2*beta := by
    have hh := mul_le_mul_of_nonneg_left hport (by simp : (0:V)≤2)
    simpa only [show (2:V)*2=4 by norm_num] using hh
  have hq : (5:V)≤q := by
    have hh := add_le_add (le_refl (1:V)) h4
    simpa only [show (1:V)+4=5 by ring] using hh
  exact ⟨hq,partial_norms_without_scaling beta⟩
end DiophantineConsistency.AdaptiveGap85ScalingSymbolic
