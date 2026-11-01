import DiophantineConsistency.AdaptiveGap85TwoStepFullZero
import DiophantineConsistency.AdaptiveGap85DoubleThreshold
import DiophantineConsistency.AdaptiveGap85FirstDivisibility
import DiophantineConsistency.AdaptiveGap85StrongNorm
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 12000000
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85SeededTwoStep
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 AdaptiveGap85Literal ArithmeticPellRecurrence
open ArithmeticAdaptiveStrongNorm2011 AdaptiveGap85StrongNorm AdaptiveGap85FirstDivisibility
open AdaptiveGap85DoubleThreshold AdaptiveGap85TwoStepFullZero
open AdaptiveGap85InverseEntry
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- If an actual positive gap zero satisfies the two displayed auxiliary
seed equations and scaling equation at a main Pell index R≥5, the full-zero two-step example
follows. The seed equations are hypotheses, not derived for all zeros. -/
theorem seeded_gap_zero_two_step (p : Fin 4 → ℕ) (z : Fin 13 → V) (R u iSeed : V)
    (hb : 0<(p 0:V)) (hb2 : 2≤z 0*(p 0:V)) (hz : ∀i,0<z i)
    (hzero : InternalZero (expressionAt85 (fun j => (p j:ℤ))) z)
    (hgapz : z 1+z 2<1+z 0*(p 0:V)) (hR : 5≤R)
    (hc : z 9+z 7*(z 9+z 10)=ycoord R (z 6*z 7+z 7))
    (hscale : z 4=delta (z 6*z 7+z 7)*iSeed)
    (hux : let a := z 6*z 7+z 7; let c := z 9+z 7*(z 9+z 10)
      let I := delta a*iSeed*c*c; xcoord R (I-2)=I*u)
    (he : let c := z 9+z 7*(z 9+z 10)
      z 3*z 3*c*z 5=u+c+z 3*z 3*R) :
    ∃ a m : Fin 13 → V, (∀i,0<a i) ∧ (∀i,0<m i) ∧
      InternalZero (expressionAt85 (fun j => (p j:ℤ))) a ∧
      InternalZero (expressionAt85 (fun j => (p j:ℤ))) m ∧
      ¬(a 1+a 2<1+a 0*(p 0:V)) ∧ ¬(m 1+m 2<1+m 0*(p 0:V)) ∧
      z 1+z 2<1+z 0*(p 0:V) ∧ PositiveBiStep p a m ∧ PositiveBiStep p m z ∧
      ¬∃ x : Fin 13 → V, PositiveBiStep p a x ∧ x 1+x 2<1+x 0*(p 0:V) := by
  let b : V := z 0*(p 0:V)
  let q : V := 1+b
  let a : V := z 6*z 7+z 7
  let c : V := z 9+z 7*(z 9+z 10)
  let I : V := delta a*iSeed*c*c
  change c=ycoord R a at hc
  change xcoord R (I-2)=I*u at hux
  change z 3*z 3*c*z 5=u+c+z 3*z 3*R at he
  obtain ⟨s,hs,hY⟩ := expressionAt_Y_quotient85 p z hb hz hzero
  have hY' : z 7=s*q^3 := by
    rw [hY]
    dsimp [q,b]
    ring
  have hstrong := expressionAt_strong_norm85 p z hzero
  change ((c*c)*z 4)*((c*c)*z 4)+((3+4*a)+a*a)=((3+4*a)+a*a)*(z 3*z 3) at hstrong
  have hdexpr : (3+4*a)+a*a=delta a := by unfold delta; ring
  rw [hdexpr] at hstrong
  have hd : 0<delta a := by unfold delta; exact mul_pos (by simp) (by simp)
  change z 4=delta a*iSeed at hscale
  have hiSeed : 0 < iSeed := pos_of_mul_pos_right (by rw [←hscale]; exact hz 4) (by simp)
  rw [hscale] at hstrong
  have hnorm : z 3*z 3=1+delta a*(iSeed*c*c)*(iSeed*c*c) := by
    apply mul_left_cancel₀ (ne_of_gt hd)
    calc
      delta a*(z 3*z 3)=((c*c)*(delta a*iSeed))*((c*c)*(delta a*iSeed))+delta a := hstrong.symm
      _=delta a*(1+delta a*(iSeed*c*c)*(iSeed*c*c)) := by ring
  have hc' : let q := 1+b; let Y := s*q^3; z 9+Y*(z 9+z 10)=ycoord R a := by
    change z 9+(s*q^3)*(z 9+z 10)=ycoord R a
    rw [←hY']
    exact hc
  have hn' : let q := 1+b; let Y := s*q^3; let c := z 9+Y*(z 9+z 10)
      z 3*z 3=1+delta a*(iSeed*c*c)*(iSeed*c*c) := by
    change z 3*z 3=1+delta a*(iSeed*(z 9+(s*q^3)*(z 9+z 10))*(z 9+(s*q^3)*(z 9+z 10)))*
      (iSeed*(z 9+(s*q^3)*(z 9+z 10))*(z 9+(s*q^3)*(z 9+z 10)))
    rw [←hY']
    exact hnorm
  have hux' : let q := 1+b; let Y := s*q^3; let c := z 9+Y*(z 9+z 10)
      let I := delta a*iSeed*c*c; xcoord R (I-2)=I*u := by
    change xcoord R (delta a*iSeed*(z 9+(s*q^3)*(z 9+z 10))*(z 9+(s*q^3)*(z 9+z 10))-2)=
      (delta a*iSeed*(z 9+(s*q^3)*(z 9+z 10))*(z 9+(s*q^3)*(z 9+z 10)))*u
    rw [←hY']
    exact hux
  have he' : let q := 1+b; let Y := s*q^3; let c := z 9+Y*(z 9+z 10)
      z 3*z 3*c*z 5=u+c+z 3*z 3*R := by
    change z 3*z 3*(z 9+(s*q^3)*(z 9+z 10))*z 5=
      u+(z 9+(s*q^3)*(z 9+z 10))+z 3*z 3*R
    rw [←hY']
    exact he
  have hthreshold := full_seed_exceeds_two_shifts a R b s (z 9) (z 10) (z 3) iSeed (z 5) u
    hR hs (hz 9) (hz 10) hiSeed (hz 3) hc' hn' hux' he'
  change b*((s*q^3)*(q*q))*(q*q-1)+b*((s*q^3)*(q*q))*(q*q-1)<z 5 at hthreshold
  rw [←hY'] at hthreshold
  exact two_step_full_zero_not_one p z hb hb2 hz hzero hgapz hthreshold
end DiophantineConsistency.AdaptiveGap85SeededTwoStep
