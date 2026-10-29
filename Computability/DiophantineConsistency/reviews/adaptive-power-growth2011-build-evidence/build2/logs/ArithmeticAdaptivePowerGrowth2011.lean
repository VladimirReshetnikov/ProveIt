import DiophantineConsistency.ArithmeticAdaptivePowerLowerBound2011
import DiophantineConsistency.ArithmeticPellPowerRecovery

/-! The actual adaptive Pell indices force Y above 2^R. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptivePowerGrowth2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticAdaptiveScaledNorms2011 ArithmeticAdaptiveExactIndices2011
open ArithmeticAdaptivePowerLowerBound2011 ArithmeticPellRecurrence ArithmeticPellPowerRecovery
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.radix CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort xcoord ycoord
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def PowerGrowth (p : Fin 4 → ℕ) (v : Fin 13 → V) : Prop :=
  let q : V := 1+v 0*(p 0:V)
  let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
  Exp.exp R<v 7

theorem growth_of_facts (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hv : ∀j,0<v j) (hX : 16≤v 6) (he : ExactIndices p v) : PowerGrowth p v := by
  let q : V := 1+v 0*(p 0:V)
  let X : V := v 6
  let Y : V := v 7
  let Q : V := X*Y*Y
  let k : V := v 9+v 10
  let c : V := v 9+Y*k
  let a : V := X*Y+Y
  let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
  obtain ⟨first,main,n,m,t,_,_,hn13,_,hmR,hnR,_,_,_,_,hny,_,hmy⟩ := he
  change m=R at hmR
  let r : V := n-1
  have hn1 : 1≤n := le_trans (by simpa only [show (1:V)+12=13 by ring] using
    (show (1:V)≤1+12 by simp)) hn13
  have hrplus : r+1=n := tsub_add_cancel_of_le hn1
  have hr2 : 2≤r := by
    apply (add_le_add_iff_right (1:V)).mp
    rw [hrplus]
    have h3 : (3:V)≤13 := by simpa only [show (3:V)+10=13 by ring] using (show (3:V)≤3+10 by simp)
    simpa only [show (2:V)+1=3 by ring] using le_trans h3 hn13
  have hR : R=2*r+1 := by
    apply add_right_cancel (b:=(1:V))
    calc
      R+1=2*n := hnR.symm
      _=2*(r+1) := by rw [hrplus]
      _=(2*r+1)+1 := by ring
  have hbase : a=Y*(X+1) := by dsimp [a,X,Y]; ring
  have hc : c=ycoord (2*r+1) (Y*(X+1)) := by
    change ycoord m a=c at hmy
    rw [←hR,←hmR,←hbase]
    exact hmy.symm
  have hk : k=2*ycoord (r+1) (2*(X*Y*Y-1)+1) := by
    change 2*ycoord n (2*(Q-1)+1)=k at hny
    rw [hrplus]
    exact hny.symm
  have hg := power_bound X Y r k c (v 9) (v 10) hX (pos_iff_one_le.mp (hv 7)) hr2
    (by dsimp [c]; ring) rfl (hv 10) hc hk
  change Exp.exp R<Y
  rw [hR]
  exact hg

theorem current_power_growth (v : Fin 13 → V) (hv : ∀j,0<v j)
    (hz : InternalZero expression v) : PowerGrowth currentPorts v :=
  growth_of_facts currentPorts v hv (current_X_lower v hv hz) (current_exact_indices v hv hz)

theorem current_natural_power_growth (v : Fin 13 → V) (hz : InternalZero naturalExpression v) :
    PowerGrowth currentPorts (fun j => v j+1) :=
  current_power_growth _ (fun j => lt_of_le_of_lt (Arithmetic.zero_le (v j)) (lt_add_one _))
    ((internalZero_positiveShift expression v).mp hz)
end DiophantineConsistency.ArithmeticAdaptivePowerGrowth2011
