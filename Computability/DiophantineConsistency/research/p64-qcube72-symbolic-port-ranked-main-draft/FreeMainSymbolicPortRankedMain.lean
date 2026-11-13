import FreeMainWindowRankedMain
import DiophantineConsistency.CompactSymbolicPorts
import DiophantineConsistency.ArithmeticStandardCasts

/-! Source-only draft. All port data are variables; no huge concrete mask or
radix numeral is reduced here. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace FreeMainSymbolicPortRankedMain
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011
open ArithmeticPellRecurrence FreeMainConditionalRank
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem q_lower (b J : V) (hb : b+1=Exp.exp (590069:V)) (hJ : 0<J) :
    33≤b*J+1 := by
  have h6 : Exp.exp (6:V)=(64:V) := by
    simpa using ArithmeticStandardCasts.cast_exp (V:=V) 6
  have hexp : (64:V)≤Exp.exp (590069:V) := by
    rw [←h6]
    exact exp_monotone_le.mpr (by norm_num)
  have hb64 : (64:V)≤b+1 := by rw [hb]; exact hexp
  have hbJ : b≤b*J := le_mul_of_one_le_right (Arithmetic.zero_le b) (pos_iff_one_le.mp hJ)
  have hbJ1 : b+1≤b*J+1 := by
    simpa only [add_comm] using add_le_add_right hbJ 1
  exact le_trans (by norm_num : (33:V)≤64) (le_trans hb64 hbJ1)

/-- Uses only symbolic cast identities and mask inequalities, supplied
separately. No concrete compact constants are unfolded. -/
theorem main_at_rank (beta K L H : ℕ) (v : Fin 14 → V)
    (hv : ∀ i,0<v i)
    (hz : InternalZero (P64QCube72Free.graph
      (fun j => (CompactSymbolicPorts.ports beta K L H j:ℤ))).output v)
    (hbeta : (beta:V)+1=Exp.exp (590069:V))
    (hL : (L:V)<(beta:V)) (hH : (beta:V)+(H:V)<2*(beta:V)) :
    let p := CompactSymbolicPorts.ports beta K L H
    ∃ g : V, g*g=1+delta (aval p v)*(cval p v)*(cval p v) ∧
      xcoord (FreeMainAuxNorm.rank p v) (aval p v)=g ∧
      ycoord (FreeMainAuxNorm.rank p v) (aval p v)=cval p v := by
  let p := CompactSymbolicPorts.ports beta K L H
  have hq : 33≤qval p v := by
    change 33≤(beta:V)*v 0+1
    exact q_lower (beta:V) (v 0) hbeta (hv 0)
  have hMC : (p 2:V)<(p 0:V) := by
    change (L:V)<(beta:V)
    exact hL
  have hMF : (p 3:V)<2*(p 0:V) := by
    change ((beta+H:ℕ):V)<2*(beta:V)
    simpa only [Nat.cast_add] using hH
  exact FreeMainWindowRankedMain.main_at_rank p v hv hz hq hMC hMF

#print axioms q_lower
#print axioms main_at_rank
end FreeMainSymbolicPortRankedMain
