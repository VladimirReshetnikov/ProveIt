import DiophantineConsistency.ArithmeticAdaptiveFirstDivisibility2011

/-! A residue obstruction to a particular direct rank-normalization strategy.
This is arithmetic only: it does not assert the existence of an 85 zero. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85RankRemainderObstruction
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticAdaptiveFirstDivisibility2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def rankPlus (q F C J mu nu : V) : V :=
  let q2 := q*q
  let neg := q*F+C
  q2*q2+neg+J*(mu+nu*q)

def rankMinus (q F C : V) : V :=
  let q2 := q*q
  let neg := q*F+C
  q2+neg*q2

theorem rankMinus_dvd (q F C : V) : q∣rankMinus q F C := by
  refine ⟨q+(q*F+C)*q,?_⟩
  dsimp [rankMinus]
  ring

theorem rankPlus_mod (q F C J mu nu : V) (hq : 0<q) :
    rankPlus q F C J mu nu % q = (C+J*mu)%q := by
  have he : rankPlus q F C J mu nu = (C+J*mu)+q*(q*q*q+F+J*nu) := by
    dsimp [rankPlus]
    ring
  rw [he,mod_add_mul' _ _ hq]

/-- If C is a multiple of q, no positive normalized pair can have the
same signed rank residue modulo q while q, J and the ports stay fixed. -/
theorem no_normalized_same_rank_residue (q F C F' C' J mu nu : V)
    (hq : 0<q) (hC : q∣C) (hC' : 0<C') (hgap : F'+C'<q) :
    ¬((rankPlus q F C J mu nu+rankMinus q F' C')%q =
      (rankMinus q F C+rankPlus q F' C' J mu nu)%q) := by
  have hn : C'<q := lt_of_le_of_lt (by simp : C'≤F'+C') hgap
  intro he
  rw [mod_add_remove_right_of_dvd (rankMinus_dvd q F' C') hq,
    mod_add_remove_left_of_dvd (rankMinus_dvd q F C) hq,
    rankPlus_mod q F C J mu nu hq,rankPlus_mod q F' C' J mu nu hq] at he
  have h := mod_cancel hq he
  have hc : C%q=0 := mod_eq_zero_iff_dvd.mpr hC
  rw [hc,mod_eq_self_of_lt hn] at h
  exact (ne_of_gt hC') h.symm
end DiophantineConsistency.AdaptiveGap85RankRemainderObstruction
