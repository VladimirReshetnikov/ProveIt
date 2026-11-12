import DiophantineConsistency.Compact44.P72Root

/-! Source-only proposal: an internal consecutive-square exclusion. Its
numerical hypotheses must be supplied by a graph-specific main-norm client.
No Lean elaboration or compilation has been performed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ModelMainSquareGapDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ModelDifferenceRing
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- With 1<c<2A and A²=Delta+1, the displayed natural expression cannot
be a square. Both bounds and the natural square equation are explicit. -/
theorem no_main_square (A c Delta d : V) (hA : 0<A) (hc : 1<c)
    (hbound : c<2*A) (hDelta : A*A=Delta+1)
    (hnorm : d*d=1+Delta*c*c) : False := by
  have hac : 1≤A*c := one_le_mul (pos_iff_one_le.mp hA)
    (le_trans (by simp : (1:V)≤1) (le_of_lt hc))
  let t : V := A*c-1
  have ht : t+1=A*c := tsub_add_cancel_of_le hac
  have htcast : ι t=ι A*ι c-1 := by
    dsimp only [t]
    rw [P72Root.ι_tsub hac]
    simp only [map_mul,map_one]
  have hcR : (1 : DiffRing V)<ι c := by
    have h := (ι_lt_ι (a := (1:V)) (b := c)).mpr hc
    simpa only [map_one] using h
  have hboundR : ι c<2*ι A := by
    have h := (ι_lt_ι (a := c) (b := 2*A)).mpr hbound
    simpa only [map_mul,map_ofNat] using h
  have hprod : (0 : DiffRing V)<ι c*(2*ι A-ι c) :=
    mul_pos (lt_trans (by norm_num) hcR) (sub_pos.mpr hboundR)
  have hc2 : (1 : DiffRing V)<ι c*ι c := by
    have h := mul_self_lt_mul_self (by norm_num : (0 : DiffRing V)≤1) hcR
    simpa only [one_mul] using h
  have hdeltaR : ι A*ι A=ι Delta+1 := by
    have h := congrArg (ι : V →+* DiffRing V) hDelta
    simpa only [map_mul,map_add,map_one] using h
  have hnormR : ι d*ι d=1+ι Delta*ι c*ι c := by
    have h := congrArg (ι : V →+* DiffRing V) hnorm
    simpa only [map_mul,map_add,map_one] using h
  have hscaled : (ι A*ι A)*(ι c*ι c)=(ι Delta+1)*(ι c*ι c) := by
    rw [hdeltaR]
  have hleftR : (ι A*ι c-1)*(ι A*ι c-1)<ι d*ι d := by
    nlinarith [hprod,hscaled,hnormR]
  have hrightR : ι d*ι d<(ι A*ι c)*(ι A*ι c) := by
    nlinarith [hc2,hscaled,hnormR]
  have hleft : t*t<d*d := (ι_lt_ι).mp (by
    simpa only [map_mul,htcast] using hleftR)
  have hright : d*d<(A*c)*(A*c) := (ι_lt_ι).mp (by
    simpa only [map_mul] using hrightR)
  have htd : t<d := lt_of_mul_self_lt_mul_self₀ (Arithmetic.zero_le _) hleft
  have hdac : d<A*c := lt_of_mul_self_lt_mul_self₀ (Arithmetic.zero_le _) hright
  have hacd : A*c≤d := by
    have h := lt_iff_succ_le.mp htd
    simpa only [ht] using h
  exact (not_lt_of_ge hacd) hdac

/-- The explicit graph-shaped main norm excludes eta+zeta=2 for positive
inputs. The natural Delta identity and natural main square are premises. -/
theorem two_ordinate_impossible (X Y eta zeta Delta d : V)
    (hX : 0<X) (hY : 0<Y) (heta : 0<eta) (hzeta : 0<zeta)
    (hDelta : (X*Y+Y+2)*(X*Y+Y+2)=Delta+1)
    (hnorm : d*d=1+Delta*(eta+Y*(eta+zeta))*(eta+Y*(eta+zeta))) :
    eta+zeta≠2 := by
  intro hk
  have heta1 : 1≤eta := pos_iff_one_le.mp heta
  have hzeta1 : 1≤zeta := pos_iff_one_le.mp hzeta
  have hetale : eta≤1 := by
    apply (add_le_add_iff_right (1:V)).mp
    calc
      eta+1≤eta+zeta := add_le_add_left hzeta1 eta
      _=2 := hk
      _=1+1 := by ring
  have hetaEq : eta=1 := le_antisymm hetale heta1
  have hzetaEq : zeta=1 := by
    apply add_left_cancel (a := (1:V))
    calc
      1+zeta=eta+zeta := by rw [hetaEq]
      _=2 := hk
      _=1+1 := by ring
  let A : V := X*Y+Y+2
  let c : V := eta+Y*(eta+zeta)
  have hA : 0<A := by dsimp [A]; simp
  have hcEq : c=2*Y+1 := by dsimp [c]; rw [hetaEq,hzetaEq]; ring
  have hc : 1<c := by
    rw [hcEq]
    have h := mul_pos (by norm_num : (0:V)<2) hY
    simpa only [add_comm] using lt_add_of_pos_right (1:V) h
  have hYle : Y≤X*Y+Y := le_add_of_nonneg_left (Arithmetic.zero_le (X*Y))
  have hcA : c<2*A := by
    rw [hcEq]
    calc
      2*Y+1<2*Y+4 := add_lt_add_left (by norm_num : (1:V)<4) _
      _≤2*(X*Y+Y)+4 := add_le_add_right
        (mul_le_mul_of_nonneg_left hYle (by simp)) _
      _=2*A := by dsimp [A]; ring
  apply no_main_square A c Delta d hA hc hcA
  · simpa only [A] using hDelta
  · simpa only [c] using hnorm

end DiophantineConsistency.ModelMainSquareGapDraft

#print axioms DiophantineConsistency.ModelMainSquareGapDraft.no_main_square
#print axioms DiophantineConsistency.ModelMainSquareGapDraft.two_ordinate_impossible
