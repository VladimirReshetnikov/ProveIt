import DiophantineConsistency.ArithmeticAdaptiveMainOrientation2011
import DiophantineConsistency.ArithmeticAdaptiveFactorThree2011

/-! Source-only proposals. These fact-level statements do not mention the
shifted graph; graph evaluation and every premise must be supplied separately.
No elaboration, compilation or kernel checking has been performed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ShiftedGuardFacts
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ArithmeticSignedPairs ArithmeticAdaptiveQuotients2011
open ArithmeticAdaptiveFirstDivisibility2011
open ArithmeticAdaptiveMainOrientation2011 ArithmeticAdaptiveFactorThree2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Proposed fact-level orientation from a positive difference and an
internally scaled natural magnitude. No transport or graph zero is assumed. -/
theorem oriented_scaled_pair (positive negative scale radicand : V)
    (hscale : 0<scale) (hrad : 0<radicand) (hpos : negative<positive)
    (hnorm : magnitude (positive,negative)*magnitude (positive,negative) =
      scale*scale*radicand) :
    ∃ root : V, 0<root ∧
      Equivalent (positive,negative) (natural (scale*root)) ∧
      root*root=radicand := by
  obtain ⟨root,hroot,hsquare⟩ :=
    scaled_quotient scale (magnitude (positive,negative)) radicand hscale hnorm
  have hrootpos : 0<root := by
    apply pos_of_mul_pos_left (b := root) _ (by simp)
    rw [hsquare]
    exact hrad
  have hsum : positive=negative+(positive-negative) := by
    rw [add_comm,tsub_add_cancel_of_le (le_of_lt hpos)]
  have hmag : magnitude (positive,negative)=positive-negative := magnitude_of_add hsum
  have hdiff : positive-negative=scale*root := hmag.symm.trans hroot
  refine ⟨root,hrootpos,?_,hsquare⟩
  change positive+0=negative+scale*root
  simpa only [add_zero,hdiff] using hsum

/-- Proposed specialization of the generic main-parts inequality to the
scaled-pair lemma. Y>=8 and k>0 are explicit; neither Bt nor an old first
coordinate occurs. The caller still has to prove the displayed scaled norm. -/
theorem sign_free_main_quotient (U X Y k eta gamma q R radicand : V)
    (hU : 0<U) (hY : 8≤Y) (hk : 0<k) (hrad : 0<radicand)
    (hnorm : let a := X*Y+Y; let c := eta+Y*k; let H := 3+4*a
      let positive := U*(X+a*c)+H*(U*gamma+X*Y*q+R+1)
      let negative := H*k
      magnitude (positive,negative)*magnitude (positive,negative)=U*U*radicand) :
    let a := X*Y+Y; let c := eta+Y*k; let H := 3+4*a
    let positive := U*(X+a*c)+H*(U*gamma+X*Y*q+R+1)
    let negative := H*k
    ∃ root : V, 0<root ∧ Equivalent (positive,negative) (natural (U*root)) ∧
      root*root=radicand := by
  dsimp only at hnorm ⊢
  apply oriented_scaled_pair _ _ U radicand hU hrad
  · exact main_parts_positive U X Y k eta gamma q R hU hY hk
  · exact hnorm

/-- Proposed graph-independent q^4 rank congruence from an explicit balanced
carrier equality. It uses the internal factor-three cancellation even if 3|q;
it does not construct the balance, first root, graph values or rank. -/
theorem q4_rank_from_balance (q Y X R k left right : V)
    (hq : 0<q) (hY : q^3∣Y)
    (hbalance : (3+4*Y*(X+1))*(X*Y*q+(R+1))+q^5*left =
      (3+4*Y*(X+1))*k+q^5*right) :
    q^4∣magnitude (R+1,k) := by
  let H : V := 3+4*Y*(X+1)
  let T : V := X*Y*q+(R+1)
  have hm5 : 0<q^5 := pow_pos hq _
  have hm4 : 0<q^4 := pow_pos hq _
  have hmod : (H*T)%(q^5)=(H*k)%(q^5) := by
    have h := congrArg (fun z : V => z%(q^5)) hbalance
    change (H*T+q^5*left)%(q^5)=(H*k+q^5*right)%(q^5) at h
    rwa [mod_add_mul' _ _ hm5,mod_add_mul' _ _ hm5] at h
  have hdiv : q^5∣H*magnitude (T,k) := by
    have h := dvd_magnitude_of_mod hm5 hmod
    have heq : magnitude (H*T,H*k)=H*magnitude (T,k) := by
      dsimp [magnitude]
      rw [mul_add H (T-k) (k-T),mul_tsub H T k,mul_tsub H k T]
    rwa [heq] at h
  have hT : q^4∣magnitude (T,k) :=
    cancel_factor_three q Y X _ hq hY (by simpa only [H] using hdiv)
  have hTmod := magnitude_mod (T,k) (q^4) hm4 hT
  obtain ⟨s,hs⟩ := hY
  have hEq : q^4∣X*Y*q := by
    refine ⟨X*s,?_⟩
    rw [hs]
    ring
  have hTR : T=X*Y*q+(R+1) := rfl
  rw [hTR,mod_add_remove_left_of_dvd hEq hm4] at hTmod
  exact dvd_magnitude_of_mod hm4 hTmod

end DiophantineConsistency.ShiftedGuardFacts

#print axioms DiophantineConsistency.ShiftedGuardFacts.oriented_scaled_pair
#print axioms DiophantineConsistency.ShiftedGuardFacts.sign_free_main_quotient
#print axioms DiophantineConsistency.ShiftedGuardFacts.q4_rank_from_balance
