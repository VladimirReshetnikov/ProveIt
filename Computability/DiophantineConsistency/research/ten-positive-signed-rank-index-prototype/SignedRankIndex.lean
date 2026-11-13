import SignedRank

/-! The strong norm and auxiliary odd index force a signed rank congruence. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace TenPositiveSignedRankIndex
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing
open ArithmeticPellRecurrence ArithmeticPellHalfIndex
open TenPositiveSignedRank
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem signed_rank_index (c F D I t u h : V) (x rank : DiffRing V)
    (hc : 0<c) (hJ : 2≤D*I) (hd : c∣I)
    (hstrong : F*F=1+D*I*I)
    (hx : x=ι (F*F)*(ι (t*c)-rank)-ι c)
    (hs : x*x=ι (u*u))
    (haux : xcoord (2*h+1) (D*I-2)=(D*I)*u) :
    ∃ rp rn : V, rank=ι rp-ι rn ∧ SignMod c (absdiff rp rn) (2*h+1) := by
  obtain ⟨rp,rn,hr⟩ := exists_mk rank
  rw [mk_eq_sub] at hr
  have hdiv : c∣D*I*I := dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hd D) I
  have hfmod : (F*F)%c=(1:V)%c := by
    rw [hstrong]
    exact mod_add_remove_right_of_dvd hdiv hc
  have hx' : x=ι (F*F)*(ι (t*c)+ι rn-ι rp)-ι c := by rw [hx,hr]; ring
  have hRank := rank_residue_of_square c F t rp rn u x hc hfmod hx' hs
  have hJpos : 0<D*I := lt_of_lt_of_le (by simp : (0:V)<2) hJ
  have hsub : D*I-2+2=D*I := tsub_add_cancel_of_le hJ
  have hu : u=oddQuotient h (D*I-2) := by
    apply mul_left_cancel₀ (ne_of_gt hJpos)
    calc
      (D*I)*u=xcoord (2*h+1) (D*I-2) := haux.symm
      _=(D*I)*oddQuotient h (D*I-2) := by rw [odd_exact,hsub]
  have hdJ : c∣D*I := dvd_mul_of_dvd_right hd D
  have hindex : SignMod c u (2*h+1) := by
    rw [hu]
    exact quotient_mod_divisor (D*I) c h hJ hc hdJ
  exact ⟨rp,rn,hr,sign_trans hc (sign_symm hRank) hindex⟩

#print axioms TenPositiveSignedRankIndex.signed_rank_index
end TenPositiveSignedRankIndex
