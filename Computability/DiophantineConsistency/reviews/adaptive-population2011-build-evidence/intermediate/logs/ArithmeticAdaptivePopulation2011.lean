import DiophantineConsistency.ArithmeticAdaptiveRadix2011
import DiophantineConsistency.ArithmeticHalfBinomial

/-! The actual adaptive radix supplies the internal rank-population bound. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptivePopulation2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticAdaptiveScaledNorms2011 ArithmeticAdaptiveFirstDivisibility2011
open ArithmeticAdaptiveExactIndices2011 ArithmeticAdaptivePowerFinish2011 ArithmeticAdaptiveRadix2011
open ArithmeticPellRecurrence ArithmeticBinaryPopulation ArithmeticHalfBinomial
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.radix CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort xcoord ycoord
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- This uses only the literal positive rank expression and its radix. -/
theorem rank_lower (q F alpha J MC MF h : V)
    (hq16 : 16≤q) (halpha : 0<alpha) (hq : q=Exp.exp h) :
    3*h+1≤((q-1)*(q-F)+alpha)*(q^2-1)+(MC+q*MF)*J := by
  let R := ((q-1)*(q-F)+alpha)*(q^2-1)+(MC+q*MF)*J
  have hR : q^2-1≤R := by
    have h1 : 1≤(q-1)*(q-F)+alpha :=
      le_trans (pos_iff_one_le.mp halpha) (le_add_of_nonneg_left (by simp))
    exact le_trans (le_mul_of_one_le_left (by simp) h1) (le_add_of_nonneg_right (by simp))
  have hhq : h+1≤q := by rw [hq]; exact lt_iff_succ_le.mp (lt_exp h)
  have hsq : 3*h+1+1≤q^2 := calc
    3*h+1+1≤3*(h+1)+(16:V) := by
      have he : 3*h+1+1+(3+14:V)=3*(h+1)+16 := by ring
      rw [←he]; exact le_add_of_nonneg_right (by simp)
    _≤3*q+q := add_le_add (mul_le_mul_of_nonneg_left hhq (by simp)) hq16
    _=4*q := by ring
    _≤q*q := mul_le_mul_of_nonneg_right (le_trans (by norm_num : (4:V)≤16) hq16) (by simp)
    _=q^2 := by ring
  exact le_trans (le_tsub_of_add_le_right hsq) hR

def PopulationBound (p : Fin 4 → ℕ) (v : Fin 13 → V) (h : V) : Prop :=
  let q : V := 1+v 0*(p 0:V)
  let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
  q=Exp.exp h → 3*h+2≤population R

theorem population_of_facts (p : Fin 4 → ℕ) (v : Fin 13 → V) (h : V)
    (hv : ∀j,0<v j) (hq16 : 16≤1+v 0*(p 0:V))
    (hY : ∃s:V, v 7=(1+v 0*(p 0:V))^3*s)
    (he : ExactIndices p v) (hp : PowerFinish p v) : PopulationBound p v h := by
  let q : V := 1+v 0*(p 0:V)
  let X : V := v 6
  let Y : V := v 7
  let Q : V := X*Y*Y
  let k : V := v 9+v 10
  let c : V := v 9+Y*k
  let a : V := X*Y+Y
  let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
  change q=Exp.exp h → 3*h+2≤population R
  intro hq
  obtain ⟨first,main,n,m,t,_,_,hn13,_,hmR,hnR,_,_,_,_,hny,_,hmy⟩ := he
  change m=R at hmR
  change 2*n=R+1 at hnR
  change X=Exp.exp R at hp
  let r : V := n-1
  have hn1 : 1≤n := le_trans (by simpa only [show (1:V)+12=13 by ring] using
    (show (1:V)≤1+12 by simp)) hn13
  have hrplus : r+1=n := tsub_add_cancel_of_le hn1
  have hr4 : 4≤r := by
    apply (add_le_add_iff_right (1:V)).mp
    rw [hrplus]
    have h5 : (5:V)≤13 := by simpa only [show (5:V)+8=13 by ring] using (show (5:V)≤5+8 by simp)
    simpa only [show (4:V)+1=5 by ring] using le_trans h5 hn13
  have hR : R=2*r+1 := by
    apply add_right_cancel (b:=(1:V))
    calc
      R+1=2*n := hnR.symm
      _=2*(r+1) := by rw [hrplus]
      _=(2*r+1)+1 := by ring
  have hXe : X=Exp.exp (2*r+1) := by rw [←hR]; exact hp
  have hY1 : 1≤Y := pos_iff_one_le.mp (hv 7)
  have hbase : a=Y*(X+1) := by dsimp [a,X,Y]; ring
  change 2*ycoord n (2*(Q-1)+1)=k at hny
  change ycoord m a=c at hmy
  have hck : ycoord (2*r+1) (Y*(X+1))=
      2*ycoord (r+1) (2*(X*Y*Y-1)+1)*Y+v 9 := by
    rw [←hbase,←hR,←hmR,hmy,hrplus,hny]
    dsimp [c]; ring
  obtain ⟨w,hw⟩ := half_binomial X Y r (v 9) (v 10) hr4 hXe hY1 hck
    (by rw [hrplus,hny]) (hv 9) (hv 10)
  obtain ⟨s,hs⟩ := hY
  have hYq : Exp.exp (3*h)∣Y := by
    refine ⟨s,?_⟩
    change Y=q^3*s at hs
    rw [hs,hq,show 3*h=h+h+h by ring,exp_add,exp_add]
    ring
  have h3 : 3*h+1≤R := rank_lower q (v 1) (v 2) (v 0) (p 2:V) (p 3:V) h hq16 (hv 2) hq
  rw [hR] at h3 ⊢
  exact population_lower X Y r w h hXe hw hYq h3

private theorem exp_four : Exp.exp (4:V)=16 := by
  rw [show (4:V)=((0+1)+1+1)+1 by ring,exp_succ,exp_succ,exp_succ,exp_succ,exp_zero]
  ring

theorem current_population_bound (v : Fin 13 → V) (hv : ∀j,0<v j)
    (hz : InternalZero expression v) :
    ∃ N : V, 0<N ∧ (1+v 0*(CurrentMasks2011.beta:V))=Exp.exp ((CurrentMasks2011.width:V)*N) ∧
      PopulationBound currentPorts v ((CurrentMasks2011.width:V)*N) := by
  obtain ⟨N,w,hN,hqN,_,_,_,_,_⟩ := current_radix v hv hz
  have hd : (4:V)≤(CurrentMasks2011.width:V) := by norm_num [CurrentMasks2011.width]
  have hh : (4:V)≤(CurrentMasks2011.width:V)*N :=
    le_trans hd (le_mul_of_one_le_right (by simp) (pos_iff_one_le.mp hN))
  have hq16 : (16:V)≤1+v 0*(CurrentMasks2011.beta:V) := by
    rw [hqN]
    have he := exp_monotone_le.mpr hh
    simpa only [exp_four] using he
  have hq16' : (16:V)≤1+v 0*(currentPorts 0:V) := by
    simpa only [currentPorts,Matrix.cons_val_zero] using hq16
  obtain ⟨s,_,hs⟩ := current_Y_quotient v hv hz
  have hs' : v 7=(1+v 0*(CurrentMasks2011.beta:V))^3*s := by
    simpa only [pow_succ,pow_zero,one_mul,mul_assoc] using hs
  have hy : ∃s:V, v 7=(1+v 0*(currentPorts 0:V))^3*s := by
    exact ⟨s,by simpa only [currentPorts,Matrix.cons_val_zero] using hs'⟩
  exact ⟨N,hN,hqN,population_of_facts currentPorts v _ hv hq16' hy
    (current_exact_indices v hv hz) (current_power_finish v hv hz)⟩

theorem current_natural_population_bound (v : Fin 13 → V) (hz : InternalZero naturalExpression v) :
    ∃ N : V, 0<N ∧ (1+(v 0+1)*(CurrentMasks2011.beta:V))=Exp.exp ((CurrentMasks2011.width:V)*N) ∧
      PopulationBound currentPorts (fun j => v j+1) ((CurrentMasks2011.width:V)*N) :=
  current_population_bound _ (fun j => lt_of_le_of_lt (Arithmetic.zero_le (v j)) (lt_add_one _))
    ((internalZero_positiveShift expression v).mp hz)
end DiophantineConsistency.ArithmeticAdaptivePopulation2011
