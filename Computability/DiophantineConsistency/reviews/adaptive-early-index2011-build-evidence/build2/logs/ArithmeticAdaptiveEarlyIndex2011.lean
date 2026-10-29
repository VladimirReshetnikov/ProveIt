import DiophantineConsistency.ArithmeticAdaptiveRankCongruence2011
import DiophantineConsistency.ArithmeticAdaptiveRankWindow2011

/-! First Pell index residue and lower bound from the literal adaptive zero. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptiveEarlyIndex2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticAdaptiveFactorMagnitude2011
open ArithmeticAdaptiveScaledNorms2011 ArithmeticAdaptiveFirstDivisibility2011
open ArithmeticAdaptivePellIndices2011 ArithmeticAdaptiveRankWindow2011 ArithmeticAdaptiveRankCongruence2011
open ArithmeticPellRecurrence ArithmeticPellCongruences
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.radix CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
private theorem magnitude_mod (p : Pair V) (m : V) (hm : 0<m)
    (hd : m∣magnitude p) : p.1%m=p.2%m := by
  have hz : magnitude p%m=0 := mod_eq_zero_iff_dvd.mpr hd
  rcases le_total p.2 p.1 with h|h
  · have he : p.1=p.2+(p.1-p.2) := by rw [add_comm,tsub_add_cancel_of_le h]
    have hg := magnitude_of_add he
    have hs : (p.1-p.2)%m=0 := by rw [←hg]; exact hz
    rw [he,mod_add hm,hs,add_zero,mod_eq_self_of_lt (mod_lt _ hm)]
  · have he : p.2=p.1+(p.2-p.1) := by rw [add_comm,tsub_add_cancel_of_le h]
    have hg : magnitude p=p.2-p.1 := by
      have h' := magnitude_of_add he
      change magnitude (swap p)=p.2-p.1 at h'
      simpa only [magnitude_swap] using h'
    have hs : (p.2-p.1)%m=0 := by rw [←hg]; exact hz
    rw [he,mod_add hm,hs,add_zero,mod_eq_self_of_lt (mod_lt _ hm)]

def EarlyIndex (p : Fin 4 → ℕ) (v : Fin 13 → V) : Prop :=
  let q : V := 1+v 0*(p 0:V)
  let M : V := (q*(q*q))*(v 0*(p 0:V))
  let Q : V := (v 6*v 7)*v 7
  let k : V := v 9+v 10
  let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
  ∃ first n : V, 0<first ∧ 13≤n ∧ n≤k ∧
    magnitude (pairEval (rootTerm (factors (fun j => (p j:ℤ))).1) v)=M*first ∧
    xcoord n (2*(Q-1)+1)=first ∧ 2*ycoord n (2*(Q-1)+1)=k ∧
    (2*n)%(q^4)=R+1 ∧ R+1≤2*n ∧ R+1≤k

theorem early_index_of_facts (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hq : 0<1+v 0*(p 0:V)) (hv : ∀j,0<v j)
    (hY : ∃s:V, v 7=((1+v 0*(p 0:V))^3)*s)
    (hi : Indices p v) (hw : RankWindow p v) (hc : RankCongruence p v) : EarlyIndex p v := by
  let q : V := 1+v 0*(p 0:V)
  let Q : V := (v 6*v 7)*v 7
  let B : V := 2*(Q-1)+1
  let k : V := v 9+v 10
  let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
  have hQ : 0<Q := mul_pos (mul_pos (hv 6) (hv 7)) (hv 7)
  have hQ1 : Q-1+1=Q := tsub_add_cancel_of_le (pos_iff_one_le.mp hQ)
  have hB : B+1=2*Q := by
    dsimp [B]
    calc
      2*(Q-1)+1+1=2*(Q-1+1) := by ring
      _=2*Q := by rw [hQ1]
  obtain ⟨s,hs⟩ := hY
  have hdiv : q^4∣B+1 := by
    rw [hB]
    refine ⟨2*v 6*(q*q)*s*s,?_⟩
    dsimp [Q]; rw [hs]; ring
  obtain ⟨first,main,n,m,hfirst,_,_,_,hnk,_,hroot,_,hnx,hny,_,_⟩ := hi
  obtain ⟨hR24,hupper⟩ := hw
  have hm : 0<q^4 := pow_pos hq _
  have hRlt : R+1<q^4 := by
    have hp : 0<q^3+q := add_pos (pow_pos hq _) hq
    calc
      R+1<(R+1)+(q^3+q) := lt_add_of_pos_right _ hp
      _=R+q^3+q+1 := by ring
      _≤q^4 := hupper
  have hres : (R+1)%(q^4)=k%(q^4) := magnitude_mod (R+1,k) (q^4) hm hc
  rw [mod_eq_self_of_lt hRlt] at hres
  obtain ⟨r,t,_,hy⟩ := residue_quotients n B (q^4) hdiv
  change 2*ycoord n B=k at hny
  have hk : k=2*n+q^4*(2*t) := by rw [←hny,hy]; ring
  have hnmod : (2*n)%(q^4)=R+1 := by
    rw [hk,mod_add_mul' _ _ hm] at hres
    exact hres.symm
  have hnlow : R+1≤2*n := by rw [←hnmod]; exact mod_le _ _
  have hklow : R+1≤k := by rw [hres]; exact mod_le _ _
  have hn13 : 13≤n := by
    have htwelve : (2:V)*12<2*n := by
      rw [show (2:V)*12=24 by ring]
      exact lt_of_le_of_lt hR24 (lt_of_lt_of_le (lt_add_one R) hnlow)
    have h12 : (12:V)<n := lt_of_mul_lt_mul_left htwelve (by simp)
    simpa only [show (12:V)+1=13 by ring] using lt_iff_succ_le.mp h12
  exact ⟨first,n,hfirst,hn13,hnk,hroot,hnx,hny,hnmod,hnlow,hklow⟩

theorem expressionAt_early_index (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hb : 0<(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀j,0<v j) (hz : InternalZero (expressionAt (fun j => (p j:ℤ))) v) : EarlyIndex p v := by
  have hp := scaled_parameters_positive p v hb hv
  obtain ⟨s,_,hs⟩ := expressionAt_Y_quotient p v hb hv hz
  have hs' : v 7=(1+v 0*(p 0:V))^3*s := by
    simpa only [pow_succ,pow_zero,one_mul,mul_assoc] using hs
  exact early_index_of_facts p v (lt_trans (by simp : (0:V)<1) hp.1) hv ⟨s,hs'⟩
    (expressionAt_indices p v hb hv hz) (expressionAt_rank_window p v hb hl hh hv hz)
    (expressionAt_rank_congruence p v hb hv hz)

theorem current_early_index (v : Fin 13 → V) (hv : ∀j,0<v j)
    (hz : InternalZero expression v) : EarlyIndex currentPorts v := by
  have hp := current_parameters_positive v hv
  obtain ⟨s,_,hs⟩ := current_Y_quotient v hv hz
  have hs' : v 7=(1+v 0*(CurrentMasks2011.beta:V))^3*s := by
    simpa only [pow_succ,pow_zero,one_mul,mul_assoc] using hs
  have hy : ∃s:V, v 7=(1+v 0*(currentPorts 0:V))^3*s := by
    refine ⟨s,?_⟩
    simpa only [currentPorts,Matrix.cons_val_zero] using hs'
  have hq : 0<1+v 0*(currentPorts 0:V) := by
    simpa only [currentPorts,Matrix.cons_val_zero] using lt_trans (by simp : (0:V)<1) hp.1
  exact early_index_of_facts currentPorts v hq hv hy (current_indices v hv hz)
    (current_rank_window v hv hz) (current_rank_congruence v hv hz)

theorem current_natural_early_index (v : Fin 13 → V) (hz : InternalZero naturalExpression v) :
    EarlyIndex currentPorts (fun j => v j+1) :=
  current_early_index _ (fun j => lt_of_le_of_lt (Arithmetic.zero_le (v j)) (lt_add_one _))
    ((internalZero_positiveShift expression v).mp hz)
end DiophantineConsistency.ArithmeticAdaptiveEarlyIndex2011
