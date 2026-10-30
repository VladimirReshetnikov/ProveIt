import DiophantineConsistency.ArithmeticAdaptiveMainOrientation2011
import DiophantineConsistency.ArithmeticAdaptiveMainCongruence2011
import DiophantineConsistency.ArithmeticAdaptiveRankCongruence2011

/-! Private additive compatibility for two upstream helper declarations, built
against the historical 87 provider. The declarations and proofs are copied
from the post-merge source; they extend the same namespaces. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency
open DiophantineConsistency.AdaptiveEquationSyntax2011
open DiophantineConsistency.ArithmeticSignedPairs
open DiophantineConsistency.ArithmeticAdaptiveFactorMagnitude2011
open DiophantineConsistency.ArithmeticAdaptiveScaledNorms2011
open DiophantineConsistency.ArithmeticAdaptiveQuotients2011
open DiophantineConsistency.ArithmeticAdaptiveTransport2011
open DiophantineConsistency.ArithmeticAdaptiveFirstDivisibility2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
namespace DiophantineConsistency.ArithmeticAdaptiveFirstDivisibility2011
theorem mod_cancel {a b c m : V} (hm : 0<m) (h : (a+c)%m=(b+c)%m) : a%m=b%m := by
  have hr := le_of_lt (mod_lt c hm)
  have hc : c+(m-c%m)=m*(c/m+1) := by
    calc
      c+(m-c%m)=(m*(c/m)+c%m)+(m-c%m) := by rw [div_add_mod]
      _=m*(c/m)+(c%m+(m-c%m)) := by ring
      _=m*(c/m)+m := by rw [add_tsub_cancel_of_le hr]
      _=m*(c/m+1) := by ring
  have hh : ((a+c)+(m-c%m))%m=((b+c)+(m-c%m))%m := by
    rw [mod_add (a:=a+c) hm,mod_add (a:=b+c) hm,h]
  simpa only [add_assoc,hc,mod_add_mul' _ _ hm] using hh

theorem magnitude_mod (p : Pair V) (m : V) (hm : 0<m)
    (hd : m∣magnitude p) : p.1 % m = p.2 % m := by
  have hz : magnitude p % m = 0 := mod_eq_zero_iff_dvd.mpr hd
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


theorem positive_Y_quotient_of_facts (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hM : 0<(1+v 0*(p 0:V))*((1+v 0*(p 0:V))*(1+v 0*(p 0:V)))*(v 0*(p 0:V)))
    (hY : 0<v 7) (hquotients : Quotients p v) :
    ∃ s : V, 0<s ∧ v 7 =
      ((1+v 0*(p 0:V))*((1+v 0*(p 0:V))*(1+v 0*(p 0:V))))*s := by
  have hq : 0<1+v 0*(p 0:V) := by simp
  have hQ := mul_pos hq (mul_pos hq hq)
  obtain ⟨t,d,_,_,ht,_,_,_⟩ := hquotients
  obtain ⟨s,hs⟩ := quotient_forces_Y_divisible p v hM hQ t ht
  exact ⟨s,pos_of_mul_pos_right (by rw [←hs]; exact hY) (by simp),hs⟩

end DiophantineConsistency.ArithmeticAdaptiveFirstDivisibility2011
namespace DiophantineConsistency.ArithmeticAdaptiveMainOrientation2011
theorem main_oriented_of_facts (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hquotients : Quotients p v) (htransport : TransportPositive p v)
    (hY : ∃ s : V, 0<s ∧ v 7 =
      ((1+v 0*(p 0:V))*((1+v 0*(p 0:V))*(1+v 0*(p 0:V))))*s) :
    MainOriented p v := by
  let b : V := v 0*(p 0:V)
  let q : V := 1+b
  let Q : V := q*(q*q)
  let U : V := v 7*(q*q)
  let E : V := v 6*v 7
  let k : V := v 9+v 10
  let c : V := v 9+v 7*k
  let a : V := E+v 7
  let H : V := 3+4*a
  let R : V := (v 2+(q-v 1)*b)*(q*q-1)+v 0*((p 2:V)+(p 3:V)*q)
  let dp : V := U*(v 6+a*c)+H*(U*v 12+E*q+R+1)
  let dn : V := H*k
  let z := pairEval (rootTerm (factors (fun j => (p j:ℤ))).2.1) v
  have hp := scaled_parameters_positive p v hb hv
  have hq : 1<q := hp.1
  have hq1 : (1:V)≤q := le_of_lt hq
  have hq2 : (2:V)≤q := by simpa only [one_add_one_eq_two] using lt_iff_succ_le.mp hq
  have hU : 0<U := hp.2.2.1
  have hk : 0<k := hp.2.2.2.1
  have hsum : v 1+v 2<q := tsub_pos_iff_lt.mp htransport.2
  have hF : v 1≤q := le_trans (by simp : v 1≤v 1+v 2) (le_of_lt hsum)
  obtain ⟨s,hs,hsY⟩ := hY
  have hQ8 : (8:V)≤Q := calc
    8=2*(2*2) := by norm_num
    _≤q*(q*q) := mul_le_mul hq2 (mul_le_mul hq2 hq2 (by simp) (by simp)) (by simp) (by simp)
  have hY8 : (8:V)≤v 7 := calc
    8≤Q := hQ8
    _≤Q*s := le_mul_of_one_le_right (by simp) (pos_iff_one_le.mp hs)
    _=v 7 := hsY.symm
  have hpos : dn<dp := main_parts_positive U (v 6) (v 7) k (v 9) (v 12) q R hU hY8 hk
  obtain ⟨first,main,_,hmainp,_,_,hmain,hnorm⟩ := hquotients
  have hre : Equivalent z (dp,dn) := main_root_rep p v hq1 hF
  have hmag : magnitude z=magnitude (dp,dn) := magnitude_equivalent hre
  have heq : dp=dn+(dp-dn) := by rw [add_comm,tsub_add_cancel_of_le (le_of_lt hpos)]
  have hcan : magnitude (dp,dn)=dp-dn := magnitude_of_add heq
  have hdiff : dp-dn=U*main := hcan.symm.trans (hmag.symm.trans hmain)
  have hpart : Equivalent (dp,dn) (natural (U*main)) := by
    change dp+0=dn+U*main
    simpa only [add_zero,hdiff] using heq
  refine ⟨main,hmainp,equivalent_trans hre hpart,?_⟩
  exact hnorm


end DiophantineConsistency.ArithmeticAdaptiveMainOrientation2011

open DiophantineConsistency.ArithmeticAdaptiveMainOrientation2011
namespace DiophantineConsistency.ArithmeticAdaptiveMainCongruence2011
theorem main_congruence_of_facts (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (htransport : TransportPositive p v)
    (hYquotient : ∃ s : V, 0<s ∧ v 7 =
      ((1+v 0*(p 0:V))*((1+v 0*(p 0:V))*(1+v 0*(p 0:V))))*s)
    (horientation : MainOriented p v) : MainCongruence p v := by
  let b : V := v 0*(p 0:V)
  let q : V := 1+b
  let U : V := v 7*(q*q)
  let E : V := v 6*v 7
  let k : V := v 9+v 10
  let c : V := v 9+v 7*k
  let a : V := E+v 7
  let H : V := 3+4*a
  let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
  let R' : V := (v 2+(q-v 1)*b)*(q*q-1)+v 0*((p 2:V)+(p 3:V)*q)
  have hq : 1≤q := by dsimp [q]; simp
  have hgap : v 1+v 2<q := tsub_pos_iff_lt.mp htransport.2
  have hF : v 1≤q := le_trans (by simp : v 1≤v 1+v 2) (le_of_lt hgap)
  have hbq : q-1=b := by dsimp [q]; rw [add_comm]; simp
  have hR : R=R' := by dsimp [R,R']; rw [hbq]; simp only [pow_two]; ring
  obtain ⟨s,hs,hsY⟩ := hYquotient
  have hY : v 7=q^3*s := by simpa only [pow_succ,pow_zero,one_mul,mul_assoc] using hsY
  have hU : U=q^5*s := by dsimp [U]; rw [hY]; ring
  obtain ⟨main,hm,horient,_⟩ := horientation
  have hrep := main_root_rep p v hq hF
  have he := equivalent_trans (equivalent_symm hrep) horient
  change (U*(v 6+a*c)+H*(U*v 12+E*q+R'+1))+0 = H*k+U*main at he
  simp only [add_zero] at he
  rw [←hR,hU] at he
  refine ⟨s,main,hs,hm,hY,?_⟩
  calc
    H*(E*q+R+1)+q^5*(s*(v 6+a*c+H*v 12)) =
        q^5*s*(v 6+a*c)+H*(q^5*s*v 12+E*q+R+1) := by ring
    _=H*k+q^5*s*main := he
    _=H*k+q^5*(s*main) := by ring


end DiophantineConsistency.ArithmeticAdaptiveMainCongruence2011

open DiophantineConsistency.ArithmeticAdaptiveMainCongruence2011
open DiophantineConsistency.ArithmeticAdaptiveFactorThree2011
namespace DiophantineConsistency.ArithmeticAdaptiveRankCongruence2011
private theorem congruence_divides_difference {x y m : V} (hm : 0<m)
    (hyx : y≤x) (h : x%m=y%m) : m∣x-y := by
  apply mod_eq_zero_iff_dvd.mp
  have he : x-y+y=x := tsub_add_cancel_of_le hyx
  have hh : ((x-y)+y)%m=(0+y)%m := by
    rw [he,zero_add]
    exact h
  have hc := mod_cancel hm hh
  simpa only [zero_mod] using hc

private theorem dvd_magnitude_of_mod {m x y : V} (hm : 0<m) (h : x%m=y%m) :
    m∣magnitude (x,y) := by
  rcases le_total y x with hle | hle
  · have he : x=y+(x-y) := by rw [add_comm,tsub_add_cancel_of_le hle]
    have hg : magnitude (x,y)=x-y := magnitude_of_add he
    rw [hg]
    exact congruence_divides_difference hm hle h
  · have he : y=x+(y-x) := by rw [add_comm,tsub_add_cancel_of_le hle]
    have hg : magnitude (x,y)=y-x := by
      have h' := magnitude_of_add he
      change magnitude (swap (x,y))=y-x at h'
      simpa only [magnitude_swap] using h'
    rw [hg]
    exact congruence_divides_difference hm hle h.symm

theorem rank_congruence_of_main (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hmain : MainCongruence p v) : RankCongruence p v := by
  let q : V := 1+v 0*(p 0:V)
  let E : V := v 6*v 7
  let k : V := v 9+v 10
  let a : V := E+v 7
  let H : V := 3+4*a
  let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
  let T : V := E*q+R+1
  have hq : 0<q := by dsimp [q]; simp
  have hm5 : 0<q^5 := pow_pos hq _
  have hm4 : 0<q^4 := pow_pos hq _
  obtain ⟨s,main,_,_,hy,he⟩ := hmain
  have hemod : (H*T)%(q^5)=(H*k)%(q^5) := by
    have h := congrArg (fun z : V => z%(q^5)) he
    rw [mod_add_mul' _ _ hm5,mod_add_mul' _ _ hm5] at h
    exact h
  have hdiv : q^5∣H*magnitude (T,k) := by
    have h := dvd_magnitude_of_mod hm5 hemod
    have heq : magnitude (H*T,H*k)=H*magnitude (T,k) := by
      dsimp [magnitude]
      rw [mul_add H (T-k) (k-T),mul_tsub H T k,mul_tsub H k T]
    rwa [heq] at h
  have hcoef : H=3+4*v 7*(v 6+1) := by dsimp [H,a,E]; ring
  rw [hcoef] at hdiv
  have hY : q^3∣v 7 := ⟨s,hy⟩
  have hT : q^4∣magnitude (T,k) := cancel_factor_three q (v 7) (v 6) _ hq hY hdiv
  have hTmod := magnitude_mod (T,k) (q^4) hm4 hT
  have hEq : q^4∣E*q := by
    refine ⟨v 6*s,?_⟩
    dsimp [E]; rw [hy]; ring
  have hTR : T=E*q+(R+1) := by dsimp [T]; ring
  rw [hTR,mod_add_remove_left_of_dvd hEq hm4] at hTmod
  exact dvd_magnitude_of_mod hm4 hTmod


end DiophantineConsistency.ArithmeticAdaptiveRankCongruence2011
