import DiophantineConsistency.FreeJFirstTransport
import DiophantineConsistency.ArithmeticAdaptiveMainOrientation2011
import DiophantineConsistency.ArithmeticAdaptiveRankCongruence2011
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace FreeJMainOrientation
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency.AdaptiveEquationSyntax2011
open DiophantineConsistency.ArithmeticSignedPairs
open DiophantineConsistency.ArithmeticSignedPairExpressions
open DiophantineConsistency.ArithmeticAdaptiveFactorMagnitude2011
open DiophantineConsistency.ArithmeticAdaptiveScaledNorms2011
open DiophantineConsistency.ArithmeticAdaptiveQuotients2011
open DiophantineConsistency.ArithmeticAdaptiveTransport2011
open DiophantineConsistency.ArithmeticAdaptiveMainOrientation2011
open DiophantineConsistency.ArithmeticAdaptiveFactorThree2011
open DiophantineConsistency.ArithmeticAdaptiveFirstDivisibility2011
open DiophantineConsistency.Ordinary12FreeJ
open FreeJRootBinding FreeJFirstTransport
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem freej_main_root_rep (p : Fin 4 → ℕ) (v : Fin 12 → V)
    (hq : 1≤1+v 0*(p 0:V)) (hF : v 1≤1+v 0*(p 0:V)) :
    let b : V := v 0*(p 0:V)
    let q : V := 1+b
    let U : V := v 6*(q*q)
    let E : V := v 5*v 6
    let k : V := v 8+v 9
    let c : V := v 8+v 6*k
    let a : V := E+v 6
    let H : V := 3+4*a
    let R : V := (v 2+(q-v 1)*b)*(q*q-1)+v 0*((p 2:V)+(p 3:V)*q)
    Equivalent (pairEval (core (fun j => (p j:ℤ))).d v)
      (U*(v 5+a*c)+H*(U*v 11+E*q+R+1),H*k) := by
  let eB : Expr (Fin 12) := .mul (.var 0) (.constant (p 0))
  let eQ : Expr (Fin 12) := .add (.constant 1) eB
  let eU : Expr (Fin 12) := .mul (.var 6) (.mul eQ eQ)
  let eE : Expr (Fin 12) := .mul (.var 5) (.var 6)
  let eK : Expr (Fin 12) := .add (.var 8) (.var 9)
  let eC : Expr (Fin 12) := .add (.var 8) (.mul (.var 6) eK)
  let eA : Expr (Fin 12) := .add eE (.var 6)
  let eH : Expr (Fin 12) := .add (.constant 3) (.mul (.constant 4) eA)
  let eR : Expr (Fin 12) := .add
    (.mul (.add (.var 2) (.mul (.sub eQ (.var 1)) eB)) (.sub (.mul eQ eQ) (.constant 1)))
    (.mul (.var 0) (.add (.constant (p 2)) (.mul (.constant (p 3)) eQ)))
  let eD : Expr (Fin 12) := .add
    (.mul eU (.add (.var 5) (.mul eA eC)))
    (.mul eH (.sub (.add (.mul eU (.var 11)) (.mul eE eQ))
      (.sub (.sub eK eR) (.constant 1))))
  let b : V := v 0*(p 0:V)
  let q : V := 1+b
  let U : V := v 6*(q*q)
  let E : V := v 5*v 6
  let k : V := v 8+v 9
  let c : V := v 8+v 6*k
  let a : V := E+v 6
  let H : V := 3+4*a
  let R : V := (v 2+(q-v 1)*b)*(q*q-1)+v 0*((p 2:V)+(p 3:V)*q)
  have hB : SignedRep eB v (natural b) := rep_mul_nat (rep_var v 0) (rep_nat v (p 0))
  have hQ : SignedRep eQ v (natural q) := rep_add_nat (rep_one v) hB
  have hU : SignedRep eU v (natural U) := rep_mul_nat (rep_var v 6) (rep_mul_nat hQ hQ)
  have hE : SignedRep eE v (natural E) := rep_mul_nat (rep_var v 5) (rep_var v 6)
  have hK : SignedRep eK v (natural k) := rep_add_nat (rep_var v 8) (rep_var v 9)
  have hC : SignedRep eC v (natural c) := rep_add_nat (rep_var v 8) (rep_mul_nat (rep_var v 6) hK)
  have hA : SignedRep eA v (natural a) := rep_add_nat hE (rep_var v 6)
  have hH : SignedRep eH v (natural H) := rep_add_nat (rep_three v) (rep_mul_nat (rep_four v) hA)
  have hq2 : (1:V)≤q*q := by simpa only [one_mul] using mul_le_mul hq hq (by simp) (by simp)
  have hR : SignedRep eR v (natural R) := rep_add_nat
    (rep_mul_nat (rep_add_nat (rep_var v 2) (rep_mul_nat (rep_tsub hQ (rep_var v 1) hF) hB))
      (rep_tsub (rep_mul_nat hQ hQ) (rep_one v) hq2))
    (rep_mul_nat (rep_var v 0) (rep_add_nat (rep_nat v (p 2)) (rep_mul_nat (rep_nat v (p 3)) hQ)))
  have hneg : SignedRep (.sub (.sub eK eR) (.constant 1)) v (k,R+1) := by
    have h := rep_sub (rep_sub hK hR) (rep_one v)
    simpa only [minus,natural,add_zero,zero_add,Nat.cast_one,add_assoc] using h
  have hshift : SignedRep (.sub (.add (.mul eU (.var 11)) (.mul eE eQ))
      (.sub (.sub eK eR) (.constant 1))) v (U*v 11+E*q+R+1,k) := by
    have h := rep_sub (rep_add_nat (rep_mul_nat hU (rep_var v 11)) (rep_mul_nat hE hQ)) hneg
    simpa only [minus,natural,add_zero,zero_add,add_assoc] using h
  have hD := rep_add (rep_mul_nat hU (rep_add_nat (rep_var v 5) (rep_mul_nat hA hC)))
    (rep_mul hH hshift)
  change SignedRep eD v (U*(v 5+a*c)+H*(U*v 11+E*q+R+1),H*k)
  simpa only [plus,multiply,natural,add_zero,zero_add,mul_zero,zero_mul] using hD



def main_rhs (p : Fin 4 → ℤ) : Expr (Fin 12) :=
  let b : Expr (Fin 12) := .mul (.var 0) (.constant (p 0))
  let q : Expr (Fin 12) := .add (.constant 1) b
  let u : Expr (Fin 12) := .mul (.var 6) (.mul q q)
  let k : Expr (Fin 12) := .add (.var 8) (.var 9)
  let c : Expr (Fin 12) := .add (.var 8) (.mul (.var 6) k)
  let a : Expr (Fin 12) := .add (.mul (.var 5) (.var 6)) (.var 6)
  let d : Expr (Fin 12) := .add (.add (.constant 3) (.mul (.constant 4) a)) (.mul a a)
  .mul (.mul u u) (.add (.constant 1) (.mul d (.mul c c)))

theorem main_shape (p : Fin 4 → ℤ) : (core p).main =
    1+((core p).d*(core p).d-main_rhs p) := by rfl

theorem main_rhs_pair (p : Fin 4 → ℕ) (v : Fin 12 → V) :
    let q : V := 1+v 0*(p 0:V)
    let U : V := v 6*(q*q)
    let k : V := v 8+v 9
    let c : V := v 8+v 6*k
    let a : V := v 5*v 6+v 6
    let delta : V := (3+4*a)+a*a
    pairEval (main_rhs (fun j => (p j:ℤ))) v = (U*U*(1+delta*(c*c)),0) := by
  simp [main_rhs,pairEval,Expr.splitNatural,NatExpr.evalSemiring]

theorem main_scaled_norm (p : Fin 4 → ℕ) (v : Fin 12 → V)
    (hz : InternalZero (literal (fun j => (p j:ℤ))) v) :
    let q : V := 1+v 0*(p 0:V)
    let U : V := v 6*(q*q)
    let k : V := v 8+v 9
    let c : V := v 8+v 6*k
    let a : V := v 5*v 6+v 6
    let delta : V := (3+4*a)+a*a
    magnitude (pairEval (core (fun j => (p j:ℤ))).d v)*
      magnitude (pairEval (core (fun j => (p j:ℤ))).d v) = U*U*(1+delta*(c*c)) := by
  have h := (literal_factor_units (fun j => (p j:ℤ)) v hz).2.1
  rw [main_shape] at h
  have hs := unit_square_norm _ _ v h
  rw [main_rhs_pair p v] at hs
  simpa only [Prod.fst,Prod.snd,add_zero] using hs


/-- The actual first and main factors orient the free-J main root, without
assuming any Pell rank or strong-norm equation. -/
theorem main_oriented (p : Fin 4 → ℕ) (v : Fin 12 → V)
    (hb : 0 < (p 0:V)) (hv : ∀ j, 0 < v j)
    (hz : InternalZero (literal (fun j => (p j:ℤ))) v) :
    let q : V := 1+v 0*(p 0:V)
    let U : V := v 6*(q*q)
    let k : V := v 8+v 9
    let c : V := v 8+v 6*k
    let a : V := v 5*v 6+v 6
    let delta : V := (3+4*a)+a*a
    ∃ main : V, 0<main ∧
      Equivalent (pairEval (core (fun j => (p j:ℤ))).d v) (natural (U*main)) ∧
      main*main=1+delta*(c*c) := by
  let b : V := v 0*(p 0:V)
  let q : V := 1+b
  let Q : V := q*(q*q)
  let U : V := v 6*(q*q)
  let E : V := v 5*v 6
  let k : V := v 8+v 9
  let c : V := v 8+v 6*k
  let a : V := E+v 6
  let H : V := 3+4*a
  let R : V := (v 2+(q-v 1)*b)*(q*q-1)+v 0*((p 2:V)+(p 3:V)*q)
  let dp : V := U*(v 5+a*c)+H*(U*v 11+E*q+R+1)
  let dn : V := H*k
  let z := pairEval (core (fun j => (p j:ℤ))).d v
  have hb0 : 0<b := mul_pos (hv 0) hb
  have hq : 1<q := lt_add_of_pos_right _ hb0
  have hq1 : (1:V)≤q := le_of_lt hq
  have hq2 : (2:V)≤q := by simpa only [one_add_one_eq_two] using lt_iff_succ_le.mp hq
  have hU : 0<U := mul_pos (hv 6) (mul_pos (lt_trans (by simp) hq) (lt_trans (by simp) hq))
  have hk : 0<k := add_pos (hv 8) (hv 9)
  have htransport := freej_first_factor_transport p v hb hv hz
  have hsum : v 1+v 2<q := tsub_pos_iff_lt.mp htransport.2
  have hF : v 1≤q := le_trans (by simp : v 1≤v 1+v 2) (le_of_lt hsum)
  obtain ⟨s,hsY⟩ := first_factor_forces_Y_divisible p v hz (hv 0) hb
  have hs : 0<s := pos_of_mul_pos_right (by rw [←hsY]; exact hv 6) (by simp)
  have hQ8 : (8:V)≤Q := calc
    8=2*(2*2) := by norm_num
    _≤q*(q*q) := mul_le_mul hq2 (mul_le_mul hq2 hq2 (by simp) (by simp)) (by simp) (by simp)
  have hY8 : (8:V)≤v 6 := calc
    8≤Q := hQ8
    _≤Q*s := le_mul_of_one_le_right (by simp) (pos_iff_one_le.mp hs)
    _=v 6 := by rw [hsY]; congr 1 <;> ring
  have hpos : dn<dp := main_parts_positive U (v 5) (v 6) k (v 8) (v 11) q R hU hY8 hk
  obtain ⟨main,hmain,hnorm⟩ := scaled_quotient _ _ _ hU (main_scaled_norm p v hz)
  have hmainp : 0<main := pos_of_mul_pos_left (by rw [hnorm]; simp) (by simp)
  have hre : Equivalent z (dp,dn) := freej_main_root_rep p v hq1 hF
  have hmag : magnitude z=magnitude (dp,dn) := magnitude_equivalent hre
  have heq : dp=dn+(dp-dn) := by rw [add_comm,tsub_add_cancel_of_le (le_of_lt hpos)]
  have hcan : magnitude (dp,dn)=dp-dn := magnitude_of_add heq
  have hdiff : dp-dn=U*main := hcan.symm.trans (hmag.symm.trans hmain)
  have hpart : Equivalent (dp,dn) (natural (U*main)) := by
    change dp+0=dn+U*main
    simpa only [add_zero,hdiff] using heq
  exact ⟨main,hmainp,equivalent_trans hre hpart,hnorm⟩

def FreeJMainCongruence (p : Fin 4 → ℕ) (v : Fin 12 → V) : Prop :=
  let q : V := 1+v 0*(p 0:V)
  let E : V := v 5*v 6
  let k : V := v 8+v 9
  let c : V := v 8+v 6*k
  let a : V := E+v 6
  let H : V := 3+4*a
  let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
  ∃ s main : V, 0<s ∧ 0<main ∧ v 6=q^3*s ∧
    H*(E*q+R+1)+q^5*(s*(v 5+a*c+H*v 11)) = H*k+q^5*(s*main)

/-- Positive transport, the Y quotient, and main orientation give the additive congruence. -/
theorem main_congruence (p : Fin 4 → ℕ) (v : Fin 12 → V)
    (hb : 0<(p 0:V)) (hv : ∀ j, 0<v j)
    (hz : InternalZero (literal (fun j => (p j:ℤ))) v) : FreeJMainCongruence p v := by
  let b : V := v 0*(p 0:V)
  let q : V := 1+b
  let U : V := v 6*(q*q)
  let E : V := v 5*v 6
  let k : V := v 8+v 9
  let c : V := v 8+v 6*k
  let a : V := E+v 6
  let H : V := 3+4*a
  let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
  let R' : V := (v 2+(q-v 1)*b)*(q*q-1)+v 0*((p 2:V)+(p 3:V)*q)
  have htransport := freej_first_factor_transport p v hb hv hz
  have horientation := main_oriented p v hb hv hz
  have hdiv := first_factor_forces_Y_divisible p v hz (hv 0) hb
  obtain ⟨s,hsY'⟩ := hdiv
  have hs : 0<s := pos_of_mul_pos_right (by rw [←hsY']; exact hv 6) (by simp)
  have hYquotient : ∃ s : V, 0<s ∧ v 6 = q*(q*q)*s := by
    refine ⟨s,hs,?_⟩
    rw [hsY']
    congr 1 <;> ring
  have hq : 1≤q := by dsimp [q]; simp
  have hgap : v 1+v 2<q := tsub_pos_iff_lt.mp htransport.2
  have hF : v 1≤q := le_trans (by simp : v 1≤v 1+v 2) (le_of_lt hgap)
  have hbq : q-1=b := by dsimp [q]; rw [add_comm]; simp
  have hR : R=R' := by dsimp [R,R']; rw [hbq]; simp only [pow_two]; ring
  obtain ⟨s,hs,hsY⟩ := hYquotient
  have hY : v 6=q^3*s := by simpa only [pow_succ,pow_zero,one_mul,mul_assoc] using hsY
  have hU : U=q^5*s := by dsimp [U]; rw [hY]; ring
  obtain ⟨main,hm,horient,_⟩ := horientation
  have hrep := freej_main_root_rep p v hq hF
  have he := equivalent_trans (equivalent_symm hrep) horient
  change (U*(v 5+a*c)+H*(U*v 11+E*q+R'+1))+0 = H*k+U*main at he
  simp only [add_zero] at he
  rw [←hR,hU] at he
  refine ⟨s,main,hs,hm,hY,?_⟩
  calc
    H*(E*q+R+1)+q^5*(s*(v 5+a*c+H*v 11)) =
        q^5*s*(v 5+a*c)+H*(q^5*s*v 11+E*q+R+1) := by ring
    _=H*k+q^5*s*main := he
    _=H*k+q^5*(s*main) := by ring



def FreeJRankCongruence (p : Fin 4 → ℕ) (v : Fin 12 → V) : Prop :=
  let q : V := 1+v 0*(p 0:V)
  let k : V := v 8+v 9
  let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
  q^4∣magnitude (R+1,k)

/-- The main-root congruence implies the signed rank congruence. -/
theorem rank_congruence_from_main (p : Fin 4 → ℕ) (v : Fin 12 → V)
    (hmain : FreeJMainCongruence p v) : FreeJRankCongruence p v := by
  let q : V := 1+v 0*(p 0:V)
  let E : V := v 5*v 6
  let k : V := v 8+v 9
  let a : V := E+v 6
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
  have hcoef : H=3+4*v 6*(v 5+1) := by dsimp [H,a,E]; ring
  rw [hcoef] at hdiv
  have hY : q^3∣v 6 := ⟨s,hy⟩
  have hT : q^4∣magnitude (T,k) := cancel_factor_three q (v 6) (v 5) _ hq hY hdiv
  have hTmod := magnitude_mod (T,k) (q^4) hm4 hT
  have hEq : q^4∣E*q := by
    refine ⟨v 5*s,?_⟩
    dsimp [E]; rw [hy]; ring
  have hTR : T=E*q+(R+1) := by dsimp [T]; ring
  rw [hTR,mod_add_remove_left_of_dvd hEq hm4] at hTmod
  exact dvd_magnitude_of_mod hm4 hTmod



/-- The signed q⁴ congruence follows from the exact free-J zero without
assuming rank, strong norm, a fixed beta value, or checker calibration. -/
theorem rank_congruence (p : Fin 4 → ℕ) (v : Fin 12 → V)
    (hb : 0<(p 0:V)) (hv : ∀ j, 0<v j)
    (hz : InternalZero (literal (fun j => (p j:ℤ))) v) : FreeJRankCongruence p v :=
  rank_congruence_from_main p v (main_congruence p v hb hv hz)

end FreeJMainOrientation
#print axioms FreeJMainOrientation.freej_main_root_rep
#print axioms FreeJMainOrientation.main_shape
#print axioms FreeJMainOrientation.main_rhs_pair
#print axioms FreeJMainOrientation.main_scaled_norm
#print axioms FreeJMainOrientation.main_oriented
#print axioms FreeJMainOrientation.main_congruence
#print axioms FreeJMainOrientation.rank_congruence_from_main
#print axioms FreeJMainOrientation.rank_congruence
