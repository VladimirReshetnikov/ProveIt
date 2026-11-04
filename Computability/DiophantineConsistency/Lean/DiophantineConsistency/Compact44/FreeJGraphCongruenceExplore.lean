import DiophantineConsistency.Compact44.CompactGraphDerivedRadix
import DiophantineConsistency.ArithmeticModularCancellation
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FreeJGraphCongruenceExplore
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs Ordinary12FreeJ
open ArithmeticAdaptiveFirstDivisibility2011 ArithmeticAdaptiveFactorMagnitude2011 FreeJRootBinding
open ArithmeticRepunit ArithmeticWindowDigits CompactSymbolicPorts
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem first_pair_mod (p : Fin 4 → ℕ) (v : Fin 12 → V)
    (hb : 0<(p 0:V)) (hv : ∀ j,0<v j)
    (hz : InternalZero (literal (fun j => (p j:ℤ))) v) :
    let b : V := v 0*(p 0:V)
    let q : V := 1+b
    let A : V := v 5+(p 1:V)*q
    ((v 1+v 2)*A+v 1*q)%b=(q*A)%b := by
  let b : V := v 0*(p 0:V)
  let q : V := 1+b
  let Q : V := q*(q*q)
  let k : V := v 8+v 9
  let ell : V := (v 5*v 6)*(v 6*k)
  let M : V := Q*b
  let W : V := 1+k*b
  let A : V := v 5+(p 1:V)*q
  let Bp : V := q*A
  let Bn : V := (v 1+v 2)*A+v 1*q
  have hb0 : 0<b := mul_pos (hv 0) hb
  have hq : 0<q := by dsimp [q,b]; simp
  have hQ : 0<Q := mul_pos hq (mul_pos hq hq)
  have hM : 0<M := mul_pos hQ hb0
  obtain ⟨t,ht⟩ := first_root_quotient p v hz hM
  have hdiv : M∣magnitude (pairEval (core (fun j => (p j:ℤ))).z v) := ⟨t,ht⟩
  have hzmod := magnitude_mod _ M hM hdiv
  have hp := equivalent_mod hM (root_rep p v) hzmod
  change (M*(ell+k+v 7)+v 6*b+Bn*(W*Q))%M = (Bp*(W*Q))%M at hp
  obtain ⟨s,hs⟩ := first_factor_forces_Y_divisible p v hz (hv 0) hb
  have hs' : v 6=Q*s := by
    rw [hs]
    dsimp [Q,q,b]
    ring
  have he1 : M*(ell+k+v 7)+v 6*b+Bn*(W*Q) = Q*(b*(ell+k+v 7+s)+Bn*W) := by rw [hs']; dsimp [M]; ring
  have he2 : Bp*(W*Q)=Q*(Bp*W) := by ring
  rw [he1,he2] at hp
  rw [ArithmeticModularCancellation.mul_mod_mul hQ hb0,ArithmeticModularCancellation.mul_mod_mul hQ hb0] at hp
  have hc : (b*(ell+k+v 7+s)+Bn*W)%b=(Bp*W)%b := mul_left_cancel₀ (ne_of_gt hQ) hp
  have hc' : (Bn*W)%b=(Bp*W)%b := by
    rw [add_comm, mod_add_mul' _ _ hb0] at hc
    exact hc
  have hW1 : Bn*W=Bn+b*(Bn*k) := by dsimp [W]; ring
  have hW2 : Bp*W=Bp+b*(Bp*k) := by dsimp [W]; ring
  rw [hW1,hW2] at hc'
  simpa only [mod_add_mul' _ _ hb0] using hc'

theorem graph_congruence (p : Fin 4 → ℕ) (v : Fin 12 → V) (w : V)
    (hb : 0<(p 0:V)) (hv : ∀ j,0<v j)
    (hz : InternalZero (literal (fun j => (p j:ℤ))) v)
    (hw : v 5=(1+v 0*(p 0:V))*w) :
    let b : V := v 0*(p 0:V)
    let q : V := 1+b
    0<b ∧ v 1<b ∧ (((p 1:V)+w)*(q-v 1-v 2))%b=v 1 := by
  let b : V := v 0*(p 0:V)
  let q : V := 1+b
  let A : V := v 5+(p 1:V)*q
  let C : V := q-v 1-v 2
  have hb0 : 0<b := mul_pos (hv 0) hb
  have hg : v 1+v 2<q := tsub_pos_iff_lt.mp (FreeJFirstTransport.freej_first_factor_transport p v hb hv hz).2
  have hlt : v 1<b := by
    have hle : v 1+1 ≤ v 1+v 2 := by simpa only [add_comm] using add_le_add_left (pos_iff_one_le.mp (hv 2)) (v 1)
    have h1 : v 1+1 < 1+b := lt_of_le_of_lt hle hg
    rw [add_comm (v 1) 1] at h1
    exact (add_lt_add_iff_left 1).mp h1
  have hC : v 1+v 2+C=q := by
    dsimp [C]
    rw [tsub_tsub,add_comm,tsub_add_cancel_of_le (le_of_lt hg)]
  have hp := first_pair_mod p v hb hv hz
  change ((v 1+v 2)*A+v 1*q)%b=(q*A)%b at hp
  have hqA : q*A=(v 1+v 2)*A+C*A := by rw [←hC]; ring
  rw [hqA] at hp
  have hmod : (v 1*q)%b=(C*A)%b := by
    apply mod_cancel hb0 (c := (v 1+v 2)*A)
    simpa only [add_comm] using hp
  have hF : (v 1*q)%b=v 1 := by
    have he : v 1*q=v 1+b*(v 1) := by dsimp [q]; ring
    rw [he,mod_add_mul' _ _ hb0,mod_eq_self_of_lt hlt]
  have hA : A=q*(w+(p 1:V)) := by dsimp [A,q,b] at hw ⊢; rw [hw]; ring
  have hCA : C*A=C*(w+(p 1:V))+b*(C*(w+(p 1:V))) := by rw [hA]; dsimp [q]; ring
  rw [hF,hCA,mod_add_mul' _ _ hb0] at hmod
  refine ⟨hb0,hlt,?_⟩
  change (((p 1:V)+w)*C)%b=v 1
  simpa only [add_comm,mul_comm] using hmod.symm

theorem graph_aligned_congruence (p : Fin 4 → ℕ) (v : Fin 12 → V) (d : V)
    (hb : 0<(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀ j,0<v j) (hz : InternalZero (literal (fun j => (p j:ℤ))) v)
    (hbeta : (46:V)≤(p 0:V)) (hd : 4≤d) (hport : (p 0:V)=Exp.exp d-1) :
    let q : V := 1+v 0*(p 0:V)
    let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
    ∃ N w : V, 0<N ∧ q=Exp.exp (d*N) ∧ d*N≤R ∧
      w=Exp.exp (R-d*N) ∧ v 5=q*w ∧
      0<v 0*(p 0:V) ∧ v 1<v 0*(p 0:V) ∧
      (((p 1:V)+w)*(q-v 1-v 2))%(v 0*(p 0:V))=v 1 := by
  obtain ⟨N,w,hN,hq,hle,hw,hv5⟩ := FreeJRadixAlignment.graph_alignment p v d hb hl hh hv hz hbeta hd hport
  obtain ⟨hpos,hbound,hcongr⟩ := graph_congruence p v w hb hv hz hv5
  exact ⟨N,w,hN,hq,hle,hw,hv5,hpos,hbound,hcongr⟩

theorem symbolic_aligned (B K L H : ℕ) (v : Fin 12 → V)
    (hB : (B:V)+1=Exp.exp ((67:V)*8807)) (hL : L=lowNat) (hH : H=highNat)
    (hv : ∀ j,0<v j)
    (hz : InternalZero (literal (fun j => (ports B K L H j:ℤ))) v) :
    let q : V := 1+v 0*(ports B K L H 0:V)
    let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((ports B K L H 2:V)+q*(ports B K L H 3:V))*v 0
    let C : V := q-v 1-v 2
    ∃ N w : V, 0<N ∧ q=Exp.exp ((67*8807)*N) ∧ v 0=rep (67*8807) N ∧
      (67*8807)*N≤R ∧ w=Exp.exp (R-(67*8807)*N) ∧ v 5=q*w ∧
      0<v 0*(ports B K L H 0:V) ∧ v 1<v 0*(ports B K L H 0:V) ∧
      (((ports B K L H 1:V)+w)*C)%(v 0*(ports B K L H 0:V))=v 1 ∧
      dig 67 C 0=1 ∧ ∀ k<8807*N, dig 67 C k≤3 := by
  let d : V := 67*8807
  obtain ⟨hb',hl',hh',_⟩ := CompactMaskBoundFinish.bounds (B:V) (v 0) hB (hv 0)
  have hb : 0<(ports B K L H 0:V) := by change 0<(B:V); exact hb'
  have hl : (ports B K L H 2:V)<(ports B K L H 0:V) := by
    change (L:V)<(B:V)
    rw [hL]
    exact hl'
  have hh : (ports B K L H 3:V)<2*(ports B K L H 0:V) := by
    change ((B+H:ℕ):V)<2*(B:V)
    rw [Nat.cast_add,hH]
    exact hh'
  have h64 : (64:V)=Exp.exp (6:V) := by
    have h := ArithmeticStandardCasts.cast_exp (V:=V) 6
    norm_num at h
    exact h.symm
  have hbig : (64:V)≤(B:V)+1 := by
    rw [hB,h64]
    exact exp_monotone_le.mpr (by norm_num)
  have hbeta : (46:V)≤(ports B K L H 0:V) := by
    change (46:V)≤(B:V)
    apply le_iff_lt_succ.mpr
    exact lt_of_lt_of_le (by norm_num : (46:V)<64) hbig
  have hport : (ports B K L H 0:V)=Exp.exp d-1 := by
    change (B:V)=Exp.exp d-1
    rw [←hB,add_tsub_cancel_right]
  obtain ⟨N,w,hN,hq,hle,hw,hv5,hpos,hbound,hcongr⟩ := graph_aligned_congruence
    (ports B K L H) v d hb hl hh hv hz hbeta (by dsimp [d]; norm_num) hport
  have hJ : v 0=rep d N := by
    apply ArithmeticRepunit.eq_rep_of_identity (by dsimp [d]; norm_num)
    calc (Exp.exp d-1)*v 0+1 = 1+v 0*(ports B K L H 0:V) := by rw [←hport]; ring
      _ = Exp.exp (d*N) := hq
  have hdigits := CompactGenericGraphDigits.graph_digits B K L H v N hB hL hH hv hz hN hq hJ
  exact ⟨N,w,hN,hq,hJ,hle,hw,hv5,hpos,hbound,hcongr,hdigits⟩

theorem fixed_symbolic_aligned (K : ℕ) (v : Fin 12 → V)
    (hv : ∀ j,0<v j)
    (hz : InternalZero (literal (fun j => (ports CompactFixedBeta.betaNat K lowNat highNat j:ℤ))) v) :
    let p := ports CompactFixedBeta.betaNat K lowNat highNat
    let q : V := 1+v 0*(p 0:V)
    let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
    let C : V := q-v 1-v 2
    ∃ N w : V, 0<N ∧ q=Exp.exp ((67*8807)*N) ∧ v 0=rep (67*8807) N ∧
      (67*8807)*N≤R ∧ w=Exp.exp (R-(67*8807)*N) ∧ v 5=q*w ∧
      0<v 0*(p 0:V) ∧ v 1<v 0*(p 0:V) ∧
      (((p 1:V)+w)*C)%(v 0*(p 0:V))=v 1 ∧
      dig 67 C 0=1 ∧ ∀ k<8807*N, dig 67 C k≤3 := by
  exact symbolic_aligned CompactFixedBeta.betaNat K lowNat highNat v CompactFixedBeta.beta_identity rfl rfl hv hz
end FreeJGraphCongruenceExplore
#print axioms FreeJGraphCongruenceExplore.fixed_symbolic_aligned
#print axioms FreeJGraphCongruenceExplore.symbolic_aligned
#print axioms FreeJGraphCongruenceExplore.first_pair_mod
#print axioms FreeJGraphCongruenceExplore.graph_congruence
#print axioms FreeJGraphCongruenceExplore.graph_aligned_congruence
