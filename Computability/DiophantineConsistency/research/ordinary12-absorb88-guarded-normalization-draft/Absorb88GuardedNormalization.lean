import Absorb88NormalizationRing
import Absorb88Conditional
import Absorb88MainRoot

/-! Draft: conditional negative-branch normalization to an 89 graph zero. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace Absorb88GuardedNormalization
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency FreeJAbsorb88 Absorb88First Absorb88FirstQuotient
open AdaptiveEquationSyntax2011 ModelDifferenceRing Absorb88NormalizationRing
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def replaced (v : Fin 12 → V) (Fnew anew rnew : V) : Fin 12 → V :=
  Function.update (Function.update (Function.update v 1 Fnew) 2 anew) 7 rnew

theorem exists_89_of_normalization_guard (p : Fin 4 → ℕ) (v : Fin 12 → V)
    (hb : 0<(p 0:V)) (hv : ∀i,0<v i)
    (hz : InternalZero (graph (integerPorts p)).output v)
    (j u Fnew anew t : V) (hF : 0<Fnew) (ha : 0<anew) (ht : 0<t)
    (hFsplit : v 1=Fnew+(v 0*(p 0:V))*j)
    (hasplit : v 2=anew+(v 0*(p 0:V))*(v 0*(p 0:V))*j)
    (htsplit : (1+v 0*(p 0:V))*((1+v 0*(p 0:V))*((p 1:V)+v 5)+1)*j=u+t)
    (hU : let b : V := v 0*(p 0:V); let q : V := 1+b; let A : V := (p 1:V)+v 5
      (ι q : DiffRing V)*(ι ((v 1+v 2)*A+v 1)-ι (q*A))=ι b*ι u) :
    ∃w : Fin 12 → V, (∀i,0<w i) ∧
      InternalZero (FreeJAbsorb89.graph (integerPorts p)).output w := by
  let b : V := v 0*(p 0:V)
  let q : V := 1+b
  let X : V := q*v 5
  let Y : V := (q*(q*q))*v 6
  let P : V := (X*Y)*Y
  let k : V := v 8+v 9
  let A : V := (p 1:V)+v 5
  let D : V := q*(q*A+1)
  let Bp : V := q*A
  let Bn : V := (v 1+v 2)*A+v 1
  let z : Fin 12 → DiffRing V := fun i => ι (v i)
  have hb0 : 0<b := mul_pos (hv 0) hb
  obtain ⟨first,hfirst,_,hnorm⟩ := first_root p v hz hb0
  let rnew : V := first+(1+k*b)*t
  let w := replaced v Fnew anew rnew
  have hfmap : (ι Fnew : DiffRing V)=ι (v 1)-ι b*ι j := by
    change v 1=Fnew+b*j at hFsplit
    have h := congrArg (fun x : V => (ι x : DiffRing V)) hFsplit
    simp only [map_add,map_mul] at h
    linarith
  have hamap : (ι anew : DiffRing V)=ι (v 2)-ι b*ι b*ι j := by
    change v 2=anew+b*b*j at hasplit
    have h := congrArg (fun x : V => (ι x : DiffRing V)) hasplit
    simp only [map_add,map_mul] at h
    linarith
  have htmap : (ι t : DiffRing V)=ι D*ι j-ι u := by
    have h := congrArg (fun x : V => (ι x : DiffRing V)) htsplit
    change (ι (D*j) : DiffRing V)=ι (u+t) at h
    simp only [map_add,map_mul] at h
    linarith
  have hp0 : (((integerPorts p) 0:ℤ):DiffRing V)=ι (p 0:V) := by simp [integerPorts]
  have hp1 : (((integerPorts p) 1:ℤ):DiffRing V)=ι (p 1:V) := by simp [integerPorts]
  have hval : (fun i => (ι (w i) : DiffRing V)) = normalize (integerPorts p) z (ι j) (ι u) (ι first) := by
    funext i
    by_cases hi1 : i=1
    · subst i
      simpa [w,replaced,norm_1,z,hp0,b,map_mul] using hfmap
    · by_cases hi2 : i=2
      · subst i
        simpa [w,replaced,norm_2,z,hp0,b,map_mul] using hamap
      · by_cases hi7 : i=7
        · subst i
          simp only [w,replaced,Function.update_self,norm_7,z,hp0,hp1,rnew,map_add,map_mul,map_one]
          have hh := congrArg (fun x : DiffRing V => ι first+(1+ι k*ι b)*x) htmap
          simpa only [D,q,A,k,b,map_add,map_mul,map_one] using hh
        · simp [w,replaced,Absorb88NormalizationRing.normalize,z,hi1,hi2,hi7]
  have htr : let br := z 0*((integerPorts p) 0:DiffRing V); let qr := 1+br
      let Ar := ((integerPorts p) 1:DiffRing V)+z 5
      qr*((qr-z 1-z 2)*Ar-z 1) = -br*(ι u) := by
    dsimp only
    rw [hp0,hp1]
    simp only [z,←map_mul]
    change (1+ι b)*(((1+ι b)-ι (v 1)-ι (v 2))*(ι (p 1:V)+ι (v 5))-ι (v 1)) = -ι b*ι u
    change (ι q : DiffRing V)*(ι Bn-ι Bp)=ι b*ι u at hU
    simp only [q,Bn,Bp,A,map_add,map_mul,map_one] at hU
    linear_combination -hU
  have hn : let qr := 1+z 0*((integerPorts p) 0:DiffRing V)
      let xr := qr*z 5; let yr := qr*(qr*qr)*z 6
      let Pr := (xr*yr)*yr; let kr := z 8+z 9
      (ι first : DiffRing V)*ι first=1+Pr*(Pr+1)*kr*kr := by
    have hh := congrArg (fun x : V => (ι x : DiffRing V)) hnorm
    simp only [map_add,map_mul,map_one] at hh
    dsimp only
    rw [hp0]
    exact hh
  have hwpos : ∀i,0<w i := by
    intro i
    by_cases hi1 : i=1
    · subst i; simpa [w,replaced] using hF
    · by_cases hi2 : i=2
      · subst i; simpa [w,replaced] using ha
      · by_cases hi7 : i=7
        · subst i
          have hr : 0<rnew := add_pos_of_pos_of_nonneg hfirst (by positivity)
          simpa [w,replaced] using hr
        · simpa [w,replaced,hi1,hi2,hi7] using hv i
  have hmain : (graph (integerPorts p)).main.evalRing z=0 := by
    have hh := Absorb88MainRoot.main_zero p v hz
    rw [internalZero_iff] at hh
    have hp : Absorb89Main.integerPorts p=integerPorts p := by rfl
    rw [hp,←Absorb88MainRoot.main_same] at hh
    exact hh
  have hord : (graph (integerPorts p)).ordinary.evalRing z=0 := by
    have hh := hz
    rw [internalZero_iff] at hh
    have hshape : (graph (integerPorts p)).output=(graph (integerPorts p)).first*(graph (integerPorts p)).first+
        (graph (integerPorts p)).main*(graph (integerPorts p)).main+
        (graph (integerPorts p)).ordinary*(graph (integerPorts p)).ordinary := by rfl
    rw [hshape] at hh
    simp only [Expr.evalRing_add,Expr.evalRing_mul] at hh
    have h1 := sq_nonneg ((graph (integerPorts p)).first.evalRing z)
    have h2 := sq_nonneg ((graph (integerPorts p)).main.evalRing z)
    have h3 := sq_nonneg ((graph (integerPorts p)).ordinary.evalRing z)
    have hs : (graph (integerPorts p)).ordinary.evalRing z*(graph (integerPorts p)).ordinary.evalRing z=0 := by nlinarith
    exact mul_self_eq_zero.mp hs
  have hwzero : InternalZero (graph (integerPorts p)).output w := by
    rw [internalZero_iff,hval]
    have hshape : (graph (integerPorts p)).output=(graph (integerPorts p)).first*(graph (integerPorts p)).first+
        (graph (integerPorts p)).main*(graph (integerPorts p)).main+
        (graph (integerPorts p)).ordinary*(graph (integerPorts p)).ordinary := by rfl
    rw [hshape]
    simp only [Expr.evalRing_add,Expr.evalRing_mul]
    rw [Absorb88NormalizationRing.first_zero (integerPorts p) z (ι j) (ι u) (ι first) htr hn,
      main_invariant,ordinary_invariant,hmain,hord]
    ring
  have hbound : (w 1+w 2)*((p 1:V)+w 5)+w 1 < (1+w 0*(p 0:V))*((p 1:V)+w 5) := by
    apply ι_lt_ι.mp
    have hbpos : (0:DiffRing V)<ι b := by rw [←map_zero ι,ι_lt_ι]; exact hb0
    have htpos : (0:DiffRing V)<ι t := by rw [←map_zero ι,ι_lt_ι]; exact ht
    have hqpos : (0:DiffRing V)<ι q := by rw [←map_zero ι,ι_lt_ι]; dsimp [q]; simp
    have hmul := mul_pos hbpos htpos
    have hnew := new_transport (integerPorts p) z (ι j) (ι u) (ι first) htr
    rw [←hval,hp0,hp1] at hnew
    simp only [z] at hnew
    simp [w,replaced] at hnew
    have hbmap : (ι b : DiffRing V)=ι (v 0)*(p 0:DiffRing V) := by simp only [b,map_mul,map_natCast]
    rw [←hbmap] at hnew
    have hD : (ι D : DiffRing V)=(1+ι b)*((1+ι b)*((p 1:DiffRing V)+ι (v 5))+1) := by
      simp only [D,q,A,map_add,map_mul,map_one,map_natCast]
    rw [←hD,←htmap] at hnew
    simp [w,replaced,map_add,map_mul,map_one] at ⊢
    rw [←hbmap] at ⊢
    by_contra hnot
    have hnonpos : (0:DiffRing V)≥((1+ι b)*((p 1:DiffRing V)+ι (v 5))-
        ((ι Fnew+ι anew)*((p 1:DiffRing V)+ι (v 5))+ι Fnew)) := by linarith only [hnot]
    have hbad := mul_nonpos_of_nonneg_of_nonpos hqpos.le hnonpos
    have hqmap : (ι q : DiffRing V)=1+ι b := by simp only [q,map_add,map_one]
    rw [hqmap] at hbad
    have hbad' : (1+ι b)*((1+ι b-ι Fnew-ι anew)*((p 1:DiffRing V)+ι (v 5))-ι Fnew)≤0 := by
      have hid : (1+ι b)*((1+ι b-ι Fnew-ι anew)*((p 1:DiffRing V)+ι (v 5))-ι Fnew) =
          (1+ι b)*((1+ι b)*((p 1:DiffRing V)+ι (v 5))-
            ((ι Fnew+ι anew)*((p 1:DiffRing V)+ι (v 5))+ι Fnew)) := by ring
      rw [hid]
      exact hbad
    rw [hnew] at hbad'
    exact (not_le_of_gt hmul) hbad'
  exact Absorb88Conditional.exists_89_of_transport p hb ⟨w,hwpos,hwzero,hbound⟩

#print axioms Absorb88GuardedNormalization.exists_89_of_normalization_guard
end Absorb88GuardedNormalization
