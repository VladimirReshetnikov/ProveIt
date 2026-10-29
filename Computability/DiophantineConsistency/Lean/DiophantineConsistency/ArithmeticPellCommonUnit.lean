import DiophantineConsistency.ArithmeticGcdNormalization
import DiophantineConsistency.ArithmeticPellKnownUnit

/-! Actual relaxed-norm common-unit coordinates and represented composition.
Both indices and the common base are derived in the internal IΣ1 model.
Strong divisibility, large-index forcing and full relaxed integrality remain
separate; no desired index, gcd, coprimality or fundamental unit is supplied. -/
set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticPellCommonUnit
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPellRecurrence
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem parameter_norm (a : V) : (a+2)*(a+2)=1+delta a := by
  unfold delta
  ring

/-- A coordinate identity derives the discriminant relation. Both composition
identities are proved together by Sigma1 induction at arbitrary internal p. -/
theorem composition (a b e : V) (hA : a+2=xcoord e b) :
    ∀ p : V, xcoord p a=xcoord (e*p) b ∧
      ycoord p a*ycoord e b=ycoord (e*p) b := by
  have hd : delta a=delta b*ycoord e b*ycoord e b := by
    apply add_left_cancel (a := (1:V))
    calc
      1+delta a=(a+2)*(a+2) := (parameter_norm a).symm
      _=xcoord e b*xcoord e b := by rw [hA]
      _=1+delta b*ycoord e b*ycoord e b := norm e b
  intro p
  induction p using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ p ih =>
    constructor
    · calc
        xcoord (p+1) a=(a+2)*xcoord p a+delta a*ycoord p a := x_succ p a
        _=xcoord (e*p) b*xcoord e b+
            delta b*ycoord (e*p) b*ycoord e b := by
          rw [←ih.1,←ih.2,←hA,hd]
          ring
        _=xcoord (e*p+e) b := (addition (e*p) e b).1.symm
        _=xcoord (e*(p+1)) b := by congr 1; ring
    · calc
        ycoord (p+1) a*ycoord e b=
            (xcoord p a+(a+2)*ycoord p a)*ycoord e b := by rw [y_succ]
        _=xcoord (e*p) b*ycoord e b+
            ycoord (e*p) b*xcoord e b := by
          rw [←ih.1,←ih.2,←hA]
          ring
        _=ycoord (e*p+e) b := (addition (e*p) e b).2.symm
        _=ycoord (e*(p+1)) b := by congr 1; ring

/-- The actual norm gives two solutions at one discriminant. One invocation
of known-unit classification supplies the same base and scale for both. -/
theorem common_unit_setup (a R f : V) (hR : 0<R) (hf : 0<f)
    (hn : R*R+delta a=delta a*(f*f)) :
    ∃ b e n S : V, 0<e ∧ 0<n ∧ 0<S ∧ S<a+2 ∧
      S=ycoord e b ∧ a+2=xcoord e b ∧ f=xcoord n b ∧
      delta a=delta b*S*S ∧ R=delta b*S*ycoord n b := by
  have hD : 0<delta a := by unfold delta; exact mul_pos (by simp) (by simp)
  have hA : 1<a+2 := lt_of_lt_of_le (by simp : (1:V)<2) (by simp)
  obtain ⟨d,s,t,hdp,hsp,htp,hd,hr,hfsol⟩ :=
    ArithmeticGcdNormalization.norm_normalization R (delta a) f hR hD hf hn
  have hseed : (a+2)*(a+2)=1+s*d*d := by
    simpa only [hd,mul_comm,mul_left_comm,mul_assoc] using parameter_norm a
  obtain ⟨b,v,hvp,_,_,hb,hclass⟩ :=
    ArithmeticPellKnownUnit.known_unit_classification s (a+2) d hsp hA hdp hseed
  obtain ⟨e,_,he,hed⟩ := hclass (a+2) d hseed
  obtain ⟨n,_,hfn,htn⟩ := hclass f t hfsol
  have hep : 0<e := pos_iff_ne_zero.mpr (fun he => (ne_of_gt hdp) (by simpa [he] using hed))
  have hnp : 0<n := pos_iff_ne_zero.mpr (fun hn => (ne_of_gt htp) (by simpa [hn] using htn))
  let S := ycoord e b
  change d=v*S at hed
  have hSp : 0<S := pos_of_mul_pos_right (by rw [← hed]; exact hdp) (by simp)
  have hdb : delta b=s*v*v := add_left_cancel ((parameter_norm b).symm.trans hb)
  have hdelta : delta a=delta b*S*S := by
    rw [hd,hed,hdb]
    ring
  have hRform : R=delta b*S*ycoord n b := by
    rw [hr,hed,htn,hdb]
    ring
  have hSbound : S<a+2 := by
    have hd1 : 1≤delta b := pos_iff_one_le.mp (by unfold delta; exact mul_pos (by simp) (by simp))
    apply lt_of_mul_self_lt_mul_self₀ (Arithmetic.zero_le (a+2))
    calc
      S*S<1+S*S := by simpa only [add_comm] using lt_add_one (S*S)
      _≤1+delta b*S*S := by
        have hm : S*S≤delta b*S*S := by
          simpa only [mul_assoc] using le_mul_of_one_le_left
            (Arithmetic.zero_le (S*S)) hd1
        exact add_le_add (le_refl (1:V)) hm
      _=xcoord e b*xcoord e b := (norm e b).symm
      _=(a+2)*(a+2) := by rw [he]
  exact ⟨b,e,n,S,hep,hnp,hSp,hSbound,rfl,he,hfn,hdelta,hRform⟩

/-- Actual norm setup and both composition identities use the same witnesses. -/
theorem common_unit_composition (a R f : V) (hR : 0<R) (hf : 0<f)
    (hn : R*R+delta a=delta a*(f*f)) :
    ∃ b e n S : V, 0<e ∧ 0<n ∧ 0<S ∧ S<a+2 ∧
      S=ycoord e b ∧ a+2=xcoord e b ∧ f=xcoord n b ∧
      delta a=delta b*S*S ∧ R=delta b*S*ycoord n b ∧
      ∀ p : V, xcoord p a=xcoord (e*p) b ∧
        ycoord p a*S=ycoord (e*p) b := by
  obtain ⟨b,e,n,S,hep,hnp,hSp,hSA,hS,he,hf',hD,hR'⟩ :=
    common_unit_setup a R f hR hf hn
  refine ⟨b,e,n,S,hep,hnp,hSp,hSA,hS,he,hf',hD,hR',?_⟩
  simpa only [hS] using composition a b e he

/-- The literal truncated input is converted only after f>0 justifies it. -/
theorem common_unit_tsub (a R f : V) (hR : 0<R) (hf : 0<f)
    (hn : R*R=delta a*(f*f-1)) :
    ∃ b e n S : V, 0<e ∧ 0<n ∧ 0<S ∧ S<a+2 ∧
      S=ycoord e b ∧ a+2=xcoord e b ∧ f=xcoord n b ∧
      delta a=delta b*S*S ∧ R=delta b*S*ycoord n b ∧
      ∀ p : V, xcoord p a=xcoord (e*p) b ∧
        ycoord p a*S=ycoord (e*p) b := by
  exact common_unit_composition a R f hR hf
    (ArithmeticGcdNormalization.norm_tsub_to_add (delta a) f R hf hn)
end DiophantineConsistency.ArithmeticPellCommonUnit
