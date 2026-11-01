import DiophantineConsistency.AdaptiveGap85Factors
import DiophantineConsistency.AdaptiveDirectOrdinate86FixedForward
import Mathlib.Tactic.Ring

/-! Construct the actual first factor from arbitrary positive first-norm data.
Other factors and full zeros are deliberately not asserted. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 12000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
namespace DiophantineConsistency.AdaptiveGap85FirstNormCompletion
open AdaptiveGap85Factors AdaptiveGap85Literal ArithmeticAdaptiveScaledNorms2011
attribute [local irreducible] CurrentMasks2011.beta CurrentKernel2011.K

def ports (beta K mu nu : ℤ) : Fin 4 → ℤ := ![beta,K,mu,nu]
def witness (J beta K X Y eta zeta t first f i T y gamma : ℤ) : Fin 13 → ℤ :=
  let b := J*beta
  let q := 1+b
  let A := X+K*q
  let k := eta+zeta
  let ell := (X*Y)*(Y*k)
  let s := ell+k+t+1
  let C := b*q*(s+1)
  let F := b*((s+1)*(A-1)+1)
  let r := first+k*(b*q*s)+b*s+1
  ![J,F,C,f,i,T,X,Y,r,eta,zeta,y,gamma]

theorem first_factor_algebra (b q A k ell Y t first : ℤ)
    (hq : q=1+b) (hY : Y=q^3*t) (hnorm : first^2=1+ell*(ell+k)) :
    let s := ell+k+t+1
    let C := b*q*(s+1)
    let F := b*((s+1)*(A-1)+1)
    let r := first+k*(b*q*s)+b*s+1
    let B := C*A-F*q
    let M := q^3*b
    let Z := M*(ell+k+r-k*B)+Y*b-B*q^3
    1+Z^2-M^2*(1+ell*(ell+k))=1 := by
  dsimp only
  let s := ell+k+t+1
  let C := b*q*(s+1)
  let F := b*((s+1)*(A-1)+1)
  let r := first+k*(b*q*s)+b*s+1
  let B := C*A-F*q
  let M := q^3*b
  let Z := M*(ell+k+r-k*B)+Y*b-B*q^3
  change 1+Z^2-M^2*(1+ell*(ell+k))=1
  have hB : B=b*q*s := by dsimp [B,C,F]; ring
  have hZ : Z=M*first := by
    dsimp [Z,r,M]
    rw [hB,hY,hq]
    dsimp [s]
    ring
  rw [hZ,mul_pow,hnorm]
  ring

theorem first_factor_completion (J beta K X Y eta zeta t first f i T y gamma mu nu : ℤ)
    (hY : Y=(1+J*beta)^3*t)
    (hnorm : first^2=1+((X*Y)*(Y*(eta+zeta)))*(((X*Y)*(Y*(eta+zeta)))+(eta+zeta))) :
    ((factors (ports beta K mu nu)).1).eval (witness J beta K X Y eta zeta t first f i T y gamma)=1 := by
  have h := first_factor_algebra (J*beta) (1+J*beta) (X+K*(1+J*beta)) (eta+zeta)
    ((X*Y)*(Y*(eta+zeta))) Y t first rfl hY hnorm
  simp [factors,Expr.eval,ports,witness,pow_succ,mul_assoc] at h ⊢
  omega

/-- The completion is positive and sits outside the reverse gap. -/
theorem positive_completion (J beta K X Y eta zeta t first f i T y gamma : ℤ)
    (hJ : 1≤J) (hb : 1≤beta) (hK : 0≤K) (hX : 1≤X) (hY : 1≤Y)
    (heta : 1≤eta) (hzeta : 1≤zeta) (ht : 1≤t) (hfirst : 1≤first)
    (hf : 1≤f) (hi : 1 ≤ i) (hT : 1≤T) (hy : 1≤y) (hgamma : 1≤gamma) :
    let v := witness J beta K X Y eta zeta t first f i T y gamma
    (∀ j, 0<v j) ∧ ¬(v 1+v 2<1+J*beta) := by
  let b := J*beta
  let q := 1+b
  let A := X+K*q
  let k := eta+zeta
  let ell := (X*Y)*(Y*k)
  let s := ell+k+t+1
  have hbpos : 0<b := mul_pos (by omega) (by omega)
  have hqpos : 0<q := by dsimp [q]; omega
  have hA : 1≤A := by dsimp [A]; have := mul_nonneg hK (le_of_lt hqpos); omega
  have hk : 0<k := by dsimp [k]; omega
  have hell : 0<ell := by dsimp [ell]; exact mul_pos (mul_pos (by omega) (by omega)) (mul_pos (by omega) hk)
  have hs : 0<s := by dsimp [s]; omega
  have hC : 0<b*q*(s+1) := by positivity
  have hF : 0<b*((s+1)*(A-1)+1) := by positivity
  have hr : 0<first+k*(b*q*s)+b*s+1 := by positivity
  have hqle : q≤b*q*(s+1) := by nlinarith [mul_nonneg (by omega : 0≤b-1) (by positivity : 0≤q), mul_nonneg (by omega : 0≤s) (le_of_lt hqpos), mul_nonneg (le_of_lt hbpos) (by positivity : 0≤q*s)]
  constructor
  · intro j
    fin_cases j <;> simp [witness] <;> assumption
  · simp [witness]
    change q≤b*((s+1)*(A-1)+1)+b*q*(s+1)
    omega

/-- At the literal ports the same completion works for every positive first-norm
configuration and every positive quotient witnessing the required cubic divisibility.
It does not assert any remaining factor is one. -/
theorem current_first_completion (J X Y eta zeta t first f i T y gamma : ℤ)
    (hJ : 1≤J) (hX : 1≤X) (hYpos : 1≤Y)
    (heta : 1≤eta) (hzeta : 1≤zeta) (ht : 1≤t) (hfirst : 1≤first)
    (hf : 1≤f) (hi : 1 ≤ i) (hT : 1≤T) (hy : 1≤y) (hgamma : 1≤gamma)
    (hY : Y=(1+J*(currentPorts 0:ℤ))^3*t)
    (hnorm : first^2=1+((X*Y)*(Y*(eta+zeta)))*(((X*Y)*(Y*(eta+zeta)))+(eta+zeta))) :
    ∃ v : Fin 13 → ℤ, (∀ j,0<v j) ∧ ¬(v 1+v 2<1+v 0*(currentPorts 0:ℤ)) ∧
      ((factors CurrentWindowCarry2011.ports).1).eval v=1 := by
  let beta : ℤ := currentPorts 0
  let K : ℤ := currentPorts 1
  let mu : ℤ := currentPorts 2
  let nu : ℤ := currentPorts 3
  have hbetaNat : 1≤currentPorts 0 := by
    have hb := ArithmeticAdaptiveRankWindow2011.current_bounds_nat.1
    change 1≤CurrentMasks2011.beta
    omega
  have hbeta : 1≤beta := by dsimp [beta]; exact_mod_cast hbetaNat
  have hK : 0≤K := by dsimp [K]; exact Int.natCast_nonneg _
  have hp : ports beta K mu nu=CurrentWindowCarry2011.ports := by
    rw [←currentPorts_cast]
    funext j
    fin_cases j <;> rfl
  let v := witness J beta K X Y eta zeta t first f i T y gamma
  have hv := positive_completion J beta K X Y eta zeta t first f i T y gamma
    hJ hbeta hK hX hYpos heta hzeta ht hfirst hf hi hT hy hgamma
  have he := first_factor_completion J beta K X Y eta zeta t first f i T y gamma mu nu hY hnorm
  rw [hp] at he
  exact ⟨v,hv.1,hv.2,he⟩

/-- For the convenient choice f=i=1, the strong factor is strictly larger
than one; the constructed partial first-factor configuration is not a full zero. -/
theorem unit_fi_nonzero (J beta K X Y eta zeta t first T y gamma mu nu : ℤ)
    (hY : 0<Y) (heta : 0<eta) (hzeta : 0<zeta) :
    (expressionAt85 (ports beta K mu nu)).eval
      (witness J beta K X Y eta zeta t first 1 1 T y gamma) ≠ 0 := by
  let v := witness J beta K X Y eta zeta t first 1 1 T y gamma
  let p := ports beta K mu nu
  let c := eta+Y*(eta+zeta)
  have hc : 0<c := by dsimp [c]; positivity
  have hs : ((factors p).2.2.2).eval v = 1+(c*c)*(c*c) := by
    simp [factors,Expr.eval,ports,witness,p,v,c]
  have hspos : 1<((factors p).2.2.2).eval v := by
    rw [hs]
    have hsq : 0<(c*c)*(c*c) := mul_pos (mul_pos hc hc) (mul_pos hc hc)
    omega
  intro hz
  change (expressionAt85 p).eval v=0 at hz
  rw [expression_factors] at hz
  change ((factors p).2.2.2).eval v *
    (((factors p).2.2.1).eval v * (((factors p).1).eval v*((factors p).2.1).eval v))-1=0 at hz
  have hd : ((factors p).2.2.2).eval v ∣ (1:ℤ) := by
    refine ⟨((factors p).2.2.1).eval v * (((factors p).1).eval v*((factors p).2.1).eval v),?_⟩
    omega
  have hle := Int.le_of_dvd (by norm_num : (0:ℤ)<1) hd
  omega

/-- Setting f=i=1 makes the fixed-port first-factor completion a genuine
nonzero of the full polynomial, not a counterexample to its reverse implication. -/
theorem current_partial_nonzero (J X Y eta zeta t first T y gamma : ℤ)
    (hJ : 1≤J) (hX : 1≤X) (hYpos : 1≤Y)
    (heta : 1≤eta) (hzeta : 1≤zeta) (ht : 1≤t) (hfirst : 1≤first)
    (hT : 1≤T) (hy : 1≤y) (hgamma : 1≤gamma)
    (hY : Y=(1+J*(currentPorts 0:ℤ))^3*t)
    (hnorm : first^2=1+((X*Y)*(Y*(eta+zeta)))*(((X*Y)*(Y*(eta+zeta)))+(eta+zeta))) :
    ∃ v : Fin 13 → ℤ, (∀ j,0<v j) ∧ ¬(v 1+v 2<1+v 0*(currentPorts 0:ℤ)) ∧
      ((factors CurrentWindowCarry2011.ports).1).eval v=1 ∧
      (expressionAt85 CurrentWindowCarry2011.ports).eval v ≠ 0 := by
  let beta : ℤ := currentPorts 0
  let K : ℤ := currentPorts 1
  let mu : ℤ := currentPorts 2
  let nu : ℤ := currentPorts 3
  have hbetaNat : 1≤currentPorts 0 := by
    have hb := ArithmeticAdaptiveRankWindow2011.current_bounds_nat.1
    change 1≤CurrentMasks2011.beta
    omega
  have hbeta : 1≤beta := by dsimp [beta]; exact_mod_cast hbetaNat
  have hK : 0≤K := by dsimp [K]; exact Int.natCast_nonneg _
  have hp : ports beta K mu nu=CurrentWindowCarry2011.ports := by
    rw [←currentPorts_cast]
    funext j
    fin_cases j <;> rfl
  let v := witness J beta K X Y eta zeta t first 1 1 T y gamma
  have hv := positive_completion J beta K X Y eta zeta t first 1 1 T y gamma
    hJ hbeta hK hX hYpos heta hzeta ht hfirst (by omega) (by omega) hT hy hgamma
  have he := first_factor_completion J beta K X Y eta zeta t first 1 1 T y gamma mu nu hY hnorm
  have hn := unit_fi_nonzero J beta K X Y eta zeta t first T y gamma mu nu (by omega) (by omega) (by omega)
  rw [hp] at he hn
  exact ⟨v,hv.1,hv.2,he,hn⟩

end DiophantineConsistency.AdaptiveGap85FirstNormCompletion
