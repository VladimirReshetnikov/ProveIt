import DiophantineConsistency.ArithmeticAdaptiveQuotients2011

/-! Literal first-root signed-pair transport to q³-divisibility, in every IΣ₁
model. No sign of the first root or positive transport gap is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptiveFirstDivisibility2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticGcdNormalization
open ArithmeticAdaptiveFactorMagnitude2011 ArithmeticAdaptiveScaledNorms2011
open ArithmeticAdaptiveQuotients2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.radix CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

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

theorem equivalent_mod {p q : Pair V} {m : V} (hm : 0<m)
    (he : Equivalent p q) (hp : p.1%m=p.2%m) : q.1%m=q.2%m := by
  have hh := congrArg (fun t : V => t%m) he
  change (p.1+q.2)%m=(p.2+q.1)%m at hh
  rw [mod_add (a:=p.1) (b:=q.2) hm,mod_add (a:=p.2) (b:=q.1) hm] at hh
  rw [←hp] at hh
  have hh' : (q.2+p.2)%m=(q.1+p.2)%m := by
    rw [mod_add (a:=q.2) (b:=p.2) hm,mod_add (a:=q.1) (b:=p.2) hm,←hp]
    simpa only [add_comm] using hh
  exact (mod_cancel hm hh').symm

theorem mod_mod_dvd {m n : V} (hm : 0<m) (h : m∣n) (a : V) :
    a%n%m=a%m := by
  conv_rhs => rw [← div_add_mod a n]
  rw [mod_add_remove_left_of_dvd (dvd_mul_of_dvd_left h _) hm]

/-- This exact internal pair represents the actual signed first root. -/
theorem first_root_rep (p : Fin 4 → ℕ) (v : Fin 13 → V) :
    let b : V := v 0*(p 0:V)
    let q : V := 1+b
    let Q : V := q*(q*q)
    let k : V := v 9+v 10
    let ell : V := (v 6*v 7)*(v 7*k)
    let M : V := Q*b
    let W : V := 1+k*b
    let A : V := v 6+(p 1:V)*q
    let Bp : V := q*A
    let Bn : V := (v 1+v 2)*A+v 1*q
    Equivalent (pairEval (rootTerm (factors (fun j => (p j:ℤ))).1) v)
      (M*(ell+k+v 8)+v 7*b+Bn*(W*Q),Bp*(W*Q)) := by
  let eB : Expr (Fin 13) := .mul (.var 0) (.constant (p 0))
  let eQ : Expr (Fin 13) := .add (.constant 1) eB
  let eQ3 : Expr (Fin 13) := .mul eQ (.mul eQ eQ)
  let eK : Expr (Fin 13) := .add (.var 9) (.var 10)
  let eL : Expr (Fin 13) := .mul (.mul (.var 6) (.var 7)) (.mul (.var 7) eK)
  let eM : Expr (Fin 13) := .mul eQ3 eB
  let eW : Expr (Fin 13) := .add (.constant 1) (.mul eK eB)
  let eC : Expr (Fin 13) := .sub (.sub eQ (.var 1)) (.var 2)
  let eA : Expr (Fin 13) := .add (.var 6) (.mul (.constant (p 1)) eQ)
  let eBt : Expr (Fin 13) := .sub (.mul eC eA) (.mul (.var 1) eQ)
  let eZ : Expr (Fin 13) := .sub
    (.add (.mul eM (.add (.add eL eK) (.var 8))) (.mul (.var 7) eB))
    (.mul eBt (.mul eW eQ3))
  change Equivalent (pairEval eZ v) _
  simp [eZ,eBt,eA,eC,eW,eM,eL,eK,eQ3,eQ,eB,pairEval,Expr.splitNatural,
    NatExpr.evalSemiring,Equivalent]
  all_goals ring

/-- The signed root's actual quotient forces q³ to divide Y; no sign of
that root or transport factor is imposed. -/
theorem quotient_forces_Y_divisible (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hM : 0<(1+v 0*(p 0:V))*((1+v 0*(p 0:V))*(1+v 0*(p 0:V)))*(v 0*(p 0:V)))
    (hQ : 0<(1+v 0*(p 0:V))*((1+v 0*(p 0:V))*(1+v 0*(p 0:V))))
    (t : V)
    (ht : magnitude (pairEval (rootTerm (factors (fun j => (p j:ℤ))).1) v) =
      ((1+v 0*(p 0:V))*((1+v 0*(p 0:V))*(1+v 0*(p 0:V)))*(v 0*(p 0:V)))*t) :
    (1+v 0*(p 0:V))*((1+v 0*(p 0:V))*(1+v 0*(p 0:V))) ∣ v 7 := by
  let b : V := v 0*(p 0:V)
  let q : V := 1+b
  let Q : V := q*(q*q)
  let k : V := v 9+v 10
  let ell : V := (v 6*v 7)*(v 7*k)
  let M : V := Q*b
  let W : V := 1+k*b
  let A : V := v 6+(p 1:V)*q
  let Bp : V := q*A
  let Bn : V := (v 1+v 2)*A+v 1*q
  let z := pairEval (rootTerm (factors (fun j => (p j:ℤ))).1) v
  have hdiv : M∣magnitude z := ⟨t,ht⟩
  have hzmod := magnitude_mod z M hM hdiv
  have hpair := equivalent_mod hM (first_root_rep p v) hzmod
  change (M*(ell+k+v 8)+v 7*b+Bn*(W*Q))%M = (Bp*(W*Q))%M at hpair
  have hdQM : Q∣M := ⟨b,rfl⟩
  have hQpair := congrArg (fun x : V => x%Q) hpair
  rw [mod_mod_dvd hQ hdQM,mod_mod_dvd hQ hdQM] at hQpair
  have hleft : M*(ell+k+v 8)+v 7*b+Bn*(W*Q) =
      v 7*b+Q*(b*(ell+k+v 8)+Bn*W) := by dsimp only [M]; ring
  have hright : Bp*(W*Q)=Q*(Bp*W) := by ring
  have hzero : (Q*(Bp*W))%Q=0 := by rw [mul_comm]; exact mod_mul_self_left _ _
  rw [hleft,hright,mod_add_mul' _ _ hQ,hzero] at hQpair
  have hby : Q∣b*v 7 := by
    apply mod_eq_zero_iff_dvd.mp
    change (v 7*b)%Q=0 at hQpair
    rw [mul_comm b (v 7)]
    exact hQpair
  have hunit : Bez b Q 1 := by
    refine ⟨q*q+q+1,0,0,1,?_⟩
    dsimp only [q,Q]
    ring
  exact unit_certificate_cancel hunit hby

/-- A literal positive zero constructs the positive block quotient of Y. -/
theorem expressionAt_Y_quotient (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : InternalZero (expressionAt (fun j => (p j:ℤ))) v) :
    ∃ s : V, 0<s ∧ v 7 =
      ((1+v 0*(p 0:V))*((1+v 0*(p 0:V))*(1+v 0*(p 0:V))))*s := by
  have hparams := scaled_parameters_positive p v hb hv
  obtain ⟨t,d,_,_,ht,_,_,_⟩ := expressionAt_quotients p v hb hv hz
  have hq : 0<1+v 0*(p 0:V) := lt_trans (by simp : (0:V)<1) hparams.1
  have hQ : 0<(1+v 0*(p 0:V))*((1+v 0*(p 0:V))*(1+v 0*(p 0:V))) :=
    mul_pos hq (mul_pos hq hq)
  obtain ⟨s,hs⟩ := quotient_forces_Y_divisible p v hparams.2.1 hQ t ht
  exact ⟨s,pos_of_mul_pos_right (by rw [←hs]; exact hv 7) (by simp),hs⟩

/-- The fixed displayed zero yields Y=q³*s for an actual positive s. -/
theorem current_Y_quotient (v : Fin 13 → V) (hv : ∀j,0<v j)
    (hz : InternalZero expression v) :
    ∃ s : V, 0<s ∧ v 7 =
      ((1+v 0*(CurrentMasks2011.beta:V))*
        ((1+v 0*(CurrentMasks2011.beta:V))*(1+v 0*(CurrentMasks2011.beta:V))))*s := by
  have hp := current_parameters_positive v hv
  obtain ⟨t,d,_,_,ht,_,_,_⟩ := current_quotients v hv hz
  have hq : 0<1+v 0*(CurrentMasks2011.beta:V) := lt_trans (by simp : (0:V)<1) hp.1
  have hQ : 0<(1+v 0*(CurrentMasks2011.beta:V))*
      ((1+v 0*(CurrentMasks2011.beta:V))*(1+v 0*(CurrentMasks2011.beta:V))) :=
    mul_pos hq (mul_pos hq hq)
  have hM := hp.2.1
  have hd := quotient_forces_Y_divisible currentPorts v
    (by simpa only [currentPorts,Matrix.cons_val_zero] using hM)
    (by simpa only [currentPorts,Matrix.cons_val_zero] using hQ) t ht
  obtain ⟨s,hs⟩ := hd
  have hs' : v 7 = ((1+v 0*(CurrentMasks2011.beta:V))*
      ((1+v 0*(CurrentMasks2011.beta:V))*(1+v 0*(CurrentMasks2011.beta:V))))*s := by
    simpa only [currentPorts,Matrix.cons_val_zero] using hs
  exact ⟨s,pos_of_mul_pos_right (by rw [←hs']; exact hv 7) (by simp),hs'⟩

theorem current_natural_Y_quotient (v : Fin 13 → V) (hz : InternalZero naturalExpression v) :
    let w := fun j => v j+1
    ∃ s : V, 0<s ∧ w 7 =
      ((1+w 0*(CurrentMasks2011.beta:V))*
        ((1+w 0*(CurrentMasks2011.beta:V))*(1+w 0*(CurrentMasks2011.beta:V))))*s :=
  current_Y_quotient _ (fun j => lt_of_le_of_lt (Arithmetic.zero_le (v j)) (lt_add_one _))
    ((internalZero_positiveShift expression v).mp hz)

end DiophantineConsistency.ArithmeticAdaptiveFirstDivisibility2011

