import DiophantineConsistency.Compact44.Ordinary12FreeJ
import DiophantineConsistency.ArithmeticAdaptiveFirstDivisibility2011
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace FreeJRootBinding
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency.AdaptiveEquationSyntax2011
open DiophantineConsistency.ArithmeticSignedPairs
open DiophantineConsistency.ArithmeticGcdNormalization
open DiophantineConsistency.ArithmeticAdaptiveFactorMagnitude2011
open DiophantineConsistency.Ordinary12FreeJ
open DiophantineConsistency.ArithmeticAdaptiveScaledNorms2011
open DiophantineConsistency.ArithmeticAdaptiveQuotients2011
open DiophantineConsistency.ArithmeticAdaptiveFirstDivisibility2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Exact 95-gate folded first root, with all four ports nonnegative. -/
theorem root_rep (p : Fin 4 → ℕ) (v : Fin 12 → V) :
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
    Equivalent (pairEval (core (fun j => (p j : ℤ))).z v)
      (M*(ell+k+v 7)+v 6*b+Bn*(W*Q),Bp*(W*Q)) := by
  let eB : Expr (Fin 12) := .mul (.var 0) (.constant (p 0))
  let eQ : Expr (Fin 12) := .add (.constant 1) eB
  let eQ3 : Expr (Fin 12) := .mul eQ (.mul eQ eQ)
  let eK : Expr (Fin 12) := .add (.var 8) (.var 9)
  let eL : Expr (Fin 12) := .mul (.mul (.var 5) (.var 6)) (.mul (.var 6) eK)
  let eM : Expr (Fin 12) := .mul eQ3 eB
  let eC : Expr (Fin 12) := .sub (.sub eQ (.var 1)) (.var 2)
  let eA : Expr (Fin 12) := .add (.var 5) (.mul (.constant (p 1)) eQ)
  let eBt : Expr (Fin 12) := .sub (.mul eC eA) (.mul (.var 1) eQ)
  let eZ : Expr (Fin 12) := .sub
    (.add (.mul eM (.sub (.add (.add eL eK) (.var 7)) (.mul eK eBt))) (.mul (.var 6) eB))
    (.mul eQ3 eBt)
  change Equivalent (pairEval eZ v) _
  simp [eZ,eBt,eA,eC,eM,eL,eK,eQ3,eQ,eB,pairEval,Expr.splitNatural,
    NatExpr.evalSemiring,Equivalent]
  all_goals ring

def rhs (p : Fin 4 → ℤ) : Expr (Fin 12) :=
  let b : Expr (Fin 12) := .mul (.var 0) (.constant (p 0))
  let q : Expr (Fin 12) := .add (.constant 1) b
  let m : Expr (Fin 12) := .mul (.mul q (.mul q q)) b
  let k : Expr (Fin 12) := .add (.var 8) (.var 9)
  let ell : Expr (Fin 12) := .mul (.mul (.var 5) (.var 6)) (.mul (.var 6) k)
  .mul (.mul m m) (.add (.constant 1) (.mul ell (.add ell k)))

theorem first_shape (p : Fin 4 → ℤ) : (core p).first =
    1 + ((core p).z * (core p).z - rhs p) := by rfl

theorem rhs_pair (p : Fin 4 → ℕ) (v : Fin 12 → V) :
    let q : V := 1+v 0*(p 0:V)
    let M : V := (q*(q*q))*(v 0*(p 0:V))
    let k : V := v 8+v 9
    let ell : V := (v 5*v 6)*(v 6*k)
    pairEval (rhs (fun j => (p j : ℤ))) v = (M*M*(1+ell*(ell+k)),0) := by
  simp [rhs,pairEval,Expr.splitNatural,NatExpr.evalSemiring]

theorem first_scaled_norm (p : Fin 4 → ℕ) (v : Fin 12 → V)
    (hz : InternalZero (literal (fun j => (p j:ℤ))) v) :
    let q : V := 1+v 0*(p 0:V)
    let M : V := (q*(q*q))*(v 0*(p 0:V))
    let k : V := v 8+v 9
    let ell : V := (v 5*v 6)*(v 6*k)
    magnitude (pairEval (core (fun j => (p j:ℤ))).z v) *
      magnitude (pairEval (core (fun j => (p j:ℤ))).z v) = M*M*(1+ell*(ell+k)) := by
  have h := (literal_factor_units (fun j => (p j:ℤ)) v hz).1
  rw [first_shape] at h
  have hs := unit_square_norm _ _ v h
  rw [rhs_pair p v] at hs
  simpa only [Prod.fst,Prod.snd,add_zero] using hs

/-- Only the first norm and positivity of the scale are needed to extract
its unsigned root quotient; no rank or other factor equation is used. -/
theorem first_root_quotient (p : Fin 4 → ℕ) (v : Fin 12 → V)
    (hz : InternalZero (literal (fun j => (p j:ℤ))) v)
    (hM : 0 < (1+v 0*(p 0:V))*((1+v 0*(p 0:V))*(1+v 0*(p 0:V)))*(v 0*(p 0:V))) :
    ∃ t : V, magnitude (pairEval (core (fun j => (p j:ℤ))).z v) =
      ((1+v 0*(p 0:V))*((1+v 0*(p 0:V))*(1+v 0*(p 0:V)))*(v 0*(p 0:V)))*t := by
  obtain ⟨t,ht,_⟩ := scaled_quotient _ _ _ hM (first_scaled_norm p v hz)
  exact ⟨t,ht⟩

theorem folded_quotient_forces_Y_divisible (p : Fin 4 → ℕ) (v : Fin 12 → V)
    (hM : 0<(1+v 0*(p 0:V))*((1+v 0*(p 0:V))*(1+v 0*(p 0:V)))*(v 0*(p 0:V)))
    (hQ : 0<(1+v 0*(p 0:V))*((1+v 0*(p 0:V))*(1+v 0*(p 0:V))))
    (t : V)
    (ht : magnitude (pairEval (core (fun j => (p j:ℤ))).z v) =
      ((1+v 0*(p 0:V))*((1+v 0*(p 0:V))*(1+v 0*(p 0:V)))*(v 0*(p 0:V)))*t) :
    (1+v 0*(p 0:V))*((1+v 0*(p 0:V))*(1+v 0*(p 0:V))) ∣ v 6 := by
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
  let z := pairEval (core (fun j => (p j:ℤ))).z v
  have hdiv : M∣magnitude z := ⟨t,ht⟩
  have hzmod := magnitude_mod z M hM hdiv
  have hpair := equivalent_mod hM (root_rep p v) hzmod
  change (M*(ell+k+v 7)+v 6*b+Bn*(W*Q))%M = (Bp*(W*Q))%M at hpair
  have hdQM : Q∣M := ⟨b,rfl⟩
  have hQpair := congrArg (fun x : V => x%Q) hpair
  rw [mod_mod_dvd hQ hdQM,mod_mod_dvd hQ hdQM] at hQpair
  have hleft : M*(ell+k+v 7)+v 6*b+Bn*(W*Q) =
      v 6*b+Q*(b*(ell+k+v 7)+Bn*W) := by dsimp only [M]; ring
  have hright : Bp*(W*Q)=Q*(Bp*W) := by ring
  have hzero : (Q*(Bp*W))%Q=0 := by rw [mul_comm]; exact mod_mul_self_left _ _
  rw [hleft,hright,mod_add_mul' _ _ hQ,hzero] at hQpair
  have hby : Q∣b*v 6 := by
    apply mod_eq_zero_iff_dvd.mp
    change (v 6*b)%Q=0 at hQpair
    rw [mul_comm b (v 6)]
    exact hQpair
  have hunit : Bez b Q 1 := by
    refine ⟨q*q+q+1,0,0,1,?_⟩
    dsimp only [q,Q]
    ring
  exact unit_certificate_cancel hunit hby



/-- A positive first input and positive beta force the actual graph Y to
be divisible by q³. No rank, later norm or checker premise is used. -/
theorem first_factor_forces_Y_divisible (p : Fin 4 → ℕ) (v : Fin 12 → V)
    (hz : InternalZero (literal (fun j => (p j:ℤ))) v)
    (hJ : 0 < v 0) (hbeta : 0 < (p 0:V)) :
    (1+v 0*(p 0:V))^3 ∣ v 6 := by
  have hb : 0 < v 0*(p 0:V) := mul_pos hJ hbeta
  have hq : 0 < 1+v 0*(p 0:V) := by simp
  have hQ := mul_pos hq (mul_pos hq hq)
  have hM := mul_pos hQ hb
  obtain ⟨t,ht⟩ := first_root_quotient p v hz hM
  have h := folded_quotient_forces_Y_divisible p v hM hQ t ht
  convert h using 1
  all_goals ring

end FreeJRootBinding
#print axioms FreeJRootBinding.root_rep
#print axioms FreeJRootBinding.first_shape
#print axioms FreeJRootBinding.rhs_pair
#print axioms FreeJRootBinding.first_scaled_norm
#print axioms FreeJRootBinding.first_root_quotient
#print axioms FreeJRootBinding.folded_quotient_forces_Y_divisible
#print axioms FreeJRootBinding.first_factor_forces_Y_divisible
