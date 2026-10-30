import DiophantineConsistency.AdaptiveDirectOrdinate86Factors
import DiophantineConsistency.ArithmeticAdaptiveFactorUnits2011

/-! Modulo-four sign exclusions for the actual direct-ordinate 86 factors. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveDirectOrdinate86Units
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticAdaptiveFactorMagnitude2011
open ArithmeticAdaptiveFactorUnits2011 AdaptiveDirectOrdinate86Literal AdaptiveDirectOrdinate86Factors
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
private theorem syntax_add {σ : Type*} (v : σ → ZMod 4) (p q : Expr σ) : syntaxEval v (p+q)=syntaxEval v p+syntaxEval v q := rfl
private theorem syntax_sub {σ : Type*} (v : σ → ZMod 4) (p q : Expr σ) : syntaxEval v (p-q)=syntaxEval v p-syntaxEval v q := rfl
private theorem syntax_mul {σ : Type*} (v : σ → ZMod 4) (p q : Expr σ) : syntaxEval v (p*q)=syntaxEval v p*syntaxEval v q := rfl
private theorem syntax_var {σ : Type*} (v : σ → ZMod 4) (i : σ) : syntaxEval v (.var i)=v i := rfl
private theorem syntax_const {σ : Type*} (v : σ → ZMod 4) (i : ℤ) : syntaxEval v (.constant i)=(i:ZMod 4) := rfl
private theorem syntax_ofNat {σ : Type*} (v : σ → ZMod 4) (n : ℕ) : syntaxEval v (ofNat(n):Expr σ)=(n:ZMod 4) := by
  change ((n:ℤ):ZMod 4)=(n:ZMod 4)
  exact Int.cast_natCast n

private theorem factor0_eval (p : Fin 4 → ℤ) (v : Fin 13 → V) :
    syntaxEval (fun i => residue (v i)) (factors p).1 =
      1+(ScalarCore.core (fun j => (p j : ZMod 4)) (fun i => residue (v i))).A0 := by
  simp only [factors,ScalarCore.core,syntax_add,syntax_sub,syntax_mul,syntax_var,syntax_const,syntax_ofNat,Nat.cast_one]
private theorem factor1_eval (p : Fin 4 → ℤ) (v : Fin 13 → V) :
    syntaxEval (fun i => residue (v i)) (factors p).2.1 =
      1+(ScalarCore.core (fun j => (p j : ZMod 4)) (fun i => residue (v i))).A1 := by
  simp only [factors,ScalarCore.core,syntax_add,syntax_sub,syntax_mul,syntax_var,syntax_const,syntax_ofNat,Nat.cast_one,Nat.cast_ofNat]
private theorem factorStrong_eval (p : Fin 4 → ℤ) (v : Fin 13 → V) :
    syntaxEval (fun i => residue (v i)) (factors p).2.2.2 =
      (ScalarCore.core (fun j => (p j : ZMod 4)) (fun i => residue (v i))).Fs := by
  simp only [factors,ScalarCore.core,syntax_add,syntax_sub,syntax_mul,syntax_var,syntax_ofNat,Nat.cast_one,Nat.cast_ofNat]
private theorem factorAux_eval86 (p : Fin 4 → ℤ) (v : Fin 13 → V) :
    syntaxEval (fun i => residue (v i)) (factors86 p).2.2.1 =
      let x := fun i => residue (v i)
      let b := ScalarCore.core (fun j => (p j : ZMod 4)) x
      (x 11)*(x 11)-b.delta*(x 3*x 3-1)*((x 11)*(x 11)-b.V*b.V) := by
  simp only [factors86,ScalarCore.core,syntax_add,syntax_sub,syntax_mul,syntax_var,syntax_const,syntax_ofNat,Nat.cast_one,Nat.cast_ofNat]
private theorem first_bad : ∀ q z n : ZMod 4, 1+z^2-(q^3*(q-1))^2*n ≠ -1 := by decide
private theorem main_bad : ∀ u a c d : ZMod 4, 1+d^2-u^2*(1+(a^2+4*a+3)*c^2) ≠ -1 := by decide
private theorem strong_bad : ∀ a f i : ZMod 4, 1+i^2-(a^2+4*a+3)*(f^2-1) ≠ -1 := by decide
private theorem aux_bad : ∀ a f v y : ZMod 4,
  (a^2+4*a+3)*(f^2-1)*v^2+(1-(a^2+4*a+3)*(f^2-1))*y^2 ≠ -1 := by decide

theorem factor_ne_negative_one_mod4_86 (p : Fin 4 → ℤ) (v : Fin 13 → V) :
    pairResidue (pairEval (factors86 p).1 v) ≠ -1 ∧
    pairResidue (pairEval (factors86 p).2.1 v) ≠ -1 ∧
    pairResidue (pairEval (factors86 p).2.2.1 v) ≠ -1 ∧
    pairResidue (pairEval (factors86 p).2.2.2 v) ≠ -1 := by
  let ports : Fin 4 → ZMod 4 := fun j => p j
  let x : Fin 13 → ZMod 4 := fun j => residue (v j)
  let b := ScalarCore.core ports x
  have hm : b.M = b.q^3*(b.q-1) := by dsimp [b,ScalarCore.core]; ring
  have hdelta : b.delta=b.a^2+4*b.a+3 := by dsimp [b,ScalarCore.core]; ring
  have h0 : 1+b.A0 = 1+b.Z^2-(b.q^3*(b.q-1))^2*(1+b.ell*(b.ell+b.k)) := by
    rw [←hm]
    change 1+(b.Z*b.Z - (b.M*b.M)*(1+b.ell*(b.ell+b.k))) = _
    ring
  have h1 : 1+b.A1 = 1+b.Dstar^2-b.U^2*(1+(b.a^2+4*b.a+3)*b.c^2) := by
    rw [←hdelta]
    change 1+(b.Dstar*b.Dstar - (b.U*b.U)*(1+b.delta*(b.c*b.c))) = _
    ring
  have hs : b.Fs=1+b.I^2-(b.a^2+4*b.a+3)*((x 3)^2-1) := by
    rw [←hdelta]
    change 1+(b.I*b.I - b.delta*(x 3*x 3-1)) = _
    ring
  have ha : (x 11)*(x 11)-b.delta*(x 3*x 3-1)*((x 11)*(x 11)-b.V*b.V)=(b.a^2+4*b.a+3)*((x 3)^2-1)*b.V^2+
      (1-(b.a^2+4*b.a+3)*((x 3)^2-1))*(x 11)^2 := by
    rw [←hdelta]
    ring
  rw [←first_factor_pair_eq p v, second_factor_eq, strong_factor_eq]
  rw [pairEval_residue,factor0_eval,pairEval_residue,factor1_eval,
      pairEval_residue,factorAux_eval86,pairEval_residue,factorStrong_eval]
  change 1+b.A0 ≠ -1 ∧ 1+b.A1 ≠ -1 ∧
    (x 11)*(x 11)-b.delta*(x 3*x 3-1)*((x 11)*(x 11)-b.V*b.V) ≠ -1 ∧ b.Fs ≠ -1
  rw [h0,h1,ha,hs]
  exact ⟨first_bad _ _ _,main_bad _ _ _ _,aux_bad _ _ _ _,strong_bad _ _ _⟩

/-- Every zero of the actual 86 expression forces all four signed factors to +1. -/
theorem expressionAt_factor_units86 (p : Fin 4 → ℤ) (v : Fin 13 → V)
    (hz : InternalZero (expressionAt86 p) v) :
    (pairEval (factors86 p).1 v).1=(pairEval (factors86 p).1 v).2+1 ∧
    (pairEval (factors86 p).2.1 v).1=(pairEval (factors86 p).2.1 v).2+1 ∧
    (pairEval (factors86 p).2.2.1 v).1=(pairEval (factors86 p).2.2.1 v).2+1 ∧
    (pairEval (factors86 p).2.2.2 v).1=(pairEval (factors86 p).2.2.2 v).2+1 := by
  obtain ⟨m0,m1,ma,ms⟩ := expressionAt_factor_magnitudes86 p v hz
  obtain ⟨n0,n1,na,ns⟩ := factor_ne_negative_one_mod4_86 p v
  have h0 : (pairEval (factors86 p).1 v).1+1 ≠ (pairEval (factors86 p).1 v).2 := fun h => n0 (negative_residue h)
  have h1 : (pairEval (factors86 p).2.1 v).1+1 ≠ (pairEval (factors86 p).2.1 v).2 := fun h => n1 (negative_residue h)
  have ha : (pairEval (factors86 p).2.2.1 v).1+1 ≠ (pairEval (factors86 p).2.2.1 v).2 := fun h => na (negative_residue h)
  have hs : (pairEval (factors86 p).2.2.2 v).1+1 ≠ (pairEval (factors86 p).2.2.2 v).2 := fun h => ns (negative_residue h)
  exact ⟨equivalent_one.mp (positive_of_magnitude_one m0 h0),
    equivalent_one.mp (positive_of_magnitude_one m1 h1),
    equivalent_one.mp (positive_of_magnitude_one ma ha),
    equivalent_one.mp (positive_of_magnitude_one ms hs)⟩
end DiophantineConsistency.AdaptiveDirectOrdinate86Units
