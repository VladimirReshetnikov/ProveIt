import DiophantineConsistency.AdaptiveGap85Magnitudes
import DiophantineConsistency.ArithmeticAdaptiveFactorUnits2011

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85Units
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticAdaptiveFactorMagnitude2011 ArithmeticAdaptiveFactorUnits2011
open AdaptiveGap85Literal AdaptiveGap85Factors AdaptiveGap85Magnitudes
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

structure Core (A : Type*) where
  qm : A
  q : A
  M : A
  ell : A
  k : A
  Z : A
  U : A
  a : A
  c : A
  Dstar : A
  Delta : A
  I : A
  V : A
  Fs : A
  Fa : A
  A0 : A
  A1 : A

def core {A : Type*} [CommRing A] (p : Fin 4 → A) (x : Fin 13 → A) : Core A :=
  let J := x 0
  let F := x 1
  let C := x 2
  let f := x 3
  let i := x 4
  let T := x 5
  let X := x 6
  let Y := x 7
  let r := x 8
  let eta := x 9
  let zeta := x 10
  let y := x 11
  let gamma := x 12
  let beta := p 0
  let K0 := p 1
  let MC := p 2
  let MF := p 3
  let qm := J * beta
  let q := 1 + qm
  let q2 := q * q
  let q3 := q * q2
  let U := Y * q2
  let qF := q - F
  let E := X * Y
  let k := eta + zeta
  let kY := Y * k
  let c := eta + kY
  let c2 := c * c
  let a := E + Y
  let g15 := 4 * a
  let H := 3 + g15
  let g17 := a * a
  let Delta := H + g17
  let g19 := a * c
  let b0 := X + g19
  let ell := E * kY
  let M := q3 * qm
  let g25 := K0 * q
  let g26 := X + g25
  let g27 := C * g26
  let g28 := F * q
  let Bt := g27 - g28
  let g30 := ell + k
  let g31 := g30 + r
  let root_skew := k * Bt
  let root_inner := g31 - root_skew
  let root_scaled := M * root_inner
  let g33 := Y * qm
  let root_btq3 := Bt * q3
  let root_sum := root_scaled + g33
  let Z := root_sum - root_btq3
  let g38 := Z * Z
  let g39 := M * M
  let g40 := ell * g30
  let g41 := 1 + g40
  let g42 := g39 * g41
  let A0 := g38 - g42
  let g44 := qF * q
  let G := g44 - C
  let g46 := q2 - 1
  let g47 := G * g46
  let g48 := MF * q
  let g49 := MC + g48
  let g50 := J * g49
  let R := g47 + g50
  let g52 := k - R
  let r0 := g52 - 1
  let g54 := U * gamma
  let g55 := E * q
  let g56 := g54 + g55
  let shift := g56 - r0
  let g58 := U * b0
  let g59 := H * shift
  let Dstar := g58 + g59
  let g61 := Dstar * Dstar
  let g62 := U * U
  let g63 := Delta * c2
  let g64 := 1 + g63
  let g65 := g62 * g64
  let A1 := g61 - g65
  let f2 := f * f
  let rho := f2 - 1
  let Q := Delta * rho
  let I := c2 * i
  let g71 := I * I
  let g72 := g71 - Q
  let Fs := 1 + g72
  let g74 := T * c
  let g75 := g74 - R
  let g76 := f2 * g75
  let V := g76 - c
  let y2 := y * y
  let g80 := V * V
  let g81 := y2 - g80
  let g82 := Q * g81
  let Fa := y2 - g82
  ⟨qm, q, M, ell, k, Z, U, a, c, Dstar, Delta, I, V, Fs, Fa, A0, A1⟩

private theorem syntax_add {σ : Type*} (v : σ → ZMod 4) (p q : Expr σ) : syntaxEval v (p+q)=syntaxEval v p+syntaxEval v q := rfl
private theorem syntax_sub {σ : Type*} (v : σ → ZMod 4) (p q : Expr σ) : syntaxEval v (p-q)=syntaxEval v p-syntaxEval v q := rfl
private theorem syntax_mul {σ : Type*} (v : σ → ZMod 4) (p q : Expr σ) : syntaxEval v (p*q)=syntaxEval v p*syntaxEval v q := rfl
private theorem syntax_var {σ : Type*} (v : σ → ZMod 4) (i : σ) : syntaxEval v (.var i)=v i := rfl
private theorem syntax_const {σ : Type*} (v : σ → ZMod 4) (i : ℤ) : syntaxEval v (.constant i)=(i:ZMod 4) := rfl
private theorem syntax_ofNat {σ : Type*} (v : σ → ZMod 4) (n : ℕ) : syntaxEval v (ofNat(n):Expr σ)=(n:ZMod 4) := by
  change ((n:ℤ):ZMod 4)=(n:ZMod 4)
  exact Int.cast_natCast n

private theorem factor0_eval (p : Fin 4 → ℤ) (v : Fin 13 → V) :
    syntaxEval (fun i => residue (v i)) (AdaptiveGap85Factors.factors p).1 =
      1+(core (fun j => (p j : ZMod 4)) (fun i => residue (v i))).A0 := by
  simp only [AdaptiveGap85Factors.factors,core,syntax_add,syntax_sub,syntax_mul,syntax_var,syntax_const,syntax_ofNat,Nat.cast_one]
private theorem factor1_eval (p : Fin 4 → ℤ) (v : Fin 13 → V) :
    syntaxEval (fun i => residue (v i)) (AdaptiveGap85Factors.factors p).2.1 =
      1+(core (fun j => (p j : ZMod 4)) (fun i => residue (v i))).A1 := by
  simp only [AdaptiveGap85Factors.factors,core,syntax_add,syntax_sub,syntax_mul,syntax_var,syntax_const,syntax_ofNat,Nat.cast_one,Nat.cast_ofNat]
private theorem factorAux_eval (p : Fin 4 → ℤ) (v : Fin 13 → V) :
    syntaxEval (fun i => residue (v i)) (AdaptiveGap85Factors.factors p).2.2.1 =
      (core (fun j => (p j : ZMod 4)) (fun i => residue (v i))).Fa := by
  simp only [AdaptiveGap85Factors.factors,core,syntax_add,syntax_sub,syntax_mul,syntax_var,syntax_const,syntax_ofNat,Nat.cast_one,Nat.cast_ofNat]
private theorem factorStrong_eval (p : Fin 4 → ℤ) (v : Fin 13 → V) :
    syntaxEval (fun i => residue (v i)) (AdaptiveGap85Factors.factors p).2.2.2 =
      (core (fun j => (p j : ZMod 4)) (fun i => residue (v i))).Fs := by
  simp only [AdaptiveGap85Factors.factors,core,syntax_add,syntax_sub,syntax_mul,syntax_var,syntax_ofNat,Nat.cast_one,Nat.cast_ofNat]
private theorem first_bad : ∀ q z n : ZMod 4, 1+z^2-(q^3*(q-1))^2*n ≠ -1 := by decide
private theorem main_bad : ∀ u a c d : ZMod 4, 1+d^2-u^2*(1+(a^2+4*a+3)*c^2) ≠ -1 := by decide
private theorem strong_bad : ∀ a f i : ZMod 4, 1+i^2-(a^2+4*a+3)*(f^2-1) ≠ -1 := by decide
private theorem aux_bad : ∀ a f v y : ZMod 4,
  (a^2+4*a+3)*(f^2-1)*v^2+(1-(a^2+4*a+3)*(f^2-1))*y^2 ≠ -1 := by decide

theorem factor_ne_negative_one_mod4_85 (p : Fin 4 → ℤ) (v : Fin 13 → V) :
    pairResidue (pairEval (AdaptiveGap85Factors.factors p).1 v) ≠ -1 ∧
    pairResidue (pairEval (AdaptiveGap85Factors.factors p).2.1 v) ≠ -1 ∧
    pairResidue (pairEval (AdaptiveGap85Factors.factors p).2.2.1 v) ≠ -1 ∧
    pairResidue (pairEval (AdaptiveGap85Factors.factors p).2.2.2 v) ≠ -1 := by
  let ports : Fin 4 → ZMod 4 := fun j => p j
  let x : Fin 13 → ZMod 4 := fun j => residue (v j)
  let b := core ports x
  have hm : b.M = b.q^3*(b.q-1) := by dsimp [b,core]; ring
  have hdelta : b.Delta=b.a^2+4*b.a+3 := by dsimp [b,core]; ring
  have h0 : 1+b.A0 = 1+b.Z^2-(b.q^3*(b.q-1))^2*(1+b.ell*(b.ell+b.k)) := by
    rw [←hm]
    change 1+(b.Z*b.Z - (b.M*b.M)*(1+b.ell*(b.ell+b.k))) = _
    ring
  have h1 : 1+b.A1 = 1+b.Dstar^2-b.U^2*(1+(b.a^2+4*b.a+3)*b.c^2) := by
    rw [←hdelta]
    change 1+(b.Dstar*b.Dstar - (b.U*b.U)*(1+b.Delta*(b.c*b.c))) = _
    ring
  have hs : b.Fs=1+b.I^2-(b.a^2+4*b.a+3)*((x 3)^2-1) := by
    rw [←hdelta]
    change 1+(b.I*b.I - b.Delta*(x 3*x 3-1)) = _
    ring
  have ha : b.Fa=(b.a^2+4*b.a+3)*((x 3)^2-1)*b.V^2+
      (1-(b.a^2+4*b.a+3)*((x 3)^2-1))*(x 11)^2 := by
    rw [←hdelta]
    change (x 11)*(x 11)-b.Delta*(x 3*x 3-1)*((x 11)*(x 11)-b.V*b.V)=_
    ring
  rw [pairEval_residue,factor0_eval,pairEval_residue,factor1_eval,
      pairEval_residue,factorAux_eval,pairEval_residue,factorStrong_eval]
  change 1+b.A0 ≠ -1 ∧ 1+b.A1 ≠ -1 ∧
    b.Fa ≠ -1 ∧ b.Fs ≠ -1
  rw [h0,h1,ha,hs]
  exact ⟨first_bad _ _ _,main_bad _ _ _ _,aux_bad _ _ _ _,strong_bad _ _ _⟩

/-- Every zero of the actual 85 expression forces all four signed factors to +1. -/
theorem expressionAt_factor_units85 (p : Fin 4 → ℤ) (v : Fin 13 → V)
    (hz : InternalZero (expressionAt85 p) v) :
    (pairEval (AdaptiveGap85Factors.factors p).1 v).1=(pairEval (AdaptiveGap85Factors.factors p).1 v).2+1 ∧
    (pairEval (AdaptiveGap85Factors.factors p).2.1 v).1=(pairEval (AdaptiveGap85Factors.factors p).2.1 v).2+1 ∧
    (pairEval (AdaptiveGap85Factors.factors p).2.2.1 v).1=(pairEval (AdaptiveGap85Factors.factors p).2.2.1 v).2+1 ∧
    (pairEval (AdaptiveGap85Factors.factors p).2.2.2 v).1=(pairEval (AdaptiveGap85Factors.factors p).2.2.2 v).2+1 := by
  obtain ⟨m0,m1,ma,ms⟩ := expressionAt_factor_magnitudes85 p v hz
  obtain ⟨n0,n1,na,ns⟩ := factor_ne_negative_one_mod4_85 p v
  have h0 : (pairEval (AdaptiveGap85Factors.factors p).1 v).1+1 ≠ (pairEval (AdaptiveGap85Factors.factors p).1 v).2 := fun h => n0 (negative_residue h)
  have h1 : (pairEval (AdaptiveGap85Factors.factors p).2.1 v).1+1 ≠ (pairEval (AdaptiveGap85Factors.factors p).2.1 v).2 := fun h => n1 (negative_residue h)
  have ha : (pairEval (AdaptiveGap85Factors.factors p).2.2.1 v).1+1 ≠ (pairEval (AdaptiveGap85Factors.factors p).2.2.1 v).2 := fun h => na (negative_residue h)
  have hs : (pairEval (AdaptiveGap85Factors.factors p).2.2.2 v).1+1 ≠ (pairEval (AdaptiveGap85Factors.factors p).2.2.2 v).2 := fun h => ns (negative_residue h)
  exact ⟨equivalent_one.mp (positive_of_magnitude_one m0 h0),
    equivalent_one.mp (positive_of_magnitude_one m1 h1),
    equivalent_one.mp (positive_of_magnitude_one ma ha),
    equivalent_one.mp (positive_of_magnitude_one ms hs)⟩
end DiophantineConsistency.AdaptiveGap85Units
