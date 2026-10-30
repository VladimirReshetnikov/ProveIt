import DiophantineConsistency.ArithmeticAdaptiveFactorMagnitude2011
import Mathlib.Data.ZMod.Basic
/-! Internal modulo-four exclusion of negative units for the actual adaptive
factors, including arbitrary internal arguments and all zero cases. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptiveFactorUnits2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem exists_residue (x : V) : ∃ n : ℕ, x % 4 = (n : V) := by
  exact eq_nat_of_lt_nat (n:=4) (mod_lt x (by simp))

private def residueNat (x : V) : ℕ := Classical.choose (exists_residue x)
private theorem residueNat_eq (x : V) : (residueNat x : V) = x % 4 :=
  (Classical.choose_spec (exists_residue x)).symm
private theorem residueNat_lt (x : V) : residueNat x < 4 := by
  have h : (residueNat x : V) < 4 := by rw [residueNat_eq]; exact mod_lt x (by simp)
  exact_mod_cast h

def residue (x : V) : ZMod 4 := residueNat x

theorem residue_equal {x y : V} (h : x%4 = y%4) : residue x = residue y := by
  have he : (residueNat x : V) = (residueNat y : V) := by rw [residueNat_eq,residueNat_eq,h]
  have hn : residueNat x = residueNat y := Nat.cast_inj.mp he
  simp only [residue,hn]

theorem cast_mod (n : ℕ) : (((n % 4):ℕ) : V) = (n : V)%4 := by
  have hn : (n : V) = ((n%4:ℕ):V)+4*((n/4:ℕ):V) := by
    have h := Nat.mod_add_div n 4
    exact_mod_cast h.symm
  rw [hn, mod_add_mul' _ _ (by simp : (0:V)<4)]
  symm
  apply mod_eq_self_of_lt
  exact_mod_cast (Nat.mod_lt n (by decide : 0<4))

theorem residue_nat (n : ℕ) : residue (n : V) = (n : ZMod 4) := by
  have he : (residueNat (n:V) : V) = ((n%4:ℕ):V) := by rw [residueNat_eq, cast_mod]
  have hn : residueNat (n:V) = n%4 := Nat.cast_inj.mp he
  simp only [residue,hn,ZMod.natCast_mod]

theorem residue_add (a b : V) : residue (a+b) = residue a + residue b := by
  have h : (a+b)%4 = (((residueNat a + residueNat b):ℕ):V)%4 := by
    rw [mod_add (by simp : (0:V)<4),Nat.cast_add,residueNat_eq,residueNat_eq]
  calc
    residue (a+b) = residue (((residueNat a + residueNat b):ℕ):V) := residue_equal h
    _ = ((residueNat a + residueNat b):ℕ) := residue_nat _
    _ = residue a + residue b := by simp only [residue, Nat.cast_add]

theorem residue_mul (a b : V) : residue (a*b) = residue a * residue b := by
  have h : (a*b)%4 = (((residueNat a * residueNat b):ℕ):V)%4 := by
    rw [mod_mul (by simp : (0:V)<4),Nat.cast_mul,residueNat_eq,residueNat_eq]
  calc
    residue (a*b) = residue (((residueNat a * residueNat b):ℕ):V) := residue_equal h
    _ = ((residueNat a * residueNat b):ℕ) := residue_nat _
    _ = residue a * residue b := by simp only [residue, Nat.cast_mul]
end DiophantineConsistency.ArithmeticAdaptiveFactorUnits2011
namespace DiophantineConsistency.ArithmeticAdaptiveFactorUnits2011.ScalarCore
structure Core (A : Type*) where
  qm : A
  q : A
  q3 : A
  C : A
  E : A
  k : A
  c : A
  a : A
  H : A
  delta : A
  ell : A
  U : A
  Bt : A
  rank : A
  V : A
  y : A
  I : A
  Z : A
  M : A
  W : A
  Dstar : A
  A0 : A
  A1 : A
  Fs : A
  Fa : A
  out : A

variable {A : Type*} [CommRing A]

/-- Every paid gate below follows the inert p13_free_J.json, with no coefficient shift. -/
def core (ports : Fin 4 → A) (x : Fin 13 → A) : Core A :=
  -- BEGIN INPUT ALIASES
  let J := x 0
  let F := x 1
  let alpha := x 2
  let f := x 3
  let i := x 4
  let T := x 5
  let X := x 6
  let Y := x 7
  let r := x 8
  let eta := x 9
  let zeta := x 10
  let u := x 11
  let gamma := x 12
  let beta := ports 0
  let K0 := ports 1
  let MC := ports 2
  let MF := ports 3
  -- END INPUT ALIASES
  -- BEGIN LITERAL GRAPH
  let qm := J * beta
  let q := 1 + qm
  let q2 := q * q
  let q3 := q * q2
  let U := Y * q2
  let qF := q - F
  let C := qF - alpha
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
  let g22 := k * qm
  let W := 1 + g22
  let M := q3 * qm
  let g25 := K0 * q
  let g26 := X + g25
  let g27 := C * g26
  let g28 := F * q
  let Bt := g27 - g28
  let g30 := ell + k
  let g31 := g30 + r
  let g32 := M * g31
  let g33 := Y * qm
  let g34 := g32 + g33
  let g35 := W * q3
  let g36 := Bt * g35
  let Z := g34 - g36
  let g38 := Z * Z
  let g39 := M * M
  let g40 := ell * g30
  let g41 := 1 + g40
  let g42 := g39 * g41
  let A0 := g38 - g42
  let g44 := qF * qm
  let G := alpha + g44
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
  let g78 := V + u
  let y2 := g78 * g78
  let g80 := V * V
  let g81 := y2 - g80
  let g82 := Q * g81
  let Fa := y2 - g82
  let F0 := 1 + A0
  let F1 := 1 + A1
  let g86 := F0 * F1
  let g87 := Fa * g86
  let g88 := Fs * g87
  let P13 := g88 - 1
  -- END LITERAL GRAPH
  { qm:=qm, q:=q, q3:=q3, C:=C, E:=E, k:=k, c:=c, a:=a, H:=H, delta:=Delta, ell:=ell, U:=U, Bt:=Bt, rank:=R, V:=V, y:=g78, I:=I, Z:=Z, M:=M, W:=W, Dstar:=Dstar, A0:=A0, A1:=A1, Fs:=Fs, Fa:=Fa, out:=P13 }

end DiophantineConsistency.ArithmeticAdaptiveFactorUnits2011.ScalarCore

namespace DiophantineConsistency.ArithmeticAdaptiveFactorUnits2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency
open DiophantineConsistency.ArithmeticSignedPairs
open DiophantineConsistency.ArithmeticAdaptiveFactorMagnitude2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def pairResidue (p : Pair V) : ZMod 4 := residue p.1 - residue p.2

def syntaxEval {σ : Type*} (v : σ → ZMod 4) : Expr σ → ZMod 4
  | .constant z => (z : ZMod 4)
  | .var i => v i
  | .add p q => syntaxEval v p + syntaxEval v q
  | .sub p q => syntaxEval v p - syntaxEval v q
  | .mul p q => syntaxEval v p * syntaxEval v q

theorem pairEval_residue {σ : Type*} (e : Expr σ) (v : σ → V) :
    pairResidue (pairEval e v) = syntaxEval (fun i => residue (v i)) e := by
  induction e with
  | constant z =>
    change residue ((z.toNat : ℕ):V) - residue (((-z).toNat : ℕ):V) = (z:ZMod 4)
    rw [residue_nat, residue_nat]
    have h := congrArg (fun w : ℤ => (w:ZMod 4)) (Int.toNat_sub_toNat_neg z)
    simpa only [Int.cast_sub,Int.cast_natCast] using h
  | var i =>
    have hz : residue (0:V)=0 := by simpa using residue_nat (V:=V) 0
    simp [pairResidue,pairEval,Expr.splitNatural,NatExpr.evalSemiring,syntaxEval,hz]
  | add p q hp hq =>
    simp only [pairResidue,pairEval,Expr.splitNatural,NatExpr.evalSemiring,residue_add,syntaxEval] at hp hq ⊢
    rw [←hp,←hq]
    ring
  | sub p q hp hq =>
    simp only [pairResidue,pairEval,Expr.splitNatural,NatExpr.evalSemiring,residue_add,syntaxEval] at hp hq ⊢
    rw [←hp,←hq]
    ring
  | mul p q hp hq =>
    simp only [pairResidue,pairEval,Expr.splitNatural,NatExpr.evalSemiring,residue_add,residue_mul,syntaxEval] at hp hq ⊢
    rw [←hp,←hq]
    ring

theorem negative_residue {p : Pair V} (h : p.1 + 1 = p.2) : pairResidue p = -1 := by
  have hh := congrArg residue h
  have ho : residue (1:V)=1 := by simpa using residue_nat (V:=V) 1
  rw [residue_add,ho] at hh
  dsimp [pairResidue]
  rw [←hh]
  ring
end DiophantineConsistency.ArithmeticAdaptiveFactorUnits2011
namespace DiophantineConsistency.ArithmeticAdaptiveFactorUnits2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency
open DiophantineConsistency.ArithmeticSignedPairs
open DiophantineConsistency.ArithmeticAdaptiveFactorMagnitude2011
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
private theorem factorAux_eval (p : Fin 4 → ℤ) (v : Fin 13 → V) :
    syntaxEval (fun i => residue (v i)) (factors p).2.2.1 =
      (ScalarCore.core (fun j => (p j : ZMod 4)) (fun i => residue (v i))).Fa := by
  simp only [factors,ScalarCore.core,syntax_add,syntax_sub,syntax_mul,syntax_var,syntax_const,syntax_ofNat,Nat.cast_one,Nat.cast_ofNat]
private theorem factorStrong_eval (p : Fin 4 → ℤ) (v : Fin 13 → V) :
    syntaxEval (fun i => residue (v i)) (factors p).2.2.2 =
      (ScalarCore.core (fun j => (p j : ZMod 4)) (fun i => residue (v i))).Fs := by
  simp only [factors,ScalarCore.core,syntax_add,syntax_sub,syntax_mul,syntax_var,syntax_ofNat,Nat.cast_one,Nat.cast_ofNat]
end DiophantineConsistency.ArithmeticAdaptiveFactorUnits2011
namespace DiophantineConsistency.ArithmeticAdaptiveFactorUnits2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency
open DiophantineConsistency.ArithmeticSignedPairs
open DiophantineConsistency.ArithmeticAdaptiveFactorMagnitude2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem first_bad : ∀ q z n : ZMod 4, 1+z^2-(q^3*(q-1))^2*n ≠ -1 := by decide
private theorem main_bad : ∀ u a c d : ZMod 4, 1+d^2-u^2*(1+(a^2+4*a+3)*c^2) ≠ -1 := by decide
private theorem strong_bad : ∀ a f i : ZMod 4, 1+i^2-(a^2+4*a+3)*(f^2-1) ≠ -1 := by decide
private theorem aux_bad : ∀ a f v y : ZMod 4,
  (a^2+4*a+3)*(f^2-1)*v^2+(1-(a^2+4*a+3)*(f^2-1))*y^2 ≠ -1 := by decide

private theorem factor_ne_negative_one_mod4 (p : Fin 4 → ℤ) (v : Fin 13 → V) :
    pairResidue (pairEval (factors p).1 v) ≠ -1 ∧
    pairResidue (pairEval (factors p).2.1 v) ≠ -1 ∧
    pairResidue (pairEval (factors p).2.2.1 v) ≠ -1 ∧
    pairResidue (pairEval (factors p).2.2.2 v) ≠ -1 := by
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
  have ha : b.Fa=(b.a^2+4*b.a+3)*((x 3)^2-1)*b.V^2+
      (1-(b.a^2+4*b.a+3)*((x 3)^2-1))*b.y^2 := by
    rw [←hdelta]
    change b.y*b.y-b.delta*(x 3*x 3-1)*(b.y*b.y-b.V*b.V) = _
    ring
  rw [pairEval_residue,factor0_eval,pairEval_residue,factor1_eval,
      pairEval_residue,factorAux_eval,pairEval_residue,factorStrong_eval]
  change 1+b.A0 ≠ -1 ∧ 1+b.A1 ≠ -1 ∧ b.Fa ≠ -1 ∧ b.Fs ≠ -1
  rw [h0,h1,ha,hs]
  exact ⟨first_bad _ _ _,main_bad _ _ _ _,aux_bad _ _ _ _,strong_bad _ _ _⟩

end DiophantineConsistency.ArithmeticAdaptiveFactorUnits2011
namespace DiophantineConsistency.ArithmeticAdaptiveFactorUnits2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency
open DiophantineConsistency.AdaptiveEquationSyntax2011
open DiophantineConsistency.ArithmeticSignedPairs
open DiophantineConsistency.ArithmeticAdaptiveFactorMagnitude2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def FactorUnits (p : Fin 4 → ℤ) (v : Fin 13 → V) : Prop :=
    (pairEval (factors p).1 v).1=(pairEval (factors p).1 v).2+1 ∧
    (pairEval (factors p).2.1 v).1=(pairEval (factors p).2.1 v).2+1 ∧
    (pairEval (factors p).2.2.1 v).1=(pairEval (factors p).2.2.1 v).2+1 ∧
    (pairEval (factors p).2.2.2 v).1=(pairEval (factors p).2.2.2 v).2+1

theorem expressionAt_factor_units (p : Fin 4 → ℤ) (v : Fin 13 → V)
    (hz : InternalZero (expressionAt p) v) : FactorUnits p v := by
  obtain ⟨m0,m1,ma,ms⟩ := expressionAt_factor_magnitudes p v hz
  obtain ⟨n0,n1,na,ns⟩ := factor_ne_negative_one_mod4 p v
  have h0 : (pairEval (factors p).1 v).1+1 ≠ (pairEval (factors p).1 v).2 :=
    fun h => n0 (negative_residue h)
  have h1 : (pairEval (factors p).2.1 v).1+1 ≠ (pairEval (factors p).2.1 v).2 :=
    fun h => n1 (negative_residue h)
  have ha : (pairEval (factors p).2.2.1 v).1+1 ≠ (pairEval (factors p).2.2.1 v).2 :=
    fun h => na (negative_residue h)
  have hs : (pairEval (factors p).2.2.2 v).1+1 ≠ (pairEval (factors p).2.2.2 v).2 :=
    fun h => ns (negative_residue h)
  exact ⟨equivalent_one.mp (positive_of_magnitude_one m0 h0),
    equivalent_one.mp (positive_of_magnitude_one m1 h1),
    equivalent_one.mp (positive_of_magnitude_one ma ha),
    equivalent_one.mp (positive_of_magnitude_one ms hs)⟩

theorem current_factor_units (v : Fin 13 → V) (hz : InternalZero expression v) :
    FactorUnits CurrentWindowCarry2011.ports v := expressionAt_factor_units _ v hz

theorem current_natural_factor_units (v : Fin 13 → V) (hz : InternalZero naturalExpression v) :
    FactorUnits CurrentWindowCarry2011.ports (fun j => v j+1) :=
  current_factor_units _ ((internalZero_positiveShift expression v).mp hz)
end DiophantineConsistency.ArithmeticAdaptiveFactorUnits2011
