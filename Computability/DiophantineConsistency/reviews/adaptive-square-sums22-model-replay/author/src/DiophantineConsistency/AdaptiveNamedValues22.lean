import DiophantineConsistency.AdaptiveRankWitness17

/-! The 112-operation, 22-variable named-value literal has the same
positive-domain zero existence as the 17-variable parent for every integer
port vector, in every IΣ₁ model. The four constraints name three positive
expressions and an arbitrary signed expression represented by a positive pair. -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveNamedValues22
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticSignedPairExpressions ArithmeticAdaptiveFactorMagnitude2011
open AdaptiveFirstRootFactor87Syntax AdaptiveDirectOrdinate86Context AdaptiveDirectOrdinate86Lift
open AdaptiveSquareWitnessDirect14 AdaptiveScaleWitness15 AdaptiveMainScaleWitness16 AdaptiveRankWitness17 AdaptiveDirectOrdinateSquareSums

def contextAt (p : Fin 4 → ℤ) : Expr (Sum (Fin 4) (Fin 17)) :=
  let J : Expr (Sum (Fin 4) (Fin 17)) := .var (Sum.inr 0)
  let F : Expr (Sum (Fin 4) (Fin 17)) := .var (Sum.inr 1)
  let alpha : Expr (Sum (Fin 4) (Fin 17)) := .var (Sum.inr 2)
  let f : Expr (Sum (Fin 4) (Fin 17)) := .var (Sum.inr 3)
  let i : Expr (Sum (Fin 4) (Fin 17)) := .var (Sum.inr 4)
  let T : Expr (Sum (Fin 4) (Fin 17)) := .var (Sum.inr 5)
  let X : Expr (Sum (Fin 4) (Fin 17)) := .var (Sum.inr 6)
  let Y : Expr (Sum (Fin 4) (Fin 17)) := .var (Sum.inr 7)
  let r : Expr (Sum (Fin 4) (Fin 17)) := .var (Sum.inr 8)
  let eta : Expr (Sum (Fin 4) (Fin 17)) := .var (Sum.inr 9)
  let zeta : Expr (Sum (Fin 4) (Fin 17)) := .var (Sum.inr 10)
  let y : Expr (Sum (Fin 4) (Fin 17)) := .var (Sum.inr 11)
  let gamma : Expr (Sum (Fin 4) (Fin 17)) := .var (Sum.inr 12)
  let squareVariable : Expr (Sum (Fin 4) (Fin 17)) := .var (Sum.inr 13)
  let scaleVariable : Expr (Sum (Fin 4) (Fin 17)) := .var (Sum.inr 14)
  let mainScaleVariable : Expr (Sum (Fin 4) (Fin 17)) := .var (Sum.inr 15)
  let rankVariable : Expr (Sum (Fin 4) (Fin 17)) := .var (Sum.inr 16)
  let beta : Expr (Sum (Fin 4) (Fin 17)) := .constant (p 0)
  let MC : Expr (Sum (Fin 4) (Fin 17)) := .constant (p 2)
  let MF : Expr (Sum (Fin 4) (Fin 17)) := .constant (p 3)
  let c : Expr (Sum (Fin 4) (Fin 17)) := .var (Sum.inl 0)
  let a : Expr (Sum (Fin 4) (Fin 17)) := .var (Sum.inl 1)
  let ell : Expr (Sum (Fin 4) (Fin 17)) := .var (Sum.inl 2)
  let Bt : Expr (Sum (Fin 4) (Fin 17)) := .var (Sum.inl 3)
  let qm := J * beta
  let q := 1 + qm
  let q2 := q * q
  let q3 := q * q2
  let U := Y * q2
  let qF := q - F
  let E := X * Y
  let k := eta + zeta
  let c2 := c * c
  let g15 := 4 * a
  let H := 3 + g15
  let g17 := a * a
  let Delta := H + g17
  let g19 := a * c
  let b0 := X + g19
  let M := q3 * qm
  let g30 := ell + k
  let g31 := g30 + r
  let root_skew := k * Bt
  let root_inner := g31 - root_skew
  let root_scaled := scaleVariable * root_inner
  let g33 := Y * qm
  let root_btq3 := Bt * q3
  let root_sum := root_scaled + g33
  let Z := root_sum - root_btq3
  let g38 := Z * Z
  let g39 := scaleVariable * scaleVariable
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
  let g52 := k - rankVariable
  let r0 := g52 - 1
  let g54 := mainScaleVariable * gamma
  let g55 := E * q
  let g56 := g54 + g55
  let shift := g56 - r0
  let g58 := mainScaleVariable * b0
  let g59 := H * shift
  let Dstar := g58 + g59
  let g61 := Dstar * Dstar
  let g62 := mainScaleVariable * mainScaleVariable
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
  let g74 := T * c
  let g75 := g74 - rankVariable
  let g76 := f2 * g75
  let V := g76 - c
  let y2 := y * y
  let g80 := V * V
  let g81 := y2 - squareVariable
  let g82 := Q * g81
  let Fa := y2 - g82
  let auxResidual := Fa - 1
  let firstSquare := A0 * A0
  let mainSquare := A1 * A1
  let auxSquare := auxResidual * auxResidual
  let strongSquare := g72 * g72
  let firstMain := firstSquare + mainSquare
  let firstMainAux := firstMain + auxSquare
  let sumSquares := firstMainAux + strongSquare
  let squareDifference := squareVariable - g80
  let squareConstraint := squareDifference * squareDifference
  let sumWithConstraint := sumSquares + squareConstraint
  let scaleDifference := scaleVariable - M
  let scaleConstraint := scaleDifference * scaleDifference
  let finalWithScale := sumWithConstraint + scaleConstraint
  let mainScaleDifference := mainScaleVariable - U
  let mainScaleConstraint := mainScaleDifference * mainScaleDifference
  let finalWithMainScale := finalWithScale + mainScaleConstraint
  let rankDifference := rankVariable - R
  let rankConstraint := rankDifference * rankDifference
  let finalWithRank := finalWithMainScale + rankConstraint
  finalWithRank

def residualsAt (p : Fin 4 → ℤ) : Expr (Sum (Fin 4) (Fin 17)) × Expr (Sum (Fin 4) (Fin 17)) × Expr (Sum (Fin 4) (Fin 17)) × Expr (Sum (Fin 4) (Fin 17)) × Expr (Sum (Fin 4) (Fin 17)) × Expr (Sum (Fin 4) (Fin 17)) × Expr (Sum (Fin 4) (Fin 17)) × Expr (Sum (Fin 4) (Fin 17)) :=
  let J : Expr (Sum (Fin 4) (Fin 17)) := .var (Sum.inr 0)
  let F : Expr (Sum (Fin 4) (Fin 17)) := .var (Sum.inr 1)
  let alpha : Expr (Sum (Fin 4) (Fin 17)) := .var (Sum.inr 2)
  let f : Expr (Sum (Fin 4) (Fin 17)) := .var (Sum.inr 3)
  let i : Expr (Sum (Fin 4) (Fin 17)) := .var (Sum.inr 4)
  let T : Expr (Sum (Fin 4) (Fin 17)) := .var (Sum.inr 5)
  let X : Expr (Sum (Fin 4) (Fin 17)) := .var (Sum.inr 6)
  let Y : Expr (Sum (Fin 4) (Fin 17)) := .var (Sum.inr 7)
  let r : Expr (Sum (Fin 4) (Fin 17)) := .var (Sum.inr 8)
  let eta : Expr (Sum (Fin 4) (Fin 17)) := .var (Sum.inr 9)
  let zeta : Expr (Sum (Fin 4) (Fin 17)) := .var (Sum.inr 10)
  let y : Expr (Sum (Fin 4) (Fin 17)) := .var (Sum.inr 11)
  let gamma : Expr (Sum (Fin 4) (Fin 17)) := .var (Sum.inr 12)
  let squareVariable : Expr (Sum (Fin 4) (Fin 17)) := .var (Sum.inr 13)
  let scaleVariable : Expr (Sum (Fin 4) (Fin 17)) := .var (Sum.inr 14)
  let mainScaleVariable : Expr (Sum (Fin 4) (Fin 17)) := .var (Sum.inr 15)
  let rankVariable : Expr (Sum (Fin 4) (Fin 17)) := .var (Sum.inr 16)
  let beta : Expr (Sum (Fin 4) (Fin 17)) := .constant (p 0)
  let MC : Expr (Sum (Fin 4) (Fin 17)) := .constant (p 2)
  let MF : Expr (Sum (Fin 4) (Fin 17)) := .constant (p 3)
  let c : Expr (Sum (Fin 4) (Fin 17)) := .var (Sum.inl 0)
  let a : Expr (Sum (Fin 4) (Fin 17)) := .var (Sum.inl 1)
  let ell : Expr (Sum (Fin 4) (Fin 17)) := .var (Sum.inl 2)
  let Bt : Expr (Sum (Fin 4) (Fin 17)) := .var (Sum.inl 3)
  let qm := J * beta
  let q := 1 + qm
  let q2 := q * q
  let q3 := q * q2
  let U := Y * q2
  let qF := q - F
  let E := X * Y
  let k := eta + zeta
  let c2 := c * c
  let g15 := 4 * a
  let H := 3 + g15
  let g17 := a * a
  let Delta := H + g17
  let g19 := a * c
  let b0 := X + g19
  let M := q3 * qm
  let g30 := ell + k
  let g31 := g30 + r
  let root_skew := k * Bt
  let root_inner := g31 - root_skew
  let root_scaled := scaleVariable * root_inner
  let g33 := Y * qm
  let root_btq3 := Bt * q3
  let root_sum := root_scaled + g33
  let Z := root_sum - root_btq3
  let g38 := Z * Z
  let g39 := scaleVariable * scaleVariable
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
  let g52 := k - rankVariable
  let r0 := g52 - 1
  let g54 := mainScaleVariable * gamma
  let g55 := E * q
  let g56 := g54 + g55
  let shift := g56 - r0
  let g58 := mainScaleVariable * b0
  let g59 := H * shift
  let Dstar := g58 + g59
  let g61 := Dstar * Dstar
  let g62 := mainScaleVariable * mainScaleVariable
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
  let g74 := T * c
  let g75 := g74 - rankVariable
  let g76 := f2 * g75
  let V := g76 - c
  let y2 := y * y
  let g80 := V * V
  let g81 := y2 - squareVariable
  let g82 := Q * g81
  let Fa := y2 - g82
  let auxResidual := Fa - 1
  let squareDifference := squareVariable - g80
  let scaleDifference := scaleVariable - M
  let mainScaleDifference := mainScaleVariable - U
  let rankDifference := rankVariable - R
  (A0,A1,auxResidual,g72,squareDifference,scaleDifference,mainScaleDifference,rankDifference)

def cExpression (_p : Fin 4 → ℤ) : Expr (Fin 17) :=
  let Y : Expr (Fin 17) := .var 7
  let eta : Expr (Fin 17) := .var 9
  let zeta : Expr (Fin 17) := .var 10
  let k := eta + zeta
  let kY := Y * k
  let c := eta + kY
  c

def aExpression (_p : Fin 4 → ℤ) : Expr (Fin 17) :=
  let X : Expr (Fin 17) := .var 6
  let Y : Expr (Fin 17) := .var 7
  let E := X * Y
  let a := E + Y
  a

def ellExpression (_p : Fin 4 → ℤ) : Expr (Fin 17) :=
  let X : Expr (Fin 17) := .var 6
  let Y : Expr (Fin 17) := .var 7
  let eta : Expr (Fin 17) := .var 9
  let zeta : Expr (Fin 17) := .var 10
  let E := X * Y
  let k := eta + zeta
  let kY := Y * k
  let ell := E * kY
  ell

def wExpression (p : Fin 4 → ℤ) : Expr (Fin 17) :=
  let J : Expr (Fin 17) := .var 0
  let F : Expr (Fin 17) := .var 1
  let alpha : Expr (Fin 17) := .var 2
  let X : Expr (Fin 17) := .var 6
  let beta : Expr (Fin 17) := .constant (p 0)
  let K0 : Expr (Fin 17) := .constant (p 1)
  let qm := J * beta
  let q := 1 + qm
  let qF := q - F
  let C := qF - alpha
  let g25 := K0 * q
  let g26 := X + g25
  let g27 := C * g26
  let g28 := F * q
  let Bt := g27 - g28
  Bt

def literal (p : Fin 4 → ℤ) : Expr (Fin 22) :=
  let J : Expr (Fin 22) := .var 0
  let F : Expr (Fin 22) := .var 1
  let alpha : Expr (Fin 22) := .var 2
  let f : Expr (Fin 22) := .var 3
  let i : Expr (Fin 22) := .var 4
  let T : Expr (Fin 22) := .var 5
  let X : Expr (Fin 22) := .var 6
  let Y : Expr (Fin 22) := .var 7
  let r : Expr (Fin 22) := .var 8
  let eta : Expr (Fin 22) := .var 9
  let zeta : Expr (Fin 22) := .var 10
  let y : Expr (Fin 22) := .var 11
  let gamma : Expr (Fin 22) := .var 12
  let squareVariable : Expr (Fin 22) := .var 13
  let scaleVariable : Expr (Fin 22) := .var 14
  let mainScaleVariable : Expr (Fin 22) := .var 15
  let rankVariable : Expr (Fin 22) := .var 16
  let cVariable : Expr (Fin 22) := .var 17
  let aVariable : Expr (Fin 22) := .var 18
  let ellVariable : Expr (Fin 22) := .var 19
  let wPositive : Expr (Fin 22) := .var 20
  let wNegative : Expr (Fin 22) := .var 21
  let beta : Expr (Fin 22) := .constant (p 0)
  let K0 : Expr (Fin 22) := .constant (p 1)
  let MC : Expr (Fin 22) := .constant (p 2)
  let MF : Expr (Fin 22) := .constant (p 3)
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
  let c2 := cVariable * cVariable
  let a := E + Y
  let g15 := 4 * aVariable
  let H := 3 + g15
  let g17 := aVariable * aVariable
  let Delta := H + g17
  let g19 := aVariable * cVariable
  let b0 := X + g19
  let ell := E * kY
  let M := q3 * qm
  let g25 := K0 * q
  let g26 := X + g25
  let g27 := C * g26
  let g28 := F * q
  let Bt := g27 - g28
  let g30 := ellVariable + k
  let g31 := g30 + r
  let namedBt := wPositive - wNegative
  let root_skew := k * namedBt
  let root_inner := g31 - root_skew
  let root_scaled := scaleVariable * root_inner
  let g33 := Y * qm
  let root_btq3 := namedBt * q3
  let root_sum := root_scaled + g33
  let Z := root_sum - root_btq3
  let g38 := Z * Z
  let g39 := scaleVariable * scaleVariable
  let g40 := ellVariable * g30
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
  let g52 := k - rankVariable
  let r0 := g52 - 1
  let g54 := mainScaleVariable * gamma
  let g55 := E * q
  let g56 := g54 + g55
  let shift := g56 - r0
  let g58 := mainScaleVariable * b0
  let g59 := H * shift
  let Dstar := g58 + g59
  let g61 := Dstar * Dstar
  let g62 := mainScaleVariable * mainScaleVariable
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
  let g74 := T * cVariable
  let g75 := g74 - rankVariable
  let g76 := f2 * g75
  let V := g76 - cVariable
  let y2 := y * y
  let g80 := V * V
  let g81 := y2 - squareVariable
  let g82 := Q * g81
  let Fa := y2 - g82
  let auxResidual := Fa - 1
  let firstSquare := A0 * A0
  let mainSquare := A1 * A1
  let auxSquare := auxResidual * auxResidual
  let strongSquare := g72 * g72
  let firstMain := firstSquare + mainSquare
  let firstMainAux := firstMain + auxSquare
  let sumSquares := firstMainAux + strongSquare
  let squareDifference := squareVariable - g80
  let squareConstraint := squareDifference * squareDifference
  let sumWithConstraint := sumSquares + squareConstraint
  let scaleDifference := scaleVariable - M
  let scaleConstraint := scaleDifference * scaleDifference
  let finalWithScale := sumWithConstraint + scaleConstraint
  let mainScaleDifference := mainScaleVariable - U
  let mainScaleConstraint := mainScaleDifference * mainScaleDifference
  let finalWithMainScale := finalWithScale + mainScaleConstraint
  let rankDifference := rankVariable - R
  let rankConstraint := rankDifference * rankDifference
  let finalWithRank := finalWithMainScale + rankConstraint
  let cDifference := cVariable - c
  let cConstraint := cDifference * cDifference
  let aDifference := aVariable - a
  let aConstraint := aDifference * aDifference
  let ellDifference := ellVariable - ell
  let ellConstraint := ellDifference * ellDifference
  let wDifference := namedBt - Bt
  let wConstraint := wDifference * wDifference
  let addC := finalWithRank + cConstraint
  let addA := addC + aConstraint
  let addEll := addA + ellConstraint
  let finalWithNamedValues := addEll + wConstraint
  finalWithNamedValues

def embed (i : Fin 17) : Fin 22 := ⟨i.val, Nat.lt_trans i.isLt (by decide)⟩
def holes : Fin 4 → Expr (Fin 22) := ![.var 17, .var 18, .var 19, .var 20 - .var 21]
def fill (e : Fin 4 → Expr (Fin 22)) : Sum (Fin 4) (Fin 17) → Expr (Fin 22)
  | .inl i => e i
  | .inr i => .var (embed i)
def origHoles (p : Fin 4 → ℤ) : Fin 4 → Expr (Fin 17) := ![cExpression p, aExpression p, ellExpression p, wExpression p]
def origFill (p : Fin 4 → ℤ) : Sum (Fin 4) (Fin 17) → Expr (Fin 17)
  | .inl i => origHoles p i
  | .inr i => .var i
def lift (e : Expr (Fin 17)) : Expr (Fin 22) := e.subst (fun i => .var (embed i))

 theorem context_original (p : Fin 4 → ℤ) :
    (contextAt p).subst (origFill p) = AdaptiveRankWitness17.literal p := by
  rfl

 theorem literal_context (p : Fin 4 → ℤ) :
    literal p = (contextAt p).subst (fill holes) +
      (holes 0-lift (cExpression p))*(holes 0-lift (cExpression p)) +
      (holes 1-lift (aExpression p))*(holes 1-lift (aExpression p)) +
      (holes 2-lift (ellExpression p))*(holes 2-lift (ellExpression p)) +
      (holes 3-lift (wExpression p))*(holes 3-lift (wExpression p)) := by
  rfl

 theorem context_squares (p : Fin 4 → ℤ) :
    contextAt p = (residualsAt p).1*(residualsAt p).1 +
      (residualsAt p).2.1*(residualsAt p).2.1 +
      (residualsAt p).2.2.1*(residualsAt p).2.2.1 +
      (residualsAt p).2.2.2.1*(residualsAt p).2.2.2.1 +
      (residualsAt p).2.2.2.2.1*(residualsAt p).2.2.2.2.1 +
      (residualsAt p).2.2.2.2.2.1*(residualsAt p).2.2.2.2.2.1 +
      (residualsAt p).2.2.2.2.2.2.1*(residualsAt p).2.2.2.2.2.2.1 +
      (residualsAt p).2.2.2.2.2.2.2*(residualsAt p).2.2.2.2.2.2.2 := by
  rfl


variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem append_square_zero_iff {σ : Type*} (a b : Expr σ) (v : σ → V) (n : V)
    (ha : SignedRep a v (natural n)) :
    InternalZero (a+b*b) v ↔ InternalZero a v ∧ InternalZero b v := by
  have hab := rep_add_nat ha (rawSquare_rep b v)
  change SignedRep (a + b*b) v (natural _) at hab
  rw [rep_zero_iff hab, rep_zero_iff ha]
  simp only [sum_eq_zero_iff, mul_self_eq_zero, magnitude_zero_iff]
  rfl

theorem literal_zero_parts (p : Fin 4 → ℤ) (v : Fin 22 → V) :
    InternalZero (literal p) v ↔
      InternalZero ((contextAt p).subst (fill holes)) v ∧
      InternalZero (holes 0-lift (cExpression p)) v ∧
      InternalZero (holes 1-lift (aExpression p)) v ∧
      InternalZero (holes 2-lift (ellExpression p)) v ∧
      InternalZero (holes 3-lift (wExpression p)) v := by
  rw [literal_context]
  let z := fill holes
  let a := ((residualsAt p).1).subst z
  let b := ((residualsAt p).2.1).subst z
  let c := ((residualsAt p).2.2.1).subst z
  let d := ((residualsAt p).2.2.2.1).subst z
  let e := ((residualsAt p).2.2.2.2.1).subst z
  let f := ((residualsAt p).2.2.2.2.2.1).subst z
  let g := ((residualsAt p).2.2.2.2.2.2.1).subst z
  let h := ((residualsAt p).2.2.2.2.2.2.2).subst z
  let i := holes 0-lift (cExpression p)
  let j := holes 1-lift (aExpression p)
  let k := holes 2-lift (ellExpression p)
  let l := holes 3-lift (wExpression p)
  let base := a*a+b*b+c*c+d*d+e*e+f*f+g*g+h*h
  have r8 := rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat
    (rawSquare_rep a v) (rawSquare_rep b v)) (rawSquare_rep c v)) (rawSquare_rep d v))
    (rawSquare_rep e v)) (rawSquare_rep f v)) (rawSquare_rep g v)) (rawSquare_rep h v)
  change SignedRep base v (natural _) at r8
  have r9 := rep_add_nat r8 (rawSquare_rep i v)
  change SignedRep (base+i*i) v (natural _) at r9
  have r10 := rep_add_nat r9 (rawSquare_rep j v)
  change SignedRep (base+i*i+j*j) v (natural _) at r10
  have r11 := rep_add_nat r10 (rawSquare_rep k v)
  change SignedRep (base+i*i+j*j+k*k) v (natural _) at r11
  change InternalZero (base+i*i+j*j+k*k+l*l) v ↔
    InternalZero base v ∧ InternalZero i v ∧ InternalZero j v ∧ InternalZero k v ∧ InternalZero l v
  rw [append_square_zero_iff _ _ _ _ r11, append_square_zero_iff _ _ _ _ r10,
    append_square_zero_iff _ _ _ _ r9, append_square_zero_iff _ _ _ _ r8]
  simp only [and_assoc]

theorem context_lift (p : Fin 4 → ℤ) :
    (contextAt p).subst (fill (fun i => lift (origHoles p i))) =
      (AdaptiveRankWitness17.literal p).subst (fun i => .var (embed i)) := by
  rw [←context_original p]
  rfl

theorem context_zero_iff_of_constraints (p : Fin 4 → ℤ) (v : Fin 22 → V)
    (hc : ∀ i : Fin 4, InternalZero (holes i-lift (origHoles p i)) v) :
    InternalZero ((contextAt p).subst (fill holes)) v ↔
      InternalZero (AdaptiveRankWitness17.literal p) (fun i => v (embed i)) := by
  have h : Equivalent (splitEval ((contextAt p).subst (fill holes)) v)
      (splitEval ((contextAt p).subst (fill (fun i => lift (origHoles p i)))) v) := by
    apply splitEval_subst_equiv
    intro i
    cases i with
    | inl j => exact (sub_zero_iff_equiv _ _ v).mp (hc j)
    | inr j => exact equivalent_refl _
  have hz := equivalent_zero_iff h
  rw [context_lift, splitEval_subst_var] at hz
  exact hz

theorem literal_zero_project (p : Fin 4 → ℤ) (v : Fin 22 → V)
    (h : InternalZero (literal p) v) :
    InternalZero (AdaptiveRankWitness17.literal p) (fun i => v (embed i)) := by
  obtain ⟨hc,h0,h1,h2,h3⟩ := (literal_zero_parts p v).mp h
  apply (context_zero_iff_of_constraints p v ?_).mp hc
  intro i
  fin_cases i <;> assumption


def extend22 (v : Fin 17 → V) (c a ell wp wn : V) : Fin 22 → V :=
  fun i => if h : i.val < 17 then v ⟨i.val,h⟩ else
    if i.val = 17 then c else if i.val = 18 then a else
    if i.val = 19 then ell else if i.val = 20 then wp else wn

omit [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
theorem extend22_embed (v : Fin 17 → V) (c a ell wp wn : V) (i : Fin 17) :
    extend22 v c a ell wp wn (embed i) = v i := by
  simp [extend22, embed, i.isLt]

omit [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
theorem extend22_last (v : Fin 17 → V) (c a ell wp wn : V) :
    extend22 v c a ell wp wn 17 = c ∧ extend22 v c a ell wp wn 18 = a ∧
    extend22 v c a ell wp wn 19 = ell ∧ extend22 v c a ell wp wn 20 = wp ∧
    extend22 v c a ell wp wn 21 = wn := by
  simp [extend22]

theorem named_natural_reps (p : Fin 4 → ℤ) (v : Fin 17 → V) :
    SignedRep (cExpression p) v (natural (v 9+v 7*(v 9+v 10))) ∧
    SignedRep (aExpression p) v (natural (v 6*v 7+v 7)) ∧
    SignedRep (ellExpression p) v (natural ((v 6*v 7)*(v 7*(v 9+v 10)))) := by
  constructor
  · exact rep_add_nat (rep_var v 9) (rep_mul_nat (rep_var v 7) (rep_add_nat (rep_var v 9) (rep_var v 10)))
  constructor
  · exact rep_add_nat (rep_mul_nat (rep_var v 6) (rep_var v 7)) (rep_var v 7)
  · exact rep_mul_nat (rep_mul_nat (rep_var v 6) (rep_var v 7))
      (rep_mul_nat (rep_var v 7) (rep_add_nat (rep_var v 9) (rep_var v 10)))


theorem exists_positive_extension (p : Fin 4 → ℤ) (v : Fin 17 → V)
    (hv : ∀ i, 0<v i) (hz : InternalZero (AdaptiveRankWitness17.literal p) v) :
    ∃ u : Fin 22 → V, (∀ i, 0<u i) ∧ InternalZero (literal p) u := by
  let c : V := v 9+v 7*(v 9+v 10)
  let a : V := v 6*v 7+v 7
  let ell : V := (v 6*v 7)*(v 7*(v 9+v 10))
  let wp : V := (pairEval (wExpression p) v).1+1
  let wn : V := (pairEval (wExpression p) v).2+1
  let u : Fin 22 → V := extend22 v c a ell wp wn
  have he : (fun i : Fin 17 => u (embed i)) = v := by
    funext i
    exact extend22_embed _ _ _ _ _ _ i
  have hcpos : 0<c := by dsimp [c]; exact add_pos (hv 9) (mul_pos (hv 7) (add_pos (hv 9) (hv 10)))
  have hapos : 0<a := by dsimp [a]; exact add_pos (mul_pos (hv 6) (hv 7)) (hv 7)
  have hellpos : 0<ell := by dsimp [ell]; exact mul_pos (mul_pos (hv 6) (hv 7)) (mul_pos (hv 7) (add_pos (hv 9) (hv 10)))
  have hwppos : 0<wp := by dsimp [wp]; exact lt_of_le_of_lt (Arithmetic.zero_le _) (lt_add_one _)
  have hwnpos : 0<wn := by dsimp [wn]; exact lt_of_le_of_lt (Arithmetic.zero_le _) (lt_add_one _)
  have hu : ∀ i, 0<u i := by
    intro i
    by_cases hi : i.val<17
    · simpa [u,extend22,hi] using hv ⟨i.val,hi⟩
    · simp only [u,extend22,hi,↓reduceDIte]
      split <;> first | exact hcpos | split <;> first | exact hapos | split <;> first | exact hellpos | split <;> first | exact hwppos | exact hwnpos
  obtain ⟨hu17,hu18,hu19,hu20,hu21⟩ := extend22_last v c a ell wp wn
  have hrep : ∀ i : Fin 4, Equivalent (pairEval (holes i) u)
      (pairEval (lift (origHoles p i)) u) := by
    intro i
    fin_cases i
    · have hr := (named_natural_reps p v).1
      have hvar : Equivalent (pairEval (holes 0) u) (natural c) := by
        simp [holes, pairEval, Expr.splitNatural, NatExpr.evalSemiring, Equivalent, natural, u, hu17]
      have hval : Equivalent (pairEval (lift (origHoles p 0)) u) (natural c) := by
        change Equivalent (splitEval (lift (cExpression p)) u) (natural c)
        rw [lift,splitEval_subst_var,he]
        exact hr
      exact equivalent_trans hvar (equivalent_symm hval)
    · have hr := (named_natural_reps p v).2.1
      have hvar : Equivalent (pairEval (holes 1) u) (natural a) := by
        simp [holes, pairEval, Expr.splitNatural, NatExpr.evalSemiring, Equivalent, natural, u, hu18]
      have hval : Equivalent (pairEval (lift (origHoles p 1)) u) (natural a) := by
        change Equivalent (splitEval (lift (aExpression p)) u) (natural a)
        rw [lift,splitEval_subst_var,he]
        exact hr
      exact equivalent_trans hvar (equivalent_symm hval)
    · have hr := (named_natural_reps p v).2.2
      have hvar : Equivalent (pairEval (holes 2) u) (natural ell) := by
        simp [holes, pairEval, Expr.splitNatural, NatExpr.evalSemiring, Equivalent, natural, u, hu19]
      have hval : Equivalent (pairEval (lift (origHoles p 2)) u) (natural ell) := by
        change Equivalent (splitEval (lift (ellExpression p)) u) (natural ell)
        rw [lift,splitEval_subst_var,he]
        exact hr
      exact equivalent_trans hvar (equivalent_symm hval)
    · have hval : pairEval (lift (origHoles p 3)) u = pairEval (wExpression p) v := by
        change splitEval (lift (wExpression p)) u = splitEval (wExpression p) v
        rw [lift,splitEval_subst_var,he]
      change Equivalent (pairEval (holes 3) u) (pairEval (lift (origHoles p 3)) u)
      rw [hval]
      change Equivalent (pairEval (Expr.sub (.var 20) (.var 21)) u) (pairEval (wExpression p) v)
      simp only [pairEval, Expr.splitNatural, NatExpr.evalSemiring, Equivalent, u, extend22]
      dsimp [wp,wn,pairEval]
      ring
  have hconstraint : ∀ i : Fin 4, InternalZero (holes i-lift (origHoles p i)) u := by
    intro i
    exact (sub_zero_iff_equiv _ _ u).mpr (hrep i)
  have hcontext : InternalZero ((contextAt p).subst (fill holes)) u :=
    (context_zero_iff_of_constraints _ u hconstraint).mpr (by simpa only [he] using hz)
  refine ⟨u,hu,(literal_zero_parts _ u).mpr ?_⟩
  exact ⟨hcontext,hconstraint 0,hconstraint 1,hconstraint 2,hconstraint 3⟩


theorem shifted_literal_to_parent (p : Fin 4 → ℤ) (v : Fin 22 → V)
    (hz : InternalZero (positiveShift (literal p)) v) :
    InternalZero (positiveShift (AdaptiveRankWitness17.literal p)) (fun i => v (embed i)) := by
  rw [internalZero_positiveShift] at hz ⊢
  exact literal_zero_project p (fun i => v i+1) hz

theorem shifted_parent_to_literal (p : Fin 4 → ℤ) (v : Fin 17 → V)
    (hz : InternalZero (positiveShift (AdaptiveRankWitness17.literal p)) v) :
    ∃ u : Fin 22 → V, InternalZero (positiveShift (literal p)) u := by
  have hp : ∀ i : Fin 17, 0<v i+1 := by
    intro i
    exact lt_of_le_of_lt (Arithmetic.zero_le _) (lt_add_one _)
  have hz' : InternalZero (AdaptiveRankWitness17.literal p) (fun i => v i+1) :=
    (internalZero_positiveShift _ _).mp hz
  obtain ⟨u,hu,hzero⟩ := exists_positive_extension p (fun i => v i+1) hp hz'
  refine ⟨fun i => u i-1, ?_⟩
  rw [internalZero_positiveShift]
  have he : (fun i => (u i-1)+1) = u := by
    funext i
    exact tsub_add_cancel_of_le (pos_iff_one_le.mp (hu i))
  rw [he]
  exact hzero

theorem shifted_no_zero_iff (p : Fin 4 → ℤ) :
    (∀ v : Fin 22 → V, ¬ InternalZero (positiveShift (literal p)) v) ↔
    (∀ v : Fin 17 → V, ¬ InternalZero (positiveShift (AdaptiveRankWitness17.literal p)) v) := by
  constructor
  · intro h v hz
    obtain ⟨u,hu⟩ := shifted_parent_to_literal p v hz
    exact h u hu
  · intro h v hz
    exact h _ (shifted_literal_to_parent p v hz)

end DiophantineConsistency.AdaptiveNamedValues22
