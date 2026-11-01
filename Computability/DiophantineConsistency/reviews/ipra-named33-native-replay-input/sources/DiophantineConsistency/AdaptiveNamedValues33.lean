import DiophantineConsistency.AdaptiveNamedValues26

/-! A degree-8 candidate obtained by naming signed values and a positive discriminant.
The shifted no-zero theorem holds for all integer port vectors in every
IΣ₁ model, including the actual fixed port vector. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
noncomputable section
namespace DiophantineConsistency.AdaptiveNamedValues33
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticSignedPairExpressions ArithmeticAdaptiveFactorMagnitude2011
open AdaptiveFirstRootFactor87Syntax AdaptiveDirectOrdinate86Context AdaptiveDirectOrdinate86Lift
open AdaptiveSquareWitnessDirect14 AdaptiveScaleWitness15 AdaptiveMainScaleWitness16 AdaptiveRankWitness17 AdaptiveDirectOrdinateSquareSums AdaptiveNamedValues22 AdaptiveNamedValues26


def contextAt (p : Fin 4 → ℤ) : Expr (Sum (Fin 4) (Fin 26)) :=
  let J : Expr (Sum (Fin 4) (Fin 26)) := .var (Sum.inr 0)
  let F : Expr (Sum (Fin 4) (Fin 26)) := .var (Sum.inr 1)
  let alpha : Expr (Sum (Fin 4) (Fin 26)) := .var (Sum.inr 2)
  let f : Expr (Sum (Fin 4) (Fin 26)) := .var (Sum.inr 3)
  let i : Expr (Sum (Fin 4) (Fin 26)) := .var (Sum.inr 4)
  let T : Expr (Sum (Fin 4) (Fin 26)) := .var (Sum.inr 5)
  let X : Expr (Sum (Fin 4) (Fin 26)) := .var (Sum.inr 6)
  let Y : Expr (Sum (Fin 4) (Fin 26)) := .var (Sum.inr 7)
  let r : Expr (Sum (Fin 4) (Fin 26)) := .var (Sum.inr 8)
  let eta : Expr (Sum (Fin 4) (Fin 26)) := .var (Sum.inr 9)
  let zeta : Expr (Sum (Fin 4) (Fin 26)) := .var (Sum.inr 10)
  let y : Expr (Sum (Fin 4) (Fin 26)) := .var (Sum.inr 11)
  let gamma : Expr (Sum (Fin 4) (Fin 26)) := .var (Sum.inr 12)
  let squareVariable : Expr (Sum (Fin 4) (Fin 26)) := .var (Sum.inr 13)
  let scaleVariable : Expr (Sum (Fin 4) (Fin 26)) := .var (Sum.inr 14)
  let mainScaleVariable : Expr (Sum (Fin 4) (Fin 26)) := .var (Sum.inr 15)
  let rankVariable : Expr (Sum (Fin 4) (Fin 26)) := .var (Sum.inr 16)
  let cVariable : Expr (Sum (Fin 4) (Fin 26)) := .var (Sum.inr 17)
  let aVariable : Expr (Sum (Fin 4) (Fin 26)) := .var (Sum.inr 18)
  let ellVariable : Expr (Sum (Fin 4) (Fin 26)) := .var (Sum.inr 19)
  let wPositive : Expr (Sum (Fin 4) (Fin 26)) := .var (Sum.inr 20)
  let wNegative : Expr (Sum (Fin 4) (Fin 26)) := .var (Sum.inr 21)
  let cubeVariable : Expr (Sum (Fin 4) (Fin 26)) := .var (Sum.inr 22)
  let productVariable : Expr (Sum (Fin 4) (Fin 26)) := .var (Sum.inr 23)
  let fSquareVariable : Expr (Sum (Fin 4) (Fin 26)) := .var (Sum.inr 24)
  let cSquareVariable : Expr (Sum (Fin 4) (Fin 26)) := .var (Sum.inr 25)
  let beta : Expr (Sum (Fin 4) (Fin 26)) := .constant (p 0)
  let K0 : Expr (Sum (Fin 4) (Fin 26)) := .constant (p 1)
  let MC : Expr (Sum (Fin 4) (Fin 26)) := .constant (p 2)
  let MF : Expr (Sum (Fin 4) (Fin 26)) := .constant (p 3)
  let hole0 : Expr (Sum (Fin 4) (Fin 26)) := .var (Sum.inl 0)
  let hole1 : Expr (Sum (Fin 4) (Fin 26)) := .var (Sum.inl 1)
  let hole2 : Expr (Sum (Fin 4) (Fin 26)) := .var (Sum.inl 2)
  let hole3 : Expr (Sum (Fin 4) (Fin 26)) := .var (Sum.inl 3)
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
  let g19 := aVariable * cVariable
  let b0 := X + g19
  let ell := E * kY
  let M := cubeVariable * qm
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
  let root_btq3 := namedBt * cubeVariable
  let root_sum := root_scaled + g33
  let Z := hole0
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
  let g56 := g54 + productVariable
  let shift := g56 - r0
  let g58 := mainScaleVariable * b0
  let g59 := H * shift
  let Dstar := hole1
  let g61 := Dstar * Dstar
  let g62 := mainScaleVariable * mainScaleVariable
  let g63 := hole3 * cSquareVariable
  let g64 := 1 + g63
  let g65 := g62 * g64
  let A1 := g61 - g65
  let f2 := f * f
  let rho := fSquareVariable - 1
  let Q := hole3 * rho
  let I := cSquareVariable * i
  let g71 := I * I
  let g72 := g71 - Q
  let g74 := T * cVariable
  let g75 := g74 - rankVariable
  let g76 := fSquareVariable * g75
  let V := hole2
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
  let cubeDifference := cubeVariable - q3
  let cubeConstraint := cubeDifference * cubeDifference
  let productDifference := productVariable - g55
  let productConstraint := productDifference * productDifference
  let fSquareDifference := fSquareVariable - f2
  let fSquareConstraint := fSquareDifference * fSquareDifference
  let cSquareDifference := cSquareVariable - c2
  let cSquareConstraint := cSquareDifference * cSquareDifference
  let addCube := finalWithNamedValues + cubeConstraint
  let addProduct := addCube + productConstraint
  let addFSquare := addProduct + fSquareConstraint
  let addCSquare := addFSquare + cSquareConstraint
  addCSquare

def residualsAt (p : Fin 4 → ℤ) : Fin 16 → Expr (Sum (Fin 4) (Fin 26)) :=
  let J : Expr (Sum (Fin 4) (Fin 26)) := .var (Sum.inr 0)
  let F : Expr (Sum (Fin 4) (Fin 26)) := .var (Sum.inr 1)
  let alpha : Expr (Sum (Fin 4) (Fin 26)) := .var (Sum.inr 2)
  let f : Expr (Sum (Fin 4) (Fin 26)) := .var (Sum.inr 3)
  let i : Expr (Sum (Fin 4) (Fin 26)) := .var (Sum.inr 4)
  let T : Expr (Sum (Fin 4) (Fin 26)) := .var (Sum.inr 5)
  let X : Expr (Sum (Fin 4) (Fin 26)) := .var (Sum.inr 6)
  let Y : Expr (Sum (Fin 4) (Fin 26)) := .var (Sum.inr 7)
  let r : Expr (Sum (Fin 4) (Fin 26)) := .var (Sum.inr 8)
  let eta : Expr (Sum (Fin 4) (Fin 26)) := .var (Sum.inr 9)
  let zeta : Expr (Sum (Fin 4) (Fin 26)) := .var (Sum.inr 10)
  let y : Expr (Sum (Fin 4) (Fin 26)) := .var (Sum.inr 11)
  let gamma : Expr (Sum (Fin 4) (Fin 26)) := .var (Sum.inr 12)
  let squareVariable : Expr (Sum (Fin 4) (Fin 26)) := .var (Sum.inr 13)
  let scaleVariable : Expr (Sum (Fin 4) (Fin 26)) := .var (Sum.inr 14)
  let mainScaleVariable : Expr (Sum (Fin 4) (Fin 26)) := .var (Sum.inr 15)
  let rankVariable : Expr (Sum (Fin 4) (Fin 26)) := .var (Sum.inr 16)
  let cVariable : Expr (Sum (Fin 4) (Fin 26)) := .var (Sum.inr 17)
  let aVariable : Expr (Sum (Fin 4) (Fin 26)) := .var (Sum.inr 18)
  let ellVariable : Expr (Sum (Fin 4) (Fin 26)) := .var (Sum.inr 19)
  let wPositive : Expr (Sum (Fin 4) (Fin 26)) := .var (Sum.inr 20)
  let wNegative : Expr (Sum (Fin 4) (Fin 26)) := .var (Sum.inr 21)
  let cubeVariable : Expr (Sum (Fin 4) (Fin 26)) := .var (Sum.inr 22)
  let productVariable : Expr (Sum (Fin 4) (Fin 26)) := .var (Sum.inr 23)
  let fSquareVariable : Expr (Sum (Fin 4) (Fin 26)) := .var (Sum.inr 24)
  let cSquareVariable : Expr (Sum (Fin 4) (Fin 26)) := .var (Sum.inr 25)
  let beta : Expr (Sum (Fin 4) (Fin 26)) := .constant (p 0)
  let K0 : Expr (Sum (Fin 4) (Fin 26)) := .constant (p 1)
  let MC : Expr (Sum (Fin 4) (Fin 26)) := .constant (p 2)
  let MF : Expr (Sum (Fin 4) (Fin 26)) := .constant (p 3)
  let hole0 : Expr (Sum (Fin 4) (Fin 26)) := .var (Sum.inl 0)
  let hole1 : Expr (Sum (Fin 4) (Fin 26)) := .var (Sum.inl 1)
  let hole2 : Expr (Sum (Fin 4) (Fin 26)) := .var (Sum.inl 2)
  let hole3 : Expr (Sum (Fin 4) (Fin 26)) := .var (Sum.inl 3)
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
  let g19 := aVariable * cVariable
  let b0 := X + g19
  let ell := E * kY
  let M := cubeVariable * qm
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
  let root_btq3 := namedBt * cubeVariable
  let root_sum := root_scaled + g33
  let Z := hole0
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
  let g56 := g54 + productVariable
  let shift := g56 - r0
  let g58 := mainScaleVariable * b0
  let g59 := H * shift
  let Dstar := hole1
  let g61 := Dstar * Dstar
  let g62 := mainScaleVariable * mainScaleVariable
  let g63 := hole3 * cSquareVariable
  let g64 := 1 + g63
  let g65 := g62 * g64
  let A1 := g61 - g65
  let f2 := f * f
  let rho := fSquareVariable - 1
  let Q := hole3 * rho
  let I := cSquareVariable * i
  let g71 := I * I
  let g72 := g71 - Q
  let g74 := T * cVariable
  let g75 := g74 - rankVariable
  let g76 := fSquareVariable * g75
  let V := hole2
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
  let cubeDifference := cubeVariable - q3
  let cubeConstraint := cubeDifference * cubeDifference
  let productDifference := productVariable - g55
  let productConstraint := productDifference * productDifference
  let fSquareDifference := fSquareVariable - f2
  let fSquareConstraint := fSquareDifference * fSquareDifference
  let cSquareDifference := cSquareVariable - c2
  let cSquareConstraint := cSquareDifference * cSquareDifference
  let addCube := finalWithNamedValues + cubeConstraint
  let addProduct := addCube + productConstraint
  let addFSquare := addProduct + fSquareConstraint
  let addCSquare := addFSquare + cSquareConstraint
  ![A0,A1,auxResidual,g72,squareDifference,scaleDifference,mainScaleDifference,rankDifference,cDifference,aDifference,ellDifference,wDifference,cubeDifference,productDifference,fSquareDifference,cSquareDifference]

def zExpression (p : Fin 4 → ℤ) : Expr (Fin 26) :=
  let J : Expr (Fin 26) := .var (0)
  let F : Expr (Fin 26) := .var (1)
  let alpha : Expr (Fin 26) := .var (2)
  let f : Expr (Fin 26) := .var (3)
  let i : Expr (Fin 26) := .var (4)
  let T : Expr (Fin 26) := .var (5)
  let X : Expr (Fin 26) := .var (6)
  let Y : Expr (Fin 26) := .var (7)
  let r : Expr (Fin 26) := .var (8)
  let eta : Expr (Fin 26) := .var (9)
  let zeta : Expr (Fin 26) := .var (10)
  let y : Expr (Fin 26) := .var (11)
  let gamma : Expr (Fin 26) := .var (12)
  let squareVariable : Expr (Fin 26) := .var (13)
  let scaleVariable : Expr (Fin 26) := .var (14)
  let mainScaleVariable : Expr (Fin 26) := .var (15)
  let rankVariable : Expr (Fin 26) := .var (16)
  let cVariable : Expr (Fin 26) := .var (17)
  let aVariable : Expr (Fin 26) := .var (18)
  let ellVariable : Expr (Fin 26) := .var (19)
  let wPositive : Expr (Fin 26) := .var (20)
  let wNegative : Expr (Fin 26) := .var (21)
  let cubeVariable : Expr (Fin 26) := .var (22)
  let productVariable : Expr (Fin 26) := .var (23)
  let fSquareVariable : Expr (Fin 26) := .var (24)
  let cSquareVariable : Expr (Fin 26) := .var (25)
  let beta : Expr (Fin 26) := .constant (p 0)
  let K0 : Expr (Fin 26) := .constant (p 1)
  let MC : Expr (Fin 26) := .constant (p 2)
  let MF : Expr (Fin 26) := .constant (p 3)
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
  let DeltaComputed := H + g17
  let g19 := aVariable * cVariable
  let b0 := X + g19
  let ell := E * kY
  let M := cubeVariable * qm
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
  let root_btq3 := namedBt * cubeVariable
  let root_sum := root_scaled + g33
  let ZComputed := root_sum - root_btq3
  ZComputed

def dExpression (p : Fin 4 → ℤ) : Expr (Fin 26) :=
  let J : Expr (Fin 26) := .var (0)
  let F : Expr (Fin 26) := .var (1)
  let alpha : Expr (Fin 26) := .var (2)
  let f : Expr (Fin 26) := .var (3)
  let i : Expr (Fin 26) := .var (4)
  let T : Expr (Fin 26) := .var (5)
  let X : Expr (Fin 26) := .var (6)
  let Y : Expr (Fin 26) := .var (7)
  let r : Expr (Fin 26) := .var (8)
  let eta : Expr (Fin 26) := .var (9)
  let zeta : Expr (Fin 26) := .var (10)
  let y : Expr (Fin 26) := .var (11)
  let gamma : Expr (Fin 26) := .var (12)
  let squareVariable : Expr (Fin 26) := .var (13)
  let scaleVariable : Expr (Fin 26) := .var (14)
  let mainScaleVariable : Expr (Fin 26) := .var (15)
  let rankVariable : Expr (Fin 26) := .var (16)
  let cVariable : Expr (Fin 26) := .var (17)
  let aVariable : Expr (Fin 26) := .var (18)
  let ellVariable : Expr (Fin 26) := .var (19)
  let wPositive : Expr (Fin 26) := .var (20)
  let wNegative : Expr (Fin 26) := .var (21)
  let cubeVariable : Expr (Fin 26) := .var (22)
  let productVariable : Expr (Fin 26) := .var (23)
  let fSquareVariable : Expr (Fin 26) := .var (24)
  let cSquareVariable : Expr (Fin 26) := .var (25)
  let beta : Expr (Fin 26) := .constant (p 0)
  let K0 : Expr (Fin 26) := .constant (p 1)
  let MC : Expr (Fin 26) := .constant (p 2)
  let MF : Expr (Fin 26) := .constant (p 3)
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
  let DeltaComputed := H + g17
  let g19 := aVariable * cVariable
  let b0 := X + g19
  let ell := E * kY
  let M := cubeVariable * qm
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
  let root_btq3 := namedBt * cubeVariable
  let root_sum := root_scaled + g33
  let ZComputed := root_sum - root_btq3
  let Z := ZComputed
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
  let g56 := g54 + productVariable
  let shift := g56 - r0
  let g58 := mainScaleVariable * b0
  let g59 := H * shift
  let DstarComputed := g58 + g59
  DstarComputed

def vExpression (p : Fin 4 → ℤ) : Expr (Fin 26) :=
  let J : Expr (Fin 26) := .var (0)
  let F : Expr (Fin 26) := .var (1)
  let alpha : Expr (Fin 26) := .var (2)
  let f : Expr (Fin 26) := .var (3)
  let i : Expr (Fin 26) := .var (4)
  let T : Expr (Fin 26) := .var (5)
  let X : Expr (Fin 26) := .var (6)
  let Y : Expr (Fin 26) := .var (7)
  let r : Expr (Fin 26) := .var (8)
  let eta : Expr (Fin 26) := .var (9)
  let zeta : Expr (Fin 26) := .var (10)
  let y : Expr (Fin 26) := .var (11)
  let gamma : Expr (Fin 26) := .var (12)
  let squareVariable : Expr (Fin 26) := .var (13)
  let scaleVariable : Expr (Fin 26) := .var (14)
  let mainScaleVariable : Expr (Fin 26) := .var (15)
  let rankVariable : Expr (Fin 26) := .var (16)
  let cVariable : Expr (Fin 26) := .var (17)
  let aVariable : Expr (Fin 26) := .var (18)
  let ellVariable : Expr (Fin 26) := .var (19)
  let wPositive : Expr (Fin 26) := .var (20)
  let wNegative : Expr (Fin 26) := .var (21)
  let cubeVariable : Expr (Fin 26) := .var (22)
  let productVariable : Expr (Fin 26) := .var (23)
  let fSquareVariable : Expr (Fin 26) := .var (24)
  let cSquareVariable : Expr (Fin 26) := .var (25)
  let beta : Expr (Fin 26) := .constant (p 0)
  let K0 : Expr (Fin 26) := .constant (p 1)
  let MC : Expr (Fin 26) := .constant (p 2)
  let MF : Expr (Fin 26) := .constant (p 3)
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
  let DeltaComputed := H + g17
  let g19 := aVariable * cVariable
  let b0 := X + g19
  let ell := E * kY
  let M := cubeVariable * qm
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
  let root_btq3 := namedBt * cubeVariable
  let root_sum := root_scaled + g33
  let ZComputed := root_sum - root_btq3
  let Z := ZComputed
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
  let g56 := g54 + productVariable
  let shift := g56 - r0
  let g58 := mainScaleVariable * b0
  let g59 := H * shift
  let DstarComputed := g58 + g59
  let Dstar := DstarComputed
  let g61 := Dstar * Dstar
  let g62 := mainScaleVariable * mainScaleVariable
  let g63 := DeltaComputed * cSquareVariable
  let g64 := 1 + g63
  let g65 := g62 * g64
  let A1 := g61 - g65
  let f2 := f * f
  let rho := fSquareVariable - 1
  let Q := DeltaComputed * rho
  let I := cSquareVariable * i
  let g71 := I * I
  let g72 := g71 - Q
  let g74 := T * cVariable
  let g75 := g74 - rankVariable
  let g76 := fSquareVariable * g75
  let VComputed := g76 - cVariable
  VComputed

def deltaExpression (p : Fin 4 → ℤ) : Expr (Fin 26) :=
  let J : Expr (Fin 26) := .var (0)
  let F : Expr (Fin 26) := .var (1)
  let alpha : Expr (Fin 26) := .var (2)
  let f : Expr (Fin 26) := .var (3)
  let i : Expr (Fin 26) := .var (4)
  let T : Expr (Fin 26) := .var (5)
  let X : Expr (Fin 26) := .var (6)
  let Y : Expr (Fin 26) := .var (7)
  let r : Expr (Fin 26) := .var (8)
  let eta : Expr (Fin 26) := .var (9)
  let zeta : Expr (Fin 26) := .var (10)
  let y : Expr (Fin 26) := .var (11)
  let gamma : Expr (Fin 26) := .var (12)
  let squareVariable : Expr (Fin 26) := .var (13)
  let scaleVariable : Expr (Fin 26) := .var (14)
  let mainScaleVariable : Expr (Fin 26) := .var (15)
  let rankVariable : Expr (Fin 26) := .var (16)
  let cVariable : Expr (Fin 26) := .var (17)
  let aVariable : Expr (Fin 26) := .var (18)
  let ellVariable : Expr (Fin 26) := .var (19)
  let wPositive : Expr (Fin 26) := .var (20)
  let wNegative : Expr (Fin 26) := .var (21)
  let cubeVariable : Expr (Fin 26) := .var (22)
  let productVariable : Expr (Fin 26) := .var (23)
  let fSquareVariable : Expr (Fin 26) := .var (24)
  let cSquareVariable : Expr (Fin 26) := .var (25)
  let beta : Expr (Fin 26) := .constant (p 0)
  let K0 : Expr (Fin 26) := .constant (p 1)
  let MC : Expr (Fin 26) := .constant (p 2)
  let MF : Expr (Fin 26) := .constant (p 3)
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
  let DeltaComputed := H + g17
  DeltaComputed

def literal (p : Fin 4 → ℤ) : Expr (Fin 33) :=
  let J : Expr (Fin 33) := .var (0)
  let F : Expr (Fin 33) := .var (1)
  let alpha : Expr (Fin 33) := .var (2)
  let f : Expr (Fin 33) := .var (3)
  let i : Expr (Fin 33) := .var (4)
  let T : Expr (Fin 33) := .var (5)
  let X : Expr (Fin 33) := .var (6)
  let Y : Expr (Fin 33) := .var (7)
  let r : Expr (Fin 33) := .var (8)
  let eta : Expr (Fin 33) := .var (9)
  let zeta : Expr (Fin 33) := .var (10)
  let y : Expr (Fin 33) := .var (11)
  let gamma : Expr (Fin 33) := .var (12)
  let squareVariable : Expr (Fin 33) := .var (13)
  let scaleVariable : Expr (Fin 33) := .var (14)
  let mainScaleVariable : Expr (Fin 33) := .var (15)
  let rankVariable : Expr (Fin 33) := .var (16)
  let cVariable : Expr (Fin 33) := .var (17)
  let aVariable : Expr (Fin 33) := .var (18)
  let ellVariable : Expr (Fin 33) := .var (19)
  let wPositive : Expr (Fin 33) := .var (20)
  let wNegative : Expr (Fin 33) := .var (21)
  let cubeVariable : Expr (Fin 33) := .var (22)
  let productVariable : Expr (Fin 33) := .var (23)
  let fSquareVariable : Expr (Fin 33) := .var (24)
  let cSquareVariable : Expr (Fin 33) := .var (25)
  let zPositive : Expr (Fin 33) := .var (26)
  let zNegative : Expr (Fin 33) := .var (27)
  let dPositive : Expr (Fin 33) := .var (28)
  let dNegative : Expr (Fin 33) := .var (29)
  let vPositive : Expr (Fin 33) := .var (30)
  let vNegative : Expr (Fin 33) := .var (31)
  let deltaVariable : Expr (Fin 33) := .var (32)
  let beta : Expr (Fin 33) := .constant (p 0)
  let K0 : Expr (Fin 33) := .constant (p 1)
  let MC : Expr (Fin 33) := .constant (p 2)
  let MF : Expr (Fin 33) := .constant (p 3)
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
  let DeltaComputed := H + g17
  let g19 := aVariable * cVariable
  let b0 := X + g19
  let ell := E * kY
  let M := cubeVariable * qm
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
  let root_btq3 := namedBt * cubeVariable
  let root_sum := root_scaled + g33
  let ZComputed := root_sum - root_btq3
  let Z := zPositive - zNegative
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
  let g56 := g54 + productVariable
  let shift := g56 - r0
  let g58 := mainScaleVariable * b0
  let g59 := H * shift
  let DstarComputed := g58 + g59
  let Dstar := dPositive - dNegative
  let g61 := Dstar * Dstar
  let g62 := mainScaleVariable * mainScaleVariable
  let g63 := deltaVariable * cSquareVariable
  let g64 := 1 + g63
  let g65 := g62 * g64
  let A1 := g61 - g65
  let f2 := f * f
  let rho := fSquareVariable - 1
  let Q := deltaVariable * rho
  let I := cSquareVariable * i
  let g71 := I * I
  let g72 := g71 - Q
  let g74 := T * cVariable
  let g75 := g74 - rankVariable
  let g76 := fSquareVariable * g75
  let VComputed := g76 - cVariable
  let V := vPositive - vNegative
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
  let cubeDifference := cubeVariable - q3
  let cubeConstraint := cubeDifference * cubeDifference
  let productDifference := productVariable - g55
  let productConstraint := productDifference * productDifference
  let fSquareDifference := fSquareVariable - f2
  let fSquareConstraint := fSquareDifference * fSquareDifference
  let cSquareDifference := cSquareVariable - c2
  let cSquareConstraint := cSquareDifference * cSquareDifference
  let addCube := finalWithNamedValues + cubeConstraint
  let addProduct := addCube + productConstraint
  let addFSquare := addProduct + fSquareConstraint
  let addCSquare := addFSquare + cSquareConstraint
  let zDifference := Z - ZComputed
  let zConstraint := zDifference * zDifference
  let dDifference := Dstar - DstarComputed
  let dConstraint := dDifference * dDifference
  let vDifference := V - VComputed
  let vConstraint := vDifference * vDifference
  let deltaDifference := deltaVariable - DeltaComputed
  let deltaConstraint := deltaDifference * deltaDifference
  let addZConstraint := addCSquare + zConstraint
  let addDConstraint := addZConstraint + dConstraint
  let addVConstraint := addDConstraint + vConstraint
  let addDELTAConstraint := addVConstraint + deltaConstraint
  addDELTAConstraint

def embed (i : Fin 26) : Fin 33 := ⟨i.val, Nat.lt_trans i.isLt (by decide)⟩
def holes : Fin 4 → Expr (Fin 33) := ![.var 26 - .var 27, .var 28 - .var 29, .var 30 - .var 31, .var 32]
def fill (e : Fin 4 → Expr (Fin 33)) : Sum (Fin 4) (Fin 26) → Expr (Fin 33)
  | .inl i => e i
  | .inr i => .var (embed i)
def origHoles (p : Fin 4 → ℤ) : Fin 4 → Expr (Fin 26) := ![zExpression p,dExpression p,vExpression p,deltaExpression p]
def origFill (p : Fin 4 → ℤ) : Sum (Fin 4) (Fin 26) → Expr (Fin 26)
  | .inl i => origHoles p i
  | .inr i => .var i
def lift (e : Expr (Fin 26)) : Expr (Fin 33) := e.subst (fun i => .var (embed i))

theorem context_original (p : Fin 4 → ℤ) :
    (contextAt p).subst (origFill p) = AdaptiveNamedValues26.literal p := by
  rfl

theorem literal_context (p : Fin 4 → ℤ) :
    literal p = (contextAt p).subst (fill holes) +
      (holes 0-lift (zExpression p))*(holes 0-lift (zExpression p)) +
      (holes 1-lift (dExpression p))*(holes 1-lift (dExpression p)) +
      (holes 2-lift (vExpression p))*(holes 2-lift (vExpression p)) +
      (holes 3-lift (deltaExpression p))*(holes 3-lift (deltaExpression p)) := by
  rfl

theorem context_squares (p : Fin 4 → ℤ) :
    contextAt p = (residualsAt p 0)*(residualsAt p 0) +
      (residualsAt p 1)*(residualsAt p 1) +
      (residualsAt p 2)*(residualsAt p 2) +
      (residualsAt p 3)*(residualsAt p 3) +
      (residualsAt p 4)*(residualsAt p 4) +
      (residualsAt p 5)*(residualsAt p 5) +
      (residualsAt p 6)*(residualsAt p 6) +
      (residualsAt p 7)*(residualsAt p 7) +
      (residualsAt p 8)*(residualsAt p 8) +
      (residualsAt p 9)*(residualsAt p 9) +
      (residualsAt p 10)*(residualsAt p 10) +
      (residualsAt p 11)*(residualsAt p 11) +
      (residualsAt p 12)*(residualsAt p 12) +
      (residualsAt p 13)*(residualsAt p 13) +
      (residualsAt p 14)*(residualsAt p 14) +
      (residualsAt p 15)*(residualsAt p 15) := by
  rfl

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]


theorem literal_zero_parts (p : Fin 4 → ℤ) (v : Fin 33 → V) :
    InternalZero (literal p) v ↔
      InternalZero ((contextAt p).subst (fill holes)) v ∧
      InternalZero (holes 0-lift (zExpression p)) v ∧
      InternalZero (holes 1-lift (dExpression p)) v ∧
      InternalZero (holes 2-lift (vExpression p)) v ∧
      InternalZero (holes 3-lift (deltaExpression p)) v := by
  rw [literal_context]
  let z := fill holes
  let r0 := (residualsAt p 0).subst z
  let r1 := (residualsAt p 1).subst z
  let r2 := (residualsAt p 2).subst z
  let r3 := (residualsAt p 3).subst z
  let r4 := (residualsAt p 4).subst z
  let r5 := (residualsAt p 5).subst z
  let r6 := (residualsAt p 6).subst z
  let r7 := (residualsAt p 7).subst z
  let r8 := (residualsAt p 8).subst z
  let r9 := (residualsAt p 9).subst z
  let r10 := (residualsAt p 10).subst z
  let r11 := (residualsAt p 11).subst z
  let r12 := (residualsAt p 12).subst z
  let r13 := (residualsAt p 13).subst z
  let r14 := (residualsAt p 14).subst z
  let r15 := (residualsAt p 15).subst z
  let c0 := holes 0 - lift (zExpression p)
  let c1 := holes 1 - lift (dExpression p)
  let c2 := holes 2 - lift (vExpression p)
  let c3 := holes 3 - lift (deltaExpression p)
  let base := r0*r0+r1*r1+r2*r2+r3*r3+r4*r4+r5*r5+r6*r6+r7*r7+r8*r8+r9*r9+r10*r10+r11*r11+r12*r12+r13*r13+r14*r14+r15*r15
  have rbase := (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rawSquare_rep r0 v) (rawSquare_rep r1 v)) (rawSquare_rep r2 v)) (rawSquare_rep r3 v)) (rawSquare_rep r4 v)) (rawSquare_rep r5 v)) (rawSquare_rep r6 v)) (rawSquare_rep r7 v)) (rawSquare_rep r8 v)) (rawSquare_rep r9 v)) (rawSquare_rep r10 v)) (rawSquare_rep r11 v)) (rawSquare_rep r12 v)) (rawSquare_rep r13 v)) (rawSquare_rep r14 v)) (rawSquare_rep r15 v))
  change SignedRep base v (natural _) at rbase
  have hr0 := rep_add_nat rbase (rawSquare_rep c0 v)
  change SignedRep (base+c0*c0) v (natural _) at hr0
  have hr1 := rep_add_nat hr0 (rawSquare_rep c1 v)
  change SignedRep (base+c0*c0+c1*c1) v (natural _) at hr1
  have hr2 := rep_add_nat hr1 (rawSquare_rep c2 v)
  change SignedRep (base+c0*c0+c1*c1+c2*c2) v (natural _) at hr2
  change InternalZero (base+c0*c0+c1*c1+c2*c2+c3*c3) v ↔ InternalZero base v ∧ InternalZero c0 v ∧ InternalZero c1 v ∧ InternalZero c2 v ∧ InternalZero c3 v
  rw [append_square_zero_iff _ _ _ _ hr2, append_square_zero_iff _ _ _ _ hr1, append_square_zero_iff _ _ _ _ hr0, append_square_zero_iff _ _ _ _ rbase]
  simp only [and_assoc]

theorem context_lift (p : Fin 4 → ℤ) :
    (contextAt p).subst (fill (fun i => lift (origHoles p i))) =
      (AdaptiveNamedValues26.literal p).subst (fun i => .var (embed i)) := by
  rw [←context_original p]
  rfl

theorem context_zero_iff_of_constraints (p : Fin 4 → ℤ) (v : Fin 33 → V)
    (hc : ∀ i : Fin 4, InternalZero (holes i-lift (origHoles p i)) v) :
    InternalZero ((contextAt p).subst (fill holes)) v ↔
      InternalZero (AdaptiveNamedValues26.literal p) (fun i => v (embed i)) := by
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

theorem literal_zero_project (p : Fin 4 → ℤ) (v : Fin 33 → V)
    (h : InternalZero (literal p) v) :
    InternalZero (AdaptiveNamedValues26.literal p) (fun i => v (embed i)) := by
  obtain ⟨hc,h0,h1,h2,h3⟩ := (literal_zero_parts p v).mp h
  apply (context_zero_iff_of_constraints p v ?_).mp hc
  intro i
  fin_cases i <;> assumption


def extend33 (v : Fin 26 → V) (zp zn dp dn vp vn delta : V) : Fin 33 → V :=
  fun i => if h : i.val < 26 then v ⟨i.val,h⟩ else
    if i.val = 26 then zp else if i.val = 27 then zn else
    if i.val = 28 then dp else if i.val = 29 then dn else
    if i.val = 30 then vp else if i.val = 31 then vn else delta

omit [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
theorem extend33_embed (v : Fin 26 → V) (zp zn dp dn vp vn delta : V) (i : Fin 26) :
    extend33 v zp zn dp dn vp vn delta (embed i) = v i := by
  simp [extend33, embed, i.isLt]

omit [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
theorem extend33_last (v : Fin 26 → V) (zp zn dp dn vp vn delta : V) :
    extend33 v zp zn dp dn vp vn delta 26 = zp ∧ extend33 v zp zn dp dn vp vn delta 27 = zn ∧
    extend33 v zp zn dp dn vp vn delta 28 = dp ∧ extend33 v zp zn dp dn vp vn delta 29 = dn ∧
    extend33 v zp zn dp dn vp vn delta 30 = vp ∧ extend33 v zp zn dp dn vp vn delta 31 = vn ∧
    extend33 v zp zn dp dn vp vn delta 32 = delta := by
  simp [extend33]

theorem delta_natural_rep (p : Fin 4 → ℤ) (v : Fin 26 → V) :
    SignedRep (deltaExpression p) v (natural ((3+4*v 18)+(v 18*v 18))) := by
  exact rep_add_nat (rep_add_nat (rep_nat v 3) (rep_mul_nat (rep_nat v 4) (rep_var v 18)))
    (rep_mul_nat (rep_var v 18) (rep_var v 18))

theorem exists_positive_extension (p : Fin 4 → ℤ) (v : Fin 26 → V)
    (hv : ∀ i, 0<v i) (hz : InternalZero (AdaptiveNamedValues26.literal p) v) :
    ∃ u : Fin 33 → V, (∀ i, 0<u i) ∧ InternalZero (literal p) u := by
  let zp : V := (pairEval (zExpression p) v).1+1
  let zn : V := (pairEval (zExpression p) v).2+1
  let dp : V := (pairEval (dExpression p) v).1+1
  let dn : V := (pairEval (dExpression p) v).2+1
  let vp : V := (pairEval (vExpression p) v).1+1
  let vn : V := (pairEval (vExpression p) v).2+1
  let delta : V := (3+4*v 18)+(v 18*v 18)
  let u : Fin 33 → V := extend33 v zp zn dp dn vp vn delta
  have he : (fun i : Fin 26 => u (embed i)) = v := by
    funext i
    exact extend33_embed _ _ _ _ _ _ _ _ i
  have hzp : 0<zp := by dsimp [zp]; exact lt_of_le_of_lt (Arithmetic.zero_le _) (lt_add_one _)
  have hzn : 0<zn := by dsimp [zn]; exact lt_of_le_of_lt (Arithmetic.zero_le _) (lt_add_one _)
  have hdp : 0<dp := by dsimp [dp]; exact lt_of_le_of_lt (Arithmetic.zero_le _) (lt_add_one _)
  have hdn : 0<dn := by dsimp [dn]; exact lt_of_le_of_lt (Arithmetic.zero_le _) (lt_add_one _)
  have hvp : 0<vp := by dsimp [vp]; exact lt_of_le_of_lt (Arithmetic.zero_le _) (lt_add_one _)
  have hvn : 0<vn := by dsimp [vn]; exact lt_of_le_of_lt (Arithmetic.zero_le _) (lt_add_one _)
  have hdelta : 0<delta := by
    dsimp [delta]
    have h3 : (0:V)<3 := by simp
    exact add_pos (add_pos h3 (mul_pos (by simp) (hv 18))) (mul_pos (hv 18) (hv 18))
  have hu : ∀ i, 0<u i := by
    intro i
    by_cases hi : i.val<26
    · simpa [u,extend33,hi] using hv ⟨i.val,hi⟩
    · simp only [u,extend33,hi,↓reduceDIte]
      split <;> first | exact hzp | split <;> first | exact hzn | split <;> first | exact hdp | split <;> first | exact hdn | split <;> first | exact hvp | split <;> first | exact hvn | exact hdelta
  obtain ⟨hu26,hu27,hu28,hu29,hu30,hu31,hu32⟩ := extend33_last v zp zn dp dn vp vn delta
  have hrep : ∀ i : Fin 4, Equivalent (pairEval (holes i) u)
      (pairEval (lift (origHoles p i)) u) := by
    intro i
    fin_cases i
    · have hval : pairEval (lift (origHoles p 0)) u = pairEval (zExpression p) v := by
        change splitEval (lift (zExpression p)) u = splitEval (zExpression p) v
        rw [lift,splitEval_subst_var,he]
      change Equivalent (pairEval (holes 0) u) (pairEval (lift (origHoles p 0)) u)
      rw [hval]
      change Equivalent (pairEval (Expr.sub (.var 26) (.var 27)) u) (pairEval (zExpression p) v)
      simp only [pairEval, Expr.splitNatural, NatExpr.evalSemiring, Equivalent, u, extend33]
      dsimp [zp,zn,pairEval]
      ring
    · have hval : pairEval (lift (origHoles p 1)) u = pairEval (dExpression p) v := by
        change splitEval (lift (dExpression p)) u = splitEval (dExpression p) v
        rw [lift,splitEval_subst_var,he]
      change Equivalent (pairEval (holes 1) u) (pairEval (lift (origHoles p 1)) u)
      rw [hval]
      change Equivalent (pairEval (Expr.sub (.var 28) (.var 29)) u) (pairEval (dExpression p) v)
      simp only [pairEval, Expr.splitNatural, NatExpr.evalSemiring, Equivalent, u, extend33]
      dsimp [dp,dn,pairEval]
      ring
    · have hval : pairEval (lift (origHoles p 2)) u = pairEval (vExpression p) v := by
        change splitEval (lift (vExpression p)) u = splitEval (vExpression p) v
        rw [lift,splitEval_subst_var,he]
      change Equivalent (pairEval (holes 2) u) (pairEval (lift (origHoles p 2)) u)
      rw [hval]
      change Equivalent (pairEval (Expr.sub (.var 30) (.var 31)) u) (pairEval (vExpression p) v)
      simp only [pairEval, Expr.splitNatural, NatExpr.evalSemiring, Equivalent, u, extend33]
      dsimp [vp,vn,pairEval]
      ring
    · have hr := delta_natural_rep p v
      have hvar : Equivalent (pairEval (holes 3) u) (natural delta) := by
        simp [holes, pairEval, Expr.splitNatural, NatExpr.evalSemiring, Equivalent, natural, u, hu32]
      have hval : Equivalent (pairEval (lift (origHoles p 3)) u) (natural delta) := by
        change Equivalent (splitEval (lift (deltaExpression p)) u) (natural delta)
        rw [lift,splitEval_subst_var,he]
        exact hr
      exact equivalent_trans hvar (equivalent_symm hval)
  have hconstraint : ∀ i : Fin 4, InternalZero (holes i-lift (origHoles p i)) u := by
    intro i
    exact (sub_zero_iff_equiv _ _ u).mpr (hrep i)
  have hcontext : InternalZero ((contextAt p).subst (fill holes)) u :=
    (context_zero_iff_of_constraints _ u hconstraint).mpr (by simpa only [he] using hz)
  refine ⟨u,hu,(literal_zero_parts _ u).mpr ?_⟩
  exact ⟨hcontext,hconstraint 0,hconstraint 1,hconstraint 2,hconstraint 3⟩

theorem shifted_literal_to_parent (p : Fin 4 → ℤ) (v : Fin 33 → V)
    (hz : InternalZero (positiveShift (literal p)) v) :
    InternalZero (positiveShift (AdaptiveNamedValues26.literal p)) (fun i => v (embed i)) := by
  rw [internalZero_positiveShift] at hz ⊢
  exact literal_zero_project p (fun i => v i+1) hz

theorem shifted_parent_to_literal (p : Fin 4 → ℤ) (v : Fin 26 → V)
    (hz : InternalZero (positiveShift (AdaptiveNamedValues26.literal p)) v) :
    ∃ u : Fin 33 → V, InternalZero (positiveShift (literal p)) u := by
  have hp : ∀ i : Fin 26, 0<v i+1 := by
    intro i
    exact lt_of_le_of_lt (Arithmetic.zero_le _) (lt_add_one _)
  have hz' : InternalZero (AdaptiveNamedValues26.literal p) (fun i => v i+1) :=
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
    (∀ v : Fin 33 → V, ¬ InternalZero (positiveShift (literal p)) v) ↔
    (∀ v : Fin 26 → V, ¬ InternalZero (positiveShift (AdaptiveNamedValues26.literal p)) v) := by
  constructor
  · intro h v hz
    obtain ⟨u,hu⟩ := shifted_parent_to_literal p v hz
    exact h u hu
  · intro h v hz
    exact h _ (shifted_literal_to_parent p v hz)

end DiophantineConsistency.AdaptiveNamedValues33
