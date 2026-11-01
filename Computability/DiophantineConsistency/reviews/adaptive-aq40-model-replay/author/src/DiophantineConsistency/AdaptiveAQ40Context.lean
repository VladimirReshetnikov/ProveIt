import DiophantineConsistency.AdaptiveNamedValues42
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveAQ40Context
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticSignedPairExpressions ArithmeticAdaptiveFactorMagnitude2011
open AdaptiveFirstRootFactor87 AdaptiveFirstRootFactor87Syntax AdaptiveDirectOrdinate86Context AdaptiveDirectOrdinate86Lift AdaptiveSquareWitnessDirect14

def oldRest (i : Fin 39) : Fin 42 := if h : i.val < 18 then ⟨i.val, by omega⟩ else ⟨i.val + 1, by omega⟩
def newRest (i : Fin 39) : Fin 40 := ⟨i.val, by omega⟩
def oldFill : Fin 2 ⊕ Fin 39 → Expr (Fin 42)
  | .inl i => if i = 0 then .var 18 else .var 40 - .var 41
  | .inr i => .var (oldRest i)
def newFill : Fin 2 ⊕ Fin 39 → Expr (Fin 40)
  | .inl i => if i = 0 then .var 33 + .var 7 else .var 39
  | .inr i => .var (newRest i)
def residuals (p : Fin 4 → ℤ) : Fin 28 → Expr (Fin 2 ⊕ Fin 39) :=
  let J : Expr (Fin 2 ⊕ Fin 39) := .var (Sum.inr 0)
  let F : Expr (Fin 2 ⊕ Fin 39) := .var (Sum.inr 1)
  let alpha : Expr (Fin 2 ⊕ Fin 39) := .var (Sum.inr 2)
  let f : Expr (Fin 2 ⊕ Fin 39) := .var (Sum.inr 3)
  let i : Expr (Fin 2 ⊕ Fin 39) := .var (Sum.inr 4)
  let T : Expr (Fin 2 ⊕ Fin 39) := .var (Sum.inr 5)
  let X : Expr (Fin 2 ⊕ Fin 39) := .var (Sum.inr 6)
  let Y : Expr (Fin 2 ⊕ Fin 39) := .var (Sum.inr 7)
  let r : Expr (Fin 2 ⊕ Fin 39) := .var (Sum.inr 8)
  let eta : Expr (Fin 2 ⊕ Fin 39) := .var (Sum.inr 9)
  let zeta : Expr (Fin 2 ⊕ Fin 39) := .var (Sum.inr 10)
  let y : Expr (Fin 2 ⊕ Fin 39) := .var (Sum.inr 11)
  let gamma : Expr (Fin 2 ⊕ Fin 39) := .var (Sum.inr 12)
  let squareVariable : Expr (Fin 2 ⊕ Fin 39) := .var (Sum.inr 13)
  let scaleVariable : Expr (Fin 2 ⊕ Fin 39) := .var (Sum.inr 14)
  let mainScaleVariable : Expr (Fin 2 ⊕ Fin 39) := .var (Sum.inr 15)
  let rankVariable : Expr (Fin 2 ⊕ Fin 39) := .var (Sum.inr 16)
  let cVariable : Expr (Fin 2 ⊕ Fin 39) := .var (Sum.inr 17)
  let ellVariable : Expr (Fin 2 ⊕ Fin 39) := .var (Sum.inr 18)
  let wPositive : Expr (Fin 2 ⊕ Fin 39) := .var (Sum.inr 19)
  let wNegative : Expr (Fin 2 ⊕ Fin 39) := .var (Sum.inr 20)
  let cubeVariable : Expr (Fin 2 ⊕ Fin 39) := .var (Sum.inr 21)
  let productVariable : Expr (Fin 2 ⊕ Fin 39) := .var (Sum.inr 22)
  let fSquareVariable : Expr (Fin 2 ⊕ Fin 39) := .var (Sum.inr 23)
  let cSquareVariable : Expr (Fin 2 ⊕ Fin 39) := .var (Sum.inr 24)
  let zPositive : Expr (Fin 2 ⊕ Fin 39) := .var (Sum.inr 25)
  let zNegative : Expr (Fin 2 ⊕ Fin 39) := .var (Sum.inr 26)
  let dPositive : Expr (Fin 2 ⊕ Fin 39) := .var (Sum.inr 27)
  let dNegative : Expr (Fin 2 ⊕ Fin 39) := .var (Sum.inr 28)
  let vPositive : Expr (Fin 2 ⊕ Fin 39) := .var (Sum.inr 29)
  let vNegative : Expr (Fin 2 ⊕ Fin 39) := .var (Sum.inr 30)
  let deltaVariable : Expr (Fin 2 ⊕ Fin 39) := .var (Sum.inr 31)
  let qSquareVariable : Expr (Fin 2 ⊕ Fin 39) := .var (Sum.inr 32)
  let productVariable2 : Expr (Fin 2 ⊕ Fin 39) := .var (Sum.inr 33)
  let psiSquareVariable : Expr (Fin 2 ⊕ Fin 39) := .var (Sum.inr 34)
  let ellProductVariable : Expr (Fin 2 ⊕ Fin 39) := .var (Sum.inr 35)
  let varphiSquareVariable : Expr (Fin 2 ⊕ Fin 39) := .var (Sum.inr 36)
  let scaledIndexVariable : Expr (Fin 2 ⊕ Fin 39) := .var (Sum.inr 37)
  let ySquareVariable : Expr (Fin 2 ⊕ Fin 39) := .var (Sum.inr 38)
  let beta : Expr (Fin 2 ⊕ Fin 39) := .constant (p 0)
  let K0 : Expr (Fin 2 ⊕ Fin 39) := .constant (p 1)
  let MC : Expr (Fin 2 ⊕ Fin 39) := .constant (p 2)
  let MF : Expr (Fin 2 ⊕ Fin 39) := .constant (p 3)
  let aVariable : Expr (Fin 2 ⊕ Fin 39) := .var (Sum.inl 0)
  let Q : Expr (Fin 2 ⊕ Fin 39) := .var (Sum.inl 1)
  let qm := J * beta
  let q := 1 + qm
  let q2 := q * q
  let q3 := q * qSquareVariable
  let U := Y * qSquareVariable
  let qF := q - F
  let C := qF - alpha
  let E := X * Y
  let k := eta + zeta
  let kY := Y * k
  let c := eta + kY
  let c2 := cVariable * cVariable
  let a := productVariable2 + Y
  let g15 := 4 * aVariable
  let H := 3 + g15
  let g17 := aVariable * aVariable
  let DeltaComputed := H + g17
  let g19 := aVariable * cVariable
  let b0 := X + g19
  let ell := productVariable2 * kY
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
  let g41 := 1 + ellProductVariable
  let g42 := psiSquareVariable * g41
  let A0 := g38 - g42
  let g44 := qF * qm
  let G := alpha + g44
  let g46 := qSquareVariable - 1
  let g47 := G * g46
  let g48 := MF * q
  let g49 := MC + g48
  let g50 := J * g49
  let R := g47 + g50
  let g52 := k - rankVariable
  let r0 := g52 - 1
  let g54 := mainScaleVariable * gamma
  let g55 := productVariable2 * q
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
  let g65 := varphiSquareVariable * g64
  let A1 := g61 - g65
  let f2 := f * f
  let rho := fSquareVariable - 1
  let QComputed := deltaVariable * rho
  let I := cSquareVariable * i
  let g71 := scaledIndexVariable * scaledIndexVariable
  let g72 := g71 - Q
  let g74 := T * cVariable
  let g75 := g74 - rankVariable
  let g76 := fSquareVariable * g75
  let VComputed := g76 - cVariable
  let V := vPositive - vNegative
  let y2 := y * y
  let g80 := V * V
  let g81 := ySquareVariable - squareVariable
  let g82 := Q * g81
  let Fa := ySquareVariable - g82
  let auxResidual := Fa - 1
  let squareDifference := squareVariable - g80
  let scaleDifference := scaleVariable - M
  let mainScaleDifference := mainScaleVariable - U
  let rankDifference := rankVariable - R
  let cDifference := cVariable - c
  let aDifference := aVariable - a
  let ellDifference := ellVariable - ell
  let wDifference := namedBt - Bt
  let cubeDifference := cubeVariable - q3
  let productDifference := productVariable - g55
  let fSquareDifference := fSquareVariable - f2
  let cSquareDifference := cSquareVariable - c2
  let zDifference := Z - ZComputed
  let dDifference := Dstar - DstarComputed
  let vDifference := V - VComputed
  let deltaDifference := deltaVariable - DeltaComputed
  let qSquareDifference := qSquareVariable - q2
  let product2Difference := productVariable2 - E
  let psiSquareDifference := psiSquareVariable - g39
  let ellProductDifference := ellProductVariable - g40
  let varphiSquareDifference := varphiSquareVariable - g62
  let scaledIndexDifference := scaledIndexVariable - I
  let ySquareDifference := ySquareVariable - y2
  let qSignedDifference := Q - QComputed
  ![A0,A1,auxResidual,g72,squareDifference,scaleDifference,mainScaleDifference,rankDifference,cDifference,aDifference,ellDifference,wDifference,cubeDifference,productDifference,fSquareDifference,cSquareDifference,zDifference,dDifference,vDifference,deltaDifference,qSquareDifference,product2Difference,psiSquareDifference,ellProductDifference,varphiSquareDifference,scaledIndexDifference,ySquareDifference,qSignedDifference]

def oldSum (p : Fin 4 → ℤ) : Expr (Fin 2 ⊕ Fin 39) := (residuals p 0)*(residuals p 0) + (residuals p 1)*(residuals p 1) + (residuals p 2)*(residuals p 2) + (residuals p 3)*(residuals p 3) + (residuals p 4)*(residuals p 4) + (residuals p 5)*(residuals p 5) + (residuals p 6)*(residuals p 6) + (residuals p 7)*(residuals p 7) + (residuals p 8)*(residuals p 8) + (residuals p 9)*(residuals p 9) + (residuals p 10)*(residuals p 10) + (residuals p 11)*(residuals p 11) + (residuals p 12)*(residuals p 12) + (residuals p 13)*(residuals p 13) + (residuals p 14)*(residuals p 14) + (residuals p 15)*(residuals p 15) + (residuals p 16)*(residuals p 16) + (residuals p 17)*(residuals p 17) + (residuals p 18)*(residuals p 18) + (residuals p 19)*(residuals p 19) + (residuals p 20)*(residuals p 20) + (residuals p 21)*(residuals p 21) + (residuals p 22)*(residuals p 22) + (residuals p 23)*(residuals p 23) + (residuals p 24)*(residuals p 24) + (residuals p 25)*(residuals p 25) + (residuals p 26)*(residuals p 26) + (residuals p 27)*(residuals p 27)
def newSum (p : Fin 4 → ℤ) : Expr (Fin 2 ⊕ Fin 39) := (residuals p 0)*(residuals p 0) + (residuals p 1)*(residuals p 1) + (residuals p 2)*(residuals p 2) + (residuals p 3)*(residuals p 3) + (residuals p 4)*(residuals p 4) + (residuals p 5)*(residuals p 5) + (residuals p 6)*(residuals p 6) + (residuals p 7)*(residuals p 7) + (residuals p 8)*(residuals p 8) + (residuals p 10)*(residuals p 10) + (residuals p 11)*(residuals p 11) + (residuals p 12)*(residuals p 12) + (residuals p 13)*(residuals p 13) + (residuals p 14)*(residuals p 14) + (residuals p 15)*(residuals p 15) + (residuals p 16)*(residuals p 16) + (residuals p 17)*(residuals p 17) + (residuals p 18)*(residuals p 18) + (residuals p 19)*(residuals p 19) + (residuals p 20)*(residuals p 20) + (residuals p 21)*(residuals p 21) + (residuals p 22)*(residuals p 22) + (residuals p 23)*(residuals p 23) + (residuals p 24)*(residuals p 24) + (residuals p 25)*(residuals p 25) + (residuals p 26)*(residuals p 26) + (residuals p 27)*(residuals p 27)

theorem old_literal (p : Fin 4 → ℤ) : (oldSum p).subst oldFill = AdaptiveNamedValues42.literal p := by rfl
end DiophantineConsistency.AdaptiveAQ40Context
