import DiophantineConsistency.AdaptiveAQ26Literal
import DiophantineConsistency.AdaptiveAQ33Zeros
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
noncomputable section
namespace DiophantineConsistency.AdaptiveAQ26Zeros
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticSignedPairExpressions ArithmeticAdaptiveFactorMagnitude2011
open AdaptiveSquareWitnessDirect14 AdaptiveDirectOrdinateSquareSums AdaptiveFoldSquares AdaptiveAQ33Zeros
def residuals (p : Fin 4 → ℤ) : Fin 17 → Expr (Fin 26) :=
  let J : Expr (Fin 26) := .var 0
  let F : Expr (Fin 26) := .var 1
  let alpha : Expr (Fin 26) := .var 2
  let f : Expr (Fin 26) := .var 3
  let i : Expr (Fin 26) := .var 4
  let T : Expr (Fin 26) := .var 5
  let X : Expr (Fin 26) := .var 6
  let Y : Expr (Fin 26) := .var 7
  let r : Expr (Fin 26) := .var 8
  let eta : Expr (Fin 26) := .var 9
  let zeta : Expr (Fin 26) := .var 10
  let y : Expr (Fin 26) := .var 11
  let gamma : Expr (Fin 26) := .var 12
  let scaleVariable : Expr (Fin 26) := .var 13
  let mainScaleVariable : Expr (Fin 26) := .var 14
  let rankVariable : Expr (Fin 26) := .var 15
  let cVariable : Expr (Fin 26) := .var 16
  let ellVariable : Expr (Fin 26) := .var 17
  let cSquareVariable : Expr (Fin 26) := .var 18
  let zValueVariable : Expr (Fin 26) := .var 19
  let dValueVariable : Expr (Fin 26) := .var 20
  let vValueVariable : Expr (Fin 26) := .var 21
  let deltaVariable : Expr (Fin 26) := .var 22
  let qSquareVariable : Expr (Fin 26) := .var 23
  let productVariable2 : Expr (Fin 26) := .var 24
  let qValueVariable : Expr (Fin 26) := .var 25
  let beta : Expr (Fin 26) := .constant (p 0)
  let K0 : Expr (Fin 26) := .constant (p 1)
  let MC : Expr (Fin 26) := .constant (p 2)
  let MF : Expr (Fin 26) := .constant (p 3)
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
  let g15 := 4 * a
  let H := 3 + g15
  let g17 := a * a
  let DeltaComputed := H + g17
  let g19 := a * cVariable
  let b0 := X + g19
  let ell := productVariable2 * kY
  let M := q3 * qm
  let g25 := K0 * q
  let g26 := X + g25
  let g27 := C * g26
  let g28 := F * q
  let Bt := g27 - g28
  let g30 := ellVariable + k
  let g31 := g30 + r
  let root_skew := k * Bt
  let root_inner := g31 - root_skew
  let root_scaled := scaleVariable * root_inner
  let g33 := Y * qm
  let root_btq3 := Bt * q3
  let root_sum := root_scaled + g33
  let ZComputed := root_sum - root_btq3
  let g38 := zValueVariable * zValueVariable
  let g39 := scaleVariable * scaleVariable
  let g40 := ellVariable * g30
  let g41 := 1 + g40
  let g42 := g39 * g41
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
  let g56 := g54 + g55
  let shift := g56 - r0
  let g58 := mainScaleVariable * b0
  let g59 := H * shift
  let DstarComputed := g58 + g59
  let g61 := dValueVariable * dValueVariable
  let g62 := mainScaleVariable * mainScaleVariable
  let g63 := deltaVariable * cSquareVariable
  let g64 := 1 + g63
  let g65 := g62 * g64
  let A1 := g61 - g65
  let f2 := f * f
  let rho := f2 - 1
  let QComputed := deltaVariable * rho
  let I := cSquareVariable * i
  let g71 := I * I
  let g72 := g71 - qValueVariable
  let g74 := T * cVariable
  let g75 := g74 - rankVariable
  let g76 := f2 * g75
  let VComputed := g76 - cVariable
  let y2 := y * y
  let g80 := vValueVariable * vValueVariable
  let g81 := y2 - g80
  let g82 := qValueVariable * g81
  let Fa := y2 - g82
  let auxResidual := Fa - 1
  let scaleDifference := scaleVariable - M
  let mainScaleDifference := mainScaleVariable - U
  let rankDifference := rankVariable - R
  let cDifference := cVariable - c
  let ellDifference := ellVariable - ell
  let cSquareDifference := cSquareVariable - c2
  let zDifference := zValueVariable - ZComputed
  let dDifference := dValueVariable - DstarComputed
  let vDifference := vValueVariable - VComputed
  let deltaDifference := deltaVariable - DeltaComputed
  let qSquareDifference := qSquareVariable - q2
  let product2Difference := productVariable2 - E
  let qSignedDifference := qValueVariable - QComputed
  ![A0,A1,auxResidual,g72,scaleDifference,mainScaleDifference,rankDifference,cDifference,ellDifference,cSquareDifference,zDifference,dDifference,vDifference,deltaDifference,qSquareDifference,product2Difference,qSignedDifference]
def sum (p : Fin 4 → ℤ) : Expr (Fin 26) := (residuals p 0)*(residuals p 0) + (residuals p 1)*(residuals p 1) + (residuals p 2)*(residuals p 2) + (residuals p 3)*(residuals p 3) + (residuals p 4)*(residuals p 4) + (residuals p 5)*(residuals p 5) + (residuals p 6)*(residuals p 6) + (residuals p 7)*(residuals p 7) + (residuals p 8)*(residuals p 8) + (residuals p 9)*(residuals p 9) + (residuals p 10)*(residuals p 10) + (residuals p 11)*(residuals p 11) + (residuals p 12)*(residuals p 12) + (residuals p 13)*(residuals p 13) + (residuals p 14)*(residuals p 14) + (residuals p 15)*(residuals p 15) + (residuals p 16)*(residuals p 16)
theorem sum_shape (p : Fin 4 → ℤ) : sum p = AdaptiveAQ26Literal.literal p := by rfl
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem sum_zero (p : Fin 4 → ℤ) (v : Fin 26 → V) :
    InternalZero (AdaptiveAQ26Literal.literal p) v ↔ ∀ i : Fin 17, InternalZero (residuals p i) v := by
  let r0 := residuals p 0
  let es : List (Expr (Fin 26)) := List.ofFn (fun i : Fin 16 => residuals p i.succ)
  have hf := foldSquares_zero_iff v es (r0*r0) _ (rawSquare_rep r0 v)
  change InternalZero (AdaptiveAQ26Literal.literal p) v ↔ InternalZero (r0*r0) v ∧
    ∀ e ∈ es, InternalZero e v at hf
  rw [square_zero] at hf
  constructor
  · intro hz i
    obtain ⟨h0,ht⟩ := hf.mp hz
    by_cases hi : i.val = 0
    · have : i = 0 := Fin.ext hi
      simpa [this] using h0
    · have hi1 : 0 < i.val := by omega
      let j : Fin 16 := ⟨i.val - 1, by omega⟩
      have hj : j.succ = i := Fin.ext (by simp [j]; omega)
      simpa [hj] using ht _ (List.mem_ofFn.mpr ⟨j, rfl⟩)
  · intro h
    apply hf.mpr
    refine ⟨h 0, ?_⟩
    intro e he
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he
    exact h i.succ
#print axioms sum_zero

end DiophantineConsistency.AdaptiveAQ26Zeros
