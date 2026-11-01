import DiophantineConsistency.AdaptiveRankSeedPositive50

/-! One positive rank-seed variable replaces the signed pair at actual zeros. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 12000000
set_option linter.unusedVariables false
noncomputable section
namespace DiophantineConsistency.AdaptiveNamedValues50
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticAdaptiveScaledNorms2011
attribute [local irreducible] CurrentMasks2011.beta CurrentMasks2011.radix CurrentKernel2011.K
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticSignedPairExpressions ArithmeticAdaptiveFactorMagnitude2011
open AdaptiveFirstRootFactor87Syntax AdaptiveDirectOrdinate86Context AdaptiveDirectOrdinate86Lift
open AdaptiveSquareWitnessDirect14 AdaptiveScaleWitness15 AdaptiveMainScaleWitness16 AdaptiveRankWitness17 AdaptiveDirectOrdinateSquareSums AdaptiveNamedValues22 AdaptiveNamedValues26 AdaptiveNamedValues33 AdaptiveNamedValues42

def contextAt := AdaptiveNamedValues51.contextAt

def residualsAt := AdaptiveNamedValues51.residualsAt

def expression0 := AdaptiveNamedValues51.expression0

def expression1 := AdaptiveNamedValues51.expression1

def expression2 := AdaptiveNamedValues51.expression2

def expression3 := AdaptiveNamedValues51.expression3

def expression4 := AdaptiveNamedValues51.expression4

def expression5 := AdaptiveNamedValues51.expression5

def expression6 := AdaptiveNamedValues51.expression6

def literal (p : Fin 4 → ℤ) : Expr (Fin 50) :=
  let J : Expr (Fin 50) := .var 0
  let F : Expr (Fin 50) := .var 1
  let alpha : Expr (Fin 50) := .var 2
  let f : Expr (Fin 50) := .var 3
  let i : Expr (Fin 50) := .var 4
  let T : Expr (Fin 50) := .var 5
  let X : Expr (Fin 50) := .var 6
  let Y : Expr (Fin 50) := .var 7
  let r : Expr (Fin 50) := .var 8
  let eta : Expr (Fin 50) := .var 9
  let zeta : Expr (Fin 50) := .var 10
  let y : Expr (Fin 50) := .var 11
  let gamma : Expr (Fin 50) := .var 12
  let squareVariable : Expr (Fin 50) := .var 13
  let scaleVariable : Expr (Fin 50) := .var 14
  let mainScaleVariable : Expr (Fin 50) := .var 15
  let rankVariable : Expr (Fin 50) := .var 16
  let cVariable : Expr (Fin 50) := .var 17
  let aVariable : Expr (Fin 50) := .var 18
  let ellVariable : Expr (Fin 50) := .var 19
  let wPositive : Expr (Fin 50) := .var 20
  let wNegative : Expr (Fin 50) := .var 21
  let cubeVariable : Expr (Fin 50) := .var 22
  let productVariable : Expr (Fin 50) := .var 23
  let fSquareVariable : Expr (Fin 50) := .var 24
  let cSquareVariable : Expr (Fin 50) := .var 25
  let zPositive : Expr (Fin 50) := .var 26
  let zNegative : Expr (Fin 50) := .var 27
  let dPositive : Expr (Fin 50) := .var 28
  let dNegative : Expr (Fin 50) := .var 29
  let vPositive : Expr (Fin 50) := .var 30
  let vNegative : Expr (Fin 50) := .var 31
  let deltaVariable : Expr (Fin 50) := .var 32
  let qSquareVariable : Expr (Fin 50) := .var 33
  let productVariable2 : Expr (Fin 50) := .var 34
  let psiSquareVariable : Expr (Fin 50) := .var 35
  let ellProductVariable : Expr (Fin 50) := .var 36
  let varphiSquareVariable : Expr (Fin 50) := .var 37
  let scaledIndexVariable : Expr (Fin 50) := .var 38
  let ySquareVariable : Expr (Fin 50) := .var 39
  let qPositive : Expr (Fin 50) := .var 40
  let qNegative : Expr (Fin 50) := .var 41
  let deltaProductVariable : Expr (Fin 50) := .var 42
  let ySumVariable : Expr (Fin 50) := .var 43
  let offsetVariable : Expr (Fin 50) := .var 44
  let gammaProductVariable : Expr (Fin 50) := .var 45
  let timeProductVariable : Expr (Fin 50) := .var 46
  let rankSeedVariable : Expr (Fin 50) := .var 47
  let rootSkewPositive : Expr (Fin 50) := .var 48
  let rootSkewNegative : Expr (Fin 50) := .var 49
  let beta : Expr (Fin 50) := .constant (p 0)
  let K0 : Expr (Fin 50) := .constant (p 1)
  let MC : Expr (Fin 50) := .constant (p 2)
  let MF : Expr (Fin 50) := .constant (p 3)
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
  let c := eta + ySumVariable
  let c2 := cVariable * cVariable
  let a := productVariable2 + Y
  let g15 := 4 * aVariable
  let H := 3 + g15
  let g17 := aVariable * aVariable
  let DeltaComputed := H + g17
  let g19 := aVariable * cVariable
  let b0 := X + g19
  let ell := productVariable2 * ySumVariable
  let M := cubeVariable * qm
  let g25 := K0 * q
  let g26 := X + g25
  let g27 := C * g26
  let g28 := F * q
  let Bt := g27 - g28
  let g30 := ellVariable + k
  let g31 := g30 + r
  let namedBt := wPositive - wNegative
  let root_skewComputed := k * namedBt
  let root_skew := rootSkewPositive - rootSkewNegative
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
  let GComputed := alpha + g44
  let g46 := qSquareVariable - 1
  let g47 := rankSeedVariable * g46
  let g48 := MF * q
  let g49 := MC + g48
  let g50 := J * g49
  let R := g47 + g50
  let g52 := k - rankVariable
  let r0 := g52 - 1
  let g54 := mainScaleVariable * gamma
  let g55 := productVariable2 * q
  let g56 := gammaProductVariable + productVariable
  let shift := g56 - r0
  let g58 := mainScaleVariable * offsetVariable
  let g59 := H * shift
  let DstarComputed := g58 + g59
  let Dstar := dPositive - dNegative
  let g61 := Dstar * Dstar
  let g62 := mainScaleVariable * mainScaleVariable
  let g63 := deltaVariable * cSquareVariable
  let g64 := 1 + deltaProductVariable
  let g65 := varphiSquareVariable * g64
  let A1 := g61 - g65
  let f2 := f * f
  let rho := fSquareVariable - 1
  let QComputed := deltaVariable * rho
  let Q := qPositive - qNegative
  let I := cSquareVariable * i
  let g71 := scaledIndexVariable * scaledIndexVariable
  let g72 := g71 - Q
  let g74 := T * cVariable
  let g75 := timeProductVariable - rankVariable
  let g76 := fSquareVariable * g75
  let VComputed := g76 - cVariable
  let V := vPositive - vNegative
  let y2 := y * y
  let g80 := V * V
  let g81 := ySquareVariable - squareVariable
  let g82 := Q * g81
  let Fa := ySquareVariable - g82
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
  let qSquareDifference := qSquareVariable - q2
  let qSquareConstraint := qSquareDifference * qSquareDifference
  let product2Difference := productVariable2 - E
  let product2Constraint := product2Difference * product2Difference
  let psiSquareDifference := psiSquareVariable - g39
  let psiSquareConstraint := psiSquareDifference * psiSquareDifference
  let ellProductDifference := ellProductVariable - g40
  let ellProductConstraint := ellProductDifference * ellProductDifference
  let varphiSquareDifference := varphiSquareVariable - g62
  let varphiSquareConstraint := varphiSquareDifference * varphiSquareDifference
  let scaledIndexDifference := scaledIndexVariable - I
  let scaledIndexConstraint := scaledIndexDifference * scaledIndexDifference
  let ySquareDifference := ySquareVariable - y2
  let ySquareConstraint := ySquareDifference * ySquareDifference
  let qSignedDifference := Q - QComputed
  let qSignedConstraint := qSignedDifference * qSignedDifference
  let add_qSquare := addDELTAConstraint + qSquareConstraint
  let add_product2 := add_qSquare + product2Constraint
  let add_psiSquare := add_product2 + psiSquareConstraint
  let add_ellProduct := add_psiSquare + ellProductConstraint
  let add_varphiSquare := add_ellProduct + varphiSquareConstraint
  let add_scaledIndex := add_varphiSquare + scaledIndexConstraint
  let add_ySquare := add_scaledIndex + ySquareConstraint
  let add_qSigned := add_ySquare + qSignedConstraint
  let deltaProductDifference := deltaProductVariable - g63
  let deltaProductConstraint := deltaProductDifference * deltaProductDifference
  let rankSeedDifference := rankSeedVariable - GComputed
  let rankSeedConstraint := rankSeedDifference * rankSeedDifference
  let ySumDifference := ySumVariable - kY
  let ySumConstraint := ySumDifference * ySumDifference
  let rootSkewDifference := root_skew - root_skewComputed
  let rootSkewConstraint := rootSkewDifference * rootSkewDifference
  let offsetDifference := offsetVariable - b0
  let offsetConstraint := offsetDifference * offsetDifference
  let gammaProductDifference := gammaProductVariable - g54
  let gammaProductConstraint := gammaProductDifference * gammaProductDifference
  let timeProductDifference := timeProductVariable - g74
  let timeProductConstraint := timeProductDifference * timeProductDifference
  let add_deltaProduct := add_qSigned + deltaProductConstraint
  let add_rankSeed := add_deltaProduct + rankSeedConstraint
  let add_ySum := add_rankSeed + ySumConstraint
  let add_rootSkew := add_ySum + rootSkewConstraint
  let add_offset := add_rootSkew + offsetConstraint
  let add_gammaProduct := add_offset + gammaProductConstraint
  let add_timeProduct := add_gammaProduct + timeProductConstraint
  add_timeProduct

def embed (i : Fin 42) : Fin 50 := ⟨i.val, Nat.lt_trans i.isLt (by decide)⟩
def holes : Fin 7 → Expr (Fin 50) := ![.var 42,.var 47,.var 43,.var 48-.var 49,.var 44,.var 45,.var 46]
def fill (e : Fin 7 → Expr (Fin 50)) : Sum (Fin 7) (Fin 42) → Expr (Fin 50)
  | .inl i => e i
  | .inr i => .var (embed i)
def origHoles (p : Fin 4 → ℤ) : Fin 7 → Expr (Fin 42) := ![expression0 p,expression1 p,expression2 p,expression3 p,expression4 p,expression5 p,expression6 p]
def origFill (p : Fin 4 → ℤ) : Sum (Fin 7) (Fin 42) → Expr (Fin 42)
  | .inl i => origHoles p i
  | .inr i => .var i
def lift (e : Expr (Fin 42)) : Expr (Fin 50) := e.subst (fun i => .var (embed i))

theorem context_original (p : Fin 4 → ℤ) :
    (contextAt p).subst (origFill p) = AdaptiveNamedValues42.literal p := by
  rfl

theorem literal_context (p : Fin 4 → ℤ) :
    literal p = (contextAt p).subst (fill holes) +
      (holes 0-lift (expression0 p))*(holes 0-lift (expression0 p)) +
      (holes 1-lift (expression1 p))*(holes 1-lift (expression1 p)) +
      (holes 2-lift (expression2 p))*(holes 2-lift (expression2 p)) +
      (holes 3-lift (expression3 p))*(holes 3-lift (expression3 p)) +
      (holes 4-lift (expression4 p))*(holes 4-lift (expression4 p)) +
      (holes 5-lift (expression5 p))*(holes 5-lift (expression5 p)) +
      (holes 6-lift (expression6 p))*(holes 6-lift (expression6 p)) := by
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
      (residualsAt p 15)*(residualsAt p 15) +
      (residualsAt p 16)*(residualsAt p 16) +
      (residualsAt p 17)*(residualsAt p 17) +
      (residualsAt p 18)*(residualsAt p 18) +
      (residualsAt p 19)*(residualsAt p 19) +
      (residualsAt p 20)*(residualsAt p 20) +
      (residualsAt p 21)*(residualsAt p 21) +
      (residualsAt p 22)*(residualsAt p 22) +
      (residualsAt p 23)*(residualsAt p 23) +
      (residualsAt p 24)*(residualsAt p 24) +
      (residualsAt p 25)*(residualsAt p 25) +
      (residualsAt p 26)*(residualsAt p 26) +
      (residualsAt p 27)*(residualsAt p 27) := by
  rfl

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem literal_zero_parts (p : Fin 4 → ℤ) (v : Fin 50 → V) :
    InternalZero (literal p) v ↔
      InternalZero ((contextAt p).subst (fill holes)) v ∧
      InternalZero (holes 0-lift (expression0 p)) v ∧
      InternalZero (holes 1-lift (expression1 p)) v ∧
      InternalZero (holes 2-lift (expression2 p)) v ∧
      InternalZero (holes 3-lift (expression3 p)) v ∧
      InternalZero (holes 4-lift (expression4 p)) v ∧
      InternalZero (holes 5-lift (expression5 p)) v ∧
      InternalZero (holes 6-lift (expression6 p)) v := by
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
  let r16 := (residualsAt p 16).subst z
  let r17 := (residualsAt p 17).subst z
  let r18 := (residualsAt p 18).subst z
  let r19 := (residualsAt p 19).subst z
  let r20 := (residualsAt p 20).subst z
  let r21 := (residualsAt p 21).subst z
  let r22 := (residualsAt p 22).subst z
  let r23 := (residualsAt p 23).subst z
  let r24 := (residualsAt p 24).subst z
  let r25 := (residualsAt p 25).subst z
  let r26 := (residualsAt p 26).subst z
  let r27 := (residualsAt p 27).subst z
  let c0 := holes 0 - lift (expression0 p)
  let c1 := holes 1 - lift (expression1 p)
  let c2 := holes 2 - lift (expression2 p)
  let c3 := holes 3 - lift (expression3 p)
  let c4 := holes 4 - lift (expression4 p)
  let c5 := holes 5 - lift (expression5 p)
  let c6 := holes 6 - lift (expression6 p)
  let base := r0*r0+r1*r1+r2*r2+r3*r3+r4*r4+r5*r5+r6*r6+r7*r7+r8*r8+r9*r9+r10*r10+r11*r11+r12*r12+r13*r13+r14*r14+r15*r15+r16*r16+r17*r17+r18*r18+r19*r19+r20*r20+r21*r21+r22*r22+r23*r23+r24*r24+r25*r25+r26*r26+r27*r27
  have rbase := (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rawSquare_rep r0 v) (rawSquare_rep r1 v)) (rawSquare_rep r2 v)) (rawSquare_rep r3 v)) (rawSquare_rep r4 v)) (rawSquare_rep r5 v)) (rawSquare_rep r6 v)) (rawSquare_rep r7 v)) (rawSquare_rep r8 v)) (rawSquare_rep r9 v)) (rawSquare_rep r10 v)) (rawSquare_rep r11 v)) (rawSquare_rep r12 v)) (rawSquare_rep r13 v)) (rawSquare_rep r14 v)) (rawSquare_rep r15 v)) (rawSquare_rep r16 v)) (rawSquare_rep r17 v)) (rawSquare_rep r18 v)) (rawSquare_rep r19 v)) (rawSquare_rep r20 v)) (rawSquare_rep r21 v)) (rawSquare_rep r22 v)) (rawSquare_rep r23 v)) (rawSquare_rep r24 v)) (rawSquare_rep r25 v)) (rawSquare_rep r26 v)) (rawSquare_rep r27 v))
  change SignedRep base v (natural _) at rbase
  have hr0 := rep_add_nat rbase (rawSquare_rep c0 v)
  change SignedRep (base+c0*c0) v (natural _) at hr0
  have hr1 := rep_add_nat hr0 (rawSquare_rep c1 v)
  change SignedRep (base+c0*c0+c1*c1) v (natural _) at hr1
  have hr2 := rep_add_nat hr1 (rawSquare_rep c2 v)
  change SignedRep (base+c0*c0+c1*c1+c2*c2) v (natural _) at hr2
  have hr3 := rep_add_nat hr2 (rawSquare_rep c3 v)
  change SignedRep (base+c0*c0+c1*c1+c2*c2+c3*c3) v (natural _) at hr3
  have hr4 := rep_add_nat hr3 (rawSquare_rep c4 v)
  change SignedRep (base+c0*c0+c1*c1+c2*c2+c3*c3+c4*c4) v (natural _) at hr4
  have hr5 := rep_add_nat hr4 (rawSquare_rep c5 v)
  change SignedRep (base+c0*c0+c1*c1+c2*c2+c3*c3+c4*c4+c5*c5) v (natural _) at hr5
  change InternalZero (base+c0*c0+c1*c1+c2*c2+c3*c3+c4*c4+c5*c5+c6*c6) v ↔ InternalZero base v ∧ InternalZero c0 v ∧ InternalZero c1 v ∧ InternalZero c2 v ∧ InternalZero c3 v ∧ InternalZero c4 v ∧ InternalZero c5 v ∧ InternalZero c6 v
  rw [append_square_zero_iff _ _ _ _ hr5, append_square_zero_iff _ _ _ _ hr4, append_square_zero_iff _ _ _ _ hr3, append_square_zero_iff _ _ _ _ hr2, append_square_zero_iff _ _ _ _ hr1, append_square_zero_iff _ _ _ _ hr0, append_square_zero_iff _ _ _ _ rbase]
  simp only [and_assoc]

theorem context_lift (p : Fin 4 → ℤ) :
    (contextAt p).subst (fill (fun i => lift (origHoles p i))) =
      (AdaptiveNamedValues42.literal p).subst (fun i => .var (embed i)) := by
  rw [←context_original p]
  rfl

theorem context_zero_iff_of_constraints (p : Fin 4 → ℤ) (v : Fin 50 → V)
    (hc : ∀ i : Fin 7, InternalZero (holes i-lift (origHoles p i)) v) :
    InternalZero ((contextAt p).subst (fill holes)) v ↔
      InternalZero (AdaptiveNamedValues42.literal p) (fun i => v (embed i)) := by
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

theorem literal_zero_project (p : Fin 4 → ℤ) (v : Fin 50 → V)
    (h : InternalZero (literal p) v) :
    InternalZero (AdaptiveNamedValues42.literal p) (fun i => v (embed i)) := by
  obtain ⟨hc,h0,h1,h2,h3,h4,h5,h6⟩ := (literal_zero_parts p v).mp h
  apply (context_zero_iff_of_constraints p v ?_).mp hc
  intro i
  fin_cases i <;> assumption


def extend50 (v : Fin 42 → V) (extra : Fin 8 → V) : Fin 50 → V :=
  fun i => if h : i.val < 42 then v ⟨i.val,h⟩ else extra ⟨i.val-42, by omega⟩

omit [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
theorem extend50_embed (v : Fin 42 → V) (extra : Fin 8 → V) (i : Fin 42) :
    extend50 v extra (embed i) = v i := by
  simp [extend50,embed,i.isLt]

theorem named_natural_reps (p : Fin 4 → ℤ) (v : Fin 42 → V) :
    SignedRep (expression0 p) v (natural (v 32*v 25)) ∧
    SignedRep (expression2 p) v (natural (v 7*(v 9+v 10))) ∧
    SignedRep (expression4 p) v (natural (v 6+v 18*v 17)) ∧
    SignedRep (expression5 p) v (natural (v 15*v 12)) ∧
    SignedRep (expression6 p) v (natural (v 5*v 17)) := by
  exact ⟨rep_mul_nat (rep_var v 32) (rep_var v 25),
    rep_mul_nat (rep_var v 7) (rep_add_nat (rep_var v 9) (rep_var v 10)),
    rep_add_nat (rep_var v 6) (rep_mul_nat (rep_var v 18) (rep_var v 17)),
    rep_mul_nat (rep_var v 15) (rep_var v 12),
    rep_mul_nat (rep_var v 5) (rep_var v 17)⟩

theorem exists_positive_extension (p : Fin 4 → ℤ) (v : Fin 42 → V)
    (hv : ∀ i, 0<v i) (hz : InternalZero (AdaptiveNamedValues42.literal p) v)
    (rank : V) (hrank : 0<rank) (hRankRep : SignedRep (expression1 p) v (natural rank)) :
    ∃ u : Fin 50 → V, (∀ i, 0<u i) ∧ InternalZero (literal p) u := by
  let a0 : V := v 32*v 25
  let a2 : V := v 7*(v 9+v 10)
  let a4 : V := v 6+v 18*v 17
  let a5 : V := v 15*v 12
  let a6 : V := v 5*v 17
  let sp : V := (pairEval (expression3 p) v).1+1
  let sn : V := (pairEval (expression3 p) v).2+1
  let extra : Fin 8 → V := ![a0,a2,a4,a5,a6,rank,sp,sn]
  let u : Fin 50 → V := extend50 v extra
  have he : (fun i : Fin 42 => u (embed i)) = v := by
    funext i
    exact extend50_embed _ _ i
  have ha0 : 0<a0 := by dsimp [a0]; exact mul_pos (hv 32) (hv 25)
  have ha2 : 0<a2 := by dsimp [a2]; exact mul_pos (hv 7) (add_pos (hv 9) (hv 10))
  have ha4 : 0<a4 := by dsimp [a4]; exact add_pos (hv 6) (mul_pos (hv 18) (hv 17))
  have ha5 : 0<a5 := by dsimp [a5]; exact mul_pos (hv 15) (hv 12)
  have ha6 : 0<a6 := by dsimp [a6]; exact mul_pos (hv 5) (hv 17)
  have hsp : 0<sp := by dsimp [sp]; exact lt_of_le_of_lt (Arithmetic.zero_le _) (lt_add_one _)
  have hsn : 0<sn := by dsimp [sn]; exact lt_of_le_of_lt (Arithmetic.zero_le _) (lt_add_one _)
  have hextra : ∀ i : Fin 8, 0<extra i := by
    intro i
    fin_cases i <;> first | exact ha0 | exact ha2 | exact ha4 | exact ha5 | exact ha6 | exact hrank | exact hsp | exact hsn
  have hu : ∀ i, 0<u i := by
    intro i
    by_cases hi : i.val<42
    · simpa [u,extend50,hi] using hv ⟨i.val,hi⟩
    · simpa [u,extend50,hi] using hextra ⟨i.val-42,by omega⟩
  have hrep : ∀ i : Fin 7, Equivalent (pairEval (holes i) u)
      (pairEval (lift (origHoles p i)) u) := by
    intro i
    fin_cases i
    · have hr := (named_natural_reps p v).1
      have hvar : Equivalent (pairEval (holes 0) u) (natural a0) := by
        simp [holes, pairEval, Expr.splitNatural, NatExpr.evalSemiring, Equivalent, natural, u, extend50, extra]
      have hval : Equivalent (pairEval (lift (origHoles p 0)) u) (natural a0) := by
        change Equivalent (splitEval (lift (expression0 p)) u) (natural a0)
        rw [lift,splitEval_subst_var,he]
        exact hr
      exact equivalent_trans hvar (equivalent_symm hval)
    · have hvar : Equivalent (pairEval (holes 1) u) (natural rank) := by
        simp [holes, pairEval, Expr.splitNatural, NatExpr.evalSemiring, Equivalent, natural, u, extend50, extra]
      have hval : Equivalent (pairEval (lift (origHoles p 1)) u) (natural rank) := by
        change Equivalent (splitEval (lift (expression1 p)) u) (natural rank)
        rw [lift,splitEval_subst_var,he]
        exact hRankRep
      exact equivalent_trans hvar (equivalent_symm hval)
    · have hr := (named_natural_reps p v).2.1
      have hvar : Equivalent (pairEval (holes 2) u) (natural a2) := by
        simp [holes, pairEval, Expr.splitNatural, NatExpr.evalSemiring, Equivalent, natural, u, extend50, extra]
      have hval : Equivalent (pairEval (lift (origHoles p 2)) u) (natural a2) := by
        change Equivalent (splitEval (lift (expression2 p)) u) (natural a2)
        rw [lift,splitEval_subst_var,he]
        exact hr
      exact equivalent_trans hvar (equivalent_symm hval)
    · have hval : pairEval (lift (origHoles p 3)) u = pairEval (expression3 p) v := by
        change splitEval (lift (expression3 p)) u = splitEval (expression3 p) v
        rw [lift,splitEval_subst_var,he]
      change Equivalent (pairEval (holes 3) u) (pairEval (lift (origHoles p 3)) u)
      rw [hval]
      change Equivalent (pairEval (Expr.sub (.var 48) (.var 49)) u) (pairEval (expression3 p) v)
      simp only [pairEval, Expr.splitNatural, NatExpr.evalSemiring, Equivalent, u, extend50, extra]
      dsimp [sp,sn,pairEval]
      ring
    · have hr := (named_natural_reps p v).2.2.1
      have hvar : Equivalent (pairEval (holes 4) u) (natural a4) := by
        simp [holes, pairEval, Expr.splitNatural, NatExpr.evalSemiring, Equivalent, natural, u, extend50, extra]
      have hval : Equivalent (pairEval (lift (origHoles p 4)) u) (natural a4) := by
        change Equivalent (splitEval (lift (expression4 p)) u) (natural a4)
        rw [lift,splitEval_subst_var,he]
        exact hr
      exact equivalent_trans hvar (equivalent_symm hval)
    · have hr := (named_natural_reps p v).2.2.2.1
      have hvar : Equivalent (pairEval (holes 5) u) (natural a5) := by
        simp [holes, pairEval, Expr.splitNatural, NatExpr.evalSemiring, Equivalent, natural, u, extend50, extra]
      have hval : Equivalent (pairEval (lift (origHoles p 5)) u) (natural a5) := by
        change Equivalent (splitEval (lift (expression5 p)) u) (natural a5)
        rw [lift,splitEval_subst_var,he]
        exact hr
      exact equivalent_trans hvar (equivalent_symm hval)
    · have hr := (named_natural_reps p v).2.2.2.2
      have hvar : Equivalent (pairEval (holes 6) u) (natural a6) := by
        simp [holes, pairEval, Expr.splitNatural, NatExpr.evalSemiring, Equivalent, natural, u, extend50, extra]
      have hval : Equivalent (pairEval (lift (origHoles p 6)) u) (natural a6) := by
        change Equivalent (splitEval (lift (expression6 p)) u) (natural a6)
        rw [lift,splitEval_subst_var,he]
        exact hr
      exact equivalent_trans hvar (equivalent_symm hval)
  have hconstraint : ∀ i : Fin 7, InternalZero (holes i-lift (origHoles p i)) u := by
    intro i
    exact (sub_zero_iff_equiv _ _ u).mpr (hrep i)
  have hcontext : InternalZero ((contextAt p).subst (fill holes)) u :=
    (context_zero_iff_of_constraints _ u hconstraint).mpr (by simpa only [he] using hz)
  refine ⟨u,hu,(literal_zero_parts _ u).mpr ?_⟩
  exact ⟨hcontext,hconstraint 0,hconstraint 1,hconstraint 2,hconstraint 3,hconstraint 4,hconstraint 5,hconstraint 6⟩


theorem shifted_literal_to_parent (p : Fin 4 → ℤ) (v : Fin 50 → V)
    (hz : InternalZero (positiveShift (literal p)) v) :
    InternalZero (positiveShift (AdaptiveNamedValues42.literal p)) (fun i => v (embed i)) := by
  rw [internalZero_positiveShift] at hz ⊢
  exact literal_zero_project p (fun i => v i+1) hz

theorem shifted_parent_to_literal (p : Fin 4 → ℕ) (v : Fin 42 → V)
    (hb : 0<(p 0:V))
    (hz : InternalZero (positiveShift (AdaptiveNamedValues42.literal (fun j => (p j:ℤ)))) v) :
    ∃ u : Fin 50 → V, InternalZero (positiveShift (literal (fun j => (p j:ℤ)))) u := by
  let v' : Fin 42 → V := fun i => v i+1
  have hp : ∀ i : Fin 42, 0<v' i := by
    intro i
    exact lt_of_le_of_lt (Arithmetic.zero_le _) (lt_add_one _)
  have hz' : InternalZero (AdaptiveNamedValues42.literal (fun j => (p j:ℤ))) v' :=
    (internalZero_positiveShift _ _).mp hz
  have gap := AdaptiveRankSeedPositive50.gap42 p v' hb hp hz'
  have hF : v' 1≤1+v' 0*(p 0:V) := le_trans (by simp : v' 1≤v' 1+v' 2) (le_of_lt gap)
  let rank : V := v' 2+((1+v' 0*(p 0:V))-v' 1)*(v' 0*(p 0:V))
  have hRankRep : SignedRep (expression1 (fun j => (p j:ℤ))) v' (natural rank) :=
    AdaptiveRankSeedPositive50.rank_rep p v' hF
  have hrank : 0<rank := by dsimp [rank]; exact add_pos_of_pos_of_nonneg (hp 2) (Arithmetic.zero_le _)
  obtain ⟨u,hu,hzero⟩ := exists_positive_extension (fun j => (p j:ℤ)) v' hp hz' rank hrank hRankRep
  refine ⟨fun i => u i-1, ?_⟩
  rw [internalZero_positiveShift]
  have he : (fun i => (u i-1)+1) = u := by
    funext i
    exact tsub_add_cancel_of_le (pos_iff_one_le.mp (hu i))
  rw [he]
  exact hzero

theorem shifted_no_zero_iff (p : Fin 4 → ℕ) (hb : 0<(p 0:V)) :
    (∀ v : Fin 50 → V, ¬ InternalZero (positiveShift (literal (fun j => (p j:ℤ)))) v) ↔
    (∀ v : Fin 42 → V, ¬ InternalZero (positiveShift (AdaptiveNamedValues42.literal (fun j => (p j:ℤ)))) v) := by
  constructor
  · intro h v hz
    obtain ⟨u,hu⟩ := shifted_parent_to_literal p v hb hz
    exact h u hu
  · intro h v hz
    exact h _ (shifted_literal_to_parent (fun j => (p j:ℤ)) v hz)

theorem current_no_zero_iff :
    (∀ v : Fin 50 → V, ¬ InternalZero (positiveShift (literal CurrentWindowCarry2011.ports)) v) ↔
    (∀ v : Fin 42 → V, ¬ InternalZero (positiveShift (AdaptiveNamedValues42.literal CurrentWindowCarry2011.ports)) v) := by
  have hb := (AdaptiveDirectOrdinate86FixedForward.fixed_port_bounds (V:=V)).1
  simpa only [currentPorts_cast] using shifted_no_zero_iff (V:=V) currentPorts hb

end DiophantineConsistency.AdaptiveNamedValues50
