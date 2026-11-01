import DiophantineConsistency.AdaptiveMainScaleWitness16
import DiophantineConsistency.AdaptiveDirectOrdinate86Residue
import DiophantineConsistency.AdaptiveDirectOrdinate86FixedForward

/-! Seventeen-variable positive rank-witness circuit.

The added coordinate names the signed rank and is constrained by a square.
Its positive representation at the actual ports follows from the 86-equation
transport and signed-residue bounds, uniformly in every IΣ₁ model. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveRankWitness17
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticSignedPairExpressions ArithmeticAdaptiveFactorMagnitude2011
open AdaptiveFirstRootFactor87Syntax AdaptiveDirectOrdinate86Context AdaptiveDirectOrdinate86Lift
open AdaptiveSquareWitnessDirect14 AdaptiveScaleWitness15 AdaptiveMainScaleWitness16 AdaptiveDirectOrdinateSquareSums

def contextAt (p : Fin 4 → ℤ) : Expr (Option (Fin 16)) :=
  let J : Expr (Option (Fin 16)) := .var (some 0)
  let F : Expr (Option (Fin 16)) := .var (some 1)
  let alpha : Expr (Option (Fin 16)) := .var (some 2)
  let f : Expr (Option (Fin 16)) := .var (some 3)
  let i : Expr (Option (Fin 16)) := .var (some 4)
  let T : Expr (Option (Fin 16)) := .var (some 5)
  let X : Expr (Option (Fin 16)) := .var (some 6)
  let Y : Expr (Option (Fin 16)) := .var (some 7)
  let r : Expr (Option (Fin 16)) := .var (some 8)
  let eta : Expr (Option (Fin 16)) := .var (some 9)
  let zeta : Expr (Option (Fin 16)) := .var (some 10)
  let y : Expr (Option (Fin 16)) := .var (some 11)
  let gamma : Expr (Option (Fin 16)) := .var (some 12)
  let squareVariable : Expr (Option (Fin 16)) := .var (some 13)
  let scaleVariable : Expr (Option (Fin 16)) := .var (some 14)
  let mainScaleVariable : Expr (Option (Fin 16)) := .var (some 15)
  let beta : Expr (Option (Fin 16)) := .constant (p 0)
  let K0 : Expr (Option (Fin 16)) := .constant (p 1)
  let R : Expr (Option (Fin 16)) := .var none
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
  let g52 := k - R
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
  let g75 := g74 - R
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
  finalWithMainScale

def residualsAt (p : Fin 4 → ℤ) : Expr (Option (Fin 16)) × Expr (Option (Fin 16)) × Expr (Option (Fin 16)) × Expr (Option (Fin 16)) × Expr (Option (Fin 16)) × Expr (Option (Fin 16)) × Expr (Option (Fin 16)) :=
  let J : Expr (Option (Fin 16)) := .var (some 0)
  let F : Expr (Option (Fin 16)) := .var (some 1)
  let alpha : Expr (Option (Fin 16)) := .var (some 2)
  let f : Expr (Option (Fin 16)) := .var (some 3)
  let i : Expr (Option (Fin 16)) := .var (some 4)
  let T : Expr (Option (Fin 16)) := .var (some 5)
  let X : Expr (Option (Fin 16)) := .var (some 6)
  let Y : Expr (Option (Fin 16)) := .var (some 7)
  let r : Expr (Option (Fin 16)) := .var (some 8)
  let eta : Expr (Option (Fin 16)) := .var (some 9)
  let zeta : Expr (Option (Fin 16)) := .var (some 10)
  let y : Expr (Option (Fin 16)) := .var (some 11)
  let gamma : Expr (Option (Fin 16)) := .var (some 12)
  let squareVariable : Expr (Option (Fin 16)) := .var (some 13)
  let scaleVariable : Expr (Option (Fin 16)) := .var (some 14)
  let mainScaleVariable : Expr (Option (Fin 16)) := .var (some 15)
  let beta : Expr (Option (Fin 16)) := .constant (p 0)
  let K0 : Expr (Option (Fin 16)) := .constant (p 1)
  let R : Expr (Option (Fin 16)) := .var none
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
  let g52 := k - R
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
  let g75 := g74 - R
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
  (A0,A1,auxResidual,g72,squareDifference,scaleDifference,mainScaleDifference)

def rankExpression (p : Fin 4 → ℤ) : Expr (Fin 16) :=
  let J : Expr (Fin 16) := .var 0
  let F : Expr (Fin 16) := .var 1
  let alpha : Expr (Fin 16) := .var 2
  let beta : Expr (Fin 16) := .constant (p 0)
  let MC : Expr (Fin 16) := .constant (p 2)
  let MF : Expr (Fin 16) := .constant (p 3)
  let qm := J * beta
  let q := 1 + qm
  let q2 := q * q
  let qF := q - F
  let g44 := qF * qm
  let G := alpha + g44
  let g46 := q2 - 1
  let g47 := G * g46
  let g48 := MF * q
  let g49 := MC + g48
  let g50 := J * g49
  let R := g47 + g50
  R

def literal (p : Fin 4 → ℤ) : Expr (Fin 17) :=
  let J : Expr (Fin 17) := .var 0
  let F : Expr (Fin 17) := .var 1
  let alpha : Expr (Fin 17) := .var 2
  let f : Expr (Fin 17) := .var 3
  let i : Expr (Fin 17) := .var 4
  let T : Expr (Fin 17) := .var 5
  let X : Expr (Fin 17) := .var 6
  let Y : Expr (Fin 17) := .var 7
  let r : Expr (Fin 17) := .var 8
  let eta : Expr (Fin 17) := .var 9
  let zeta : Expr (Fin 17) := .var 10
  let y : Expr (Fin 17) := .var 11
  let gamma : Expr (Fin 17) := .var 12
  let squareVariable : Expr (Fin 17) := .var 13
  let scaleVariable : Expr (Fin 17) := .var 14
  let mainScaleVariable : Expr (Fin 17) := .var 15
  let rankVariable : Expr (Fin 17) := .var 16
  let beta : Expr (Fin 17) := .constant (p 0)
  let K0 : Expr (Fin 17) := .constant (p 1)
  let MC : Expr (Fin 17) := .constant (p 2)
  let MF : Expr (Fin 17) := .constant (p 3)
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

def embed (i : Fin 16) : Fin 17 := ⟨i.val, Nat.lt_trans i.isLt (by decide)⟩
def fill (e : Expr (Fin 17)) : Option (Fin 16) → Expr (Fin 17)
  | none => e
  | some i => .var (embed i)
def origFill (p : Fin 4 → ℤ) : Option (Fin 16) → Expr (Fin 16)
  | none => rankExpression p
  | some i => .var i
def w : Expr (Fin 17) := .var 16
def liftedRank (p : Fin 4 → ℤ) : Expr (Fin 17) := (rankExpression p).subst (fun i => .var (embed i))

 theorem context_original (p : Fin 4 → ℤ) :
    (contextAt p).subst (origFill p) = AdaptiveMainScaleWitness16.literal p := by
  rfl

 theorem literal_context (p : Fin 4 → ℤ) :
    literal p = (contextAt p).subst (fill w) + (w-liftedRank p)*(w-liftedRank p) := by
  rfl

 theorem context_squares (p : Fin 4 → ℤ) :
    contextAt p = (residualsAt p).1*(residualsAt p).1 +
      (residualsAt p).2.1*(residualsAt p).2.1 +
      (residualsAt p).2.2.1*(residualsAt p).2.2.1 +
      (residualsAt p).2.2.2.1*(residualsAt p).2.2.2.1 +
      (residualsAt p).2.2.2.2.1*(residualsAt p).2.2.2.2.1 +
      (residualsAt p).2.2.2.2.2.1*(residualsAt p).2.2.2.2.2.1 +
      (residualsAt p).2.2.2.2.2.2*(residualsAt p).2.2.2.2.2.2 := by
  rfl


variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem sum_eight_zero_iff {σ : Type*} (a b c d e f g h : Expr σ) (v : σ → V) :
    InternalZero (a*a+b*b+c*c+d*d+e*e+f*f+g*g+h*h) v ↔
      ((((InternalZero a v ∧ InternalZero b v ∧ InternalZero c v ∧ InternalZero d v) ∧
        InternalZero e v) ∧ InternalZero f v) ∧ InternalZero g v) ∧ InternalZero h v := by
  have hr := rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat
    (rawSquare_rep a v) (rawSquare_rep b v)) (rawSquare_rep c v))
    (rawSquare_rep d v)) (rawSquare_rep e v)) (rawSquare_rep f v)) (rawSquare_rep g v)) (rawSquare_rep h v)
  have hr' : SignedRep (a*a+b*b+c*c+d*d+e*e+f*f+g*g+h*h) v _ := hr
  rw [rep_zero_iff hr']
  simp only [sum_eq_zero_iff,mul_self_eq_zero,magnitude_zero_iff, and_assoc]
  rfl

theorem literal_zero_parts (p : Fin 4 → ℤ) (v : Fin 17 → V) :
    InternalZero (literal p) v ↔
      InternalZero ((contextAt p).subst (fill w)) v ∧
      InternalZero (w-liftedRank p) v := by
  rw [literal_context, context_squares]
  let r := fill w
  let a := ((residualsAt p).1).subst r
  let b := ((residualsAt p).2.1).subst r
  let c := ((residualsAt p).2.2.1).subst r
  let d := ((residualsAt p).2.2.2.1).subst r
  let e := ((residualsAt p).2.2.2.2.1).subst r
  let f := ((residualsAt p).2.2.2.2.2.1).subst r
  let g := ((residualsAt p).2.2.2.2.2.2).subst r
  let h := w-liftedRank p
  change InternalZero (a*a+b*b+c*c+d*d+e*e+f*f+g*g+h*h) v ↔
    InternalZero (a*a+b*b+c*c+d*d+e*e+f*f+g*g) v ∧ InternalZero h v
  rw [sum_eight_zero_iff, sum_seven_zero_iff]

theorem context_lift (p : Fin 4 → ℤ) :
    (contextAt p).subst (fill (liftedRank p)) =
      (AdaptiveMainScaleWitness16.literal p).subst (fun i => .var (embed i)) := by
  rw [←context_original p]
  rfl

theorem context_zero_iff_of_constraint (p : Fin 4 → ℤ) (v : Fin 17 → V)
    (hc : InternalZero (w-liftedRank p) v) :
    InternalZero ((contextAt p).subst (fill w)) v ↔
      InternalZero (AdaptiveMainScaleWitness16.literal p) (fun i => v (embed i)) := by
  have h : Equivalent (splitEval ((contextAt p).subst (fill w)) v)
      (splitEval ((contextAt p).subst (fill (liftedRank p))) v) := by
    apply splitEval_subst_equiv
    intro i
    cases i with
    | none => exact (sub_zero_iff_equiv _ _ v).mp hc
    | some i => exact equivalent_refl _
  have hz := equivalent_zero_iff h
  rw [context_lift, splitEval_subst_var] at hz
  exact hz

theorem literal_zero_project (p : Fin 4 → ℤ) (v : Fin 17 → V)
    (h : InternalZero (literal p) v) :
    InternalZero (AdaptiveMainScaleWitness16.literal p) (fun i => v (embed i)) := by
  obtain ⟨hc, hw⟩ := (literal_zero_parts p v).mp h
  exact (context_zero_iff_of_constraint p v hw).mp hc


def extend (v : Fin 16 → V) (last : V) : Fin 17 → V :=
  fun i => if h : i.val<16 then v ⟨i.val,h⟩ else last

omit [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
theorem extend_embed (v : Fin 16 → V) (last : V) (i : Fin 16) :
    extend v last (embed i) = v i := by
  simp [extend,embed,i.isLt]

omit [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
theorem extend_last (v : Fin 16 → V) (last : V) : extend v last 16 = last := by
  simp [extend]

theorem exists_positive_extension (p : Fin 4 → ℤ) (v : Fin 16 → V)
    (hv : ∀ i, 0<v i) (hz : InternalZero (AdaptiveMainScaleWitness16.literal p) v)
    (m : V) (hm : 0<m) (hr : SignedRep (rankExpression p) v (natural m)) :
    ∃ u : Fin 17 → V, (∀ i, 0<u i) ∧ InternalZero (literal p) u := by
  let u : Fin 17 → V := extend v m
  have he : (fun i : Fin 16 => u (embed i)) = v := by
    funext i
    exact extend_embed _ _ i
  have hu : ∀ i, 0<u i := by
    intro i
    by_cases hi : i.val<16
    · simpa [u,extend,hi] using hv ⟨i.val,hi⟩
    · simpa [u,extend,hi] using hm
  have hrank : SignedRep (liftedRank p) u (natural m) := by
    change Equivalent (splitEval (liftedRank p) u) (natural m)
    rw [liftedRank,splitEval_subst_var,he]
    exact hr
  have hw : Equivalent (pairEval w u) (natural m) := by
    change Equivalent (pairEval (.var 16) u) (natural m)
    simp only [pairEval,Expr.splitNatural,NatExpr.evalSemiring,Equivalent,natural]
    rw [show u 16=m by exact extend_last _ _]
    simp
  have hwv : Equivalent (pairEval w u) (pairEval (liftedRank p) u) :=
    equivalent_trans hw (equivalent_symm hrank)
  have hc : InternalZero (w-liftedRank p) u := (sub_zero_iff_equiv _ _ u).mpr hwv
  have hcontext : InternalZero ((contextAt p).subst (fill w)) u :=
    (context_zero_iff_of_constraint _ u hc).mpr (by simpa only [he] using hz)
  exact ⟨u,hu,(literal_zero_parts _ u).mpr ⟨hcontext,hc⟩⟩

theorem shifted_literal_to_parent (p : Fin 4 → ℤ) (v : Fin 17 → V)
    (hz : InternalZero (positiveShift (literal p)) v) :
    InternalZero (positiveShift (AdaptiveMainScaleWitness16.literal p)) (fun i => v (embed i)) := by
  rw [internalZero_positiveShift] at hz ⊢
  exact literal_zero_project p (fun i => v i+1) hz

theorem shifted_parent_to_literal (p : Fin 4 → ℤ) (v : Fin 16 → V)
    (hpos : ∀ t : Fin 16 → V, (∀ i, 0<t i) → InternalZero (AdaptiveMainScaleWitness16.literal p) t →
      ∃ m : V, 0<m ∧ SignedRep (rankExpression p) t (natural m))
    (hz : InternalZero (positiveShift (AdaptiveMainScaleWitness16.literal p)) v) :
    ∃ u : Fin 17 → V, InternalZero (positiveShift (literal p)) u := by
  have hp : ∀ i : Fin 16, 0<v i+1 := by
    intro i
    exact lt_of_le_of_lt (Arithmetic.zero_le _) (lt_add_one _)
  have hz' : InternalZero (AdaptiveMainScaleWitness16.literal p) (fun i => v i+1) :=
    (internalZero_positiveShift _ _).mp hz
  obtain ⟨m,hm,hr⟩ := hpos _ hp hz'
  obtain ⟨u,hu,hzero⟩ := exists_positive_extension p (fun i => v i+1) hp hz' m hm hr
  refine ⟨fun i => u i-1, ?_⟩
  rw [internalZero_positiveShift]
  have he : (fun i => (u i-1)+1) = u := by
    funext i
    exact tsub_add_cancel_of_le (pos_iff_one_le.mp (hu i))
  rw [he]
  exact hzero

theorem shifted_no_zero_iff (p : Fin 4 → ℤ)
    (hpos : ∀ t : Fin 16 → V, (∀ i, 0<t i) → InternalZero (AdaptiveMainScaleWitness16.literal p) t →
      ∃ m : V, 0<m ∧ SignedRep (rankExpression p) t (natural m)) :
    (∀ v : Fin 17 → V, ¬ InternalZero (positiveShift (literal p)) v) ↔
    (∀ v : Fin 16 → V, ¬ InternalZero (positiveShift (AdaptiveMainScaleWitness16.literal p)) v) := by
  constructor
  · intro h v hz
    obtain ⟨u,hu⟩ := shifted_parent_to_literal p v hpos hz
    exact h u hu
  · intro h v hz
    exact h _ (shifted_literal_to_parent p v hz)


theorem rank_rep (p : Fin 4 → ℕ) (v : Fin 16 → V)
    (hF : v 1 ≤ 1+v 0*(p 0:V)) :
    let q : V := 1+v 0*(p 0:V)
    let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
    SignedRep (rankExpression (fun j => (p j:ℤ))) v (natural R) := by
  let eB : Expr (Fin 16) := .mul (.var 0) (.constant (p 0))
  let eQ : Expr (Fin 16) := .add (.constant 1) eB
  let eR : Expr (Fin 16) := .add
    (.mul (.add (.var 2) (.mul (.sub eQ (.var 1)) eB)) (.sub (.mul eQ eQ) (.constant 1)))
    (.mul (.var 0) (.add (.constant (p 2)) (.mul (.constant (p 3)) eQ)))
  let b : V := v 0*(p 0:V)
  let q : V := 1+b
  let R' : V := (v 2+(q-v 1)*b)*(q*q-1)+v 0*((p 2:V)+(p 3:V)*q)
  let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
  have hq : 1≤q := by dsimp [q]; simp
  have hbq : q-1=b := by dsimp [q]; rw [add_comm]; simp
  have hRank : R'=R := by dsimp [R,R']; rw [hbq]; simp only [pow_two]; ring
  have hB : SignedRep eB v (natural b) := rep_mul_nat (rep_var v 0) (rep_nat v (p 0))
  have hQ : SignedRep eQ v (natural q) := rep_add_nat (rep_one v) hB
  have hq2 : (1:V)≤q*q := by simpa only [one_mul] using mul_le_mul hq hq (by simp) (by simp)
  have hR' : SignedRep eR v (natural R') := rep_add_nat
    (rep_mul_nat (rep_add_nat (rep_var v 2) (rep_mul_nat (rep_tsub hQ (rep_var v 1) hF) hB))
      (rep_tsub (rep_mul_nat hQ hQ) (rep_one v) hq2))
    (rep_mul_nat (rep_var v 0) (rep_add_nat (rep_nat v (p 2)) (rep_mul_nat (rep_nat v (p 3)) hQ)))
  have hR : SignedRep eR v (natural R) := by rw [hRank] at hR'; exact hR'
  exact hR


open AdaptiveDirectOrdinate86Literal AdaptiveDirectOrdinate86Residue AdaptiveDirectOrdinate86Transport
open ArithmeticPellHalfIndex ArithmeticAdaptiveScaledNorms2011 AdaptiveDirectOrdinate86FixedForward

theorem positive_rank_of_zero (p : Fin 4 → ℕ) (v : Fin 16 → V)
    (hb : 0<(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀ i, 0<v i) (hz : InternalZero (AdaptiveMainScaleWitness16.literal (fun j => (p j:ℤ))) v) :
    ∃ m : V, 0<m ∧ SignedRep (rankExpression (fun j => (p j:ℤ))) v (natural m) := by
  let v15 : Fin 15 → V := fun i => v (AdaptiveMainScaleWitness16.embed i)
  let v14 : Fin 14 → V := fun i => v15 (AdaptiveScaleWitness15.embed i)
  let v13 : Fin 13 → V := fun i => v14 (AdaptiveSquareWitnessDirect14.embed i)
  have h15 : InternalZero (AdaptiveScaleWitness15.literal (fun j => (p j:ℤ))) v15 :=
    AdaptiveMainScaleWitness16.literal_zero_project _ v hz
  have h14 : InternalZero (AdaptiveSquareWitnessDirect14.literal (fun j => (p j:ℤ))) v14 :=
    AdaptiveScaleWitness15.literal_zero_project _ v15 h15
  have h13 : InternalZero (optimized (fun j => (p j:ℤ))) v13 :=
    AdaptiveSquareWitnessDirect14.literal_zero_project _ v14 h14
  have h86 : InternalZero (expressionAt86 (fun j => (p j:ℤ))) v13 :=
    (optimized_zero_iff_original _ v13).mp h13
  have hv13 : ∀ i : Fin 13, 0<v13 i := by
    intro i
    exact hv _
  let q : V := 1+v 0*(p 0:V)
  let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
  have htransport := expressionAt_transport_positive86 p v13 hb hv13 h86
  have hgap : v 1+v 2<q := by
    have h := tsub_pos_iff_lt.mp htransport.2
    simpa [v13,v14,v15,AdaptiveMainScaleWitness16.embed,AdaptiveScaleWitness15.embed,
      AdaptiveSquareWitnessDirect14.embed,q] using h
  have hF : v 1≤q := le_trans (by simp : v 1≤v 1+v 2) (le_of_lt hgap)
  have hs := expressionAt_signed_residue86 p v13 hb hl hh hv13 h86
  have hR : 2≤R := by
    simpa [v13,v14,v15,AdaptiveMainScaleWitness16.embed,AdaptiveScaleWitness15.embed,
      AdaptiveSquareWitnessDirect14.embed,q,R] using hs.2.1
  refine ⟨R,lt_of_lt_of_le (by simp : (0:V)<2) hR,?_⟩
  exact rank_rep p v hF

theorem fixed_positive_rank (v : Fin 16 → V) (hv : ∀ i, 0<v i)
    (hz : InternalZero (AdaptiveMainScaleWitness16.literal CurrentWindowCarry2011.ports) v) :
    ∃ m : V, 0<m ∧ SignedRep (rankExpression CurrentWindowCarry2011.ports) v (natural m) := by
  obtain ⟨hb,hl,hh⟩ := fixed_port_bounds (V:=V)
  have hz' : InternalZero (AdaptiveMainScaleWitness16.literal (fun j => (currentPorts j:ℤ))) v := by
    simpa only [currentPorts_cast] using hz
  simpa only [currentPorts_cast] using positive_rank_of_zero currentPorts v hb hl hh hv hz'

theorem current_no_zero_iff :
    (∀ v : Fin 17 → V, ¬ InternalZero (positiveShift (literal CurrentWindowCarry2011.ports)) v) ↔
    (∀ v : Fin 16 → V, ¬ InternalZero
      (positiveShift (AdaptiveMainScaleWitness16.literal CurrentWindowCarry2011.ports)) v) :=
  shifted_no_zero_iff CurrentWindowCarry2011.ports fixed_positive_rank

end DiophantineConsistency.AdaptiveRankWitness17
