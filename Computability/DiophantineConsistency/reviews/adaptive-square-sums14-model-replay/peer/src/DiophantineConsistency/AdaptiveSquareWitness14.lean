import DiophantineConsistency.AdaptiveDirectOrdinateSquareSums
import DiophantineConsistency.AdaptiveFirstRootFactor87Context
import DiophantineConsistency.AdaptiveDirectOrdinate86Lift

/-! Fourteen-variable degree-oriented square-witness circuit.

The extra positive coordinate names V²+1. All zero transfers below are proved
in every IΣ₁ model, including construction of the positive witness. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveSquareWitness14
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 AdaptiveDirectOrdinateSquareSums AdaptiveFirstRootFactor87Context
open ArithmeticSignedPairs ArithmeticSignedPairExpressions ArithmeticAdaptiveFactorMagnitude2011

def contextAt (p : Fin 4 → ℤ) : Expr (Option (Fin 13)) :=
  let J : Expr (Option (Fin 13)) := .var (some 0)
  let F : Expr (Option (Fin 13)) := .var (some 1)
  let alpha : Expr (Option (Fin 13)) := .var (some 2)
  let f : Expr (Option (Fin 13)) := .var (some 3)
  let i : Expr (Option (Fin 13)) := .var (some 4)
  let X : Expr (Option (Fin 13)) := .var (some 6)
  let Y : Expr (Option (Fin 13)) := .var (some 7)
  let r : Expr (Option (Fin 13)) := .var (some 8)
  let eta : Expr (Option (Fin 13)) := .var (some 9)
  let zeta : Expr (Option (Fin 13)) := .var (some 10)
  let y : Expr (Option (Fin 13)) := .var (some 11)
  let gamma : Expr (Option (Fin 13)) := .var (some 12)
  let beta : Expr (Option (Fin 13)) := .constant (p 0)
  let K0 : Expr (Option (Fin 13)) := .constant (p 1)
  let MC : Expr (Option (Fin 13)) := .constant (p 2)
  let MF : Expr (Option (Fin 13)) := .constant (p 3)
  let g80 : Expr (Option (Fin 13)) := .var none
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
  let y2 := y * y
  let g81 := y2 - g80
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
  sumSquares

def residualsAt (p : Fin 4 → ℤ) : Expr (Option (Fin 13)) × Expr (Option (Fin 13)) × Expr (Option (Fin 13)) × Expr (Option (Fin 13)) :=
  let J : Expr (Option (Fin 13)) := .var (some 0)
  let F : Expr (Option (Fin 13)) := .var (some 1)
  let alpha : Expr (Option (Fin 13)) := .var (some 2)
  let f : Expr (Option (Fin 13)) := .var (some 3)
  let i : Expr (Option (Fin 13)) := .var (some 4)
  let X : Expr (Option (Fin 13)) := .var (some 6)
  let Y : Expr (Option (Fin 13)) := .var (some 7)
  let r : Expr (Option (Fin 13)) := .var (some 8)
  let eta : Expr (Option (Fin 13)) := .var (some 9)
  let zeta : Expr (Option (Fin 13)) := .var (some 10)
  let y : Expr (Option (Fin 13)) := .var (some 11)
  let gamma : Expr (Option (Fin 13)) := .var (some 12)
  let beta : Expr (Option (Fin 13)) := .constant (p 0)
  let K0 : Expr (Option (Fin 13)) := .constant (p 1)
  let MC : Expr (Option (Fin 13)) := .constant (p 2)
  let MF : Expr (Option (Fin 13)) := .constant (p 3)
  let g80 : Expr (Option (Fin 13)) := .var none
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
  let y2 := y * y
  let g81 := y2 - g80
  let g82 := Q * g81
  let Fa := y2 - g82
  let auxResidual := Fa - 1
  (A0, A1, auxResidual, g72)

def vExpression (p : Fin 4 → ℤ) : Expr (Fin 13) :=
  let J : Expr (Fin 13) := .var 0
  let F : Expr (Fin 13) := .var 1
  let alpha : Expr (Fin 13) := .var 2
  let f : Expr (Fin 13) := .var 3
  let T : Expr (Fin 13) := .var 5
  let Y : Expr (Fin 13) := .var 7
  let eta : Expr (Fin 13) := .var 9
  let zeta : Expr (Fin 13) := .var 10
  let beta : Expr (Fin 13) := .constant (p 0)
  let MC : Expr (Fin 13) := .constant (p 2)
  let MF : Expr (Fin 13) := .constant (p 3)
  let qm := J * beta
  let q := 1 + qm
  let q2 := q * q
  let qF := q - F
  let k := eta + zeta
  let kY := Y * k
  let c := eta + kY
  let g44 := qF * qm
  let G := alpha + g44
  let g46 := q2 - 1
  let g47 := G * g46
  let g48 := MF * q
  let g49 := MC + g48
  let g50 := J * g49
  let R := g47 + g50
  let f2 := f * f
  let g74 := T * c
  let g75 := g74 - R
  let g76 := f2 * g75
  let V := g76 - c
  V

def literal (p : Fin 4 → ℤ) : Expr (Fin 14) :=
  let J : Expr (Fin 14) := .var 0
  let F : Expr (Fin 14) := .var 1
  let alpha : Expr (Fin 14) := .var 2
  let f : Expr (Fin 14) := .var 3
  let i : Expr (Fin 14) := .var 4
  let T : Expr (Fin 14) := .var 5
  let X : Expr (Fin 14) := .var 6
  let Y : Expr (Fin 14) := .var 7
  let r : Expr (Fin 14) := .var 8
  let eta : Expr (Fin 14) := .var 9
  let zeta : Expr (Fin 14) := .var 10
  let y : Expr (Fin 14) := .var 11
  let gamma : Expr (Fin 14) := .var 12
  let squareVariable : Expr (Fin 14) := .var 13
  let beta : Expr (Fin 14) := .constant (p 0)
  let K0 : Expr (Fin 14) := .constant (p 1)
  let MC : Expr (Fin 14) := .constant (p 2)
  let MF : Expr (Fin 14) := .constant (p 3)
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
  let g74 := T * c
  let g75 := g74 - R
  let g76 := f2 * g75
  let V := g76 - c
  let y2 := y * y
  let g80 := V * V
  let squareWitness := squareVariable - 1
  let g81 := y2 - squareWitness
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
  let squareDifference := squareWitness - g80
  let squareConstraint := squareDifference * squareDifference
  let sumWithConstraint := sumSquares + squareConstraint
  sumWithConstraint

def embed (i : Fin 13) : Fin 14 := ⟨i.val, Nat.lt_trans i.isLt (by decide)⟩
def fill (e : Expr (Fin 14)) : Option (Fin 13) → Expr (Fin 14)
  | none => e
  | some i => .var (embed i)
def origFill (p : Fin 4 → ℤ) : Option (Fin 13) → Expr (Fin 13)
  | none => vExpression p * vExpression p
  | some i => .var i
def w : Expr (Fin 14) := .var 13 - 1
def liftedV (p : Fin 4 → ℤ) : Expr (Fin 14) := (vExpression p).subst (fun i => .var (embed i))

/-- The unmodified 13-coordinate expression is this context with V² filled in. -/
 theorem context_original (p : Fin 4 → ℤ) :
    (contextAt p).subst (origFill p) = optimized p := by
  rfl

/-- The 91-gate DAG is the same context plus the square-witness constraint. -/
 theorem literal_context (p : Fin 4 → ℤ) :
    literal p = (contextAt p).subst (fill w) + (w-liftedV p*liftedV p)*(w-liftedV p*liftedV p) := by
  rfl


open AdaptiveFirstRootFactor87Syntax AdaptiveDirectOrdinate86Context AdaptiveDirectOrdinate86Lift
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem rawSquare_rep {σ : Type*} (e : Expr σ) (v : σ → V) :
    SignedRep (e*e) v (natural (magnitude (pairEval e v)*magnitude (pairEval e v))) :=
  equivalent_trans (rep_mul (equivalent_refl _) (equivalent_refl _)) (square_magnitude _)

theorem sum_four_zero_iff {σ : Type*} (a b c d : Expr σ) (v : σ → V) :
    InternalZero (a*a+b*b+c*c+d*d) v ↔
      InternalZero a v ∧ InternalZero b v ∧ InternalZero c v ∧ InternalZero d v := by
  have h := rep_add_nat (rep_add_nat (rep_add_nat (rawSquare_rep a v) (rawSquare_rep b v))
    (rawSquare_rep c v)) (rawSquare_rep d v)
  have h' : SignedRep (a*a+b*b+c*c+d*d) v _ := h
  rw [rep_zero_iff h']
  simp only [sum_eq_zero_iff,mul_self_eq_zero,magnitude_zero_iff, and_assoc]
  rfl

theorem sum_five_zero_iff {σ : Type*} (a b c d e : Expr σ) (v : σ → V) :
    InternalZero (a*a+b*b+c*c+d*d+e*e) v ↔
      (InternalZero a v ∧ InternalZero b v ∧ InternalZero c v ∧ InternalZero d v) ∧ InternalZero e v := by
  have h := rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rawSquare_rep a v) (rawSquare_rep b v))
    (rawSquare_rep c v)) (rawSquare_rep d v)) (rawSquare_rep e v)
  have h' : SignedRep (a*a+b*b+c*c+d*d+e*e) v _ := h
  rw [rep_zero_iff h']
  simp only [sum_eq_zero_iff,mul_self_eq_zero,magnitude_zero_iff, and_assoc]
  rfl


theorem context_squares (p : Fin 4 → ℤ) :
    contextAt p = (residualsAt p).1*(residualsAt p).1 +
      (residualsAt p).2.1*(residualsAt p).2.1 +
      (residualsAt p).2.2.1*(residualsAt p).2.2.1 +
      (residualsAt p).2.2.2*(residualsAt p).2.2.2 := by
  rfl

theorem literal_zero_parts (p : Fin 4 → ℤ) (v : Fin 14 → V) :
    InternalZero (literal p) v ↔
      InternalZero ((contextAt p).subst (fill w)) v ∧
      InternalZero (w-liftedV p*liftedV p) v := by
  rw [literal_context, context_squares]
  let f := fill w
  let a := ((residualsAt p).1).subst f
  let b := ((residualsAt p).2.1).subst f
  let c := ((residualsAt p).2.2.1).subst f
  let d := ((residualsAt p).2.2.2).subst f
  let e := w-liftedV p*liftedV p
  change InternalZero (a*a+b*b+c*c+d*d+e*e) v ↔
    InternalZero (a*a+b*b+c*c+d*d) v ∧ InternalZero e v
  rw [sum_five_zero_iff, sum_four_zero_iff]

theorem sub_zero_iff_equiv {σ : Type*} (a b : Expr σ) (v : σ → V) :
    InternalZero (a-b) v ↔ Equivalent (pairEval a v) (pairEval b v) := by
  change (Expr.sub a b).splitNatural.1.evalSemiring v =
    (Expr.sub a b).splitNatural.2.evalSemiring v ↔ _
  simp only [Expr.splitNatural,NatExpr.evalSemiring,pairEval,Equivalent]

theorem context_lift (p : Fin 4 → ℤ) :
    (contextAt p).subst (fill (liftedV p*liftedV p)) =
      (optimized p).subst (fun i => .var (embed i)) := by
  rw [←context_original p]
  rfl

theorem context_zero_iff_of_constraint (p : Fin 4 → ℤ) (v : Fin 14 → V)
    (hc : InternalZero (w-liftedV p*liftedV p) v) :
    InternalZero ((contextAt p).subst (fill w)) v ↔
      InternalZero (optimized p) (fun i => v (embed i)) := by
  have h : Equivalent (splitEval ((contextAt p).subst (fill w)) v)
      (splitEval ((contextAt p).subst (fill (liftedV p*liftedV p))) v) := by
    apply splitEval_subst_equiv
    intro i
    cases i with
    | none => exact (sub_zero_iff_equiv _ _ v).mp hc
    | some i => exact equivalent_refl _
  have hz := equivalent_zero_iff h
  rw [context_lift, splitEval_subst_var] at hz
  exact hz


/-- A fourteen-coordinate zero projects to a zero of the optimized parent. -/
theorem literal_zero_project (p : Fin 4 → ℤ) (v : Fin 14 → V)
    (h : InternalZero (literal p) v) :
    InternalZero (optimized p) (fun i => v (embed i)) := by
  obtain ⟨hc, hw⟩ := (literal_zero_parts p v).mp h
  exact (context_zero_iff_of_constraint p v hw).mp hc

def extend (v : Fin 13 → V) (last : V) : Fin 14 → V :=
  fun i => if h : i.val<13 then v ⟨i.val,h⟩ else last

omit [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
theorem extend_embed (v : Fin 13 → V) (last : V) (i : Fin 13) :
    extend v last (embed i) = v i := by
  simp [extend,embed,i.isLt]

omit [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
theorem extend_last (v : Fin 13 → V) (last : V) : extend v last 13 = last := by
  simp [extend]

/-- The named square can always be supplied by the magnitude of the signed V. -/
theorem exists_positive_extension (p : Fin 4 → ℤ) (v : Fin 13 → V)
    (hv : ∀ i, 0 < v i) (hz : InternalZero (optimized p) v) :
    ∃ u : Fin 14 → V, (∀ i, 0 < u i) ∧ InternalZero (literal p) u := by
  let m := magnitude (pairEval (vExpression p) v)
  let u : Fin 14 → V := extend v (m*m+1)
  have he : (fun i : Fin 13 => u (embed i)) = v := by
    funext i
    exact extend_embed _ _ i
  have hu : ∀ i, 0 < u i := by
    intro i
    by_cases hi : i.val<13
    · simpa [u,extend,hi] using hv ⟨i.val,hi⟩
    · simp only [u,extend,hi]
      exact lt_of_le_of_lt (Arithmetic.zero_le _) (lt_add_one _)
  have hvexpr : pairEval (liftedV p) u = pairEval (vExpression p) v := by
    change splitEval (liftedV p) u = splitEval (vExpression p) v
    rw [liftedV,splitEval_subst_var,he]
  have hs : Equivalent (pairEval (liftedV p * liftedV p) u) (natural (m*m)) := by
    change Equivalent (multiply (pairEval (liftedV p) u) (pairEval (liftedV p) u)) (natural (m*m))
    rw [hvexpr]
    exact square_magnitude _
  have hw : Equivalent (pairEval w u) (natural (m*m)) := by
    change Equivalent (pairEval (Expr.sub (.var 13) (.constant 1)) u) (natural (m*m))
    simp only [pairEval,Expr.splitNatural,NatExpr.evalSemiring,Equivalent,natural]
    rw [show u 13=m*m+1 by exact extend_last _ _]
    norm_num
    ring
  have hwv : Equivalent (pairEval w u) (pairEval (liftedV p*liftedV p) u) :=
    equivalent_trans hw (equivalent_symm hs)
  have hc : InternalZero (w-liftedV p*liftedV p) u := (sub_zero_iff_equiv _ _ u).mpr hwv
  have hcontext : InternalZero ((contextAt p).subst (fill w)) u :=
    (context_zero_iff_of_constraint p u hc).mpr (by simpa only [he] using hz)
  exact ⟨u,hu,(literal_zero_parts p u).mpr ⟨hcontext,hc⟩⟩


/-- A natural zero of the shifted fourteen-variable literal projects to a parent zero. -/
theorem shifted_literal_to_parent (p : Fin 4 → ℤ) (v : Fin 14 → V)
    (hz : InternalZero (positiveShift (literal p)) v) :
    InternalZero (positiveShift (optimized p)) (fun i => v (embed i)) := by
  rw [internalZero_positiveShift] at hz ⊢
  exact literal_zero_project p (fun i => v i+1) hz

/-- Every natural parent zero supplies a positive fourteenth square witness. -/
theorem shifted_parent_to_literal (p : Fin 4 → ℤ) (v : Fin 13 → V)
    (hz : InternalZero (positiveShift (optimized p)) v) :
    ∃ u : Fin 14 → V, InternalZero (positiveShift (literal p)) u := by
  have hp : ∀ i : Fin 13, 0 < v i+1 := by
    intro i
    exact lt_of_le_of_lt (Arithmetic.zero_le _) (lt_add_one _)
  have hz' : InternalZero (optimized p) (fun i => v i+1) :=
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
    (∀ v : Fin 14 → V, ¬ InternalZero (positiveShift (literal p)) v) ↔
    (∀ v : Fin 13 → V, ¬ InternalZero (positiveShift (optimized p)) v) := by
  constructor
  · intro h v hz
    obtain ⟨u,hu⟩ := shifted_parent_to_literal p v hz
    exact h u hu
  · intro h v hz
    exact h _ (shifted_literal_to_parent p v hz)

end DiophantineConsistency.AdaptiveSquareWitness14
