import DiophantineConsistency.AdaptiveSquareWitnessDirect14

/-! Fifteen-variable scale-witness circuit.

The additional positive coordinate names M=q³(q−1), with a squared defining
constraint. Both zero transfers hold in every IΣ₁ model under the fixed-port
positivity assumptions, without assuming standard natural numbers. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveScaleWitness15
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticSignedPairExpressions ArithmeticAdaptiveFactorMagnitude2011
open AdaptiveFirstRootFactor87Syntax AdaptiveDirectOrdinate86Context AdaptiveDirectOrdinate86Lift
open AdaptiveSquareWitnessDirect14

def contextAt (p : Fin 4 → ℤ) : Expr (Option (Fin 14)) :=
  let J : Expr (Option (Fin 14)) := .var (some 0)
  let F : Expr (Option (Fin 14)) := .var (some 1)
  let alpha : Expr (Option (Fin 14)) := .var (some 2)
  let f : Expr (Option (Fin 14)) := .var (some 3)
  let i : Expr (Option (Fin 14)) := .var (some 4)
  let T : Expr (Option (Fin 14)) := .var (some 5)
  let X : Expr (Option (Fin 14)) := .var (some 6)
  let Y : Expr (Option (Fin 14)) := .var (some 7)
  let r : Expr (Option (Fin 14)) := .var (some 8)
  let eta : Expr (Option (Fin 14)) := .var (some 9)
  let zeta : Expr (Option (Fin 14)) := .var (some 10)
  let y : Expr (Option (Fin 14)) := .var (some 11)
  let gamma : Expr (Option (Fin 14)) := .var (some 12)
  let squareVariable : Expr (Option (Fin 14)) := .var (some 13)
  let beta : Expr (Option (Fin 14)) := .constant (p 0)
  let K0 : Expr (Option (Fin 14)) := .constant (p 1)
  let MC : Expr (Option (Fin 14)) := .constant (p 2)
  let MF : Expr (Option (Fin 14)) := .constant (p 3)
  let M : Expr (Option (Fin 14)) := .var none
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
  sumWithConstraint

def residualsAt (p : Fin 4 → ℤ) : Expr (Option (Fin 14)) × Expr (Option (Fin 14)) × Expr (Option (Fin 14)) × Expr (Option (Fin 14)) × Expr (Option (Fin 14)) :=
  let J : Expr (Option (Fin 14)) := .var (some 0)
  let F : Expr (Option (Fin 14)) := .var (some 1)
  let alpha : Expr (Option (Fin 14)) := .var (some 2)
  let f : Expr (Option (Fin 14)) := .var (some 3)
  let i : Expr (Option (Fin 14)) := .var (some 4)
  let T : Expr (Option (Fin 14)) := .var (some 5)
  let X : Expr (Option (Fin 14)) := .var (some 6)
  let Y : Expr (Option (Fin 14)) := .var (some 7)
  let r : Expr (Option (Fin 14)) := .var (some 8)
  let eta : Expr (Option (Fin 14)) := .var (some 9)
  let zeta : Expr (Option (Fin 14)) := .var (some 10)
  let y : Expr (Option (Fin 14)) := .var (some 11)
  let gamma : Expr (Option (Fin 14)) := .var (some 12)
  let squareVariable : Expr (Option (Fin 14)) := .var (some 13)
  let beta : Expr (Option (Fin 14)) := .constant (p 0)
  let K0 : Expr (Option (Fin 14)) := .constant (p 1)
  let MC : Expr (Option (Fin 14)) := .constant (p 2)
  let MF : Expr (Option (Fin 14)) := .constant (p 3)
  let M : Expr (Option (Fin 14)) := .var none
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
  let g81 := y2 - squareVariable
  let g82 := Q * g81
  let Fa := y2 - g82
  let auxResidual := Fa - 1
  let squareDifference := squareVariable - g80
  (A0,A1,auxResidual,g72,squareDifference)

def scaleExpression (p : Fin 4 → ℤ) : Expr (Fin 14) :=
  let J : Expr (Fin 14) := .var 0
  let beta : Expr (Fin 14) := .constant (p 0)
  let qm := J * beta
  let q := 1 + qm
  let q2 := q * q
  let q3 := q * q2
  let M := q3 * qm
  M

def literal (p : Fin 4 → ℤ) : Expr (Fin 15) :=
  let J : Expr (Fin 15) := .var 0
  let F : Expr (Fin 15) := .var 1
  let alpha : Expr (Fin 15) := .var 2
  let f : Expr (Fin 15) := .var 3
  let i : Expr (Fin 15) := .var 4
  let T : Expr (Fin 15) := .var 5
  let X : Expr (Fin 15) := .var 6
  let Y : Expr (Fin 15) := .var 7
  let r : Expr (Fin 15) := .var 8
  let eta : Expr (Fin 15) := .var 9
  let zeta : Expr (Fin 15) := .var 10
  let y : Expr (Fin 15) := .var 11
  let gamma : Expr (Fin 15) := .var 12
  let squareVariable : Expr (Fin 15) := .var 13
  let scaleVariable : Expr (Fin 15) := .var 14
  let beta : Expr (Fin 15) := .constant (p 0)
  let K0 : Expr (Fin 15) := .constant (p 1)
  let MC : Expr (Fin 15) := .constant (p 2)
  let MF : Expr (Fin 15) := .constant (p 3)
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
  finalWithScale

def embed (i : Fin 14) : Fin 15 := ⟨i.val, Nat.lt_trans i.isLt (by decide)⟩
def fill (e : Expr (Fin 15)) : Option (Fin 14) → Expr (Fin 15)
  | none => e
  | some i => .var (embed i)
def origFill (p : Fin 4 → ℤ) : Option (Fin 14) → Expr (Fin 14)
  | none => scaleExpression p
  | some i => .var i
def w : Expr (Fin 15) := .var 14
def liftedScale (p : Fin 4 → ℤ) : Expr (Fin 15) := (scaleExpression p).subst (fun i => .var (embed i))

 theorem context_original (p : Fin 4 → ℤ) :
    (contextAt p).subst (origFill p) = AdaptiveSquareWitnessDirect14.literal p := by
  rfl

 theorem literal_context (p : Fin 4 → ℤ) :
    literal p = (contextAt p).subst (fill w) + (w-liftedScale p)*(w-liftedScale p) := by
  rfl

 theorem context_squares (p : Fin 4 → ℤ) :
    contextAt p = (residualsAt p).1*(residualsAt p).1 +
      (residualsAt p).2.1*(residualsAt p).2.1 +
      (residualsAt p).2.2.1*(residualsAt p).2.2.1 +
      (residualsAt p).2.2.2.1*(residualsAt p).2.2.2.1 +
      (residualsAt p).2.2.2.2*(residualsAt p).2.2.2.2 := by
  rfl


open AdaptiveDirectOrdinateSquareSums
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem sum_six_zero_iff {σ : Type*} (a b c d e f : Expr σ) (v : σ → V) :
    InternalZero (a*a+b*b+c*c+d*d+e*e+f*f) v ↔
      ((InternalZero a v ∧ InternalZero b v ∧ InternalZero c v ∧ InternalZero d v) ∧
        InternalZero e v) ∧ InternalZero f v := by
  have h := rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat
    (rawSquare_rep a v) (rawSquare_rep b v)) (rawSquare_rep c v))
    (rawSquare_rep d v)) (rawSquare_rep e v)) (rawSquare_rep f v)
  have h' : SignedRep (a*a+b*b+c*c+d*d+e*e+f*f) v _ := h
  rw [rep_zero_iff h']
  simp only [sum_eq_zero_iff,mul_self_eq_zero,magnitude_zero_iff, and_assoc]
  rfl

theorem literal_zero_parts (p : Fin 4 → ℤ) (v : Fin 15 → V) :
    InternalZero (literal p) v ↔
      InternalZero ((contextAt p).subst (fill w)) v ∧
      InternalZero (w-liftedScale p) v := by
  rw [literal_context, context_squares]
  let g := fill w
  let a := ((residualsAt p).1).subst g
  let b := ((residualsAt p).2.1).subst g
  let c := ((residualsAt p).2.2.1).subst g
  let d := ((residualsAt p).2.2.2.1).subst g
  let e := ((residualsAt p).2.2.2.2).subst g
  let f := w-liftedScale p
  change InternalZero (a*a+b*b+c*c+d*d+e*e+f*f) v ↔
    InternalZero (a*a+b*b+c*c+d*d+e*e) v ∧ InternalZero f v
  rw [sum_six_zero_iff, sum_five_zero_iff]

theorem context_lift (p : Fin 4 → ℤ) :
    (contextAt p).subst (fill (liftedScale p)) =
      (AdaptiveSquareWitnessDirect14.literal p).subst (fun i => .var (embed i)) := by
  rw [←context_original p]
  rfl

theorem context_zero_iff_of_constraint (p : Fin 4 → ℤ) (v : Fin 15 → V)
    (hc : InternalZero (w-liftedScale p) v) :
    InternalZero ((contextAt p).subst (fill w)) v ↔
      InternalZero (AdaptiveSquareWitnessDirect14.literal p) (fun i => v (embed i)) := by
  have h : Equivalent (splitEval ((contextAt p).subst (fill w)) v)
      (splitEval ((contextAt p).subst (fill (liftedScale p))) v) := by
    apply splitEval_subst_equiv
    intro i
    cases i with
    | none => exact (sub_zero_iff_equiv _ _ v).mp hc
    | some i => exact equivalent_refl _
  have hz := equivalent_zero_iff h
  rw [context_lift, splitEval_subst_var] at hz
  exact hz

theorem literal_zero_project (p : Fin 4 → ℤ) (v : Fin 15 → V)
    (h : InternalZero (literal p) v) :
    InternalZero (AdaptiveSquareWitnessDirect14.literal p) (fun i => v (embed i)) := by
  obtain ⟨hc, hw⟩ := (literal_zero_parts p v).mp h
  exact (context_zero_iff_of_constraint p v hw).mp hc


theorem scale_rep (p : Fin 4 → ℕ) (v : Fin 14 → V) :
    let b : V := v 0 * (p 0:V)
    let q : V := 1+b
    SignedRep (scaleExpression (fun j => (p j:ℤ))) v (natural (q*(q*q)*b)) := by
  let b : V := v 0*(p 0:V)
  let q : V := 1+b
  have hb : SignedRep (.mul (.var 0) (.constant ((p 0:ℕ):ℤ))) v (natural b) :=
    rep_mul_nat (rep_var v 0) (rep_nat v (p 0))
  have hq : SignedRep (.add (.constant 1) (.mul (.var 0) (.constant ((p 0:ℕ):ℤ)))) v (natural q) :=
    rep_add_nat (rep_one v) hb
  have hq2 := rep_mul_nat hq hq
  have hq3 := rep_mul_nat hq hq2
  exact rep_mul_nat hq3 hb

def extend (v : Fin 14 → V) (last : V) : Fin 15 → V :=
  fun i => if h : i.val<14 then v ⟨i.val,h⟩ else last

omit [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
theorem extend_embed (v : Fin 14 → V) (last : V) (i : Fin 14) :
    extend v last (embed i) = v i := by
  simp [extend,embed,i.isLt]

omit [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
theorem extend_last (v : Fin 14 → V) (last : V) : extend v last 14 = last := by
  simp [extend]

theorem exists_positive_extension (p : Fin 4 → ℕ) (v : Fin 14 → V)
    (hb : 0<(p 0:V)) (hv : ∀ i, 0<v i)
    (hz : InternalZero (AdaptiveSquareWitnessDirect14.literal (fun j => (p j:ℤ))) v) :
    ∃ u : Fin 15 → V, (∀ i, 0<u i) ∧ InternalZero (literal (fun j => (p j:ℤ))) u := by
  let b : V := v 0*(p 0:V)
  let q : V := 1+b
  let m : V := q*(q*q)*b
  have hb' : 0<b := mul_pos (hv 0) hb
  have hq : 0<q := add_pos (by simp) hb'
  have hm : 0<m := mul_pos (mul_pos hq (mul_pos hq hq)) hb'
  let u : Fin 15 → V := extend v m
  have he : (fun i : Fin 14 => u (embed i)) = v := by
    funext i
    exact extend_embed _ _ i
  have hu : ∀ i, 0<u i := by
    intro i
    by_cases hi : i.val<14
    · simpa [u,extend,hi] using hv ⟨i.val,hi⟩
    · simpa [u,extend,hi] using hm
  have hscale : SignedRep (liftedScale (fun j => (p j:ℤ))) u (natural m) := by
    change Equivalent (splitEval (liftedScale (fun j => (p j:ℤ))) u) (natural m)
    rw [liftedScale,splitEval_subst_var,he]
    exact scale_rep p v
  have hw : Equivalent (pairEval w u) (natural m) := by
    change Equivalent (pairEval (.var 14) u) (natural m)
    simp only [pairEval,Expr.splitNatural,NatExpr.evalSemiring,Equivalent,natural]
    rw [show u 14=m by exact extend_last _ _]
    simp
  have hwv : Equivalent (pairEval w u) (pairEval (liftedScale (fun j => (p j:ℤ))) u) :=
    equivalent_trans hw (equivalent_symm hscale)
  have hc : InternalZero (w-liftedScale (fun j => (p j:ℤ))) u := (sub_zero_iff_equiv _ _ u).mpr hwv
  have hcontext : InternalZero ((contextAt (fun j => (p j:ℤ))).subst (fill w)) u :=
    (context_zero_iff_of_constraint _ u hc).mpr (by simpa only [he] using hz)
  exact ⟨u,hu,(literal_zero_parts _ u).mpr ⟨hcontext,hc⟩⟩


theorem shifted_literal_to_parent (p : Fin 4 → ℤ) (v : Fin 15 → V)
    (hz : InternalZero (positiveShift (literal p)) v) :
    InternalZero (positiveShift (AdaptiveSquareWitnessDirect14.literal p)) (fun i => v (embed i)) := by
  rw [internalZero_positiveShift] at hz ⊢
  exact literal_zero_project p (fun i => v i+1) hz

theorem shifted_parent_to_literal (p : Fin 4 → ℕ) (v : Fin 14 → V) (hb : 0<(p 0:V))
    (hz : InternalZero (positiveShift (AdaptiveSquareWitnessDirect14.literal (fun j => (p j:ℤ)))) v) :
    ∃ u : Fin 15 → V, InternalZero (positiveShift (literal (fun j => (p j:ℤ)))) u := by
  have hp : ∀ i : Fin 14, 0<v i+1 := by
    intro i
    exact lt_of_le_of_lt (Arithmetic.zero_le _) (lt_add_one _)
  have hz' : InternalZero (AdaptiveSquareWitnessDirect14.literal (fun j => (p j:ℤ))) (fun i => v i+1) :=
    (internalZero_positiveShift _ _).mp hz
  obtain ⟨u,hu,hzero⟩ := exists_positive_extension p (fun i => v i+1) hb hp hz'
  refine ⟨fun i => u i-1, ?_⟩
  rw [internalZero_positiveShift]
  have he : (fun i => (u i-1)+1) = u := by
    funext i
    exact tsub_add_cancel_of_le (pos_iff_one_le.mp (hu i))
  rw [he]
  exact hzero

theorem shifted_no_zero_iff (p : Fin 4 → ℕ) (hb : 0<(p 0:V)) :
    (∀ v : Fin 15 → V, ¬ InternalZero (positiveShift (literal (fun j => (p j:ℤ)))) v) ↔
    (∀ v : Fin 14 → V, ¬ InternalZero (positiveShift (AdaptiveSquareWitnessDirect14.literal (fun j => (p j:ℤ)))) v) := by
  constructor
  · intro h v hz
    obtain ⟨u,hu⟩ := shifted_parent_to_literal p v hb hz
    exact h u hu
  · intro h v hz
    exact h _ (shifted_literal_to_parent _ v hz)

open ArithmeticAdaptiveScaledNorms2011 AdaptiveDirectOrdinate86FixedForward

theorem current_no_zero_iff :
    (∀ v : Fin 15 → V, ¬ InternalZero (positiveShift (literal CurrentWindowCarry2011.ports)) v) ↔
    (∀ v : Fin 14 → V, ¬ InternalZero
      (positiveShift (AdaptiveSquareWitnessDirect14.literal CurrentWindowCarry2011.ports)) v) := by
  obtain ⟨hb,_,_⟩ := fixed_port_bounds (V:=V)
  simpa only [currentPorts_cast] using (shifted_no_zero_iff currentPorts hb)

end DiophantineConsistency.AdaptiveScaleWitness15
