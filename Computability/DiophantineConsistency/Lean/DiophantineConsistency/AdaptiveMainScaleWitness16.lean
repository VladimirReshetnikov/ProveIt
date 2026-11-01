import DiophantineConsistency.AdaptiveScaleWitness15

/-! Sixteen-variable main-scale-witness circuit.

The added positive coordinate names U=Yq² and is constrained by a square.
Both zero transfers are proved in every IΣ₁ model under fixed-port bounds. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveMainScaleWitness16
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticSignedPairExpressions ArithmeticAdaptiveFactorMagnitude2011
open AdaptiveFirstRootFactor87Syntax AdaptiveDirectOrdinate86Context AdaptiveDirectOrdinate86Lift
open AdaptiveSquareWitnessDirect14 AdaptiveScaleWitness15 AdaptiveDirectOrdinateSquareSums

def contextAt (p : Fin 4 → ℤ) : Expr (Option (Fin 15)) :=
  let J : Expr (Option (Fin 15)) := .var (some 0)
  let F : Expr (Option (Fin 15)) := .var (some 1)
  let alpha : Expr (Option (Fin 15)) := .var (some 2)
  let f : Expr (Option (Fin 15)) := .var (some 3)
  let i : Expr (Option (Fin 15)) := .var (some 4)
  let T : Expr (Option (Fin 15)) := .var (some 5)
  let X : Expr (Option (Fin 15)) := .var (some 6)
  let Y : Expr (Option (Fin 15)) := .var (some 7)
  let r : Expr (Option (Fin 15)) := .var (some 8)
  let eta : Expr (Option (Fin 15)) := .var (some 9)
  let zeta : Expr (Option (Fin 15)) := .var (some 10)
  let y : Expr (Option (Fin 15)) := .var (some 11)
  let gamma : Expr (Option (Fin 15)) := .var (some 12)
  let squareVariable : Expr (Option (Fin 15)) := .var (some 13)
  let scaleVariable : Expr (Option (Fin 15)) := .var (some 14)
  let beta : Expr (Option (Fin 15)) := .constant (p 0)
  let K0 : Expr (Option (Fin 15)) := .constant (p 1)
  let MC : Expr (Option (Fin 15)) := .constant (p 2)
  let MF : Expr (Option (Fin 15)) := .constant (p 3)
  let U : Expr (Option (Fin 15)) := .var none
  let qm := J * beta
  let q := 1 + qm
  let q2 := q * q
  let q3 := q * q2
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

def residualsAt (p : Fin 4 → ℤ) : Expr (Option (Fin 15)) × Expr (Option (Fin 15)) × Expr (Option (Fin 15)) × Expr (Option (Fin 15)) × Expr (Option (Fin 15)) × Expr (Option (Fin 15)) :=
  let J : Expr (Option (Fin 15)) := .var (some 0)
  let F : Expr (Option (Fin 15)) := .var (some 1)
  let alpha : Expr (Option (Fin 15)) := .var (some 2)
  let f : Expr (Option (Fin 15)) := .var (some 3)
  let i : Expr (Option (Fin 15)) := .var (some 4)
  let T : Expr (Option (Fin 15)) := .var (some 5)
  let X : Expr (Option (Fin 15)) := .var (some 6)
  let Y : Expr (Option (Fin 15)) := .var (some 7)
  let r : Expr (Option (Fin 15)) := .var (some 8)
  let eta : Expr (Option (Fin 15)) := .var (some 9)
  let zeta : Expr (Option (Fin 15)) := .var (some 10)
  let y : Expr (Option (Fin 15)) := .var (some 11)
  let gamma : Expr (Option (Fin 15)) := .var (some 12)
  let squareVariable : Expr (Option (Fin 15)) := .var (some 13)
  let scaleVariable : Expr (Option (Fin 15)) := .var (some 14)
  let beta : Expr (Option (Fin 15)) := .constant (p 0)
  let K0 : Expr (Option (Fin 15)) := .constant (p 1)
  let MC : Expr (Option (Fin 15)) := .constant (p 2)
  let MF : Expr (Option (Fin 15)) := .constant (p 3)
  let U : Expr (Option (Fin 15)) := .var none
  let qm := J * beta
  let q := 1 + qm
  let q2 := q * q
  let q3 := q * q2
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
  let squareDifference := squareVariable - g80
  let scaleDifference := scaleVariable - M
  (A0,A1,auxResidual,g72,squareDifference,scaleDifference)

def scaleExpression (p : Fin 4 → ℤ) : Expr (Fin 15) :=
  let J : Expr (Fin 15) := .var 0
  let Y : Expr (Fin 15) := .var 7
  let beta : Expr (Fin 15) := .constant (p 0)
  let qm := J * beta
  let q := 1 + qm
  let q2 := q * q
  let U := Y * q2
  U

def literal (p : Fin 4 → ℤ) : Expr (Fin 16) :=
  let J : Expr (Fin 16) := .var 0
  let F : Expr (Fin 16) := .var 1
  let alpha : Expr (Fin 16) := .var 2
  let f : Expr (Fin 16) := .var 3
  let i : Expr (Fin 16) := .var 4
  let T : Expr (Fin 16) := .var 5
  let X : Expr (Fin 16) := .var 6
  let Y : Expr (Fin 16) := .var 7
  let r : Expr (Fin 16) := .var 8
  let eta : Expr (Fin 16) := .var 9
  let zeta : Expr (Fin 16) := .var 10
  let y : Expr (Fin 16) := .var 11
  let gamma : Expr (Fin 16) := .var 12
  let squareVariable : Expr (Fin 16) := .var 13
  let scaleVariable : Expr (Fin 16) := .var 14
  let mainScaleVariable : Expr (Fin 16) := .var 15
  let beta : Expr (Fin 16) := .constant (p 0)
  let K0 : Expr (Fin 16) := .constant (p 1)
  let MC : Expr (Fin 16) := .constant (p 2)
  let MF : Expr (Fin 16) := .constant (p 3)
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

def embed (i : Fin 15) : Fin 16 := ⟨i.val, Nat.lt_trans i.isLt (by decide)⟩
def fill (e : Expr (Fin 16)) : Option (Fin 15) → Expr (Fin 16)
  | none => e
  | some i => .var (embed i)
def origFill (p : Fin 4 → ℤ) : Option (Fin 15) → Expr (Fin 15)
  | none => scaleExpression p
  | some i => .var i
def w : Expr (Fin 16) := .var 15
def liftedScale (p : Fin 4 → ℤ) : Expr (Fin 16) := (scaleExpression p).subst (fun i => .var (embed i))

 theorem context_original (p : Fin 4 → ℤ) :
    (contextAt p).subst (origFill p) = AdaptiveScaleWitness15.literal p := by
  rfl

 theorem literal_context (p : Fin 4 → ℤ) :
    literal p = (contextAt p).subst (fill w) + (w-liftedScale p)*(w-liftedScale p) := by
  rfl

 theorem context_squares (p : Fin 4 → ℤ) :
    contextAt p = (residualsAt p).1*(residualsAt p).1 +
      (residualsAt p).2.1*(residualsAt p).2.1 +
      (residualsAt p).2.2.1*(residualsAt p).2.2.1 +
      (residualsAt p).2.2.2.1*(residualsAt p).2.2.2.1 +
      (residualsAt p).2.2.2.2.1*(residualsAt p).2.2.2.2.1 +
      (residualsAt p).2.2.2.2.2*(residualsAt p).2.2.2.2.2 := by
  rfl


variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem sum_seven_zero_iff {σ : Type*} (a b c d e f g : Expr σ) (v : σ → V) :
    InternalZero (a*a+b*b+c*c+d*d+e*e+f*f+g*g) v ↔
      (((InternalZero a v ∧ InternalZero b v ∧ InternalZero c v ∧ InternalZero d v) ∧
        InternalZero e v) ∧ InternalZero f v) ∧ InternalZero g v := by
  have h := rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat
    (rawSquare_rep a v) (rawSquare_rep b v)) (rawSquare_rep c v))
    (rawSquare_rep d v)) (rawSquare_rep e v)) (rawSquare_rep f v)) (rawSquare_rep g v)
  have h' : SignedRep (a*a+b*b+c*c+d*d+e*e+f*f+g*g) v _ := h
  rw [rep_zero_iff h']
  simp only [sum_eq_zero_iff,mul_self_eq_zero,magnitude_zero_iff, and_assoc]
  rfl

theorem literal_zero_parts (p : Fin 4 → ℤ) (v : Fin 16 → V) :
    InternalZero (literal p) v ↔
      InternalZero ((contextAt p).subst (fill w)) v ∧
      InternalZero (w-liftedScale p) v := by
  rw [literal_context, context_squares]
  let r := fill w
  let a := ((residualsAt p).1).subst r
  let b := ((residualsAt p).2.1).subst r
  let c := ((residualsAt p).2.2.1).subst r
  let d := ((residualsAt p).2.2.2.1).subst r
  let e := ((residualsAt p).2.2.2.2.1).subst r
  let f := ((residualsAt p).2.2.2.2.2).subst r
  let g := w-liftedScale p
  change InternalZero (a*a+b*b+c*c+d*d+e*e+f*f+g*g) v ↔
    InternalZero (a*a+b*b+c*c+d*d+e*e+f*f) v ∧ InternalZero g v
  rw [sum_seven_zero_iff, sum_six_zero_iff]

theorem context_lift (p : Fin 4 → ℤ) :
    (contextAt p).subst (fill (liftedScale p)) =
      (AdaptiveScaleWitness15.literal p).subst (fun i => .var (embed i)) := by
  rw [←context_original p]
  rfl

theorem context_zero_iff_of_constraint (p : Fin 4 → ℤ) (v : Fin 16 → V)
    (hc : InternalZero (w-liftedScale p) v) :
    InternalZero ((contextAt p).subst (fill w)) v ↔
      InternalZero (AdaptiveScaleWitness15.literal p) (fun i => v (embed i)) := by
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

theorem literal_zero_project (p : Fin 4 → ℤ) (v : Fin 16 → V)
    (h : InternalZero (literal p) v) :
    InternalZero (AdaptiveScaleWitness15.literal p) (fun i => v (embed i)) := by
  obtain ⟨hc, hw⟩ := (literal_zero_parts p v).mp h
  exact (context_zero_iff_of_constraint p v hw).mp hc


theorem scale_rep (p : Fin 4 → ℕ) (v : Fin 15 → V) :
    let b : V := v 0 * (p 0:V)
    let q : V := 1+b
    SignedRep (scaleExpression (fun j => (p j:ℤ))) v (natural (v 7*(q*q))) := by
  let b : V := v 0*(p 0:V)
  let q : V := 1+b
  have hb : SignedRep (.mul (.var 0) (.constant ((p 0:ℕ):ℤ))) v (natural b) :=
    rep_mul_nat (rep_var v 0) (rep_nat v (p 0))
  have hq : SignedRep (.add (.constant 1) (.mul (.var 0) (.constant ((p 0:ℕ):ℤ)))) v (natural q) :=
    rep_add_nat (rep_one v) hb
  exact rep_mul_nat (rep_var v 7) (rep_mul_nat hq hq)

def extend (v : Fin 15 → V) (last : V) : Fin 16 → V :=
  fun i => if h : i.val<15 then v ⟨i.val,h⟩ else last

omit [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
theorem extend_embed (v : Fin 15 → V) (last : V) (i : Fin 15) :
    extend v last (embed i) = v i := by
  simp [extend,embed,i.isLt]

omit [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
theorem extend_last (v : Fin 15 → V) (last : V) : extend v last 15 = last := by
  simp [extend]

theorem exists_positive_extension (p : Fin 4 → ℕ) (v : Fin 15 → V)
    (hb : 0<(p 0:V)) (hv : ∀ i, 0<v i)
    (hz : InternalZero (AdaptiveScaleWitness15.literal (fun j => (p j:ℤ))) v) :
    ∃ u : Fin 16 → V, (∀ i, 0<u i) ∧ InternalZero (literal (fun j => (p j:ℤ))) u := by
  let b : V := v 0*(p 0:V)
  let q : V := 1+b
  let m : V := v 7*(q*q)
  have hb' : 0<b := mul_pos (hv 0) hb
  have hq : 0<q := add_pos (by simp) hb'
  have hm : 0<m := mul_pos (hv 7) (mul_pos hq hq)
  let u : Fin 16 → V := extend v m
  have he : (fun i : Fin 15 => u (embed i)) = v := by
    funext i
    exact extend_embed _ _ i
  have hu : ∀ i, 0<u i := by
    intro i
    by_cases hi : i.val<15
    · simpa [u,extend,hi] using hv ⟨i.val,hi⟩
    · simpa [u,extend,hi] using hm
  have hscale : SignedRep (liftedScale (fun j => (p j:ℤ))) u (natural m) := by
    change Equivalent (splitEval (liftedScale (fun j => (p j:ℤ))) u) (natural m)
    rw [liftedScale,splitEval_subst_var,he]
    exact scale_rep p v
  have hw : Equivalent (pairEval w u) (natural m) := by
    change Equivalent (pairEval (.var 15) u) (natural m)
    simp only [pairEval,Expr.splitNatural,NatExpr.evalSemiring,Equivalent,natural]
    rw [show u 15=m by exact extend_last _ _]
    simp
  have hwv : Equivalent (pairEval w u) (pairEval (liftedScale (fun j => (p j:ℤ))) u) :=
    equivalent_trans hw (equivalent_symm hscale)
  have hc : InternalZero (w-liftedScale (fun j => (p j:ℤ))) u := (sub_zero_iff_equiv _ _ u).mpr hwv
  have hcontext : InternalZero ((contextAt (fun j => (p j:ℤ))).subst (fill w)) u :=
    (context_zero_iff_of_constraint _ u hc).mpr (by simpa only [he] using hz)
  exact ⟨u,hu,(literal_zero_parts _ u).mpr ⟨hcontext,hc⟩⟩


theorem shifted_literal_to_parent (p : Fin 4 → ℤ) (v : Fin 16 → V)
    (hz : InternalZero (positiveShift (literal p)) v) :
    InternalZero (positiveShift (AdaptiveScaleWitness15.literal p)) (fun i => v (embed i)) := by
  rw [internalZero_positiveShift] at hz ⊢
  exact literal_zero_project p (fun i => v i+1) hz

theorem shifted_parent_to_literal (p : Fin 4 → ℕ) (v : Fin 15 → V) (hb : 0<(p 0:V))
    (hz : InternalZero (positiveShift (AdaptiveScaleWitness15.literal (fun j => (p j:ℤ)))) v) :
    ∃ u : Fin 16 → V, InternalZero (positiveShift (literal (fun j => (p j:ℤ)))) u := by
  have hp : ∀ i : Fin 15, 0<v i+1 := by
    intro i
    exact lt_of_le_of_lt (Arithmetic.zero_le _) (lt_add_one _)
  have hz' : InternalZero (AdaptiveScaleWitness15.literal (fun j => (p j:ℤ))) (fun i => v i+1) :=
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
    (∀ v : Fin 16 → V, ¬ InternalZero (positiveShift (literal (fun j => (p j:ℤ)))) v) ↔
    (∀ v : Fin 15 → V, ¬ InternalZero (positiveShift (AdaptiveScaleWitness15.literal (fun j => (p j:ℤ)))) v) := by
  constructor
  · intro h v hz
    obtain ⟨u,hu⟩ := shifted_parent_to_literal p v hb hz
    exact h u hu
  · intro h v hz
    exact h _ (shifted_literal_to_parent _ v hz)

open ArithmeticAdaptiveScaledNorms2011 AdaptiveDirectOrdinate86FixedForward

theorem current_no_zero_iff :
    (∀ v : Fin 16 → V, ¬ InternalZero (positiveShift (literal CurrentWindowCarry2011.ports)) v) ↔
    (∀ v : Fin 15 → V, ¬ InternalZero
      (positiveShift (AdaptiveScaleWitness15.literal CurrentWindowCarry2011.ports)) v) := by
  obtain ⟨hb,_,_⟩ := fixed_port_bounds (V:=V)
  simpa only [currentPorts_cast] using (shifted_no_zero_iff currentPorts hb)

end DiophantineConsistency.AdaptiveMainScaleWitness16
