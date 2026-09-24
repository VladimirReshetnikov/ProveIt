import Diophantine.Paper1982.ShortQuarticMaster

/-!
# Eliminating eighteen witnesses: a quartic system in forty witnesses

Eighteen witnesses of the 58-witness quadratic system of §5 are defined by one of its equations
as a sum of products of other witnesses (`λB`, `b²`, `AC₁`, `c⁴`, `Q⁴`, `N²`, `YK`, `AC`, `C²`,
`AE`, `F²`, `c`, `l`, `e`, `P`, `U`, `I`, `H`).  Substituting these definitions ("substitute unknowns
which appear alone on the left side of an equation in which the right side is positive", §1)
leaves 28 equations of degree at most four in the remaining forty witnesses and the input.
The substituted values are automatically positive, so solvability is unchanged.
-/

namespace Jones1982

namespace ShortQuadraticExpr

/-- Simultaneous substitution of witnesses. -/
def subst (σ : ShortQuadraticVar → ShortQuadraticExpr) : ShortQuadraticExpr → ShortQuadraticExpr
  | .constant a => .constant a
  | .input => .input
  | .witness v => σ v
  | .add p q => .add (p.subst σ) (q.subst σ)
  | .sub p q => .sub (p.subst σ) (q.subst σ)
  | .mul p q => .mul (p.subst σ) (q.subst σ)
  | .pow p n => .pow (p.subst σ) n

theorem eval_subst (σ : ShortQuadraticVar → ShortQuadraticExpr) (p : ShortQuadraticExpr)
    (a : Option ShortQuadraticVar → ℤ) :
    MvPolynomial.eval a (p.subst σ).toPolynomial =
      MvPolynomial.eval (fun o => match o with
        | none => a none
        | some v => MvPolynomial.eval a (σ v).toPolynomial) p.toPolynomial := by
  induction p <;> simp_all [subst, toPolynomial]

theorem subst_add (σ) (p q : ShortQuadraticExpr) : (p + q).subst σ = p.subst σ + q.subst σ := rfl
theorem subst_sub (σ) (p q : ShortQuadraticExpr) : (p - q).subst σ = p.subst σ - q.subst σ := rfl
theorem subst_mul (σ) (p q : ShortQuadraticExpr) : (p * q).subst σ = p.subst σ * q.subst σ := rfl
theorem subst_pow (σ) (p : ShortQuadraticExpr) (n : ℕ) : (p ^ n).subst σ = p.subst σ ^ n := rfl
theorem subst_ofNat (σ) (n : ℕ) :
    (@OfNat.ofNat ShortQuadraticExpr n (instOfNat n)).subst σ = OfNat.ofNat n := rfl

/-- The witnesses occurring in an expression. -/
def occurs (v : ShortQuadraticVar) : ShortQuadraticExpr → Bool
  | .constant _ => false
  | .input => false
  | .witness w => decide (w = v)
  | .add p q => p.occurs v || q.occurs v
  | .sub p q => p.occurs v || q.occurs v
  | .mul p q => p.occurs v || q.occurs v
  | .pow p _ => p.occurs v

theorem eval_congr (p : ShortQuadraticExpr) {a a' : Option ShortQuadraticVar → ℤ}
    (hn : a none = a' none) (h : ∀ v, p.occurs v = true → a (some v) = a' (some v)) :
    MvPolynomial.eval a p.toPolynomial = MvPolynomial.eval a' p.toPolynomial := by
  induction p with
  | constant c => simp [toPolynomial]
  | input => simp [toPolynomial, hn]
  | witness w => simpa [toPolynomial] using h w (by simp [occurs])
  | add p q hp hq =>
    simp only [toPolynomial, map_add]
    rw [hp fun v hv => h v (by simp [occurs, hv]), hq fun v hv => h v (by simp [occurs, hv])]
  | sub p q hp hq =>
    simp only [toPolynomial, map_sub]
    rw [hp fun v hv => h v (by simp [occurs, hv]), hq fun v hv => h v (by simp [occurs, hv])]
  | mul p q hp hq =>
    simp only [toPolynomial, map_mul]
    rw [hp fun v hv => h v (by simp [occurs, hv]), hq fun v hv => h v (by simp [occurs, hv])]
  | pow p n hp =>
    simp only [toPolynomial, map_pow]
    rw [hp fun v hv => h v (by simpa [occurs] using hv)]

end ShortQuadraticExpr

namespace Pair40

open ShortQuadraticExpr ShortQuadratic

/-- The eighteen eliminated witnesses. -/
def elim : ShortQuadraticVar → Bool
  | .AC | .AC₁ | .AE | .CSq | .FSq | .H | .I | .NSq | .P | .QFourth | .U | .YK | .bSq | .c
  | .cFourth | .e | .l | .lamB => true
  | _ => false

/-- The defining equation of an eliminated witness. -/
def defEq : ShortQuadraticVar → ShortQuadraticEquation
  | .AC => .AC | .AC₁ => .AC₁ | .AE => .AE | .CSq => .CSq | .FSq => .FSq | .H => .D36
  | .I => .D31 | .NSq => .NSq | .P => .D19 | .QFourth => .QFourth | .U => .D26 | .YK => .YK
  | .bSq => .bSq | .c => .D6 | .cFourth => .cFourth | .e => .D10 | .l => .D9 | _ => .lamB

/-- Its right-hand side. -/
def defn (z u y : ℕ) (v : ShortQuadraticVar) : ShortQuadraticExpr :=
  let w := witness
  let Z := constant (z : ℤ)
  let U₀ := constant (u : ℤ)
  let Y₀ := constant (y : ℤ)
  match v with
  | .AC => AExpr * CExpr
  | .AC₁ => AExpr * w .C₁
  | .AE => AExpr * w .E
  | .CSq => CExpr ^ 2
  | .FSq => w .F ^ 2
  | .H => 2 * w .R + 1 + w .j * CExpr
  | .I => w .D + w .o * w .F
  | .NSq => w .N ^ 2
  | .P => 2 * w .M * w .MU
  | .QFourth => w .QSq ^ 2
  | .U => w .NSq * w .w
  | .YK => w .Y * w .K
  | .bSq => bExpr ^ 2
  | .c => 1 + input * w .B + w .g
  | .cFourth => w .cSq ^ 2
  | .e => Y₀ + w .m * (w .B - 2 * Z)
  | .l => U₀ + w .t * (w .B - 2 * Z)
  | .lamB => w .lam * w .B
  | v => witness v

theorem expression_defEq (z u y L : ℕ) (v : ShortQuadraticVar) (hv : elim v = true) :
    expression z u y L (defEq v) = witness v - defn z u y v := by
  cases v <;> first | rfl | exact absurd hv (by decide)

/-- One round of substitution. -/
def σ₁ (z u y : ℕ) (v : ShortQuadraticVar) : ShortQuadraticExpr :=
  if elim v then defn z u y v else witness v

/-- The full substitution (two rounds suffice: `U` refers to `N²`). -/
def full (z u y : ℕ) (v : ShortQuadraticVar) : ShortQuadraticExpr :=
  if elim v then (defn z u y v).subst (σ₁ z u y) else witness v

theorem full_fix (z u y : ℕ) (v : ShortQuadraticVar) (hv : elim v = true) :
    (defn z u y v).subst (full z u y) = full z u y v := by
  cases v <;> first | rfl | exact absurd hv (by decide)

theorem full_kept (z u y : ℕ) (v : ShortQuadraticVar) (hv : elim v = false) :
    full z u y v = witness v := by
  simp [full, hv]

theorem full_noElim (z u y : ℕ) (v w : ShortQuadraticVar) (hw : elim w = true) :
    (full z u y v).occurs w = false := by
  cases v <;> cases w <;> first | rfl | exact absurd hw (by decide)

/-- The kept equations. -/
def kept (i : ShortQuadraticEquation) : Bool :=
  !(i == .AC || i == .AC₁ || i == .AE || i == .CSq || i == .FSq || i == .D36 || i == .D31 ||
    i == .NSq || i == .D19 || i == .QFourth || i == .D26 || i == .YK || i == .bSq || i == .D6 ||
    i == .cFourth || i == .D10 || i == .D9 || i == .lamB)

theorem kept_card : (Finset.univ.filter fun i => kept i = true).card = 28 := by decide

theorem defEq_not_kept (v : ShortQuadraticVar) (hv : elim v = true) : kept (defEq v) = false := by
  cases v <;> first | rfl | exact absurd hv (by decide)

/-- Every equation is kept or defines an eliminated witness. -/
theorem kept_or_defEq (i : ShortQuadraticEquation) :
    kept i = true ∨ ∃ v, elim v = true ∧ defEq v = i := by
  cases i <;> first
    | exact Or.inl rfl
    | exact Or.inr ⟨.AC, rfl, rfl⟩ | exact Or.inr ⟨.AC₁, rfl, rfl⟩ | exact Or.inr ⟨.AE, rfl, rfl⟩
    | exact Or.inr ⟨.CSq, rfl, rfl⟩ | exact Or.inr ⟨.FSq, rfl, rfl⟩ | exact Or.inr ⟨.H, rfl, rfl⟩
    | exact Or.inr ⟨.I, rfl, rfl⟩ | exact Or.inr ⟨.NSq, rfl, rfl⟩ | exact Or.inr ⟨.P, rfl, rfl⟩
    | exact Or.inr ⟨.QFourth, rfl, rfl⟩ | exact Or.inr ⟨.U, rfl, rfl⟩
    | exact Or.inr ⟨.YK, rfl, rfl⟩ | exact Or.inr ⟨.bSq, rfl, rfl⟩ | exact Or.inr ⟨.c, rfl, rfl⟩
    | exact Or.inr ⟨.cFourth, rfl, rfl⟩ | exact Or.inr ⟨.e, rfl, rfl⟩
    | exact Or.inr ⟨.l, rfl, rfl⟩ | exact Or.inr ⟨.lamB, rfl, rfl⟩

/-- The reduced residual expressions. -/
def redExpr (z u y L : ℕ) (i : ShortQuadraticEquation) : ShortQuadraticExpr :=
  (expression z u y L i).subst (full z u y)

set_option maxHeartbeats 8000000 in
theorem redExpr_degreeBound_le_four (z u y L : ℕ) (i : ShortQuadraticEquation) (hi : kept i = true) :
    (redExpr z u y L i).degreeBound ≤ 4 := by
  cases i <;> first | exact absurd hi (by decide) | exact Nat.le_of_ble_eq_true rfl

theorem redExpr_noElim (z u y L : ℕ) (i : ShortQuadraticEquation) (w : ShortQuadraticVar)
    (hw : elim w = true) : (redExpr z u y L i).occurs w = false := by
  cases i <;> cases w <;> first | rfl | exact absurd hw (by decide)

/-! ### Solvability -/

section Semantics

variable {x z u y L : ℕ}

theorem eval_defn_of_equations (val : ShortQuadraticVar → ℕ)
    (h : ∀ i, MvPolynomial.eval (assignment x val) (residual z u y L i) = 0)
    (v : ShortQuadraticVar) (hv : elim v = true) :
    MvPolynomial.eval (assignment x val) (defn z u y v).toPolynomial = val v := by
  have := h (defEq v)
  rw [ShortQuadratic.residual, expression_defEq z u y L v hv] at this
  rw [ShortQuadraticExpr.toPolynomial_sub, map_sub] at this
  simp only [ShortQuadraticExpr.toPolynomial, MvPolynomial.eval_X, assignment] at this
  linarith

theorem eval_σ₁_of_equations (val : ShortQuadraticVar → ℕ)
    (h : ∀ i, MvPolynomial.eval (assignment x val) (residual z u y L i) = 0)
    (v : ShortQuadraticVar) :
    MvPolynomial.eval (assignment x val) (σ₁ z u y v).toPolynomial = val v := by
  unfold σ₁
  cases hv : elim v
  · simp [toPolynomial, assignment]
  · simpa using eval_defn_of_equations val h v hv

theorem eval_full_of_equations (val : ShortQuadraticVar → ℕ)
    (h : ∀ i, MvPolynomial.eval (assignment x val) (residual z u y L i) = 0)
    (v : ShortQuadraticVar) :
    MvPolynomial.eval (assignment x val) (full z u y v).toPolynomial = val v := by
  unfold full
  cases hv : elim v
  · simp [toPolynomial, assignment]
  · simp only [if_true]
    rw [eval_subst]
    have hfun : (fun o : Option ShortQuadraticVar => match o with
        | none => assignment x val none
        | some v => MvPolynomial.eval (assignment x val) (σ₁ z u y v).toPolynomial) =
        assignment x val := by
      funext o; cases o with
      | none => rfl
      | some w => exact eval_σ₁_of_equations val h w
    rw [hfun]
    exact eval_defn_of_equations val h v hv

/-- A solution of the full system solves the reduced equations. -/
theorem red_of_full (val : ShortQuadraticVar → ℕ)
    (h : ∀ i, MvPolynomial.eval (assignment x val) (residual z u y L i) = 0)
    (i : ShortQuadraticEquation) :
    MvPolynomial.eval (assignment x val) (redExpr z u y L i).toPolynomial = 0 := by
  rw [redExpr, eval_subst]
  have hfun : (fun o : Option ShortQuadraticVar => match o with
      | none => assignment x val none
      | some v => MvPolynomial.eval (assignment x val) (full z u y v).toPolynomial) =
      assignment x val := by
    funext o; cases o with
    | none => rfl
    | some w => exact eval_full_of_equations val h w
  rw [hfun]
  exact h i


set_option maxHeartbeats 4000000 in
/-- The eliminated values are positive at shifted (positive) kept witnesses. -/
theorem full_pos (hz : 1 ≤ z) (w : ShortQuadraticVar → ℕ)
    (hD2 : MvPolynomial.eval (assignment x (fun v => w v + 1)) (redExpr z u y L .D2).toPolynomial = 0)
    (v : ShortQuadraticVar) (hv : elim v = true) :
    0 < MvPolynomial.eval (assignment x (fun v => w v + 1)) (full z u y v).toPolynomial := by
  have hB : 2 * (z : ℤ) < (w .B : ℤ) + 1 := by
    simp only [redExpr, expression, ShortQuadraticExpr.subst_add, ShortQuadraticExpr.subst_sub, ShortQuadraticExpr.subst_mul, ShortQuadraticExpr.subst_pow, ShortQuadraticExpr.subst_ofNat, subst, full, σ₁, defn, elim, bExpr, ShortQuadraticExpr.toPolynomial_add, ShortQuadraticExpr.toPolynomial_sub, ShortQuadraticExpr.toPolynomial_mul, ShortQuadraticExpr.toPolynomial_pow, ShortQuadraticExpr.toPolynomial_ofNat, Bool.false_eq_true, ↓reduceIte, ShortQuadraticExpr.toPolynomial,
      if_true, if_false, map_sub, map_mul, map_pow, map_add, MvPolynomial.eval_C,
      MvPolynomial.eval_X, assignment, Nat.cast_add, Nat.cast_one] at hD2
    have h1 : (2 * (z : ℤ)) ≤ (2 * z) ^ (L + 1) := by
      have : (1 : ℤ) ≤ 2 * z := by omega
      calc (2 * (z : ℤ)) = (2 * z) ^ 1 := (pow_one _).symm
        _ ≤ (2 * z) ^ (L + 1) := pow_le_pow_right₀ this (by omega)
    have h2 : (1 : ℤ) ≤ ((((w .epsilon : ℤ) + 1) + x) ^ 2) ^ 2 := by
      have : (1 : ℤ) ≤ ((w .epsilon : ℤ) + 1) + x := by omega
      exact one_le_pow₀ (one_le_pow₀ this)
    have h3 : (0 : ℤ) ≤ (2 * z) ^ (L + 1) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h2 h3]
  cases v <;> first | exact absurd hv (by decide) |
    (simp only [full, σ₁, defn, elim, ShortQuadraticExpr.subst_add, ShortQuadraticExpr.subst_sub, ShortQuadraticExpr.subst_mul, ShortQuadraticExpr.subst_pow, ShortQuadraticExpr.subst_ofNat, subst, AExpr, CExpr, bExpr, ShortQuadraticExpr.toPolynomial_add, ShortQuadraticExpr.toPolynomial_sub, ShortQuadraticExpr.toPolynomial_mul, ShortQuadraticExpr.toPolynomial_pow, ShortQuadraticExpr.toPolynomial_ofNat, Bool.false_eq_true, ↓reduceIte, ShortQuadraticExpr.toPolynomial,
      if_true, if_false, map_sub, map_mul, map_pow, map_add, MvPolynomial.eval_C,
      MvPolynomial.eval_X, assignment, Nat.cast_add, Nat.cast_one]
     first | positivity | nlinarith [hB] | skip)

/-- The values of the eliminated witnesses. -/
noncomputable def extend (x z u y : ℕ) (w : ShortQuadraticVar → ℕ) : ShortQuadraticVar → ℕ :=
  fun v => if elim v then
    (MvPolynomial.eval (assignment x w) (full z u y v).toPolynomial).toNat else w v

theorem extend_cast (hz : 1 ≤ z) (w : ShortQuadraticVar → ℕ)
    (hD2 : MvPolynomial.eval (assignment x (fun v => w v + 1)) (redExpr z u y L .D2).toPolynomial = 0)
    (v : ShortQuadraticVar) :
    (extend x z u y (fun v => w v + 1) v : ℤ) =
      MvPolynomial.eval (assignment x (fun v => w v + 1)) (full z u y v).toPolynomial := by
  unfold extend
  cases hv : elim v
  · simp [full, hv, ShortQuadraticExpr.toPolynomial, assignment]
  · simp only [if_true]
    exact Int.toNat_of_nonneg (full_pos hz w hD2 v hv).le

theorem extend_pos (hz : 1 ≤ z) (w : ShortQuadraticVar → ℕ)
    (hD2 : MvPolynomial.eval (assignment x (fun v => w v + 1)) (redExpr z u y L .D2).toPolynomial = 0)
    (v : ShortQuadraticVar) : 0 < extend x z u y (fun v => w v + 1) v := by
  have := extend_cast hz w hD2 v
  cases hv : elim v
  · simp [extend, hv]
  · have hp := full_pos hz w hD2 v hv
    omega

/-- Reduced solutions at shifted witnesses extend to positive solutions of the full system. -/
theorem full_of_red (hz : 1 ≤ z) (w : ShortQuadraticVar → ℕ)
    (h : ∀ i, kept i = true →
      MvPolynomial.eval (assignment x (fun v => w v + 1)) (redExpr z u y L i).toPolynomial = 0) :
    Nonempty (PositiveWitnesses x z u y L) := by
  have hD2 := h .D2 rfl
  set val := extend x z u y (fun v => w v + 1) with hval
  have hc := extend_cast hz w hD2
  -- evaluation of substituted expressions at `val` agrees with the shifted witnesses
  have hcongr : ∀ p : ShortQuadraticExpr, (∀ e, elim e = true → p.occurs e = false) →
      MvPolynomial.eval (assignment x val) p.toPolynomial =
        MvPolynomial.eval (assignment x (fun v => w v + 1)) p.toPolynomial := by
    intro p hp
    apply eval_congr p (a := assignment x val) (a' := assignment x (fun v => w v + 1)) rfl
    intro e he
    cases hee : elim e
    · simp [assignment, hval, extend, hee]
    · exact absurd he (by rw [hp e hee]; decide)
  have hfull : ∀ v, MvPolynomial.eval (assignment x val) (full z u y v).toPolynomial = val v := by
    intro v
    rw [hcongr _ (fun e he => full_noElim z u y v e he), ← hc v]
  have hfun : (fun o : Option ShortQuadraticVar => match o with
      | none => assignment x val none
      | some v => MvPolynomial.eval (assignment x val) (full z u y v).toPolynomial) =
      assignment x val := by
    funext o; cases o with
    | none => rfl
    | some e => exact hfull e
  refine ⟨⟨val, extend_pos hz w hD2, fun i => ?_⟩⟩
  rcases kept_or_defEq i with hi | ⟨v, hv, rfl⟩
  · have := h i hi
    rw [← hcongr _ (fun e he => redExpr_noElim z u y L i e he), redExpr, eval_subst, hfun] at this
    exact this
  · rw [ShortQuadratic.residual, expression_defEq z u y L v hv, ShortQuadraticExpr.toPolynomial_sub,
      map_sub]
    have hd : MvPolynomial.eval (assignment x val) (defn z u y v).toPolynomial = val v := by
      rw [← hfun, ← eval_subst, full_fix z u y v hv]
      exact hfull v
    simp only [ShortQuadraticExpr.toPolynomial, MvPolynomial.eval_X, assignment] at hd ⊢
    rw [hd]; ring

end Semantics

/-! ### Forty witnesses in standard coordinates -/

/-- The kept witnesses. -/
def keptList : List ShortQuadraticVar :=
  [.B, .C₁, .D, .D₁, .E, .F, .G, .K, .M, .N, .R, .S, .T, .Y, .g, .h, .i, .j, .m, .o, .s, .t, .w,
    .alpha, .delta, .gamma, .lam, .phi, .epsilon, .pellMod, .cSq, .xi, .QSq, .QCube,
    .cFourthQCube, .MU, .PK, .tau, .eta, .GH]

theorem keptList_length : keptList.length = 40 := rfl

def keepIdx (j : Fin 40) : ShortQuadraticVar := keptList.get ⟨j, by rw [keptList_length]; exact j.isLt⟩

def posOf (v : ShortQuadraticVar) : Fin 40 :=
  ⟨min (keptList.idxOf v) 39, by omega⟩

theorem keepIdx_posOf (v : ShortQuadraticVar) (hv : elim v = false) : keepIdx (posOf v) = v := by
  cases v <;> first | rfl | exact absurd hv (by decide)

/-- Coordinates: the input first, then the kept witnesses. -/
def coord (o : Option ShortQuadraticVar) : Fin 41 :=
  match o with
  | none => 0
  | some v => (posOf v).succ

/-- The shifted reduced residuals. -/
noncomputable def redShift (z u y L : ℕ) (i : ShortQuadraticEquation) : Poly :=
  (redExpr z u y L i).shiftWitnesses.toPolynomial

/-- The sum of squares of the 28 kept residuals. -/
noncomputable def redSum (z u y L : ℕ) : Poly :=
  ∑ i ∈ Finset.univ.filter (fun i => kept i = true), redShift z u y L i ^ 2

theorem redSum_totalDegree_le (z u y L : ℕ) : (redSum z u y L).totalDegree ≤ 8 :=
  Diophantine.totalDegree_sum_pow_le _ (redShift z u y L) 2 4 fun i hi => by
    refine (ShortQuadraticExpr.totalDegree_toPolynomial_le _).trans ?_
    rw [ShortQuadraticExpr.degreeBound_shiftWitnesses]
    exact redExpr_degreeBound_le_four z u y L i (Finset.mem_filter.1 hi).2

/-- The octic polynomial with one input and forty witnesses. -/
noncomputable def octic40 (z u y L : ℕ) : MvPolynomial (Fin 41) ℤ :=
  MvPolynomial.rename coord (redSum z u y L)

theorem octic40_totalDegree_le (z u y L : ℕ) : (octic40 z u y L).totalDegree ≤ 8 :=
  (MvPolynomial.totalDegree_rename_le _ _).trans (redSum_totalDegree_le z u y L)

theorem shiftAssignment_assignment (x : ℕ) (w : ShortQuadraticVar → ℕ) :
    shiftAssignment (assignment x w) = assignment x (fun v => w v + 1) := by
  funext o; cases o <;> simp [shiftAssignment, assignment]

/-- **Forty witnesses**: natural solutions of the octic are positive solutions of the 58-witness
quadratic system. -/
theorem exists_octic40_iff {x z u y L : ℕ} (hz : 1 ≤ z) :
    (∃ a : Fin 40 → ℕ, MvPolynomial.eval (fun k => ((Fin.cons x a : Fin 41 → ℕ) k : ℤ))
      (octic40 z u y L) = 0) ↔ Nonempty (PositiveWitnesses x z u y L) := by
  have hsum : ∀ w : ShortQuadraticVar → ℕ,
      MvPolynomial.eval (assignment x w) (redSum z u y L) = 0 ↔
        ∀ i, kept i = true → MvPolynomial.eval (assignment x (fun v => w v + 1))
          (redExpr z u y L i).toPolynomial = 0 := by
    intro w
    simp only [redSum, map_sum, map_pow, redShift, ShortQuadraticExpr.eval_shiftWitnesses,
      shiftAssignment_assignment]
    rw [show (∑ i ∈ Finset.univ.filter (fun i => kept i = true),
        MvPolynomial.eval (assignment x (fun v => w v + 1)) (redExpr z u y L i).toPolynomial ^ 2) =
        ∑ i ∈ Finset.univ.filter (fun i => kept i = true),
          MvPolynomial.eval (assignment x (fun v => w v + 1)) (redExpr z u y L i).toPolynomial *
          MvPolynomial.eval (assignment x (fun v => w v + 1)) (redExpr z u y L i).toPolynomial by
        simp only [sq], Finset.sum_mul_self_eq_zero_iff]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mul_self_eq_zero]
  have heval : ∀ a : Fin 40 → ℕ,
      MvPolynomial.eval (fun k => ((Fin.cons x a : Fin 41 → ℕ) k : ℤ)) (octic40 z u y L) =
        MvPolynomial.eval (assignment x (fun v => a (posOf v))) (redSum z u y L) := by
    intro a
    rw [octic40, MvPolynomial.eval_rename]
    congr 2
    funext o; cases o <;> rfl
  constructor
  · rintro ⟨a, ha⟩
    rw [heval, hsum] at ha
    exact full_of_red hz _ ha
  · rintro ⟨h⟩
    refine ⟨fun j => h.val (keepIdx j) - 1, ?_⟩
    rw [heval, hsum]
    intro i hi
    rw [← red_of_full h.val h.equations i]
    apply eval_congr (redExpr z u y L i)
      (a := assignment x (fun v => h.val (keepIdx (posOf v)) - 1 + 1)) (a' := assignment x h.val) rfl
    intro e he
    cases hee : elim e
    · have := h.pos (keepIdx (posOf e))
      simp only [assignment, keepIdx_posOf e hee] at this ⊢
      push_cast [Nat.sub_add_cancel this]
      rfl
    · exact absurd he (by rw [redExpr_noElim z u y L i e hee]; decide)

/-- Every positive input of a normalized quartic with an admissible index is represented with
forty witnesses and degree eight. -/
theorem wset_octic40_iff {ν : ℕ} {P : MvPolynomial (Fin (ν + 1)) ℤ} {z u y x : ℕ}
    (hν : 1 ≤ ν) (hP : P.totalDegree ≤ 4) (hnorm : Normalized P) (hI : Index ν P z u y)
    (hx : 0 < x) :
    Wset P x ↔ ∃ a : Fin 40 → ℕ,
      MvPolynomial.eval (fun k => ((Fin.cons x a : Fin 41 → ℕ) k : ℤ))
        (octic40 z u y (L4 ν)) = 0 := by
  rw [short_polynomial_master hν hP hnorm hI hx, short_polynomial_iff_quadratic hI.two_le hx,
    exists_octic40_iff (by have := hI.two_le; omega)]

end Pair40

end Jones1982
