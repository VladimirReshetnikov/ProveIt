import FreshModel106
/-! # iPRA endpoints for the nonzero-sphere fourteen-variable carrier forms

`CarrierNonzeroSpheres` gives two forms on the maintained fourteen coordinates,
with profiles 14/71/80 and 14/72/68, whose positive zeros are exactly the
Carrier65 zeros. Its integer argument needs the units `±1`, nonvanishing of
three near-square Pell norms (an integer descent), the consecutive-product
negative-unit exclusion and one congruence modulo four. All four hold in the
ring of differences of every model of `𝗜𝚺₁` (`ModelArithmetic`), so the
argument is replayed there and the maintained all-model bridge transfers. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace DiophantineConsistency.FreshCarrierSpheres
open AdaptiveEquationSyntax2011 ModelDifferenceRing DiscreteOrderedRingFacts Carrier65
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix

/-! ### The integer argument in a discretely ordered ring -/

section Generic
variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

def auxiliary (d : Core R) : R := d.delta*(d.f^2-1)*(d.V^2-d.y^2)+d.y^2

def value71 (p : Fin 4 → R) (v : Fin 14 → R) : R :=
  let d := core p v
  (d.P*d.Q)^2 + (auxiliary d*d.W-1)^2 + (strong d)^2 - 2

def value72 (p : Fin 4 → R) (v : Fin 14 → R) : R :=
  let d := core p v
  d.P^2 + (auxiliary d)^2 + (strong d)^2 + (d.Q*d.W-1)^2 - 3

/-- The integer-like facts the argument uses. -/
structure Facts (R : Type*) [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] : Prop where
  discrete : Discrete R
  mod4 : Nonempty (R →+* ZMod 4)
  near : ∀ A x y : R, 2 ≤ A → y ≠ 0 → x ^ 2 - (A ^ 2 - 1) * y ^ 2 ≠ 0
  consecutive : ∀ n x y : R, 2 ≤ n → x ^ 2 - n * (n + 1) * y ^ 2 ≠ -1

variable (F : Facts R) (p : Fin 4 → R) (v : Fin 14 → R) (hb : 0 < p 0) (hv : ∀ j, 0 < v j)
include F hb hv

theorem scales_pos : 0 < (core p v).q ∧ 0 < (core p v).X ∧ 0 < (core p v).Y ∧
    0 < (core p v).E ∧ 0 < (core p v).a := by
  have hq : 0 < (core p v).q :=
    lt_of_lt_of_le (by norm_num) (ModelCarrierScaled.q_ge_two F.discrete p v hb hv)
  have hX : 0 < (core p v).X := mul_pos (hv 8) hq
  have hY : 0 < (core p v).Y := mul_pos (hv 7) (pow_pos hq 3)
  have hE : 0 < (core p v).E := mul_pos hX hY
  exact ⟨hq, hX, hY, hE, add_pos hE hY⟩

theorem firstParameter_ge_two : 2 ≤ (core p v).E * (core p v).Y := by
  have hq := ModelCarrierScaled.q_ge_two F.discrete p v hb hv
  obtain ⟨_, _, hY, _, _⟩ := scales_pos F p v hb hv
  have hw : 1 ≤ v 8 := F.discrete _ (hv 8)
  have hX : 2 ≤ (core p v).X := by
    change 2 ≤ v 8 * (core p v).q
    nlinarith
  have hY1 : 1 ≤ (core p v).Y := F.discrete _ hY
  have hE : 2 ≤ (core p v).E := by
    change 2 ≤ (core p v).X * (core p v).Y
    nlinarith
  nlinarith

theorem c_pos : 0 < (core p v).c := by
  obtain ⟨_, _, hY, _, _⟩ := scales_pos F p v hb hv
  change 0 < (v 10+v 11)*(core p v).Y+v 10
  exact add_pos (mul_pos (add_pos (hv 10) (hv 11)) hY) (hv 10)

theorem first_ne_zero : (core p v).P ≠ 0 := by
  have hm := firstParameter_ge_two F p v hb hv
  have hk : 0 < (core p v).k := add_pos (hv 10) (hv 11)
  have hi : 4*(core p v).P = (2*(core p v).tau)^2 -
      ((2*((core p v).E*(core p v).Y)+1)^2-1)*(core p v).k^2 := by
    rw [first_shape]; ring
  intro hz
  exact F.near (2*((core p v).E*(core p v).Y)+1) (2*(core p v).tau) (core p v).k
    (by linarith) hk.ne' (by rw [← hi, hz]; ring)

theorem main_ne_zero : (core p v).Q ≠ 0 := by
  obtain ⟨_, _, _, _, ha⟩ := scales_pos F p v hb hv
  change (core p v).D^2-(core p v).delta*(core p v).c^2 ≠ 0
  rw [delta_shape]
  exact F.near _ _ _ (by linarith) (c_pos F p v hb hv).ne'

theorem strong_ne_zero : strong (core p v) ≠ 0 := by
  obtain ⟨_, _, _, _, ha⟩ := scales_pos F p v hb hv
  have hc := c_pos F p v hb hv
  unfold strong
  rw [delta_shape]
  exact F.near _ _ _ (by linarith) (mul_pos (hv 5) (pow_pos hc 2)).ne'

theorem auxiliary_ne_zero : auxiliary (core p v) ≠ 0 := by
  have hf : 0 < (core p v).f := hv 4
  have hy : 0 < (core p v).y := hv 12
  have hd : 0 < (core p v).delta := ModelCarrierScaled.delta_pos F.discrete p v hb hv
  have hd1 : 1 ≤ (core p v).delta := F.discrete _ hd
  by_cases hf1 : (core p v).f = 1
  · unfold auxiliary
    rw [hf1]
    simpa only [one_pow, sub_self, mul_zero, zero_mul, zero_add] using (pow_pos hy 2).ne'
  · have hf2 : 2 ≤ (core p v).f := by
      have h1 : 1 ≤ (core p v).f := F.discrete _ hf
      have : 1 < (core p v).f := lt_of_le_of_ne h1 (Ne.symm hf1)
      have := F.discrete ((core p v).f - 1) (by linarith)
      linarith
    have hs : 3 ≤ (core p v).f^2-1 := by nlinarith
    have ht : 2 ≤ (core p v).delta*((core p v).f^2-1) := by nlinarith
    have hi : 4*((core p v).delta*((core p v).f^2-1))*auxiliary (core p v) =
        (2*((core p v).delta*((core p v).f^2-1))*(core p v).V)^2 -
          ((2*((core p v).delta*((core p v).f^2-1))-1)^2-1)*(core p v).y^2 := by
      unfold auxiliary; ring
    intro hz
    exact F.near (2*((core p v).delta*((core p v).f^2-1))-1)
      (2*((core p v).delta*((core p v).f^2-1))*(core p v).V) (core p v).y
      (by linarith) hy.ne' (by rw [← hi, hz]; ring)

theorem negative_unit_exclusions :
    (core p v).P ≠ -1 ∧ (core p v).Q ≠ -1 ∧ strong (core p v) ≠ -1 := by
  obtain ⟨φ⟩ := F.mod4
  refine ⟨?_, ?_, ?_⟩
  · rw [first_shape]
    exact F.consecutive _ _ _ (firstParameter_ge_two F p v hb hv)
  · change (core p v).D^2-(core p v).delta*(core p v).c^2 ≠ -1
    rw [delta_shape]
    exact ModelCarrierScaled.strong_ne_neg_one φ _ _ _
  · unfold strong
    rw [delta_shape]
    exact ModelCarrierScaled.strong_ne_neg_one φ _ _ _

omit hb hv in
theorem square_aux_ne_neg_one (t h y : R) : t ^ 2 * (h ^ 2 - y ^ 2) + y ^ 2 ≠ -1 := by
  obtain ⟨φ⟩ := F.mod4
  have := ModelCarrierScaled.strong_ne_neg_one φ (t - 2) (t * h) y
  intro hc; apply this; linear_combination hc

omit F hb hv in
theorem auxiliary_of_strong_one (hs : strong (core p v) = 1) :
    auxiliary (core p v) = (core p v).U := by
  have hf : (core p v).f^2-1 = (core p v).delta*((core p v).i*(core p v).c^2)^2 := by
    unfold strong at hs; linear_combination hs
  change (core p v).delta*((core p v).f^2-1)*((core p v).V^2-(core p v).y^2)+(core p v).y^2 =
    ((core p v).i*(core p v).delta*(core p v).c^2)^2*((core p v).V^2-(core p v).y^2)+(core p v).y^2
  rw [hf]; ring

omit hb hv in
theorem auxiliary_ne_neg_one_of_strong_one (hs : strong (core p v) = 1) :
    auxiliary (core p v) ≠ -1 := by
  rw [auxiliary_of_strong_one p v hs]
  exact square_aux_ne_neg_one F _ _ _

omit hb hv in
theorem square_ge_one {x : R} (hx : x ≠ 0) : 1 ≤ x ^ 2 := F.discrete _ (pow_pos (abs_pos.mpr hx) 2 |>.trans_eq (sq_abs x))

omit hb hv in
theorem unit_factors {x y : R} (h : x * y = 1) (hx : x ≠ -1) : x = 1 ∧ y = 1 := by
  have h1 := (eq_one_or_neg_one_of_mul_eq_one F.discrete h).resolve_right hx
  exact ⟨h1, by simpa only [h1, one_mul] using h⟩

omit hb hv in
theorem product_ne_neg_one {x y : R} (hx : x ≠ -1) (hy : y ≠ -1) : x * y ≠ -1 := by
  intro h
  have h1 := (eq_one_or_neg_one_of_mul_eq_one F.discrete
    (show x * (-y) = 1 by linear_combination -h)).resolve_right hx
  exact hy (by simpa only [h1, one_mul] using h)

omit F hb hv in
theorem sq_one {x : R} (hx : x ≠ -1) (h : x ^ 2 = 1) : x = 1 := by
  have h2 : (x - 1) * (x + 1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h2 with h1 | h1
  · linear_combination h1
  · exact absurd (by linear_combination h1) hx

def Norms : Prop :=
  (core p v).P = 1 ∧ (core p v).Q = 1 ∧ auxiliary (core p v) = 1 ∧
    strong (core p v) = 1 ∧ (core p v).W = 1

theorem value71_zero_iff_norms : value71 p v = 0 ↔ Norms p v := by
  constructor
  · intro hz
    have hp : 1 ≤ ((core p v).P*(core p v).Q)^2 := square_ge_one F
      (mul_ne_zero (first_ne_zero F p v hb hv) (main_ne_zero F p v hb hv))
    have hs : 1 ≤ (strong (core p v))^2 := square_ge_one F (strong_ne_zero F p v hb hv)
    have hr := sq_nonneg (auxiliary (core p v)*(core p v).W-1)
    change ((core p v).P*(core p v).Q)^2+(auxiliary (core p v)*(core p v).W-1)^2+
      (strong (core p v))^2-2 = 0 at hz
    have hps : ((core p v).P*(core p v).Q)^2 = 1 := by nlinarith only [hz,hp,hs,hr]
    have hss : (strong (core p v))^2 = 1 := by nlinarith only [hz,hp,hs,hr]
    have hrs : (auxiliary (core p v)*(core p v).W-1)^2 = 0 := by nlinarith only [hz,hp,hs,hr]
    have huw : auxiliary (core p v)*(core p v).W = 1 := sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hrs)
    obtain ⟨hnP,hnQ,hnZ⟩ := negative_unit_exclusions F p v hb hv
    have hpq := sq_one (product_ne_neg_one F hnP hnQ) hps
    have hz1 := sq_one hnZ hss
    obtain ⟨hP,hQ⟩ := unit_factors F hpq hnP
    obtain ⟨hU,hW⟩ := unit_factors F huw (auxiliary_ne_neg_one_of_strong_one F p v hz1)
    exact ⟨hP,hQ,hU,hz1,hW⟩
  · rintro ⟨hP,hQ,hU,hZ,hW⟩
    simp only [value71,hP,hQ,hU,hZ,hW]
    norm_num

theorem value72_zero_iff_norms : value72 p v = 0 ↔ Norms p v := by
  constructor
  · intro hz
    have hp : 1 ≤ (core p v).P^2 := square_ge_one F (first_ne_zero F p v hb hv)
    have hu : 1 ≤ (auxiliary (core p v))^2 := square_ge_one F (auxiliary_ne_zero F p v hb hv)
    have hs : 1 ≤ (strong (core p v))^2 := square_ge_one F (strong_ne_zero F p v hb hv)
    have hr := sq_nonneg ((core p v).Q*(core p v).W-1)
    change (core p v).P^2+(auxiliary (core p v))^2+(strong (core p v))^2+
      ((core p v).Q*(core p v).W-1)^2-3 = 0 at hz
    have hps : (core p v).P^2 = 1 := by nlinarith only [hz,hp,hu,hs,hr]
    have hus : (auxiliary (core p v))^2 = 1 := by nlinarith only [hz,hp,hu,hs,hr]
    have hss : (strong (core p v))^2 = 1 := by nlinarith only [hz,hp,hu,hs,hr]
    have hrs : ((core p v).Q*(core p v).W-1)^2 = 0 := by nlinarith only [hz,hp,hu,hs,hr]
    have hqw : (core p v).Q*(core p v).W = 1 := sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hrs)
    obtain ⟨hnP,hnQ,hnZ⟩ := negative_unit_exclusions F p v hb hv
    have hP := sq_one hnP hps
    have hZ := sq_one hnZ hss
    have hU := sq_one (auxiliary_ne_neg_one_of_strong_one F p v hZ) hus
    obtain ⟨hQ,hW⟩ := unit_factors F hqw hnQ
    exact ⟨hP,hQ,hU,hZ,hW⟩
  · rintro ⟨hP,hQ,hU,hZ,hW⟩
    simp only [value72,hP,hQ,hU,hZ,hW]
    norm_num

omit F hb hv in
theorem unit_eq_one {a b : R} (hd : Discrete R) (h : a * b = 1) (ha : a ≠ -1) : a = 1 :=
  (eq_one_or_neg_one_of_mul_eq_one hd h).resolve_right ha

/-- `Carrier65.value_zero_iff_norms`, in the ring. -/
theorem value65_zero_iff_norms :
    Carrier65.value p v = 0 ↔
      (core p v).P = 1 ∧ (core p v).Q = 1 ∧ (core p v).U = 1 ∧
        strong (core p v) = 1 ∧ (core p v).W = 1 := by
  obtain ⟨hnP, hnQ, hnS⟩ := negative_unit_exclusions F p v hb hv
  have hU : (core p v).U ≠ -1 := square_aux_ne_neg_one F _ _ _
  have hdelta := (ModelCarrierScaled.delta_pos F.discrete p v hb hv).ne'
  rw [Carrier65.scaled_identity, mul_eq_zero]
  simp only [hdelta, false_or, sub_eq_zero]
  set P := (core p v).P; set Q := (core p v).Q; set U := (core p v).U
  set W := (core p v).W; set S := strong (core p v)
  constructor
  · intro hp
    have hS : S = 1 := unit_eq_one F.discrete (show S * (P*Q*U*W) = 1 by linear_combination hp) hnS
    have hP1 : P = 1 := unit_eq_one F.discrete (show P * (Q*U*W*S) = 1 by linear_combination hp) hnP
    have hQ1 : Q = 1 := unit_eq_one F.discrete (show Q * (P*U*W*S) = 1 by linear_combination hp) hnQ
    have hU1 : U = 1 := unit_eq_one F.discrete (show U * (P*Q*W*S) = 1 by linear_combination hp) hU
    refine ⟨hP1, hQ1, hU1, hS, ?_⟩
    rw [hP1, hQ1, hU1, hS] at hp; linear_combination hp
  · rintro ⟨hP1, hQ1, hU1, hS, hW1⟩
    rw [hP1, hQ1, hU1, hS, hW1]; ring

theorem norms_iff_original : Norms p v ↔ Carrier65.value p v = 0 := by
  rw [value65_zero_iff_norms F p v hb hv]
  constructor
  · rintro ⟨hP,hQ,hU,hZ,hW⟩
    exact ⟨hP,hQ,by rw [← auxiliary_of_strong_one p v hZ]; exact hU,hZ,hW⟩
  · rintro ⟨hP,hQ,hU,hZ,hW⟩
    exact ⟨hP,hQ,by rw [auxiliary_of_strong_one p v hZ]; exact hU,hZ,hW⟩

theorem zero_iff71 : value71 p v = 0 ↔ Carrier65.value p v = 0 :=
  (value71_zero_iff_norms F p v hb hv).trans (norms_iff_original F p v hb hv)

theorem zero_iff72 : value72 p v = 0 ↔ Carrier65.value p v = 0 :=
  (value72_zero_iff_norms F p v hb hv).trans (norms_iff_original F p v hb hv)

end Generic

/-! ### Literal syntax -/

/-- The common Carrier65 front, followed by `final` built from its blocks. -/
def frontAt (p : Fin 4 → ℤ)
    (final : Expr (Fin 14) → Expr (Fin 14) → Expr (Fin 14) → Expr (Fin 14) → Expr (Fin 14) →
      Expr (Fin 14)) : Expr (Fin 14) :=
  let J : Expr (Fin 14) := .var 0
  let F : Expr (Fin 14) := .var 1
  let alpha : Expr (Fin 14) := .var 2
  let z : Expr (Fin 14) := .var 3
  let f : Expr (Fin 14) := .var 4
  let i : Expr (Fin 14) := .var 5
  let T : Expr (Fin 14) := .var 6
  let s : Expr (Fin 14) := .var 7
  let w : Expr (Fin 14) := .var 8
  let n : Expr (Fin 14) := .var 9
  let eta : Expr (Fin 14) := .var 10
  let zeta : Expr (Fin 14) := .var 11
  let y : Expr (Fin 14) := .var 12
  let gamma : Expr (Fin 14) := .var 13
  let b := Expr.constant (p 0) * J
  let q := b + 1
  let C := q - F - alpha
  let X := w * q
  let Y := s * q ^ 3
  let E := X * Y
  let k := eta + zeta
  let ell := E * k * Y
  let c := k * Y + eta
  let a := E + Y
  let H := 4 * a + 3
  let delta := a ^ 2 + H
  let D := X + a * c + gamma * H
  let rank := (b * (q - F) + alpha) * (q ^ 2 - 1) +
    (Expr.constant (p 2) + q * Expr.constant (p 3)) * J
  let tau := E * n + k - rank
  let V := f ^ 2 * (c * T - rank) - c
  let P := tau ^ 2 - ell * (ell + k)
  let Q := D ^ 2 - delta * c ^ 2
  let W := (Expr.constant (p 1) + w) * C + (q - F) - z * b
  final P Q (delta * (f ^ 2 - 1) * (V ^ 2 - y ^ 2) + y ^ 2) W
    (f ^ 2 - delta * (i * c ^ 2) ^ 2)

/-- The 14/71/80 nonzero-sphere polynomial. -/
def expressionAt71 (p : Fin 4 → ℤ) : Expr (Fin 14) :=
  frontAt p fun P Q U W S => (P * Q) ^ 2 + (U * W - 1) ^ 2 + S ^ 2 - 2

/-- The 14/72/68 nonzero-sphere polynomial. -/
def expressionAt72 (p : Fin 4 → ℤ) : Expr (Fin 14) :=
  frontAt p fun P Q U W S => P ^ 2 + U ^ 2 + S ^ 2 + (Q * W - 1) ^ 2 - 3

section Eval
variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

theorem evalRing_expressionAt71 (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (expressionAt71 p).evalRing v = value71 (fun j => (p j : R)) v := by
  simp only [expressionAt71, frontAt, Expr.evalRing_add, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_pow, Expr.evalRing_var,
    Expr.evalRing_constant, Expr.evalRing_ofNat, Nat.cast_ofNat, Nat.cast_one,
    value71, auxiliary, Carrier65.strong, Carrier65.core]

theorem evalRing_expressionAt72 (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (expressionAt72 p).evalRing v = value72 (fun j => (p j : R)) v := by
  simp only [expressionAt72, frontAt, Expr.evalRing_add, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_pow, Expr.evalRing_var,
    Expr.evalRing_constant, Expr.evalRing_ofNat, Nat.cast_ofNat, Nat.cast_one,
    value72, auxiliary, Carrier65.strong, Carrier65.core]

end Eval

/-! ### Models of `𝗜𝚺₁` -/

section Model
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelArithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem modelFacts : Facts (DiffRing V) where
  discrete := model_discrete
  mod4 := ⟨mod4⟩
  near := fun A x y hA hy => near_square_ne_zero A x y hA hy
  consecutive := fun n x y hn => consecutive_ne_neg_one n x y hn

theorem sameZero71 (v : Fin 14 → V) :
    InternalZero (positiveShift (expressionAt71 CurrentWindowCarry2011.ports)) v ↔
      InternalZero ObjectCurrentEquation2011.naturalExpression v := by
  change InternalZero (positiveShift (expressionAt71 CurrentWindowCarry2011.ports)) v ↔
    InternalZero (positiveShift ObjectCurrentEquation2011.expression) v
  rw [internalZero_positiveShift, internalZero_positiveShift, internalZero_iff, internalZero_iff,
    evalRing_expressionAt71, ObjectCurrentEquation2011.expression,
    FreshModel106.evalRing_expressionAt65]
  exact zero_iff71 modelFacts _ _ FreshModel106.beta_pos (FreshModel106.shifted_pos v)

theorem sameZero72 (v : Fin 14 → V) :
    InternalZero (positiveShift (expressionAt72 CurrentWindowCarry2011.ports)) v ↔
      InternalZero ObjectCurrentEquation2011.naturalExpression v := by
  change InternalZero (positiveShift (expressionAt72 CurrentWindowCarry2011.ports)) v ↔
    InternalZero (positiveShift ObjectCurrentEquation2011.expression) v
  rw [internalZero_positiveShift, internalZero_positiveShift, internalZero_iff, internalZero_iff,
    evalRing_expressionAt72, ObjectCurrentEquation2011.expression,
    FreshModel106.evalRing_expressionAt65]
  exact zero_iff72 modelFacts _ _ FreshModel106.beta_pos (FreshModel106.shifted_pos v)

end Model

/-! ### Direct fresh-base iPRA transfer -/
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation
open HAExpressionAssembly FoundationHANoZero

theorem bridge71 : PolynomialBridge
    (positiveShift (expressionAt71 CurrentWindowCarry2011.ports)) := by
  intro V _ _
  have eqv : (classicalNoZero (positiveShift
      (expressionAt71 CurrentWindowCarry2011.ports))).Evalb (M := V) ![] ↔
      (classicalNoZero ObjectCurrentEquation2011.naturalExpression).Evalb (M := V) ![] := by
    rw [classicalNoZero_iff, classicalNoZero_iff]
    simpa only [InternalZero, ne_eq] using
      (forall_congr' fun v : Fin 14 → V => not_congr (sameZero71 v))
  exact eqv.trans (HACurrentEquation2011.polynomialBridge V)

theorem bridge72 : PolynomialBridge
    (positiveShift (expressionAt72 CurrentWindowCarry2011.ports)) := by
  intro V _ _
  have eqv : (classicalNoZero (positiveShift
      (expressionAt72 CurrentWindowCarry2011.ports))).Evalb (M := V) ![] ↔
      (classicalNoZero ObjectCurrentEquation2011.naturalExpression).Evalb (M := V) ![] := by
    rw [classicalNoZero_iff, classicalNoZero_iff]
    simpa only [InternalZero, ne_eq] using
      (forall_congr' fun v : Fin 14 → V => not_congr (sameZero72 v))
  exact eqv.trans (HACurrentEquation2011.polynomialBridge V)

theorem standard_equivalence71 : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift (expressionAt71 CurrentWindowCarry2011.ports)) 🡘
      ∼mappedNativeRefutation embedding :=
  (IPRAStandardTheory.provable_iff _).2 (IPRAExpressionNative.equivalence_of_bridge _ bridge71)

theorem standard_equivalence72 : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift (expressionAt72 CurrentWindowCarry2011.ports)) 🡘
      ∼mappedNativeRefutation embedding :=
  (IPRAStandardTheory.provable_iff _).2 (IPRAExpressionNative.equivalence_of_bridge _ bridge72)

#print axioms sameZero71
#print axioms sameZero72
#print axioms standard_equivalence71
#print axioms standard_equivalence72

end DiophantineConsistency.FreshCarrierSpheres
