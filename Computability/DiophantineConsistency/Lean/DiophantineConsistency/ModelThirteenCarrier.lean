import DiophantineConsistency.ModelThirteenRestoration
import DiophantineConsistency.ArithmeticThirteenSeed
import DiophantineConsistency.ArithmeticThirteenOuter
import DiophantineConsistency.ArithmeticPellFirstIndex
import DiophantineConsistency.HAExpressionNoZeroEquiv
/-! # iPRA endpoint for the thirteen-variable 69/174 carrier form

In every model of `𝗜𝚺₁`, the 13-variable form `ThirteenCarrier.value69` and the
maintained 14-variable Carrier65 polynomial have zeros together:

* restoration (`ModelThirteenRestoration`) maps a positive 69-zero to a
  positive Carrier65 zero;
* completion (`complete`) maps a Carrier65 zero to a 69-zero. The outer data
  come from the internal soundness lemmas (`maintained_first_indices`,
  `ArithmeticThirteenOuter`), the strong seed from the internal pigeonhole
  (`ArithmeticThirteenSeed.strong_index`) and the auxiliary pair from
  `auxiliary_seed_of`; the independent coordinate `m` is solved exactly.

This is the internal counterpart of `CurrentCarrierArithmetic2011.positive_zero_65_iff_69`,
so the maintained all-model bridge transfers to the 69 form, giving native,
standard and equality-only iPRA proofs of its no-zero sentence iff Foundation's
ZFC consistency predicate. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.ModelThirteenCarrier
open AdaptiveEquationSyntax2011 ModelDifferenceRing DiscreteOrderedRingFacts ModelCarrierSpheres

/-! ### Literal thirteen-coordinate syntax -/

/-- The common thirteen-coordinate front, followed by `final P Q S f δ gap y t`. -/
def front13 (p : Fin 4 → ℤ)
    (final : Expr (Fin 13) → Expr (Fin 13) → Expr (Fin 13) → Expr (Fin 13) →
      Expr (Fin 13) → Expr (Fin 13) → Expr (Fin 13) → Expr (Fin 13) → Expr (Fin 13)) :
    Expr (Fin 13) :=
  let J : Expr (Fin 13) := .var 0
  let F : Expr (Fin 13) := .var 1
  let alpha : Expr (Fin 13) := .var 2
  let f : Expr (Fin 13) := .var 3
  let i : Expr (Fin 13) := .var 4
  let T : Expr (Fin 13) := .var 5
  let s : Expr (Fin 13) := .var 6
  let w : Expr (Fin 13) := .var 7
  let n : Expr (Fin 13) := .var 8
  let eta : Expr (Fin 13) := .var 9
  let zeta : Expr (Fin 13) := .var 10
  let m : Expr (Fin 13) := .var 11
  let gamma : Expr (Fin 13) := .var 12
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
  let G := (Expr.constant (p 1) + w) * C - F
  let y := 1 + 4 * (b * (m - V ^ 2 * G) - G)
  final (tau ^ 2 - ell * (ell + k)) (D ^ 2 - delta * c ^ 2) (delta * (b * i * c ^ 2))
    f delta (V ^ 2 - y ^ 2) y (b * i * c ^ 2)

/-- The 13/69/174 polynomial. -/
def expressionAt69 (p : Fin 4 → ℤ) : Expr (Fin 13) :=
  front13 p fun P Q S f delta gap y _ =>
    P * Q * (S ^ 2 * gap + y ^ 2) * (delta * f ^ 2 - S ^ 2) - delta

theorem evalRing_expressionAt69 {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (expressionAt69 p).evalRing v = ThirteenCarrier.value69 (fun j => (p j : R)) v := by
  simp only [expressionAt69, front13, Expr.evalRing_add, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_pow, Expr.evalRing_var,
    Expr.evalRing_constant, Expr.evalRing_ofNat, Nat.cast_ofNat, Nat.cast_one,
    ThirteenCarrier.value69, ThirteenCarrier.core]

/-! ### The completion map (generic ring definitions, as in `ThirteenCarrierComplete`) -/

section Replace
variable {R : Type*} [CommRing R]

def transport (p : Fin 4 → R) (v : Fin 14 → R) : R :=
  (p 1 + v 8) * (Carrier65.core p v).C - v 1

/-- Preserve J,F,alpha,s,w,n,eta,zeta,gamma and replace only f,i,T,m. -/
def replace (v : Fin 14 → R) (f i T m : R) (j : Fin 13) : R :=
  match j.val with
  | 0 => v 0
  | 1 => v 1
  | 2 => v 2
  | 3 => f
  | 4 => i
  | 5 => T
  | 6 => v 7
  | 7 => v 8
  | 8 => v 9
  | 9 => v 10
  | 10 => v 11
  | 11 => m
  | _ => v 13

theorem core_replace (p : Fin 4 → R) (v : Fin 14 → R) (f i T m : R) :
    let b := Carrier65.core p v
    let V := f ^ 2 * (b.c * T - b.rank) - b.c
    let y := 1 + 4 * (p 0 * v 0 * (m - V ^ 2 * transport p v) - transport p v)
    ThirteenCarrier.core p (replace v f i T m) =
      ⟨b.a, b.delta, p 0 * v 0 * i * b.c ^ 2, f, V ^ 2 - y ^ 2, y, b.P, b.Q⟩ := rfl

theorem replace_zero69 (p : Fin 4 → R) (v : Fin 14 → R) (f i T m : R)
    (hP : (Carrier65.core p v).P = 1) (hQ : (Carrier65.core p v).Q = 1)
    (hs : f ^ 2 - (Carrier65.core p v).delta *
      (p 0 * v 0 * i * (Carrier65.core p v).c ^ 2) ^ 2 = 1)
    (hu : let b := Carrier65.core p v
      let S := b.delta * (p 0 * v 0 * i * b.c ^ 2)
      let V := f ^ 2 * (b.c * T - b.rank) - b.c
      let y := 1 + 4 * (p 0 * v 0 * (m - V ^ 2 * transport p v) - transport p v)
      S ^ 2 * (V ^ 2 - y ^ 2) + y ^ 2 = 1) :
    ThirteenCarrier.value69 p (replace v f i T m) = 0 := by
  have hz : (Carrier65.core p v).delta * f ^ 2 -
      ((Carrier65.core p v).delta * (p 0 * v 0 * i * (Carrier65.core p v).c ^ 2)) ^ 2 =
      (Carrier65.core p v).delta := by
    linear_combination (Carrier65.core p v).delta * hs
  dsimp only [ThirteenCarrier.value69]
  rw [core_replace]
  dsimp only
  rw [hP, hQ, hu, hz]
  ring

theorem replace_pos [PartialOrder R] (v : Fin 14 → R) (hv : ∀ j, 0 < v j)
    (f i T m : R) (hf : 0 < f) (hi : 0 < i) (hT : 0 < T) (hm : 0 < m) :
    ∀ j, 0 < replace v f i T m j := by
  intro j
  fin_cases j
  · exact hv 0
  · exact hv 1
  · exact hv 2
  · exact hf
  · exact hi
  · exact hT
  · exact hv 7
  · exact hv 8
  · exact hv 9
  · exact hv 10
  · exact hv 11
  · exact hm
  · exact hv 13

end Replace

/-! ### Completion in every model of `𝗜𝚺₁` -/

section Model
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelArithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ArithmeticPellRecurrence ArithmeticCarrierRadix2011 ArithmeticCurrentSentence2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The ports in the ring of differences. -/
abbrev ringPorts : Fin 4 → DiffRing V := fun j => ((CurrentWindowCarry2011.ports j : ℤ) : DiffRing V)

theorem port0 : (ringPorts (V := V)) 0 = ι (CurrentMasks2011.beta : V) := by
  show ((CurrentWindowCarry2011.ports 0 : ℤ) : DiffRing V) = _
  rw [show CurrentWindowCarry2011.ports 0 = (CurrentMasks2011.beta : ℤ) from rfl,
    Int.cast_natCast, map_natCast]
theorem port1 : (ringPorts (V := V)) 1 = ι (CurrentKernel2011.K : V) := by
  show ((CurrentWindowCarry2011.ports 1 : ℤ) : DiffRing V) = _
  rw [show CurrentWindowCarry2011.ports 1 = (CurrentKernel2011.K : ℤ) from rfl,
    Int.cast_natCast, map_natCast]
theorem port2 : (ringPorts (V := V)) 2 = ι (CurrentMasks2011.lowPort : V) := by
  show ((CurrentWindowCarry2011.ports 2 : ℤ) : DiffRing V) = _
  rw [show CurrentWindowCarry2011.ports 2 = (CurrentMasks2011.lowPort : ℤ) from rfl,
    Int.cast_natCast, map_natCast]
theorem port3 : (ringPorts (V := V)) 3 =
    ι (((CurrentMasks2011.highPort + CurrentMasks2011.beta : ℕ) : V)) := by
  show ((CurrentWindowCarry2011.ports 3 : ℤ) : DiffRing V) = _
  rw [show CurrentWindowCarry2011.ports 3 =
    (CurrentMasks2011.highPort : ℤ) + (CurrentMasks2011.beta : ℤ) from rfl,
    Int.cast_add, Int.cast_natCast, Int.cast_natCast, map_natCast, Nat.cast_add]

theorem positive_of_ι {x : DiffRing V} (h : 0 < x) : ∃ a : V, 0 < a ∧ x = ι a := by
  obtain ⟨a, rfl⟩ := nonneg_iff.mp h.le
  exact ⟨a, ι_lt_ι.mp (by rwa [map_zero]), rfl⟩

/-- A positive ring point is the shift of a model point. -/
theorem shifted_of_positive {n : ℕ} (x : Fin n → DiffRing V) (hx : ∀ j, 0 < x j) :
    ∃ u : Fin n → V, ∀ j, x j = ι (u j + 1) := by
  choose a ha hxa using fun j => positive_of_ι (hx j)
  refine ⟨fun j => a j - 1, fun j => ?_⟩
  rw [tsub_add_cancel_of_le (pos_iff_one_le.mp (ha j))]
  exact hxa j

/-- **Completion**: every model zero of the maintained equation gives a model
zero of the 13/69/174 form. -/
theorem complete (v : Fin 14 → V)
    (hz : InternalZero ObjectCurrentEquation2011.naturalExpression v) :
    ∃ u : Fin 13 → V, InternalZero (positiveShift (expressionAt69 CurrentWindowCarry2011.ports)) u := by
  set w : Fin 14 → V := fun j => v j + 1 with hwdef
  have hw : ∀ j, 0 < w j := fun j => lt_of_lt_of_le _root_.zero_lt_one le_add_self
  have hzw : ObjectCurrentEquation2011.expression.splitNatural.1.evalSemiring w =
      ObjectCurrentEquation2011.expression.splitNatural.2.evalSemiring w :=
    (ObjectCurrentEquation2011.internalZero_positiveShift ObjectCurrentEquation2011.expression v).mp hz
  have hpz : PositiveZero w := ⟨hw, hzw⟩
  -- ring-level zero and norms
  set x : Fin 14 → DiffRing V := fun j => ι (w j) with hxdef
  have hx : ∀ j, 0 < x j := fun j => ι_pos (hw j)
  have hz65 : Carrier65.value ringPorts x = 0 := by
    have := (internalZero_iff ObjectCurrentEquation2011.expression w).mp hzw
    rwa [ObjectCurrentEquation2011.expression, ModelCarrierCurrent.evalRing_expressionAt65] at this
  have hb : (0 : DiffRing V) < ringPorts 0 := ModelCarrierCurrent.beta_pos
  obtain ⟨hP, hQ, _, _, hW⟩ := (value65_zero_iff_norms modelFacts ringPorts x hb hx).mp hz65
  -- internal outer data
  obtain ⟨hβ, hMC, hMF⟩ := ArithmeticCarrierSoundness2011.current_bounds (V := V)
  have hβ0 : (0 : V) < (CurrentMasks2011.beta : V) := lt_of_lt_of_le (by norm_num) hβ
  obtain ⟨ht, hfirst, hmain, hstrong, haux⟩ := ArithmeticCarrierSoundness2011.current_natural_equations v hz
  obtain ⟨_, _, _, _, _, _, _, _, hcR, _⟩ :=
    ArithmeticPellFirstIndex.maintained_first_indices
      (CurrentMasks2011.beta:V) (CurrentKernel2011.K:V) (CurrentMasks2011.lowPort:V)
      ((CurrentMasks2011.highPort+CurrentMasks2011.beta:ℕ):V) (w 0) (w 1) (w 2) (w 3) (w 4) (w 5)
      (w 6) (w 7) (w 8) (w 9) (w 10) (w 11) (w 12) (w 13) hβ0 hMC hMF (hw 0) (hw 1) (hw 2) (hw 3)
      (hw 4) (hw 5) (hw 6) (hw 7) (hw 8) (hw 9) (hw 10) (hw 11) (hw 12) (hw 13)
      ht hfirst hmain hstrong haux
  clear ht hfirst hmain hstrong haux
  have hR4 := ArithmeticThirteenOuter.rank_mod_four w hpz
  have hqw := ArithmeticThirteenOuter.base_lt_shift w hpz
  obtain ⟨hαq, hFq⟩ := ArithmeticThirteenOuter.window_positive w hpz
  change (w 10 + w 11) * Y w + w 10 = ycoord (rank w) (X w * Y w + Y w) at hcR
  have hq1 : 1 ≤ q w := by show 1 ≤ (CurrentMasks2011.beta : V) * w 0 + 1; exact le_add_self
  have hq2 : 1 ≤ q w ^ 2 := one_le_pow₀ hq1
  -- ring-level core quantities are images of the model quantities
  have eq_q : (Carrier65.core ringPorts x).q = ι (q w) := by
    change ringPorts 0 * x 0 + 1 = _; rw [port0]
    simp only [hxdef, q, map_add, map_mul, map_one]
  have eq_Y : (Carrier65.core ringPorts x).Y = ι (Y w) := by
    change x 7 * (Carrier65.core ringPorts x).q ^ 3 = _; rw [eq_q]
    simp only [hxdef, Y, map_mul, map_pow]
  have eq_E : (Carrier65.core ringPorts x).E = ι (X w * Y w) := by
    change (x 8 * (Carrier65.core ringPorts x).q) * (Carrier65.core ringPorts x).Y = _
    rw [eq_q, eq_Y]; simp only [hxdef, X, map_mul]
  have eq_a : (Carrier65.core ringPorts x).a = ι (X w * Y w + Y w) := by
    change (Carrier65.core ringPorts x).E + (Carrier65.core ringPorts x).Y = _
    rw [eq_E, eq_Y, map_add]
  have eq_c : (Carrier65.core ringPorts x).c = ι ((w 10 + w 11) * Y w + w 10) := by
    change (x 10 + x 11) * (Carrier65.core ringPorts x).Y + x 10 = _
    rw [eq_Y]; simp only [hxdef, map_add, map_mul]
  have eq_delta : (Carrier65.core ringPorts x).delta = ι (delta (X w * Y w + Y w)) := by
    change (Carrier65.core ringPorts x).a ^ 2 + (4 * (Carrier65.core ringPorts x).a + 3) = _
    rw [eq_a]; unfold delta; simp only [map_mul, map_add, map_ofNat, map_one]; ring
  have eq_rank : (Carrier65.core ringPorts x).rank = ι (rank w) := by
    change (ringPorts 0 * x 0 * ((Carrier65.core ringPorts x).q - x 1) + x 2) *
      ((Carrier65.core ringPorts x).q ^ 2 - 1) +
      (ringPorts 2 + (Carrier65.core ringPorts x).q * ringPorts 3) * x 0 = _
    rw [eq_q, port0, port2, port3]
    show _ = ι (((q w - 1) * (q w - w 1) + w 2) * (q w ^ 2 - 1) +
      ((CurrentMasks2011.lowPort : V) + q w * ((CurrentMasks2011.highPort + CurrentMasks2011.beta : ℕ) : V)) * w 0)
    simp only [map_add, map_mul, map_pow, ArithmeticThirteenOuter.ι_tsub hq1,
      ArithmeticThirteenOuter.ι_tsub hFq.le, ArithmeticThirteenOuter.ι_tsub hq2, map_one]
    have hqx : ι (q w) = ι (CurrentMasks2011.beta : V) * x 0 + 1 := by
      simp only [hxdef, q, map_add, map_mul, map_one]
    rw [hqx]
    simp only [hxdef]
    ring
  set aV := X w * Y w + Y w with haV
  set cV := (w 10 + w 11) * Y w + w 10 with hcV
  set RV := rank w with hRV
  have hc : cV = ycoord RV aV := hcR
  -- transport: G = b (z - 1) > 0 with b ∣ G
  have hbJ : 0 < (CurrentMasks2011.beta : V) * w 0 := mul_pos hβ0 (hw 0)
  have hG : 0 < transport ringPorts x := by
    have hC : 0 < (Carrier65.core ringPorts x).C := by
      change 0 < (Carrier65.core ringPorts x).q - x 1 - x 2
      rw [eq_q]
      have h1 := ι_lt_ι.mpr hαq
      rw [ArithmeticThirteenOuter.ι_tsub hFq.le] at h1
      linarith only [h1]
    have hC1 : 1 ≤ (Carrier65.core ringPorts x).C := model_discrete _ hC
    have hK : 0 ≤ ringPorts (V := V) 1 := by rw [port1]; exact ι_nonneg _
    have hwq : (Carrier65.core ringPorts x).q < x 8 := by rw [eq_q]; exact ι_lt_ι.mpr hqw
    have hFq' : x 1 < (Carrier65.core ringPorts x).q := by rw [eq_q]; exact ι_lt_ι.mpr hFq
    have hx8 : 0 ≤ x 8 := (hx 8).le
    have hmul : (ringPorts 1 + x 8) * 1 ≤ (ringPorts 1 + x 8) * (Carrier65.core ringPorts x).C :=
      mul_le_mul_of_nonneg_left hC1 (by linarith only [hK, hx8])
    unfold transport
    linarith only [hmul, hK, hwq, hFq']
  have hGb : transport ringPorts x = (ringPorts 0 * x 0) * (x 3 - 1) := by
    change (ringPorts 1 + x 8) * (Carrier65.core ringPorts x).C +
      ((Carrier65.core ringPorts x).q - x 1) - x 3 * (ringPorts 0 * x 0) = 1 at hW
    have hqshape : (Carrier65.core ringPorts x).q = ringPorts 0 * x 0 + 1 := rfl
    unfold transport
    rw [hqshape] at hW
    linear_combination hW
  -- fresh strong and auxiliary seeds
  have hcpos : 0 < cV := by
    have := ι_lt_ι.mp (show ι 0 < ι cV by rw [map_zero, ← eq_c]; exact c_pos modelFacts ringPorts x hb hx)
    exact this
  obtain ⟨t, j, _, hj, hyt⟩ := ArithmeticThirteenSeed.strong_index aV ((CurrentMasks2011.beta : V) * w 0) cV hbJ hcpos
  have hR3 : RV % 4 = 3 := hR4
  obtain ⟨T, u, y, hf, hT, hu, hy, hn, hyI, _, hlit, _, haux', hres⟩ :=
    ArithmeticThirteenSeed.auxiliary_seed_of aV RV t ((CurrentMasks2011.beta : V) * w 0 * j) hR3
      (mul_pos hbJ hj) (by rw [hyt, ← hc])
  rw [← hc] at hn hlit haux' hres
  -- ring-level fresh coordinates
  set fR := ι (xcoord t aV)
  set iR := ι j
  set TR := ι T
  set IV := delta aV * ((CurrentMasks2011.beta : V) * w 0 * j) * cV * cV with hIV
  have hstrongR : fR ^ 2 - (Carrier65.core ringPorts x).delta *
      (ringPorts 0 * x 0 * iR * (Carrier65.core ringPorts x).c ^ 2) ^ 2 = 1 := by
    rw [eq_delta, eq_c, port0]
    have e := congrArg (ι : V →+* DiffRing V) hn
    simp only [map_add, map_mul, map_one] at e
    simp only [hxdef] at e ⊢
    linear_combination e
  have hVdef : ι u = fR ^ 2 * ((Carrier65.core ringPorts x).c * TR - (Carrier65.core ringPorts x).rank) -
      (Carrier65.core ringPorts x).c := by
    rw [eq_c, eq_rank]
    have e := congrArg (ι : V →+* DiffRing V) hlit
    simp only [map_add, map_mul] at e
    linear_combination -e
  -- the independent m
  obtain ⟨e4, he4⟩ : (4 * ((CurrentMasks2011.beta : V) * w 0)) ∣ y + 1 := by
    have h1 : 4 * IV * IV ∣ y + 1 := mod_eq_zero_iff_dvd.mp hres
    refine dvd_trans ⟨delta aV * j * cV * cV * IV, by ring⟩ h1
  set yR : DiffRing V := -ι y
  have hSR : (Carrier65.core ringPorts x).delta * (ringPorts 0 * x 0 * iR * (Carrier65.core ringPorts x).c ^ 2) = ι IV := by
    rw [eq_delta, eq_c, port0]; simp only [hxdef, map_mul, IV]; ring
  have hauxR : (ι IV) ^ 2 * ((ι u) ^ 2 - yR ^ 2) + yR ^ 2 = 1 := by
    have e := congrArg (ι : V →+* DiffRing V) haux'
    simp only [map_add, map_mul, map_one] at e
    simp only [yR]
    linear_combination e
  set bR := ringPorts 0 * x 0
  have hbR : bR = ι ((CurrentMasks2011.beta : V) * w 0) := by simp only [bR, port0, hxdef, map_mul]
  have hS2 : 2 ≤ ι IV := by
    rw [← hSR]
    have ha0 : 0 ≤ (Carrier65.core ringPorts x).a := by rw [eq_a]; exact ι_nonneg _
    have hδ3 : 3 ≤ (Carrier65.core ringPorts x).delta := by
      change 3 ≤ (Carrier65.core ringPorts x).a ^ 2 + (4 * (Carrier65.core ringPorts x).a + 3)
      linarith only [sq_nonneg (Carrier65.core ringPorts x).a, ha0]
    have hb1 : 1 ≤ bR := model_discrete _ (by rw [hbR]; exact ι_pos hbJ)
    have hi1 : 1 ≤ iR := model_discrete _ (ι_pos hj)
    have hc1 : 1 ≤ (Carrier65.core ringPorts x).c := model_discrete _ (c_pos modelFacts ringPorts x hb hx)
    have hc2 : 1 ≤ (Carrier65.core ringPorts x).c ^ 2 := one_le_pow₀ hc1
    have hbi : 1 ≤ bR * iR := one_le_mul_of_one_le_of_one_le hb1 hi1
    have hbic : 1 ≤ bR * iR * (Carrier65.core ringPorts x).c ^ 2 :=
      one_le_mul_of_one_le_of_one_le hbi hc2
    have := le_mul_of_one_le_right (by linarith only [hδ3] : (0 : DiffRing V) ≤ _) hbic
    linarith only [this, hδ3]
  obtain ⟨_, hsmall⟩ := ModelThirteenRestoration.auxiliary_estimates modelFacts hS2
    (show (ι IV) ^ 2 * (ι u) ^ 2 - ((ι IV) ^ 2 - 1) * yR ^ 2 = 1 by linear_combination hauxR)
  set gR := x 3 - 1
  have hgR : transport ringPorts x = bR * gR := hGb
  set mR : DiffRing V := -ι e4 + (1 + bR * (ι u) ^ 2) * gR
  have hym : yR = 1 + 4 * (bR * (mR - (ι u) ^ 2 * transport ringPorts x) - transport ringPorts x) := by
    have e := congrArg (ι : V →+* DiffRing V) he4
    simp only [map_add, map_mul, map_one, map_ofNat] at e
    simp only [yR, mR, hgR]
    rw [hbR]
    simp only [map_mul]
    linear_combination -e
  have hmpos : 0 < mR := by
    have hbpos : 0 < bR := by rw [hbR]; exact ι_pos hbJ
    have hsm : -2 * ι u < yR := by
      have := neg_abs_le yR
      have hu0 : |ι u| = ι u := abs_of_nonneg (ι_nonneg u)
      linarith only [this, hu0, hsmall]
    exact ModelThirteenRestoration.affine_carrier_pos modelFacts hbpos hG hsm hym
  -- the thirteen-coordinate ring zero
  have hzero : ThirteenCarrier.value69 ringPorts (replace x fR iR TR mR) = 0 := by
    apply replace_zero69 ringPorts x fR iR TR mR hP hQ hstrongR
    dsimp only
    rw [hSR, ← hVdef]
    have : 1 + 4 * (ringPorts 0 * x 0 * (mR - (ι u) ^ 2 * transport ringPorts x) - transport ringPorts x) = yR :=
      hym.symm
    rw [this]
    exact hauxR
  have hpos : ∀ k, 0 < replace x fR iR TR mR k :=
    replace_pos x hx fR iR TR mR (ι_pos hf) (ι_pos hj) (ι_pos hT) hmpos
  obtain ⟨u13, hu13⟩ := shifted_of_positive _ hpos
  refine ⟨u13, ?_⟩
  rw [internalZero_positiveShift, internalZero_iff, evalRing_expressionAt69]
  have hfun : (fun k => ι (u13 k + 1)) = replace x fR iR TR mR := funext fun k => (hu13 k).symm
  rw [hfun]
  exact hzero

end Model


/-! ### The 69 form has exactly the maintained zeros in every model, and its iPRA endpoints -/

section Bridge
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelArithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic

theorem sameNoZero69 : HAExpressionNoZeroEquiv.SameNoZero
    (positiveShift (expressionAt69 CurrentWindowCarry2011.ports))
    ObjectCurrentEquation2011.naturalExpression := by
  intro V _ _
  constructor
  · intro h v hz
    obtain ⟨u, hu⟩ := complete v hz
    exact h u hu
  · intro h u hz
    have hz' := (internalZero_iff _ _).mp ((internalZero_positiveShift _ u).mp hz)
    rw [evalRing_expressionAt69] at hz'
    obtain ⟨w14, hpos, hval⟩ := ModelThirteenRestoration.restores_positive_zero69 modelFacts
      ringPorts (fun j => ι (u j + 1)) ModelCarrierCurrent.beta_pos
      (fun j => ι_pos (lt_of_lt_of_le _root_.zero_lt_one le_add_self))
      ModelThirteenRestoration.modelSignedResidue hz'
    obtain ⟨v, hv⟩ := shifted_of_positive w14 hpos
    apply h v
    change InternalZero (positiveShift ObjectCurrentEquation2011.expression) v
    rw [internalZero_positiveShift, internalZero_iff, ObjectCurrentEquation2011.expression,
      ModelCarrierCurrent.evalRing_expressionAt65]
    have hfun : (fun k => ι (v k + 1)) = w14 := funext fun k => (hv k).symm
    rw [hfun]
    exact hval

end Bridge

open LO LO.FirstOrder LO.Entailment
open scoped LO.FirstOrder
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation

theorem bridge69 : HAExpressionAssembly.PolynomialBridge
    (positiveShift (expressionAt69 CurrentWindowCarry2011.ports)) :=
  HAExpressionNoZeroEquiv.bridge _ _ sameNoZero69 ModelCarrierCurrent.currentBridge

/-- **Native iPRA: the 13/69/174 form has no positive zero iff ZFC is consistent.** -/
theorem native_equivalence69 : nativeTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift (expressionAt69 CurrentWindowCarry2011.ports)) 🡘
      ∼mappedNativeRefutation embedding :=
  IPRAExpressionNative.equivalence_of_bridge _ bridge69

theorem standard_equivalence69 : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift (expressionAt69 CurrentWindowCarry2011.ports)) 🡘
      ∼mappedNativeRefutation embedding :=
  (IPRAStandardTheory.provable_iff _).2 native_equivalence69

theorem reference_equivalence69 : IPRAEqualityOnlyReference.referenceTheory ⊢
    IPRAOrderErasure.erase (IPRAExpressionNative.nativeNoZero
      (positiveShift (expressionAt69 CurrentWindowCarry2011.ports))) 🡘
      ∼IPRAOrderErasure.erase (mappedNativeRefutation embedding) :=
  IPRAReferenceInductionConversion.nativeToReference native_equivalence69

end DiophantineConsistency.ModelThirteenCarrier
