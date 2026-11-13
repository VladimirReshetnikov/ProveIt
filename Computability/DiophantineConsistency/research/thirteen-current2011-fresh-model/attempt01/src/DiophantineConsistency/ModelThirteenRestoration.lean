import FrontierBridge
import DiophantineConsistency.ArithmeticOddOrdinateResidue
import DiophantineConsistency.ThirteenCarrier
/-! # Restoring a fourteen-coordinate Carrier65 zero from a thirteen-coordinate one

`ThirteenCarrierSoundness` proves over `ℤ` that every positive zero of the
13-variable 69/70/71 forms restores to a positive Carrier65 zero. The argument
uses positivity, the units `±1`, the norm exclusions, one congruence modulo
four and the signed odd-index Pell residue `four_square_dvd_sub_one`. Here it is
replayed over any discretely ordered ring with those facts, and instantiated in
the ring of differences of every model of `𝗜𝚺₁`, where the residue is the
internal `ArithmeticOddOrdinateResidue.four_square_dvd_sub_one`. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace DiophantineConsistency.ModelThirteenRestoration
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix
open FreshCarrierSpheres DiscreteOrderedRingFacts


/-! ### The restoration map (generic ring definitions, as in `ThirteenCarrierSoundness`)

Copied here because `ThirteenCarrierSoundness` imports Mathlib's Pell theory,
whose `Matrix` definitions clash with Foundation's `Vorspiel.Matrix`. -/

section Defs
variable {R : Type*} [CommRing R]

def b (p : Fin 4 → R) (v : Fin 13 → R) : R := p 0 * v 0

/-- Insert z and y, and multiply the parent's i by b exactly once. -/
def parent (p : Fin 4 → R) (v : Fin 13 → R) (z y : R) (j : Fin 14) : R :=
  match j.val with
  | 0 => v 0
  | 1 => v 1
  | 2 => v 2
  | 3 => z
  | 4 => v 3
  | 5 => b p v * v 4
  | 6 => v 5
  | 7 => v 6
  | 8 => v 7
  | 9 => v 8
  | 10 => v 9
  | 11 => v 10
  | 12 => y
  | _ => v 12

def data (p : Fin 4 → R) (v : Fin 13 → R) : Carrier65.Core R :=
  Carrier65.core p (parent p v 1 1)

def G (p : Fin 4 → R) (v : Fin 13 → R) : R :=
  (p 1 + v 7) * (data p v).C - v 1

def signedY (p : Fin 4 → R) (v : Fin 13 → R) : R := (ThirteenCarrier.core p v).y

def auxiliary (p : Fin 4 → R) (v : Fin 13 → R) : R :=
  (data p v).S ^ 2 * ((data p v).V ^ 2 - signedY p v ^ 2) + signedY p v ^ 2

theorem signedY_shape (p : Fin 4 → R) (v : Fin 13 → R) :
    signedY p v = 1 + 4 * (b p v * (v 11 - (data p v).V ^ 2 * G p v) - G p v) := rfl

theorem scale_shape (p : Fin 4 → R) (v : Fin 13 → R) :
    (ThirteenCarrier.core p v).delta * (ThirteenCarrier.core p v).t = (data p v).S := by
  change (data p v).delta * (b p v * v 4 * (data p v).c ^ 2) =
    (b p v * v 4) * (data p v).delta * (data p v).c ^ 2
  ring

theorem core_parent (p : Fin 4 → R) (v : Fin 13 → R) (z y : R) :
    Carrier65.core p (parent p v z y) =
      { data p v with
        U := (data p v).S ^ 2 * ((data p v).V ^ 2 - y ^ 2) + y ^ 2
        W := G p v + (data p v).q - z * b p v
        y := y } := by
  dsimp only [data, Carrier65.core]
  congr 1; first | rfl | (dsimp [G, data, parent, Carrier65.core, b]; ring_nf; abel)

theorem value69_scaled (p : Fin 4 → R) (v : Fin 13 → R) :
    ThirteenCarrier.value69 p v = (data p v).delta *
      ((data p v).P * (data p v).Q * auxiliary p v * Carrier65.strong (data p v) - 1) := by
  dsimp only [ThirteenCarrier.value69]
  rw [scale_shape]
  change (data p v).P * (data p v).Q * auxiliary p v *
    ((data p v).delta * (data p v).f ^ 2 - (data p v).S ^ 2) - (data p v).delta = _
  change (data p v).P * (data p v).Q * auxiliary p v *
    (data p v).Z - (data p v).delta = _
  rw [show (data p v).Z = (data p v).delta * Carrier65.strong (data p v) from
    Carrier65.strong_scale p (parent p v 1 1)]
  ring

end Defs

section Generic
variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- The signed residue, as a hypothesis on the ring. -/
def SignedResidue (R : Type*) [CommRing R] [LinearOrder R] : Prop :=
  ∀ S W y : R, 2 ≤ S → S ^ 2 * W ^ 2 - (S ^ 2 - 1) * y ^ 2 = 1 → (∃ k, y - 1 = 4 * k) →
    ∃ u, y - 1 = 4 * S ^ 2 * u

variable (F : Facts R) (p : Fin 4 → R) (v : Fin 13 → R) (hb : 0 < p 0) (hv : ∀ j, 0 < v j)
include F hb hv

theorem parent_pos {z y : R} (hz : 0 < z) (hy : 0 < y) : ∀ j, 0 < parent p v z y j := by
  have hi : 0 < b p v * v 4 := mul_pos (mul_pos hb (hv 0)) (hv 4)
  intro j
  fin_cases j <;> first
    | exact hz | exact hy | exact hi
    | exact hv 0 | exact hv 1 | exact hv 2 | exact hv 3 | exact hv 5 | exact hv 6
    | exact hv 7 | exact hv 8 | exact hv 9 | exact hv 10 | exact hv 12

theorem parent_pos1 : ∀ j, 0 < parent p v 1 1 j := parent_pos F p v hb hv one_pos one_pos

theorem norms_of_zero (hz : ThirteenCarrier.value69 p v = 0) :
    (data p v).P = 1 ∧ (data p v).Q = 1 ∧ auxiliary p v = 1 ∧
      Carrier65.strong (data p v) = 1 := by
  have hp := parent_pos1 F p v hb hv
  have hd := ModelCarrierScaled.delta_pos F.discrete p (parent p v 1 1) hb hp
  obtain ⟨hP, hQ, hs⟩ := negative_unit_exclusions F p (parent p v 1 1) hb hp
  have hu : auxiliary p v ≠ -1 := square_aux_ne_neg_one F _ _ _
  rw [value69_scaled, mul_eq_zero] at hz
  have hprod : (data p v).P * (data p v).Q * auxiliary p v *
      Carrier65.strong (data p v) = 1 := sub_eq_zero.mp (hz.resolve_left hd.ne')
  set P := (data p v).P; set Q := (data p v).Q; set U := auxiliary p v
  set S := Carrier65.strong (data p v)
  have hS1 : S = 1 := unit_eq_one F.discrete (show S * (P*Q*U) = 1 by linear_combination hprod) hs
  have hP1 : P = 1 := unit_eq_one F.discrete (show P * (Q*U*S) = 1 by linear_combination hprod) hP
  have hQ1 : Q = 1 := unit_eq_one F.discrete (show Q * (P*U*S) = 1 by linear_combination hprod) hQ
  refine ⟨hP1, hQ1, ?_, hS1⟩
  rw [hP1, hQ1, hS1] at hprod; linear_combination hprod

theorem scale_ge_two : 2 ≤ (data p v).S := by
  have hp := parent_pos1 F p v hb hv
  obtain ⟨_, _, hY, _, _⟩ := scales_pos F p (parent p v 1 1) hb hp
  have hd := ModelCarrierScaled.delta_pos F.discrete p (parent p v 1 1) hb hp
  have hd1 : 1 ≤ (data p v).delta := F.discrete _ hd
  have hi : 0 < (data p v).i := mul_pos (mul_pos hb (hv 0)) (hv 4)
  have hi1 : 1 ≤ (data p v).i := F.discrete _ hi
  have h9 : 1 ≤ v 9 := F.discrete _ (hv 9)
  have h10 : 1 ≤ v 10 := F.discrete _ (hv 10)
  have hY1 : 1 ≤ (data p v).Y := F.discrete _ hY
  have hk : 2 ≤ (data p v).k := by change 2 ≤ v 9 + v 10; linarith
  have hc : 2 ≤ (data p v).c := by
    change 2 ≤ (data p v).k * (data p v).Y + v 9
    nlinarith
  have hid : 1 ≤ (data p v).i * (data p v).delta := by nlinarith
  change 2 ≤ ((data p v).i * (data p v).delta) * (data p v).c ^ 2
  have hc2 : 4 ≤ (data p v).c ^ 2 := by nlinarith
  nlinarith

omit F hb hv in
theorem auxiliary_norm (hu : auxiliary p v = 1) :
    (data p v).S ^ 2 * (data p v).V ^ 2 -
      ((data p v).S ^ 2 - 1) * signedY p v ^ 2 = 1 := by
  unfold auxiliary at hu
  linear_combination hu

omit p v hb hv in
theorem auxiliary_estimates {S W y : R} (hS : 2 ≤ S)
    (hn : S ^ 2 * W ^ 2 - (S ^ 2 - 1) * y ^ 2 = 1) :
    y ≠ 0 ∧ |y| < 2 * |W| := by
  have hS2 : 4 ≤ S ^ 2 := by nlinarith
  have hW : W ≠ 0 := by
    intro hW
    rw [hW] at hn
    have hm := mul_nonneg (by linarith : (0:R) ≤ S ^ 2 - 1) (sq_nonneg y)
    nlinarith
  have hW2 : 1 ≤ W ^ 2 := F.discrete _ (pow_pos (abs_pos.mpr hW) 2 |>.trans_eq (sq_abs W))
  have hy : y ≠ 0 := by
    intro hy
    rw [hy] at hn
    have hm := mul_le_mul_of_nonneg_right hS2 (sq_nonneg W)
    nlinarith
  refine ⟨hy, ?_⟩
  have hsq : y ^ 2 < 4 * W ^ 2 := by
    by_contra h
    push_neg at h
    have h1 := mul_nonneg (by linarith : (0:R) ≤ S ^ 2 - 1)
      (by linarith : (0:R) ≤ y ^ 2 - 4 * W ^ 2)
    have h2 := mul_nonneg (by linarith : (0:R) ≤ 3 * S ^ 2 - 4) (sq_nonneg W)
    nlinarith only [hn, h1, h2]
  by_contra h
  push_neg at h
  have h1 := mul_nonneg (by linarith : (0:R) ≤ |y| - 2 * |W|)
    (show (0:R) ≤ |y| + 2 * |W| by positivity)
  nlinarith [sq_abs y, sq_abs W]

omit p v hb hv in
theorem affine_carrier_pos {b G W y m : R} (hb : 0 < b) (hG : 0 < G)
    (hsmall : -2 * W < y) (hy : y = 1 + 4 * (b * (m - W ^ 2 * G) - G)) : 0 < m := by
  by_contra hm
  push_neg at hm
  have hb1 : 1 ≤ b := F.discrete _ hb
  have hG1 : 1 ≤ G := F.discrete _ hG
  have hbm := mul_nonpos_of_nonneg_of_nonpos hb.le hm
  have hAG := mul_nonneg (show (0:R) ≤ 1 + b * W ^ 2 by positivity)
    (show (0:R) ≤ G - 1 by linarith)
  have hbV := mul_nonneg (show (0:R) ≤ b - 1 by linarith) (sq_nonneg W)
  nlinarith only [hy, hsmall, hbm, hAG, hbV, sq_nonneg (4 * W - 1)]

omit p v hb hv in
theorem transport_nonneg {b m G W y : R} (hb : 0 < b) (hm : 0 < m)
    (hy : y = 1 + 4 * (b * (m - W ^ 2 * G) - G)) (hsmall : |y| < 2 * |W|) : 0 ≤ G := by
  by_contra hG
  push_neg at hG
  have hsmall' : -2 * |W| < 2 - y := by
    have := le_abs_self y
    have := neg_abs_le y
    linarith
  have hreflect : 2 - y = 1 + 4 * (b * (-m - |W| ^ 2 * -G) - -G) := by
    rw [sq_abs]; linear_combination -hy
  have := affine_carrier_pos F hb (show (0:R) < -G by linarith) hsmall' hreflect
  linarith

theorem base_dvd_transport (hres : SignedResidue R) (hu : auxiliary p v = 1) :
    ∃ g, G p v = b p v * g := by
  have hs := scale_ge_two F p v hb hv
  have hn := auxiliary_norm p v hu
  obtain ⟨u, hu4⟩ := hres _ _ _ hs hn
    ⟨b p v * (v 11 - (data p v).V ^ 2 * G p v) - G p v,
      by rw [signedY_shape]; ring⟩
  rw [signedY_shape] at hu4
  -- S = b * (v 4 * delta * c²), so G = b*(v 11 - V² G) - S² u
  refine ⟨(v 11 - (data p v).V ^ 2 * G p v) -
    b p v * (v 4 * (data p v).delta * (data p v).c ^ 2) ^ 2 * u, ?_⟩
  have hS : (data p v).S = b p v * (v 4 * (data p v).delta * (data p v).c ^ 2) := by
    change (b p v * v 4) * (data p v).delta * (data p v).c ^ 2 = _
    ring
  rw [hS] at hu4
  have h4 : (4:R) * (G p v - b p v * ((v 11 - (data p v).V ^ 2 * G p v) -
      b p v * (v 4 * (data p v).delta * (data p v).c ^ 2) ^ 2 * u)) = 0 := by
    linear_combination -hu4
  rcases mul_eq_zero.mp h4 with h | h
  · exact absurd h (by norm_num)
  · linear_combination h

/-- The restored fourteen-coordinate assignment, with an explicit quotient. -/
def restoredWith (g : R) : Fin 14 → R := parent p v (g + 1) |signedY p v|

theorem restores_positive_zero69 (hres : SignedResidue R)
    (hz : ThirteenCarrier.value69 p v = 0) :
    ∃ w : Fin 14 → R, (∀ j, 0 < w j) ∧ Carrier65.value p w = 0 := by
  obtain ⟨hP, hQ, hu, hs⟩ := norms_of_zero F p v hb hv hz
  have hbv : 0 < b p v := mul_pos hb (hv 0)
  obtain ⟨hyne, hsmall⟩ := auxiliary_estimates F (scale_ge_two F p v hb hv) (auxiliary_norm p v hu)
  have hG := transport_nonneg F hbv (hv 11) (signedY_shape p v) hsmall
  obtain ⟨g, hg⟩ := base_dvd_transport F p v hb hv hres hu
  have hg0 : 0 ≤ g := by
    by_contra hneg; push_neg at hneg
    have := mul_neg_of_pos_of_neg hbv hneg
    linarith
  have hzpos : 0 < g + 1 := by linarith
  have hW : G p v + (data p v).q - (g + 1) * b p v = 1 := by
    change G p v + (b p v + 1) - (g + 1) * b p v = 1
    rw [hg]; ring
  have hZ : (data p v).Z = (data p v).delta := by
    change (Carrier65.core p (parent p v 1 1)).Z = _
    rw [Carrier65.strong_scale]
    change (data p v).delta * Carrier65.strong (data p v) = (data p v).delta
    rw [hs, mul_one]
  refine ⟨restoredWith p v g, parent_pos F p v hb hv hzpos (abs_pos.mpr hyne), ?_⟩
  unfold restoredWith Carrier65.value
  rw [core_parent]
  change (data p v).P * (data p v).Q *
    ((data p v).S ^ 2 * ((data p v).V ^ 2 - |signedY p v| ^ 2) + |signedY p v| ^ 2) *
    (G p v + (data p v).q - (g + 1) * b p v) * (data p v).Z -
    (data p v).delta = 0
  rw [sq_abs]
  change (data p v).P * (data p v).Q * auxiliary p v *
    (G p v + (data p v).q - (g + 1) * b p v) * (data p v).Z -
    (data p v).delta = 0
  rw [hP, hQ, hu, hW, hZ]
  ring

end Generic

section Model
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem modelSignedResidue : SignedResidue (DiffRing V) :=
  fun S W y hS hn hy => ArithmeticOddOrdinateResidue.four_square_dvd_sub_one S W y hS hn hy

end Model

end DiophantineConsistency.ModelThirteenRestoration
