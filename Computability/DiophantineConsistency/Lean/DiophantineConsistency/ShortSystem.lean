import DiophantineConsistency.ShortCircuit
import DiophantineConsistency.ConsecutivePell
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# Five equations for the short product circuit

This is a local zero-set equivalence for the actual P69 arithmetic schedule.
Four Pell/auxiliary factors have positive sign at a product zero. Only the
product of the index and transport factors needs to be retained as one equation.
Combining the five residuals by squares gives one polynomial, without adding
unknowns. No native-window compiler or independent Con(ZFC) claim is asserted.
-/

namespace DiophantineConsistency.ShortSystem

open ShortCircuit
open MvPolynomial

private theorem unit_eq_one {a b : ℤ} (h : a * b = 1) (hne : a ≠ -1) : a = 1 := by
  have hu : IsUnit a := IsUnit.of_mul_eq_one_right b (by simpa only [mul_comm] using h)
  rcases Int.isUnit_iff.mp hu with hpos | hneg
  · exact hpos
  · exact (hne hneg).elim

/-- The square-coefficient auxiliary norm also excludes the negative unit modulo four. -/
theorem square_aux_ne_neg_one (t h y : ℤ) :
    t ^ 2 * (h ^ 2 - y ^ 2) + y ^ 2 ≠ -1 := by
  intro he
  have hm := congrArg (fun z : ℤ => (z : ZMod 4)) he
  push_cast at hm
  have bad : ∀ t h y : ZMod 4, t ^ 2 * (h ^ 2 - y ^ 2) + y ^ 2 ≠ -1 := by decide
  exact bad _ _ _ hm

/-- Sign-fixed factors can be separated; the remaining pair stays combined. -/
theorem product_eq_one_iff (n0 n1 na nk nt ns : ℤ)
    (h0 : n0 ≠ -1) (h1 : n1 ≠ -1) (hs : ns ≠ -1)
    (ha : ns = 1 → na ≠ -1) :
    n0 * n1 * na * nk * nt * ns = 1 ↔
      n0 = 1 ∧ n1 = 1 ∧ na = 1 ∧ ns = 1 ∧ nk * nt = 1 := by
  constructor
  · intro hp
    have hs1 : ns = 1 := unit_eq_one (b := n0 * n1 * na * nk * nt)
      (by calc ns * (n0 * n1 * na * nk * nt) = n0 * n1 * na * nk * nt * ns := by ring
               _ = 1 := hp) hs
    have h01 : n0 = 1 := unit_eq_one (b := n1 * na * nk * nt * ns)
      (by calc n0 * (n1 * na * nk * nt * ns) = n0 * n1 * na * nk * nt * ns := by ring
               _ = 1 := hp) h0
    have h11 : n1 = 1 := unit_eq_one (b := n0 * na * nk * nt * ns)
      (by calc n1 * (n0 * na * nk * nt * ns) = n0 * n1 * na * nk * nt * ns := by ring
               _ = 1 := hp) h1
    have ha1 : na = 1 := unit_eq_one (b := n0 * n1 * nk * nt * ns)
      (by calc na * (n0 * n1 * nk * nt * ns) = n0 * n1 * na * nk * nt * ns := by ring
               _ = 1 := hp) (ha hs1)
    exact ⟨h01, h11, ha1, hs1, by simpa only [h01, h11, ha1, hs1, one_mul, mul_one] using hp⟩
  · rintro ⟨h01, h11, ha1, hs1, hkt⟩
    simpa only [h01, h11, ha1, hs1, one_mul, mul_one] using hkt

/-- Five residuals, using only the product of the last two unconstrained signs. -/
def residualSum {R : Type*} [CommRing R] (n0 n1 na ns nk nt : R) : R :=
  (n0 - 1) ^ 2 + (n1 - 1) ^ 2 + (na - 1) ^ 2 + (ns - 1) ^ 2 + (nk * nt - 1) ^ 2

theorem residualSum_zero_iff (n0 n1 na ns nk nt : ℤ) :
    residualSum n0 n1 na ns nk nt = 0 ↔
      n0 = 1 ∧ n1 = 1 ∧ na = 1 ∧ ns = 1 ∧ nk * nt = 1 := by
  unfold residualSum
  constructor
  · intro h
    have h0 : (n0 - 1) ^ 2 = 0 := by
      nlinarith [sq_nonneg (n1 - 1), sq_nonneg (na - 1), sq_nonneg (ns - 1),
        sq_nonneg (nk * nt - 1), sq_nonneg (n0 - 1)]
    have h1 : (n1 - 1) ^ 2 = 0 := by
      nlinarith [sq_nonneg (n0 - 1), sq_nonneg (na - 1), sq_nonneg (ns - 1),
        sq_nonneg (nk * nt - 1), sq_nonneg (n1 - 1)]
    have ha : (na - 1) ^ 2 = 0 := by
      nlinarith [sq_nonneg (n0 - 1), sq_nonneg (n1 - 1), sq_nonneg (ns - 1),
        sq_nonneg (nk * nt - 1), sq_nonneg (na - 1)]
    have hs : (ns - 1) ^ 2 = 0 := by
      nlinarith [sq_nonneg (n0 - 1), sq_nonneg (n1 - 1), sq_nonneg (na - 1),
        sq_nonneg (nk * nt - 1), sq_nonneg (ns - 1)]
    have hkt : (nk * nt - 1) ^ 2 = 0 := by
      nlinarith [sq_nonneg (n0 - 1), sq_nonneg (n1 - 1), sq_nonneg (na - 1),
        sq_nonneg (ns - 1), sq_nonneg (nk * nt - 1)]
    exact ⟨sub_eq_zero.mp (sq_eq_zero_iff.mp h0), sub_eq_zero.mp (sq_eq_zero_iff.mp h1),
      sub_eq_zero.mp (sq_eq_zero_iff.mp ha), sub_eq_zero.mp (sq_eq_zero_iff.mp hs),
      sub_eq_zero.mp (sq_eq_zero_iff.mp hkt)⟩
  · rintro ⟨rfl, rfl, rfl, rfl, hkt⟩
    simp only [hkt, sub_self, zero_pow (by decide : 2 ≠ 0), add_zero]

variable {R S : Type*} [CommRing R] [CommRing S]

def q (p : Fin 4 → R) (v : Fin 15 → R) : R := p 0 * v 0 + 1
def leftScale (p : Fin 4 → R) (v : Fin 15 → R) : R := v 9 * q p v
def rightScale (p : Fin 4 → R) (v : Fin 15 → R) : R := v 8 * (q p v * q p v * q p v)
def firstParameter (p : Fin 4 → R) (v : Fin 15 → R) : R :=
  leftScale p v * rightScale p v * rightScale p v

def mainRoot (p : Fin 4 → R) (v : Fin 15 → R) : R :=
  leftScale p v + (core p v).c * (core p v).a + v 14 * (4 * (core p v).a + 3)

def auxiliaryRoot (p : Fin 4 → R) (v : Fin 15 → R) : R :=
  let r := ((p 0 * v 0) * (q p v - v 1) + v 2) * (q p v * q p v - 1) +
    (p 2 + q p v * p 3) * v 0
  (core p v).c * (v 7 * (core p v).f - 1) - r * (core p v).f ^ 2

def auxiliary (b : Core R) : R := b.delta * (b.f ^ 2 - 1) * b.gap + b.y ^ 2
def strong (b : Core R) : R := b.f ^ 2 - b.delta * (b.i * b.c ^ 2) ^ 2

theorem first_shape (p : Fin 4 → R) (v : Fin 15 → R) :
    (core p v).n0 = (v 10) ^ 2 - firstParameter p v * (firstParameter p v + 1) *
      (v 11 + v 12) ^ 2 := by
  unfold core firstParameter leftScale rightScale q
  ring

theorem main_shape (p : Fin 4 → R) (v : Fin 15 → R) :
    (core p v).n1 = mainRoot p v ^ 2 - (core p v).delta * (core p v).c ^ 2 := by
  simp only [core, mainRoot, leftScale, q, pow_two]

theorem gap_shape (p : Fin 4 → R) (v : Fin 15 → R) :
    (core p v).gap = auxiliaryRoot p v ^ 2 - (core p v).y ^ 2 := by
  simp only [auxiliaryRoot, core, q, pow_two]

theorem firstParameter_ge_two (p : Fin 4 → ℤ) (v : Fin 15 → ℤ)
    (hbeta : 0 < p 0) (hv : ∀ j, 0 < v j) : 2 ≤ firstParameter p v := by
  have hq : 2 ≤ q p v := by
    have h := mul_pos hbeta (hv 0)
    dsimp only [q]
    omega
  have hl : 2 ≤ leftScale p v := by
    have hw := hv 9
    dsimp only [leftScale]
    nlinarith
  have hr : 1 ≤ rightScale p v := by
    have hs := hv 8
    have : 0 < rightScale p v := by dsimp only [rightScale]; positivity
    omega
  dsimp only [firstParameter]
  have hmid : leftScale p v ≤ leftScale p v * rightScale p v := by nlinarith
  nlinarith

theorem auxiliary_ne_neg_one (p : Fin 4 → ℤ) (v : Fin 15 → ℤ)
    (hs : strong (core p v) = 1) : auxiliary (core p v) ≠ -1 := by
  have hf : (core p v).f ^ 2 - 1 = (core p v).delta * ((core p v).i * (core p v).c ^ 2) ^ 2 := by
    dsimp only [strong] at hs
    linarith
  have hc : (core p v).delta * ((core p v).f ^ 2 - 1) =
      ((core p v).delta * ((core p v).i * (core p v).c ^ 2)) ^ 2 := by rw [hf]; ring
  unfold auxiliary
  rw [hc, gap_shape]
  exact square_aux_ne_neg_one _ _ _

/-- The five-equation sum of squares, with the actual P69 coordinate convention. -/
def value (p : Fin 4 → R) (v : Fin 15 → R) : R :=
  let b := core p v
  residualSum b.n0 b.n1 (auxiliary b) (strong b) b.nk b.nt

/-- Exact local equivalence, for every positive assignment and positive beta port. -/
theorem value_zero_iff_shortCircuit_zero (p : Fin 4 → ℤ) (v : Fin 15 → ℤ)
    (hbeta : 0 < p 0) (hv : ∀ j, 0 < v j) :
    value p v = 0 ↔ ShortCircuit.value p v = 0 := by
  have h0 : (core p v).n0 ≠ -1 := by
    rw [first_shape]
    exact ConsecutivePell.norm_ne_neg_one _ _ _ (firstParameter_ge_two p v hbeta hv)
  have h1 : (core p v).n1 ≠ -1 := by
    rw [main_shape, core_delta]
    exact ShortEquation.strong_ne_neg_one _ _ _
  have hs : strong (core p v) ≠ -1 := by
    unfold strong
    rw [core_delta]
    exact ShortEquation.strong_ne_neg_one _ _ _
  have hp := product_eq_one_iff (core p v).n0 (core p v).n1 (auxiliary (core p v))
    (core p v).nk (core p v).nt (strong (core p v)) h0 h1 hs (auxiliary_ne_neg_one p v)
  have hout : ShortCircuit.value p v =
      (core p v).n0 * (core p v).n1 * auxiliary (core p v) * (core p v).nk *
        (core p v).nt * strong (core p v) - 1 := by
    rw [value_eq_core, coreValue_eq]
    unfold auxiliary strong
    ring
  rw [value, residualSum_zero_iff, hout]
  exact hp.symm.trans (by omega)

def compactResidualSum (n0 n1 na ns nk nt : R) : R :=
  (n0 - 1) ^ 2 + (na - 1) ^ 2 + (ns - 1) ^ 2 + (n1 * nk * nt - 1) ^ 2

theorem compactResidualSum_zero_iff (n0 n1 na ns nk nt : ℤ) :
    compactResidualSum n0 n1 na ns nk nt = 0 ↔
      n0 = 1 ∧ na = 1 ∧ ns = 1 ∧ n1 * nk * nt = 1 := by
  simpa only [compactResidualSum, residualSum, sub_self, zero_pow (by decide : 2 ≠ 0),
    add_zero, and_true, true_and] using residualSum_zero_iff n0 na ns 1 (n1 * nk) nt

/-- Four groups combine the main, index and transport factors. -/
def compactValue (p : Fin 4 → R) (v : Fin 15 → R) : R :=
  let b := core p v
  compactResidualSum b.n0 b.n1 (auxiliary b) (strong b) b.nk b.nt

theorem compactValue_zero_iff_shortCircuit_zero (p : Fin 4 → ℤ) (v : Fin 15 → ℤ)
    (hbeta : 0 < p 0) (hv : ∀ j, 0 < v j) :
    compactValue p v = 0 ↔ ShortCircuit.value p v = 0 := by
  have hfive := value_zero_iff_shortCircuit_zero p v hbeta hv
  have hout : ShortCircuit.value p v =
      (core p v).n0 * (core p v).n1 * auxiliary (core p v) * (core p v).nk *
        (core p v).nt * strong (core p v) - 1 := by
    rw [value_eq_core, coreValue_eq]
    unfold auxiliary strong
    ring
  rw [compactValue, compactResidualSum_zero_iff]
  constructor
  · rintro ⟨h0, ha, hs, hcombined⟩
    rw [hout]
    calc
      _ = (core p v).n0 * auxiliary (core p v) * strong (core p v) *
          ((core p v).n1 * (core p v).nk * (core p v).nt) - 1 := by ring
      _ = 0 := by rw [h0, ha, hs, hcombined]; norm_num
  · intro h
    obtain ⟨h0, h1, ha, hs, hkt⟩ :=
      (residualSum_zero_iff _ _ _ _ _ _).mp (hfive.mpr h)
    exact ⟨h0, ha, hs, by rw [h1, one_mul, hkt]⟩

-- BEGIN GENERATED P77 LITERAL EVALUATOR
/-- Literal evaluator of circuits/p77_sos.json; no implicit abbreviation costs. -/
def literalValue (p : Fin 4 → R) (v : Fin 15 → R) : R :=
  let J := v 0
  let F := v 1
  let alpha := v 2
  let z := v 3
  let f := v 4
  let h := v 5
  let i := v 6
  let T := v 7
  let s := v 8
  let w := v 9
  let tau := v 10
  let eta := v 11
  let zeta := v 12
  let y := v 13
  let gamma := v 14
  let beta := p 0
  let K0 := p 1
  let MC := p 2
  let MF := p 3
  let tau_square := tau * tau
  let repunit := beta * J
  let q := repunit + 1
  let Lbig := q * q
  let n2 := Lbig * q
  let wn2 := w * q
  let sn2 := s * n2
  let UM := wn2 * sn2
  let R10b := eta + zeta
  let ksn2 := R10b * sn2
  let first_root_base := UM * ksn2
  let first_next := first_root_base + R10b
  let first_product := first_root_base * first_next
  let norm_first := tau_square - first_product
  let R10a := ksn2 + eta
  let R12 := UM + sn2
  let cam2 := R10a * R12
  let D1 := wn2 + cam2
  let a4 := 4 * R12
  let a4m5 := a4 + 3
  let gam := gamma * a4m5
  let R14 := D1 + gam
  let L15 := R14 * R14
  let a_square := R12 * R12
  let A := a_square + a4m5
  let c2 := R10a * R10a
  let Ac2 := A * c2
  let norm_main := L15 - Ac2
  let q_minus_F := q - F
  let C := q_minus_F - alpha
  let aux_y2 := y * y
  let hpm1 := h * UM
  let index_difference := R10b - hpm1
  let gap_product := repunit * q_minus_F
  let gap := gap_product + alpha
  let Lm1 := Lbig - 1
  let rproduct := gap * Lm1
  let qMF := q * MF
  let mask_factor := MC + qMF
  let mask := mask_factor * J
  let r_lhs := rproduct + mask
  let norm_index := index_difference - r_lhs
  let kinner := K0 + w
  let innerC := kinner * C
  let transport_partial := innerC + q_minus_F
  let local_rhs := z * repunit
  let norm_transport := transport_partial - local_rhs
  let L16 := f * f
  let auxiliary_Tf := T * f
  let auxiliary_Tf_minus_one := auxiliary_Tf - 1
  let auxiliary_c_Tf := R10a * auxiliary_Tf_minus_one
  let auxiliary_R_f2 := r_lhs * L16
  let aux_u_rhs := auxiliary_c_Tf - auxiliary_R_f2
  let H2 := aux_u_rhs * aux_u_rhs
  let aux_square_gap := H2 - aux_y2
  let aux_coefficient_root := i * c2
  let R16 := aux_coefficient_root * aux_coefficient_root
  let strong_square_scaled := A * R16
  let aux_f2_minus_one := L16 - 1
  let aux_reduced_coefficient := A * aux_f2_minus_one
  let L17 := aux_reduced_coefficient * aux_square_gap
  let norm_aux := L17 + aux_y2
  let index_transport := norm_index * norm_transport
  let residual_first := norm_first - 1
  let residual_main := norm_main - 1
  let residual_aux := norm_aux - 1
  let residual_strong := aux_f2_minus_one - strong_square_scaled
  let residual_index_transport := index_transport - 1
  let residual_first_square := residual_first * residual_first
  let residual_main_square := residual_main * residual_main
  let residual_aux_square := residual_aux * residual_aux
  let residual_strong_square := residual_strong * residual_strong
  let residual_index_transport_square := residual_index_transport * residual_index_transport
  let sum_1 := residual_first_square + residual_main_square
  let sum_2 := sum_1 + residual_aux_square
  let sum_3 := sum_2 + residual_strong_square
  let polynomial := sum_3 + residual_index_transport_square
  polynomial
-- END GENERATED P77 LITERAL EVALUATOR

private def literalCoreValue (b : Core R) : R :=
  let c2 := b.c * b.c
  let L16 := b.f * b.f
  let aux_y2 := b.y * b.y
  let aux_coefficient_root := b.i * c2
  let R16 := aux_coefficient_root * aux_coefficient_root
  let strong_square_scaled := b.delta * R16
  let aux_f2_minus_one := L16 - 1
  let aux_reduced_coefficient := b.delta * aux_f2_minus_one
  let L17 := aux_reduced_coefficient * b.gap
  let norm_aux := L17 + aux_y2
  let index_transport := b.nk * b.nt
  let residual_first := b.n0 - 1
  let residual_main := b.n1 - 1
  let residual_aux := norm_aux - 1
  let residual_strong := aux_f2_minus_one - strong_square_scaled
  let residual_index_transport := index_transport - 1
  let residual_first_square := residual_first * residual_first
  let residual_main_square := residual_main * residual_main
  let residual_aux_square := residual_aux * residual_aux
  let residual_strong_square := residual_strong * residual_strong
  let residual_index_transport_square := residual_index_transport * residual_index_transport
  let sum_1 := residual_first_square + residual_main_square
  let sum_2 := sum_1 + residual_aux_square
  let sum_3 := sum_2 + residual_strong_square
  sum_3 + residual_index_transport_square

private theorem literalValue_eq_core (p : Fin 4 → R) (v : Fin 15 → R) :
    literalValue p v = literalCoreValue (core p v) := rfl

/-- The literal 77-gate schedule is exactly the five-residual polynomial expression. -/
theorem literalValue_eq_value (p : Fin 4 → R) (v : Fin 15 → R) :
    literalValue p v = value p v := by
  rw [literalValue_eq_core]
  change literalCoreValue (core p v) =
    residualSum (core p v).n0 (core p v).n1 (auxiliary (core p v))
      (strong (core p v)) (core p v).nk (core p v).nt
  generalize core p v = b
  unfold literalCoreValue residualSum auxiliary strong
  ring

-- BEGIN GENERATED P75 LITERAL EVALUATOR
/-- Literal evaluator of circuits/p75_sos.json; no implicit abbreviation costs. -/
def compactLiteralValue (p : Fin 4 → R) (v : Fin 15 → R) : R :=
  let J := v 0
  let F := v 1
  let alpha := v 2
  let z := v 3
  let f := v 4
  let h := v 5
  let i := v 6
  let T := v 7
  let s := v 8
  let w := v 9
  let tau := v 10
  let eta := v 11
  let zeta := v 12
  let y := v 13
  let gamma := v 14
  let beta := p 0
  let K0 := p 1
  let MC := p 2
  let MF := p 3
  let tau_square := tau * tau
  let repunit := beta * J
  let q := repunit + 1
  let Lbig := q * q
  let n2 := Lbig * q
  let wn2 := w * q
  let sn2 := s * n2
  let UM := wn2 * sn2
  let R10b := eta + zeta
  let ksn2 := R10b * sn2
  let first_root_base := UM * ksn2
  let first_next := first_root_base + R10b
  let first_product := first_root_base * first_next
  let norm_first := tau_square - first_product
  let R10a := ksn2 + eta
  let R12 := UM + sn2
  let cam2 := R10a * R12
  let D1 := wn2 + cam2
  let a4 := 4 * R12
  let a4m5 := a4 + 3
  let gam := gamma * a4m5
  let R14 := D1 + gam
  let L15 := R14 * R14
  let a_square := R12 * R12
  let A := a_square + a4m5
  let c2 := R10a * R10a
  let Ac2 := A * c2
  let norm_main := L15 - Ac2
  let q_minus_F := q - F
  let C := q_minus_F - alpha
  let aux_y2 := y * y
  let hpm1 := h * UM
  let index_difference := R10b - hpm1
  let gap_product := repunit * q_minus_F
  let gap := gap_product + alpha
  let Lm1 := Lbig - 1
  let rproduct := gap * Lm1
  let qMF := q * MF
  let mask_factor := MC + qMF
  let mask := mask_factor * J
  let r_lhs := rproduct + mask
  let norm_index := index_difference - r_lhs
  let kinner := K0 + w
  let innerC := kinner * C
  let transport_partial := innerC + q_minus_F
  let local_rhs := z * repunit
  let norm_transport := transport_partial - local_rhs
  let L16 := f * f
  let auxiliary_Tf := T * f
  let auxiliary_Tf_minus_one := auxiliary_Tf - 1
  let auxiliary_c_Tf := R10a * auxiliary_Tf_minus_one
  let auxiliary_R_f2 := r_lhs * L16
  let aux_u_rhs := auxiliary_c_Tf - auxiliary_R_f2
  let H2 := aux_u_rhs * aux_u_rhs
  let aux_square_gap := H2 - aux_y2
  let aux_coefficient_root := i * c2
  let R16 := aux_coefficient_root * aux_coefficient_root
  let strong_square_scaled := A * R16
  let aux_f2_minus_one := L16 - 1
  let aux_reduced_coefficient := A * aux_f2_minus_one
  let L17 := aux_reduced_coefficient * aux_square_gap
  let norm_aux := L17 + aux_y2
  let main_index := norm_main * norm_index
  let main_index_transport := main_index * norm_transport
  let residual_first := norm_first - 1
  let residual_aux := norm_aux - 1
  let residual_strong := aux_f2_minus_one - strong_square_scaled
  let residual_main_index_transport := main_index_transport - 1
  let residual_first_square := residual_first * residual_first
  let residual_aux_square := residual_aux * residual_aux
  let residual_strong_square := residual_strong * residual_strong
  let residual_main_index_transport_square := residual_main_index_transport * residual_main_index_transport
  let sum_1 := residual_first_square + residual_aux_square
  let sum_2 := sum_1 + residual_strong_square
  let polynomial := sum_2 + residual_main_index_transport_square
  polynomial
-- END GENERATED P75 LITERAL EVALUATOR

private def compactLiteralCoreValue (b : Core R) : R :=
  let c2 := b.c * b.c
  let L16 := b.f * b.f
  let aux_y2 := b.y * b.y
  let aux_coefficient_root := b.i * c2
  let R16 := aux_coefficient_root * aux_coefficient_root
  let strong_square_scaled := b.delta * R16
  let aux_f2_minus_one := L16 - 1
  let aux_reduced_coefficient := b.delta * aux_f2_minus_one
  let L17 := aux_reduced_coefficient * b.gap
  let norm_aux := L17 + aux_y2
  let main_index := b.n1 * b.nk
  let main_index_transport := main_index * b.nt
  let residual_first := b.n0 - 1
  let residual_aux := norm_aux - 1
  let residual_strong := aux_f2_minus_one - strong_square_scaled
  let residual_main_index_transport := main_index_transport - 1
  let residual_first_square := residual_first * residual_first
  let residual_aux_square := residual_aux * residual_aux
  let residual_strong_square := residual_strong * residual_strong
  let residual_main_index_transport_square := residual_main_index_transport * residual_main_index_transport
  let sum_1 := residual_first_square + residual_aux_square
  let sum_2 := sum_1 + residual_strong_square
  sum_2 + residual_main_index_transport_square

private theorem compactLiteralValue_eq_core (p : Fin 4 → R) (v : Fin 15 → R) :
    compactLiteralValue p v = compactLiteralCoreValue (core p v) := rfl

/-- Exact equality between the live 75-operation DAG and the four grouped residuals. -/
theorem compactLiteralValue_eq_compactValue (p : Fin 4 → R) (v : Fin 15 → R) :
    compactLiteralValue p v = compactValue p v := by
  rw [compactLiteralValue_eq_core]
  change compactLiteralCoreValue (core p v) =
    compactResidualSum (core p v).n0 (core p v).n1 (auxiliary (core p v))
      (strong (core p v)) (core p v).nk (core p v).nt
  generalize core p v = b
  unfold compactLiteralCoreValue compactResidualSum auxiliary strong
  ring

/-- Ring homomorphisms preserve the complete five-equation expression. -/
theorem value_map (φ : R →+* S) (p : Fin 4 → R) (v : Fin 15 → R) :
    φ (value p v) = value (fun j => φ (p j)) (fun j => φ (v j)) := by
  simp only [value, residualSum, auxiliary, strong, core,
    map_add, map_sub, map_mul, map_pow, map_one, map_ofNat]

/-- The ordinary fifteen-variable integer polynomial given by the five residuals. -/
noncomputable def polynomial (p : Fin 4 → ℤ) : MvPolynomial (Fin 15) ℤ :=
  value (fun j => MvPolynomial.C (p j)) MvPolynomial.X

theorem eval_polynomial (p : Fin 4 → ℤ) (v : Fin 15 → ℤ) :
    MvPolynomial.eval v (polynomial p) = value p v := by
  simpa only [polynomial, MvPolynomial.eval_C, MvPolynomial.eval_X] using
    value_map (MvPolynomial.eval v) (fun j => MvPolynomial.C (p j)) MvPolynomial.X

/-- The actual sum-of-squares polynomial has exactly the positive zeros of P67. -/
theorem eval_polynomial_zero_iff_baselineValue_zero (p : Fin 4 → ℤ) (v : Fin 15 → ℤ)
    (hbeta : 0 < p 0) (hv : ∀ j, 0 < v j) :
    MvPolynomial.eval v (polynomial p) = 0 ↔ ShortCircuit.baselineValue p v = 0 := by
  rw [eval_polynomial]
  exact (value_zero_iff_shortCircuit_zero p v hbeta hv).trans
    (ShortCircuit.value_zero_iff_baselineValue_zero p v hbeta hv)

theorem compactValue_map (φ : R →+* S) (p : Fin 4 → R) (v : Fin 15 → R) :
    φ (compactValue p v) = compactValue (fun j => φ (p j)) (fun j => φ (v j)) := by
  simp only [compactValue, compactResidualSum, auxiliary, strong, core,
    map_add, map_sub, map_mul, map_pow, map_one, map_ofNat]

/-- The 75-operation polynomial, retaining the same fifteen positive unknowns. -/
noncomputable def compactPolynomial (p : Fin 4 → ℤ) : MvPolynomial (Fin 15) ℤ :=
  compactValue (fun j => MvPolynomial.C (p j)) MvPolynomial.X

theorem eval_compactPolynomial (p : Fin 4 → ℤ) (v : Fin 15 → ℤ) :
    MvPolynomial.eval v (compactPolynomial p) = compactValue p v := by
  simpa only [compactPolynomial, MvPolynomial.eval_C, MvPolynomial.eval_X] using
    compactValue_map (MvPolynomial.eval v) (fun j => MvPolynomial.C (p j)) MvPolynomial.X

/-- Complete positive zero-set equivalence for the ordinary P75 polynomial. -/
theorem eval_compactPolynomial_zero_iff_baselineValue_zero
    (p : Fin 4 → ℤ) (v : Fin 15 → ℤ) (hbeta : 0 < p 0) (hv : ∀ j, 0 < v j) :
    MvPolynomial.eval v (compactPolynomial p) = 0 ↔ ShortCircuit.baselineValue p v = 0 := by
  rw [eval_compactPolynomial]
  exact (compactValue_zero_iff_shortCircuit_zero p v hbeta hv).trans
    (ShortCircuit.value_zero_iff_baselineValue_zero p v hbeta hv)

private theorem degree_add {a b : MvPolynomial (Fin 15) ℤ} {m n : ℕ}
    (ha : a.totalDegree ≤ m) (hb : b.totalDegree ≤ n) :
    (a + b).totalDegree ≤ max m n :=
  (MvPolynomial.totalDegree_add a b).trans (max_le_max ha hb)

private theorem degree_sub {a b : MvPolynomial (Fin 15) ℤ} {m n : ℕ}
    (ha : a.totalDegree ≤ m) (hb : b.totalDegree ≤ n) :
    (a - b).totalDegree ≤ max m n :=
  (MvPolynomial.totalDegree_sub a b).trans (max_le_max ha hb)

private theorem degree_mul {a b : MvPolynomial (Fin 15) ℤ} {m n : ℕ}
    (ha : a.totalDegree ≤ m) (hb : b.totalDegree ≤ n) :
    (a * b).totalDegree ≤ m + n :=
  (MvPolynomial.totalDegree_mul a b).trans (Nat.add_le_add ha hb)

private theorem degree_numeral (n : ℕ) : (n : MvPolynomial (Fin 15) ℤ).totalDegree ≤ 0 := by
  simpa only [map_natCast] using
    (MvPolynomial.totalDegree_C (σ := Fin 15) (n : ℤ)).le

-- BEGIN GENERATED P77 DEGREE CERTIFICATE
/-- A kernel-checked upper degree bound for the actual polynomial. -/
theorem polynomial_totalDegree_le (p : Fin 4 → ℤ) :
    (polynomial p).totalDegree ≤ 68 := by
  let J : MvPolynomial (Fin 15) ℤ := MvPolynomial.X (0 : Fin 15)
  have h_J : J.totalDegree ≤ 1 := by simp only [J, MvPolynomial.totalDegree_X, le_refl]
  let F : MvPolynomial (Fin 15) ℤ := MvPolynomial.X (1 : Fin 15)
  have h_F : F.totalDegree ≤ 1 := by simp only [F, MvPolynomial.totalDegree_X, le_refl]
  let alpha : MvPolynomial (Fin 15) ℤ := MvPolynomial.X (2 : Fin 15)
  have h_alpha : alpha.totalDegree ≤ 1 := by simp only [alpha, MvPolynomial.totalDegree_X, le_refl]
  let z : MvPolynomial (Fin 15) ℤ := MvPolynomial.X (3 : Fin 15)
  have h_z : z.totalDegree ≤ 1 := by simp only [z, MvPolynomial.totalDegree_X, le_refl]
  let f : MvPolynomial (Fin 15) ℤ := MvPolynomial.X (4 : Fin 15)
  have h_f : f.totalDegree ≤ 1 := by simp only [f, MvPolynomial.totalDegree_X, le_refl]
  let h : MvPolynomial (Fin 15) ℤ := MvPolynomial.X (5 : Fin 15)
  have h_h : h.totalDegree ≤ 1 := by simp only [h, MvPolynomial.totalDegree_X, le_refl]
  let i : MvPolynomial (Fin 15) ℤ := MvPolynomial.X (6 : Fin 15)
  have h_i : i.totalDegree ≤ 1 := by simp only [i, MvPolynomial.totalDegree_X, le_refl]
  let T : MvPolynomial (Fin 15) ℤ := MvPolynomial.X (7 : Fin 15)
  have h_T : T.totalDegree ≤ 1 := by simp only [T, MvPolynomial.totalDegree_X, le_refl]
  let s : MvPolynomial (Fin 15) ℤ := MvPolynomial.X (8 : Fin 15)
  have h_s : s.totalDegree ≤ 1 := by simp only [s, MvPolynomial.totalDegree_X, le_refl]
  let w : MvPolynomial (Fin 15) ℤ := MvPolynomial.X (9 : Fin 15)
  have h_w : w.totalDegree ≤ 1 := by simp only [w, MvPolynomial.totalDegree_X, le_refl]
  let tau : MvPolynomial (Fin 15) ℤ := MvPolynomial.X (10 : Fin 15)
  have h_tau : tau.totalDegree ≤ 1 := by simp only [tau, MvPolynomial.totalDegree_X, le_refl]
  let eta : MvPolynomial (Fin 15) ℤ := MvPolynomial.X (11 : Fin 15)
  have h_eta : eta.totalDegree ≤ 1 := by simp only [eta, MvPolynomial.totalDegree_X, le_refl]
  let zeta : MvPolynomial (Fin 15) ℤ := MvPolynomial.X (12 : Fin 15)
  have h_zeta : zeta.totalDegree ≤ 1 := by simp only [zeta, MvPolynomial.totalDegree_X, le_refl]
  let y : MvPolynomial (Fin 15) ℤ := MvPolynomial.X (13 : Fin 15)
  have h_y : y.totalDegree ≤ 1 := by simp only [y, MvPolynomial.totalDegree_X, le_refl]
  let gamma : MvPolynomial (Fin 15) ℤ := MvPolynomial.X (14 : Fin 15)
  have h_gamma : gamma.totalDegree ≤ 1 := by simp only [gamma, MvPolynomial.totalDegree_X, le_refl]
  let beta : MvPolynomial (Fin 15) ℤ := MvPolynomial.C (p 0)
  have h_beta : beta.totalDegree ≤ 0 := (MvPolynomial.totalDegree_C _).le
  let K0 : MvPolynomial (Fin 15) ℤ := MvPolynomial.C (p 1)
  have h_K0 : K0.totalDegree ≤ 0 := (MvPolynomial.totalDegree_C _).le
  let MC : MvPolynomial (Fin 15) ℤ := MvPolynomial.C (p 2)
  have h_MC : MC.totalDegree ≤ 0 := (MvPolynomial.totalDegree_C _).le
  let MF : MvPolynomial (Fin 15) ℤ := MvPolynomial.C (p 3)
  have h_MF : MF.totalDegree ≤ 0 := (MvPolynomial.totalDegree_C _).le
  let tau_square := tau * tau
  have h_tau_square : tau_square.totalDegree ≤ 2 :=
    degree_mul h_tau h_tau
  let repunit := beta * J
  have h_repunit : repunit.totalDegree ≤ 1 :=
    degree_mul h_beta h_J
  let q := repunit + 1
  have h_q : q.totalDegree ≤ 1 :=
    degree_add h_repunit (degree_numeral 1)
  let Lbig := q * q
  have h_Lbig : Lbig.totalDegree ≤ 2 :=
    degree_mul h_q h_q
  let n2 := Lbig * q
  have h_n2 : n2.totalDegree ≤ 3 :=
    degree_mul h_Lbig h_q
  let wn2 := w * q
  have h_wn2 : wn2.totalDegree ≤ 2 :=
    degree_mul h_w h_q
  let sn2 := s * n2
  have h_sn2 : sn2.totalDegree ≤ 4 :=
    degree_mul h_s h_n2
  let UM := wn2 * sn2
  have h_UM : UM.totalDegree ≤ 6 :=
    degree_mul h_wn2 h_sn2
  let R10b := eta + zeta
  have h_R10b : R10b.totalDegree ≤ 1 :=
    degree_add h_eta h_zeta
  let ksn2 := R10b * sn2
  have h_ksn2 : ksn2.totalDegree ≤ 5 :=
    degree_mul h_R10b h_sn2
  let first_root_base := UM * ksn2
  have h_first_root_base : first_root_base.totalDegree ≤ 11 :=
    degree_mul h_UM h_ksn2
  let first_next := first_root_base + R10b
  have h_first_next : first_next.totalDegree ≤ 11 :=
    degree_add h_first_root_base h_R10b
  let first_product := first_root_base * first_next
  have h_first_product : first_product.totalDegree ≤ 22 :=
    degree_mul h_first_root_base h_first_next
  let norm_first := tau_square - first_product
  have h_norm_first : norm_first.totalDegree ≤ 22 :=
    degree_sub h_tau_square h_first_product
  let R10a := ksn2 + eta
  have h_R10a : R10a.totalDegree ≤ 5 :=
    degree_add h_ksn2 h_eta
  let R12 := UM + sn2
  have h_R12 : R12.totalDegree ≤ 6 :=
    degree_add h_UM h_sn2
  let cam2 := R10a * R12
  have h_cam2 : cam2.totalDegree ≤ 11 :=
    degree_mul h_R10a h_R12
  let D1 := wn2 + cam2
  have h_D1 : D1.totalDegree ≤ 11 :=
    degree_add h_wn2 h_cam2
  let a4 := 4 * R12
  have h_a4 : a4.totalDegree ≤ 6 :=
    degree_mul (degree_numeral 4) h_R12
  let a4m5 := a4 + 3
  have h_a4m5 : a4m5.totalDegree ≤ 6 :=
    degree_add h_a4 (degree_numeral 3)
  let gam := gamma * a4m5
  have h_gam : gam.totalDegree ≤ 7 :=
    degree_mul h_gamma h_a4m5
  let R14 := D1 + gam
  have h_R14 : R14.totalDegree ≤ 11 :=
    degree_add h_D1 h_gam
  let L15 := R14 * R14
  have h_L15 : L15.totalDegree ≤ 22 :=
    degree_mul h_R14 h_R14
  let a_square := R12 * R12
  have h_a_square : a_square.totalDegree ≤ 12 :=
    degree_mul h_R12 h_R12
  let A := a_square + a4m5
  have h_A : A.totalDegree ≤ 12 :=
    degree_add h_a_square h_a4m5
  let c2 := R10a * R10a
  have h_c2 : c2.totalDegree ≤ 10 :=
    degree_mul h_R10a h_R10a
  let Ac2 := A * c2
  have h_Ac2 : Ac2.totalDegree ≤ 22 :=
    degree_mul h_A h_c2
  let norm_main := L15 - Ac2
  have h_norm_main : norm_main.totalDegree ≤ 22 :=
    degree_sub h_L15 h_Ac2
  let q_minus_F := q - F
  have h_q_minus_F : q_minus_F.totalDegree ≤ 1 :=
    degree_sub h_q h_F
  let C := q_minus_F - alpha
  have h_C : C.totalDegree ≤ 1 :=
    degree_sub h_q_minus_F h_alpha
  let aux_y2 := y * y
  have h_aux_y2 : aux_y2.totalDegree ≤ 2 :=
    degree_mul h_y h_y
  let hpm1 := h * UM
  have h_hpm1 : hpm1.totalDegree ≤ 7 :=
    degree_mul h_h h_UM
  let index_difference := R10b - hpm1
  have h_index_difference : index_difference.totalDegree ≤ 7 :=
    degree_sub h_R10b h_hpm1
  let gap_product := repunit * q_minus_F
  have h_gap_product : gap_product.totalDegree ≤ 2 :=
    degree_mul h_repunit h_q_minus_F
  let gap := gap_product + alpha
  have h_gap : gap.totalDegree ≤ 2 :=
    degree_add h_gap_product h_alpha
  let Lm1 := Lbig - 1
  have h_Lm1 : Lm1.totalDegree ≤ 2 :=
    degree_sub h_Lbig (degree_numeral 1)
  let rproduct := gap * Lm1
  have h_rproduct : rproduct.totalDegree ≤ 4 :=
    degree_mul h_gap h_Lm1
  let qMF := q * MF
  have h_qMF : qMF.totalDegree ≤ 1 :=
    degree_mul h_q h_MF
  let mask_factor := MC + qMF
  have h_mask_factor : mask_factor.totalDegree ≤ 1 :=
    degree_add h_MC h_qMF
  let mask := mask_factor * J
  have h_mask : mask.totalDegree ≤ 2 :=
    degree_mul h_mask_factor h_J
  let r_lhs := rproduct + mask
  have h_r_lhs : r_lhs.totalDegree ≤ 4 :=
    degree_add h_rproduct h_mask
  let norm_index := index_difference - r_lhs
  have h_norm_index : norm_index.totalDegree ≤ 7 :=
    degree_sub h_index_difference h_r_lhs
  let kinner := K0 + w
  have h_kinner : kinner.totalDegree ≤ 1 :=
    degree_add h_K0 h_w
  let innerC := kinner * C
  have h_innerC : innerC.totalDegree ≤ 2 :=
    degree_mul h_kinner h_C
  let transport_partial := innerC + q_minus_F
  have h_transport_partial : transport_partial.totalDegree ≤ 2 :=
    degree_add h_innerC h_q_minus_F
  let local_rhs := z * repunit
  have h_local_rhs : local_rhs.totalDegree ≤ 2 :=
    degree_mul h_z h_repunit
  let norm_transport := transport_partial - local_rhs
  have h_norm_transport : norm_transport.totalDegree ≤ 2 :=
    degree_sub h_transport_partial h_local_rhs
  let L16 := f * f
  have h_L16 : L16.totalDegree ≤ 2 :=
    degree_mul h_f h_f
  let auxiliary_Tf := T * f
  have h_auxiliary_Tf : auxiliary_Tf.totalDegree ≤ 2 :=
    degree_mul h_T h_f
  let auxiliary_Tf_minus_one := auxiliary_Tf - 1
  have h_auxiliary_Tf_minus_one : auxiliary_Tf_minus_one.totalDegree ≤ 2 :=
    degree_sub h_auxiliary_Tf (degree_numeral 1)
  let auxiliary_c_Tf := R10a * auxiliary_Tf_minus_one
  have h_auxiliary_c_Tf : auxiliary_c_Tf.totalDegree ≤ 7 :=
    degree_mul h_R10a h_auxiliary_Tf_minus_one
  let auxiliary_R_f2 := r_lhs * L16
  have h_auxiliary_R_f2 : auxiliary_R_f2.totalDegree ≤ 6 :=
    degree_mul h_r_lhs h_L16
  let aux_u_rhs := auxiliary_c_Tf - auxiliary_R_f2
  have h_aux_u_rhs : aux_u_rhs.totalDegree ≤ 7 :=
    degree_sub h_auxiliary_c_Tf h_auxiliary_R_f2
  let H2 := aux_u_rhs * aux_u_rhs
  have h_H2 : H2.totalDegree ≤ 14 :=
    degree_mul h_aux_u_rhs h_aux_u_rhs
  let aux_square_gap := H2 - aux_y2
  have h_aux_square_gap : aux_square_gap.totalDegree ≤ 14 :=
    degree_sub h_H2 h_aux_y2
  let aux_coefficient_root := i * c2
  have h_aux_coefficient_root : aux_coefficient_root.totalDegree ≤ 11 :=
    degree_mul h_i h_c2
  let R16 := aux_coefficient_root * aux_coefficient_root
  have h_R16 : R16.totalDegree ≤ 22 :=
    degree_mul h_aux_coefficient_root h_aux_coefficient_root
  let strong_square_scaled := A * R16
  have h_strong_square_scaled : strong_square_scaled.totalDegree ≤ 34 :=
    degree_mul h_A h_R16
  let aux_f2_minus_one := L16 - 1
  have h_aux_f2_minus_one : aux_f2_minus_one.totalDegree ≤ 2 :=
    degree_sub h_L16 (degree_numeral 1)
  let aux_reduced_coefficient := A * aux_f2_minus_one
  have h_aux_reduced_coefficient : aux_reduced_coefficient.totalDegree ≤ 14 :=
    degree_mul h_A h_aux_f2_minus_one
  let L17 := aux_reduced_coefficient * aux_square_gap
  have h_L17 : L17.totalDegree ≤ 28 :=
    degree_mul h_aux_reduced_coefficient h_aux_square_gap
  let norm_aux := L17 + aux_y2
  have h_norm_aux : norm_aux.totalDegree ≤ 28 :=
    degree_add h_L17 h_aux_y2
  let index_transport := norm_index * norm_transport
  have h_index_transport : index_transport.totalDegree ≤ 9 :=
    degree_mul h_norm_index h_norm_transport
  let residual_first := norm_first - 1
  have h_residual_first : residual_first.totalDegree ≤ 22 :=
    degree_sub h_norm_first (degree_numeral 1)
  let residual_main := norm_main - 1
  have h_residual_main : residual_main.totalDegree ≤ 22 :=
    degree_sub h_norm_main (degree_numeral 1)
  let residual_aux := norm_aux - 1
  have h_residual_aux : residual_aux.totalDegree ≤ 28 :=
    degree_sub h_norm_aux (degree_numeral 1)
  let residual_strong := aux_f2_minus_one - strong_square_scaled
  have h_residual_strong : residual_strong.totalDegree ≤ 34 :=
    degree_sub h_aux_f2_minus_one h_strong_square_scaled
  let residual_index_transport := index_transport - 1
  have h_residual_index_transport : residual_index_transport.totalDegree ≤ 9 :=
    degree_sub h_index_transport (degree_numeral 1)
  let residual_first_square := residual_first * residual_first
  have h_residual_first_square : residual_first_square.totalDegree ≤ 44 :=
    degree_mul h_residual_first h_residual_first
  let residual_main_square := residual_main * residual_main
  have h_residual_main_square : residual_main_square.totalDegree ≤ 44 :=
    degree_mul h_residual_main h_residual_main
  let residual_aux_square := residual_aux * residual_aux
  have h_residual_aux_square : residual_aux_square.totalDegree ≤ 56 :=
    degree_mul h_residual_aux h_residual_aux
  let residual_strong_square := residual_strong * residual_strong
  have h_residual_strong_square : residual_strong_square.totalDegree ≤ 68 :=
    degree_mul h_residual_strong h_residual_strong
  let residual_index_transport_square := residual_index_transport * residual_index_transport
  have h_residual_index_transport_square : residual_index_transport_square.totalDegree ≤ 18 :=
    degree_mul h_residual_index_transport h_residual_index_transport
  let sum_1 := residual_first_square + residual_main_square
  have h_sum_1 : sum_1.totalDegree ≤ 44 :=
    degree_add h_residual_first_square h_residual_main_square
  let sum_2 := sum_1 + residual_aux_square
  have h_sum_2 : sum_2.totalDegree ≤ 56 :=
    degree_add h_sum_1 h_residual_aux_square
  let sum_3 := sum_2 + residual_strong_square
  have h_sum_3 : sum_3.totalDegree ≤ 68 :=
    degree_add h_sum_2 h_residual_strong_square
  let polynomial := sum_3 + residual_index_transport_square
  have h_polynomial : polynomial.totalDegree ≤ 68 :=
    degree_add h_sum_3 h_residual_index_transport_square
  change (value (fun j => MvPolynomial.C (p j)) MvPolynomial.X).totalDegree ≤ 68
  rw [← literalValue_eq_value]
  change polynomial.totalDegree ≤ 68
  exact h_polynomial
-- END GENERATED P77 DEGREE CERTIFICATE

-- BEGIN GENERATED P75 DEGREE CERTIFICATE
/-- A kernel-checked upper degree bound for the actual polynomial. -/
theorem compactPolynomial_totalDegree_le (p : Fin 4 → ℤ) :
    (compactPolynomial p).totalDegree ≤ 68 := by
  let J : MvPolynomial (Fin 15) ℤ := MvPolynomial.X (0 : Fin 15)
  have h_J : J.totalDegree ≤ 1 := by simp only [J, MvPolynomial.totalDegree_X, le_refl]
  let F : MvPolynomial (Fin 15) ℤ := MvPolynomial.X (1 : Fin 15)
  have h_F : F.totalDegree ≤ 1 := by simp only [F, MvPolynomial.totalDegree_X, le_refl]
  let alpha : MvPolynomial (Fin 15) ℤ := MvPolynomial.X (2 : Fin 15)
  have h_alpha : alpha.totalDegree ≤ 1 := by simp only [alpha, MvPolynomial.totalDegree_X, le_refl]
  let z : MvPolynomial (Fin 15) ℤ := MvPolynomial.X (3 : Fin 15)
  have h_z : z.totalDegree ≤ 1 := by simp only [z, MvPolynomial.totalDegree_X, le_refl]
  let f : MvPolynomial (Fin 15) ℤ := MvPolynomial.X (4 : Fin 15)
  have h_f : f.totalDegree ≤ 1 := by simp only [f, MvPolynomial.totalDegree_X, le_refl]
  let h : MvPolynomial (Fin 15) ℤ := MvPolynomial.X (5 : Fin 15)
  have h_h : h.totalDegree ≤ 1 := by simp only [h, MvPolynomial.totalDegree_X, le_refl]
  let i : MvPolynomial (Fin 15) ℤ := MvPolynomial.X (6 : Fin 15)
  have h_i : i.totalDegree ≤ 1 := by simp only [i, MvPolynomial.totalDegree_X, le_refl]
  let T : MvPolynomial (Fin 15) ℤ := MvPolynomial.X (7 : Fin 15)
  have h_T : T.totalDegree ≤ 1 := by simp only [T, MvPolynomial.totalDegree_X, le_refl]
  let s : MvPolynomial (Fin 15) ℤ := MvPolynomial.X (8 : Fin 15)
  have h_s : s.totalDegree ≤ 1 := by simp only [s, MvPolynomial.totalDegree_X, le_refl]
  let w : MvPolynomial (Fin 15) ℤ := MvPolynomial.X (9 : Fin 15)
  have h_w : w.totalDegree ≤ 1 := by simp only [w, MvPolynomial.totalDegree_X, le_refl]
  let tau : MvPolynomial (Fin 15) ℤ := MvPolynomial.X (10 : Fin 15)
  have h_tau : tau.totalDegree ≤ 1 := by simp only [tau, MvPolynomial.totalDegree_X, le_refl]
  let eta : MvPolynomial (Fin 15) ℤ := MvPolynomial.X (11 : Fin 15)
  have h_eta : eta.totalDegree ≤ 1 := by simp only [eta, MvPolynomial.totalDegree_X, le_refl]
  let zeta : MvPolynomial (Fin 15) ℤ := MvPolynomial.X (12 : Fin 15)
  have h_zeta : zeta.totalDegree ≤ 1 := by simp only [zeta, MvPolynomial.totalDegree_X, le_refl]
  let y : MvPolynomial (Fin 15) ℤ := MvPolynomial.X (13 : Fin 15)
  have h_y : y.totalDegree ≤ 1 := by simp only [y, MvPolynomial.totalDegree_X, le_refl]
  let gamma : MvPolynomial (Fin 15) ℤ := MvPolynomial.X (14 : Fin 15)
  have h_gamma : gamma.totalDegree ≤ 1 := by simp only [gamma, MvPolynomial.totalDegree_X, le_refl]
  let beta : MvPolynomial (Fin 15) ℤ := MvPolynomial.C (p 0)
  have h_beta : beta.totalDegree ≤ 0 := (MvPolynomial.totalDegree_C _).le
  let K0 : MvPolynomial (Fin 15) ℤ := MvPolynomial.C (p 1)
  have h_K0 : K0.totalDegree ≤ 0 := (MvPolynomial.totalDegree_C _).le
  let MC : MvPolynomial (Fin 15) ℤ := MvPolynomial.C (p 2)
  have h_MC : MC.totalDegree ≤ 0 := (MvPolynomial.totalDegree_C _).le
  let MF : MvPolynomial (Fin 15) ℤ := MvPolynomial.C (p 3)
  have h_MF : MF.totalDegree ≤ 0 := (MvPolynomial.totalDegree_C _).le
  let tau_square := tau * tau
  have h_tau_square : tau_square.totalDegree ≤ 2 :=
    degree_mul h_tau h_tau
  let repunit := beta * J
  have h_repunit : repunit.totalDegree ≤ 1 :=
    degree_mul h_beta h_J
  let q := repunit + 1
  have h_q : q.totalDegree ≤ 1 :=
    degree_add h_repunit (degree_numeral 1)
  let Lbig := q * q
  have h_Lbig : Lbig.totalDegree ≤ 2 :=
    degree_mul h_q h_q
  let n2 := Lbig * q
  have h_n2 : n2.totalDegree ≤ 3 :=
    degree_mul h_Lbig h_q
  let wn2 := w * q
  have h_wn2 : wn2.totalDegree ≤ 2 :=
    degree_mul h_w h_q
  let sn2 := s * n2
  have h_sn2 : sn2.totalDegree ≤ 4 :=
    degree_mul h_s h_n2
  let UM := wn2 * sn2
  have h_UM : UM.totalDegree ≤ 6 :=
    degree_mul h_wn2 h_sn2
  let R10b := eta + zeta
  have h_R10b : R10b.totalDegree ≤ 1 :=
    degree_add h_eta h_zeta
  let ksn2 := R10b * sn2
  have h_ksn2 : ksn2.totalDegree ≤ 5 :=
    degree_mul h_R10b h_sn2
  let first_root_base := UM * ksn2
  have h_first_root_base : first_root_base.totalDegree ≤ 11 :=
    degree_mul h_UM h_ksn2
  let first_next := first_root_base + R10b
  have h_first_next : first_next.totalDegree ≤ 11 :=
    degree_add h_first_root_base h_R10b
  let first_product := first_root_base * first_next
  have h_first_product : first_product.totalDegree ≤ 22 :=
    degree_mul h_first_root_base h_first_next
  let norm_first := tau_square - first_product
  have h_norm_first : norm_first.totalDegree ≤ 22 :=
    degree_sub h_tau_square h_first_product
  let R10a := ksn2 + eta
  have h_R10a : R10a.totalDegree ≤ 5 :=
    degree_add h_ksn2 h_eta
  let R12 := UM + sn2
  have h_R12 : R12.totalDegree ≤ 6 :=
    degree_add h_UM h_sn2
  let cam2 := R10a * R12
  have h_cam2 : cam2.totalDegree ≤ 11 :=
    degree_mul h_R10a h_R12
  let D1 := wn2 + cam2
  have h_D1 : D1.totalDegree ≤ 11 :=
    degree_add h_wn2 h_cam2
  let a4 := 4 * R12
  have h_a4 : a4.totalDegree ≤ 6 :=
    degree_mul (degree_numeral 4) h_R12
  let a4m5 := a4 + 3
  have h_a4m5 : a4m5.totalDegree ≤ 6 :=
    degree_add h_a4 (degree_numeral 3)
  let gam := gamma * a4m5
  have h_gam : gam.totalDegree ≤ 7 :=
    degree_mul h_gamma h_a4m5
  let R14 := D1 + gam
  have h_R14 : R14.totalDegree ≤ 11 :=
    degree_add h_D1 h_gam
  let L15 := R14 * R14
  have h_L15 : L15.totalDegree ≤ 22 :=
    degree_mul h_R14 h_R14
  let a_square := R12 * R12
  have h_a_square : a_square.totalDegree ≤ 12 :=
    degree_mul h_R12 h_R12
  let A := a_square + a4m5
  have h_A : A.totalDegree ≤ 12 :=
    degree_add h_a_square h_a4m5
  let c2 := R10a * R10a
  have h_c2 : c2.totalDegree ≤ 10 :=
    degree_mul h_R10a h_R10a
  let Ac2 := A * c2
  have h_Ac2 : Ac2.totalDegree ≤ 22 :=
    degree_mul h_A h_c2
  let norm_main := L15 - Ac2
  have h_norm_main : norm_main.totalDegree ≤ 22 :=
    degree_sub h_L15 h_Ac2
  let q_minus_F := q - F
  have h_q_minus_F : q_minus_F.totalDegree ≤ 1 :=
    degree_sub h_q h_F
  let C := q_minus_F - alpha
  have h_C : C.totalDegree ≤ 1 :=
    degree_sub h_q_minus_F h_alpha
  let aux_y2 := y * y
  have h_aux_y2 : aux_y2.totalDegree ≤ 2 :=
    degree_mul h_y h_y
  let hpm1 := h * UM
  have h_hpm1 : hpm1.totalDegree ≤ 7 :=
    degree_mul h_h h_UM
  let index_difference := R10b - hpm1
  have h_index_difference : index_difference.totalDegree ≤ 7 :=
    degree_sub h_R10b h_hpm1
  let gap_product := repunit * q_minus_F
  have h_gap_product : gap_product.totalDegree ≤ 2 :=
    degree_mul h_repunit h_q_minus_F
  let gap := gap_product + alpha
  have h_gap : gap.totalDegree ≤ 2 :=
    degree_add h_gap_product h_alpha
  let Lm1 := Lbig - 1
  have h_Lm1 : Lm1.totalDegree ≤ 2 :=
    degree_sub h_Lbig (degree_numeral 1)
  let rproduct := gap * Lm1
  have h_rproduct : rproduct.totalDegree ≤ 4 :=
    degree_mul h_gap h_Lm1
  let qMF := q * MF
  have h_qMF : qMF.totalDegree ≤ 1 :=
    degree_mul h_q h_MF
  let mask_factor := MC + qMF
  have h_mask_factor : mask_factor.totalDegree ≤ 1 :=
    degree_add h_MC h_qMF
  let mask := mask_factor * J
  have h_mask : mask.totalDegree ≤ 2 :=
    degree_mul h_mask_factor h_J
  let r_lhs := rproduct + mask
  have h_r_lhs : r_lhs.totalDegree ≤ 4 :=
    degree_add h_rproduct h_mask
  let norm_index := index_difference - r_lhs
  have h_norm_index : norm_index.totalDegree ≤ 7 :=
    degree_sub h_index_difference h_r_lhs
  let kinner := K0 + w
  have h_kinner : kinner.totalDegree ≤ 1 :=
    degree_add h_K0 h_w
  let innerC := kinner * C
  have h_innerC : innerC.totalDegree ≤ 2 :=
    degree_mul h_kinner h_C
  let transport_partial := innerC + q_minus_F
  have h_transport_partial : transport_partial.totalDegree ≤ 2 :=
    degree_add h_innerC h_q_minus_F
  let local_rhs := z * repunit
  have h_local_rhs : local_rhs.totalDegree ≤ 2 :=
    degree_mul h_z h_repunit
  let norm_transport := transport_partial - local_rhs
  have h_norm_transport : norm_transport.totalDegree ≤ 2 :=
    degree_sub h_transport_partial h_local_rhs
  let L16 := f * f
  have h_L16 : L16.totalDegree ≤ 2 :=
    degree_mul h_f h_f
  let auxiliary_Tf := T * f
  have h_auxiliary_Tf : auxiliary_Tf.totalDegree ≤ 2 :=
    degree_mul h_T h_f
  let auxiliary_Tf_minus_one := auxiliary_Tf - 1
  have h_auxiliary_Tf_minus_one : auxiliary_Tf_minus_one.totalDegree ≤ 2 :=
    degree_sub h_auxiliary_Tf (degree_numeral 1)
  let auxiliary_c_Tf := R10a * auxiliary_Tf_minus_one
  have h_auxiliary_c_Tf : auxiliary_c_Tf.totalDegree ≤ 7 :=
    degree_mul h_R10a h_auxiliary_Tf_minus_one
  let auxiliary_R_f2 := r_lhs * L16
  have h_auxiliary_R_f2 : auxiliary_R_f2.totalDegree ≤ 6 :=
    degree_mul h_r_lhs h_L16
  let aux_u_rhs := auxiliary_c_Tf - auxiliary_R_f2
  have h_aux_u_rhs : aux_u_rhs.totalDegree ≤ 7 :=
    degree_sub h_auxiliary_c_Tf h_auxiliary_R_f2
  let H2 := aux_u_rhs * aux_u_rhs
  have h_H2 : H2.totalDegree ≤ 14 :=
    degree_mul h_aux_u_rhs h_aux_u_rhs
  let aux_square_gap := H2 - aux_y2
  have h_aux_square_gap : aux_square_gap.totalDegree ≤ 14 :=
    degree_sub h_H2 h_aux_y2
  let aux_coefficient_root := i * c2
  have h_aux_coefficient_root : aux_coefficient_root.totalDegree ≤ 11 :=
    degree_mul h_i h_c2
  let R16 := aux_coefficient_root * aux_coefficient_root
  have h_R16 : R16.totalDegree ≤ 22 :=
    degree_mul h_aux_coefficient_root h_aux_coefficient_root
  let strong_square_scaled := A * R16
  have h_strong_square_scaled : strong_square_scaled.totalDegree ≤ 34 :=
    degree_mul h_A h_R16
  let aux_f2_minus_one := L16 - 1
  have h_aux_f2_minus_one : aux_f2_minus_one.totalDegree ≤ 2 :=
    degree_sub h_L16 (degree_numeral 1)
  let aux_reduced_coefficient := A * aux_f2_minus_one
  have h_aux_reduced_coefficient : aux_reduced_coefficient.totalDegree ≤ 14 :=
    degree_mul h_A h_aux_f2_minus_one
  let L17 := aux_reduced_coefficient * aux_square_gap
  have h_L17 : L17.totalDegree ≤ 28 :=
    degree_mul h_aux_reduced_coefficient h_aux_square_gap
  let norm_aux := L17 + aux_y2
  have h_norm_aux : norm_aux.totalDegree ≤ 28 :=
    degree_add h_L17 h_aux_y2
  let main_index := norm_main * norm_index
  have h_main_index : main_index.totalDegree ≤ 29 :=
    degree_mul h_norm_main h_norm_index
  let main_index_transport := main_index * norm_transport
  have h_main_index_transport : main_index_transport.totalDegree ≤ 31 :=
    degree_mul h_main_index h_norm_transport
  let residual_first := norm_first - 1
  have h_residual_first : residual_first.totalDegree ≤ 22 :=
    degree_sub h_norm_first (degree_numeral 1)
  let residual_aux := norm_aux - 1
  have h_residual_aux : residual_aux.totalDegree ≤ 28 :=
    degree_sub h_norm_aux (degree_numeral 1)
  let residual_strong := aux_f2_minus_one - strong_square_scaled
  have h_residual_strong : residual_strong.totalDegree ≤ 34 :=
    degree_sub h_aux_f2_minus_one h_strong_square_scaled
  let residual_main_index_transport := main_index_transport - 1
  have h_residual_main_index_transport : residual_main_index_transport.totalDegree ≤ 31 :=
    degree_sub h_main_index_transport (degree_numeral 1)
  let residual_first_square := residual_first * residual_first
  have h_residual_first_square : residual_first_square.totalDegree ≤ 44 :=
    degree_mul h_residual_first h_residual_first
  let residual_aux_square := residual_aux * residual_aux
  have h_residual_aux_square : residual_aux_square.totalDegree ≤ 56 :=
    degree_mul h_residual_aux h_residual_aux
  let residual_strong_square := residual_strong * residual_strong
  have h_residual_strong_square : residual_strong_square.totalDegree ≤ 68 :=
    degree_mul h_residual_strong h_residual_strong
  let residual_main_index_transport_square := residual_main_index_transport * residual_main_index_transport
  have h_residual_main_index_transport_square : residual_main_index_transport_square.totalDegree ≤ 62 :=
    degree_mul h_residual_main_index_transport h_residual_main_index_transport
  let sum_1 := residual_first_square + residual_aux_square
  have h_sum_1 : sum_1.totalDegree ≤ 56 :=
    degree_add h_residual_first_square h_residual_aux_square
  let sum_2 := sum_1 + residual_strong_square
  have h_sum_2 : sum_2.totalDegree ≤ 68 :=
    degree_add h_sum_1 h_residual_strong_square
  let polynomial := sum_2 + residual_main_index_transport_square
  have h_polynomial : polynomial.totalDegree ≤ 68 :=
    degree_add h_sum_2 h_residual_main_index_transport_square
  change (compactValue (fun j => MvPolynomial.C (p j)) MvPolynomial.X).totalDegree ≤ 68
  rw [← compactLiteralValue_eq_compactValue]
  change polynomial.totalDegree ≤ 68
  exact h_polynomial
-- END GENERATED P75 DEGREE CERTIFICATE

end DiophantineConsistency.ShortSystem
