import DiophantineConsistency.ShortSystem
import DiophantineConsistency.TotalDegreeBound

/-!
# Three grouped residuals: 73 operations and degree at most 80

This alternative keeps the same positive zero set and fifteen unknowns as
P75, at a different degree/operation tradeoff. Its correctness remains local
to the P67 arithmetic equation; it assumes no native-window compiler theorem.
-/

namespace DiophantineConsistency.ShortFrontier

open ShortCircuit ShortSystem MvPolynomial

variable {R S : Type*} [CommRing R] [CommRing S]

def residuals (n0 n1 na ns nk nt : R) : R :=
  (n0 * n1 - 1) ^ 2 + (na * nk * nt - 1) ^ 2 + (ns - 1) ^ 2

theorem residuals_zero_iff (n0 n1 na ns nk nt : ℤ) :
    residuals n0 n1 na ns nk nt = 0 ↔
      n0 * n1 = 1 ∧ na * nk * nt = 1 ∧ ns = 1 := by
  simpa only [residuals, ShortSystem.residualSum, one_mul, sub_self,
    zero_pow (by decide : 2 ≠ 0), add_zero, and_true, true_and] using
    ShortSystem.residualSum_zero_iff (n0 * n1) (na * nk * nt) ns 1 1 1

def value (p : Fin 4 → R) (v : Fin 15 → R) : R :=
  let b := core p v
  residuals b.n0 b.n1 (auxiliary b) (strong b) b.nk b.nt

theorem value_zero_iff_shortCircuit_zero (p : Fin 4 → ℤ) (v : Fin 15 → ℤ)
    (hbeta : 0 < p 0) (hv : ∀ j, 0 < v j) :
    value p v = 0 ↔ ShortCircuit.value p v = 0 := by
  have hfive := ShortSystem.value_zero_iff_shortCircuit_zero p v hbeta hv
  have hout : ShortCircuit.value p v =
      (core p v).n0 * (core p v).n1 * auxiliary (core p v) * (core p v).nk *
        (core p v).nt * strong (core p v) - 1 := by
    rw [value_eq_core, coreValue_eq]
    unfold auxiliary strong
    ring
  rw [value, residuals_zero_iff]
  constructor
  · rintro ⟨h01, hakt, hs⟩
    rw [hout]
    calc
      _ = ((core p v).n0 * (core p v).n1) *
          (auxiliary (core p v) * (core p v).nk * (core p v).nt) * strong (core p v) - 1 := by ring
      _ = 0 := by rw [h01, hakt, hs]; norm_num
  · intro h
    obtain ⟨h0, h1, ha, hs, hkt⟩ :=
      (ShortSystem.residualSum_zero_iff _ _ _ _ _ _).mp (hfive.mpr h)
    exact ⟨by rw [h0, h1]; norm_num, by rw [ha, one_mul, hkt], hs⟩

theorem value_map (φ : R →+* S) (p : Fin 4 → R) (v : Fin 15 → R) :
    φ (value p v) = value (fun j => φ (p j)) (fun j => φ (v j)) := by
  simp only [value, residuals, auxiliary, strong, core,
    map_add, map_sub, map_mul, map_pow, map_one, map_ofNat]

noncomputable def polynomial (p : Fin 4 → ℤ) : MvPolynomial (Fin 15) ℤ :=
  value (fun j => MvPolynomial.C (p j)) MvPolynomial.X

theorem eval_polynomial (p : Fin 4 → ℤ) (v : Fin 15 → ℤ) :
    MvPolynomial.eval v (polynomial p) = value p v := by
  simpa only [polynomial, MvPolynomial.eval_C, MvPolynomial.eval_X] using
    value_map (MvPolynomial.eval v) (fun j => MvPolynomial.C (p j)) MvPolynomial.X

theorem eval_polynomial_zero_iff_baselineValue_zero
    (p : Fin 4 → ℤ) (v : Fin 15 → ℤ) (hbeta : 0 < p 0) (hv : ∀ j, 0 < v j) :
    MvPolynomial.eval v (polynomial p) = 0 ↔ ShortCircuit.baselineValue p v = 0 := by
  rw [eval_polynomial]
  exact (value_zero_iff_shortCircuit_zero p v hbeta hv).trans
    (ShortCircuit.value_zero_iff_baselineValue_zero p v hbeta hv)

-- BEGIN GENERATED P73 LITERAL EVALUATOR
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
  let first_main := norm_first * norm_main
  let aux_index := norm_aux * norm_index
  let aux_index_transport := aux_index * norm_transport
  let residual_first_main := first_main - 1
  let residual_aux_index_transport := aux_index_transport - 1
  let residual_strong := aux_f2_minus_one - strong_square_scaled
  let first_main_square := residual_first_main * residual_first_main
  let aux_index_transport_square := residual_aux_index_transport * residual_aux_index_transport
  let strong_residual_square := residual_strong * residual_strong
  let partial_sum := first_main_square + aux_index_transport_square
  let polynomial := partial_sum + strong_residual_square
  polynomial
-- END GENERATED P73 LITERAL EVALUATOR

private def literalCoreValue (b : Core R) : R :=
  let c2 := b.c * b.c
  let f2 := b.f * b.f
  let root := b.i * c2
  let scaled := b.delta * (root * root)
  let f2m1 := f2 - 1
  let na := b.delta * f2m1 * b.gap + b.y * b.y
  let first_main := b.n0 * b.n1
  let aux_index := na * b.nk
  let aux_index_transport := aux_index * b.nt
  let r0 := first_main - 1
  let ra := aux_index_transport - 1
  let rs := f2m1 - scaled
  (r0 * r0 + ra * ra) + rs * rs

private theorem literalValue_eq_core (p : Fin 4 → R) (v : Fin 15 → R) :
    literalValue p v = literalCoreValue (core p v) := rfl

theorem literalValue_eq_value (p : Fin 4 → R) (v : Fin 15 → R) :
    literalValue p v = value p v := by
  rw [literalValue_eq_core]
  change literalCoreValue (core p v) = residuals (core p v).n0 (core p v).n1
    (auxiliary (core p v)) (strong (core p v)) (core p v).nk (core p v).nt
  generalize core p v = b
  unfold literalCoreValue residuals auxiliary strong
  ring

/-- The cancellation behind the degree bound: the main norm `(R₁₂c + x + g)² - Ac²`
has degree eighteen, not the twenty-two of its two terms. -/
private theorem core_n1 (p : Fin 4 → R) (v : Fin 15 → R) :
    let q := p 0 * v 0 + 1
    let wn2 := v 9 * q
    let sn2 := v 8 * (q * q * q)
    let R10a := (v 11 + v 12) * sn2 + v 11
    let R12 := wn2 * sn2 + sn2
    let a4m5 := 4 * R12 + 3
    let gam := v 14 * a4m5
    (core p v).n1 = wn2 ^ 2 + 2 * (R12 * R10a) * (wn2 + gam) + 2 * wn2 * gam + gam ^ 2 -
      a4m5 * R10a ^ 2 := by
  simp only [core]
  ring

theorem polynomial_totalDegree_le (p : Fin 4 → ℤ) :
    (polynomial p).totalDegree ≤ 80 := by
  have h := core_n1 (fun j => MvPolynomial.C (p j))
    (MvPolynomial.X : Fin 15 → MvPolynomial (Fin 15) ℤ)
  dsimp only at h
  simp only [polynomial, value, residuals, auxiliary, strong, h]
  dsimp only [core]
  total_degree_bound

end DiophantineConsistency.ShortFrontier
