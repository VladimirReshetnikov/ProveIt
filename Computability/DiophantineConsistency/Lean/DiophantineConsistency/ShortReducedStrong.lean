import DiophantineConsistency.ShortSystem
import DiophantineConsistency.TotalDegreeBound

/-!
# A degree-64 correction of the strong norm with fifteen positive variables

Add the first norm residual inside the strong norm's coefficient. The first
residual already vanishes at every zero, so this triangular change preserves
all integer zeros of the four-residual sum. Its highest terms cancel, and the
literal evaluator requires only one additional addition.
-/

namespace DiophantineConsistency.ShortReducedStrong

open ShortCircuit ShortSystem MvPolynomial

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The first norm residual is added before multiplying by `i²c²`. -/
def correctedStrong (b : Core R) : R :=
  b.f ^ 2 - (b.i ^ 2 * b.c ^ 2) * (b.delta * b.c ^ 2 + (b.n0 - 1))

theorem correctedStrong_eq (b : Core R) :
    correctedStrong b = strong b - (b.i * b.c) ^ 2 * (b.n0 - 1) := by
  unfold correctedStrong strong
  ring

theorem correctedStrong_eq_of_first (b : Core R) (h : b.n0 = 1) :
    correctedStrong b = strong b := by
  rw [correctedStrong_eq, h]
  ring

/-- Four squared residuals with the corrected strong norm. -/
def value (p : Fin 4 → R) (v : Fin 15 → R) : R :=
  let b := core p v
  compactResidualSum b.n0 b.n1 (auxiliary b) (correctedStrong b) b.nk b.nt

/-- The triangular correction preserves the complete integer zero set. -/
theorem value_zero_iff_compactValue_zero (p : Fin 4 → ℤ) (v : Fin 15 → ℤ) :
    value p v = 0 ↔ ShortSystem.compactValue p v = 0 := by
  rw [value, compactValue, compactResidualSum_zero_iff, compactResidualSum_zero_iff]
  constructor
  · rintro ⟨h0, ha, hs, ht⟩
    exact ⟨h0, ha, by rwa [correctedStrong_eq_of_first _ h0] at hs, ht⟩
  · rintro ⟨h0, ha, hs, ht⟩
    exact ⟨h0, ha, by rwa [correctedStrong_eq_of_first _ h0], ht⟩

/-- Positive zeros agree with the pinned P67 circuit, at identical coordinates. -/
theorem value_zero_iff_baselineValue_zero (p : Fin 4 → ℤ) (v : Fin 15 → ℤ)
    (hbeta : 0 < p 0) (hv : ∀ j, 0 < v j) :
    value p v = 0 ↔ ShortCircuit.baselineValue p v = 0 :=
  (value_zero_iff_compactValue_zero p v).trans
    ((compactValue_zero_iff_shortCircuit_zero p v hbeta hv).trans
      (ShortCircuit.value_zero_iff_baselineValue_zero p v hbeta hv))

-- BEGIN GENERATED P76 LITERAL EVALUATOR
/-- Literal evaluator of circuits/p76_sos.json, including every paid operation. -/
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
  let residual_first := norm_first - 1
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
  let i_square := i * i
  let strong_coefficient := i_square * c2
  let strong_corrected_main := Ac2 + residual_first
  let strong_square_scaled := strong_coefficient * strong_corrected_main
  let aux_f2_minus_one := L16 - 1
  let aux_reduced_coefficient := A * aux_f2_minus_one
  let L17 := aux_reduced_coefficient * aux_square_gap
  let norm_aux := L17 + aux_y2
  let main_index := norm_main * norm_index
  let main_index_transport := main_index * norm_transport
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
-- END GENERATED P76 LITERAL EVALUATOR

private def literalCoreValue (b : Core R) : R :=
  let c2 := b.c * b.c
  let residual_first := b.n0 - 1
  let i_square := b.i * b.i
  let strong_coefficient := i_square * c2
  let strong_corrected_main := b.delta * c2 + residual_first
  let strong_square_scaled := strong_coefficient * strong_corrected_main
  let aux_f2_minus_one := b.f * b.f - 1
  let norm_aux := b.delta * aux_f2_minus_one * b.gap + b.y * b.y
  let residual_aux := norm_aux - 1
  let residual_strong := aux_f2_minus_one - strong_square_scaled
  let residual_main_index_transport := b.n1 * b.nk * b.nt - 1
  (residual_first * residual_first + residual_aux * residual_aux +
    residual_strong * residual_strong) +
    residual_main_index_transport * residual_main_index_transport

private theorem literalValue_eq_core (p : Fin 4 → R) (v : Fin 15 → R) :
    literalValue p v = literalCoreValue (core p v) := rfl

/-- Exact agreement of the literal 76-operation DAG and the corrected expression. -/
theorem literalValue_eq_value (p : Fin 4 → R) (v : Fin 15 → R) :
    literalValue p v = value p v := by
  rw [literalValue_eq_core]
  change literalCoreValue (core p v) =
    compactResidualSum (core p v).n0 (core p v).n1 (auxiliary (core p v))
      (correctedStrong (core p v)) (core p v).nk (core p v).nt
  generalize core p v = b
  unfold literalCoreValue compactResidualSum auxiliary correctedStrong
  ring

theorem value_map (φ : R →+* S) (p : Fin 4 → R) (v : Fin 15 → R) :
    φ (value p v) = value (fun j => φ (p j)) (fun j => φ (v j)) := by
  simp only [value, compactResidualSum, correctedStrong, auxiliary, core,
    map_add, map_sub, map_mul, map_pow, map_one, map_ofNat]

/-- The actual integer polynomial, with the same fifteen witness coordinates. -/
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
  exact value_zero_iff_baselineValue_zero p v hbeta hv

/-- The cancellation behind the degree bound: the corrected strong coefficient
`δc² + (n₀ - 1)` has degree twenty, not the twenty-two of its summands. -/
private theorem correctedStrong_core (p : Fin 4 → R) (v : Fin 15 → R) :
    let q := p 0 * v 0 + 1
    let wn2 := v 9 * q
    let sn2 := v 8 * (q * q * q)
    let UM := wn2 * sn2
    let R10b := v 11 + v 12
    let ksn2 := R10b * sn2
    let R10a := ksn2 + v 11
    correctedStrong (core p v) = v 4 ^ 2 - (v 6 ^ 2 * R10a ^ 2) *
      (((2 * wn2 + 1) * sn2 ^ 2 + (4 * (UM + sn2) + 3)) * R10a ^ 2 +
        UM ^ 2 * v 11 * (2 * ksn2 + v 11) - wn2 * sn2 ^ 2 * R10b ^ 2 + v 10 ^ 2 - 1) := by
  simp only [correctedStrong, core]
  ring

theorem polynomial_totalDegree_le (p : Fin 4 → ℤ) :
    (polynomial p).totalDegree ≤ 64 := by
  have h := correctedStrong_core (fun j => MvPolynomial.C (p j))
    (MvPolynomial.X : Fin 15 → MvPolynomial (Fin 15) ℤ)
  dsimp only at h
  simp only [polynomial, value, compactResidualSum, auxiliary, h]
  dsimp only [core]
  total_degree_bound

end DiophantineConsistency.ShortReducedStrong
