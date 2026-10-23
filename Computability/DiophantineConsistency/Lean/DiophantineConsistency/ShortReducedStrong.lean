import DiophantineConsistency.ShortSystem

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

private theorem degree_add {p q : MvPolynomial (Fin 15) ℤ} {a b : ℕ}
    (hp : p.totalDegree ≤ a) (hq : q.totalDegree ≤ b) :
    (p + q).totalDegree ≤ max a b :=
  (MvPolynomial.totalDegree_add p q).trans (max_le_max hp hq)

private theorem degree_sub {p q : MvPolynomial (Fin 15) ℤ} {a b : ℕ}
    (hp : p.totalDegree ≤ a) (hq : q.totalDegree ≤ b) :
    (p - q).totalDegree ≤ max a b :=
  (MvPolynomial.totalDegree_sub p q).trans (max_le_max hp hq)

private theorem degree_mul {p q : MvPolynomial (Fin 15) ℤ} {a b : ℕ}
    (hp : p.totalDegree ≤ a) (hq : q.totalDegree ≤ b) :
    (p * q).totalDegree ≤ a + b :=
  (MvPolynomial.totalDegree_mul p q).trans (Nat.add_le_add hp hq)

private theorem degree_numeral (n : ℕ) :
    (n : MvPolynomial (Fin 15) ℤ).totalDegree ≤ 0 := by
  simpa only [map_natCast] using
    (MvPolynomial.totalDegree_C (σ := Fin 15) (n : ℤ)).le

-- BEGIN GENERATED P76 DEGREE CERTIFICATE
/-- A checked cancellation lowers the strong residual to degree32. -/
theorem polynomial_totalDegree_le (p : Fin 4 → ℤ) :
    (polynomial p).totalDegree ≤ 64 := by
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
  let residual_first := norm_first - 1
  have h_residual_first : residual_first.totalDegree ≤ 22 :=
    degree_sub h_norm_first (degree_numeral 1)
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
  let i_square := i * i
  have h_i_square : i_square.totalDegree ≤ 2 :=
    degree_mul h_i h_i
  let strong_coefficient := i_square * c2
  have h_strong_coefficient : strong_coefficient.totalDegree ≤ 12 :=
    degree_mul h_i_square h_c2
  let strong_corrected_main := Ac2 + residual_first
  let degree_two_x := 2 * wn2
  have h_degree_two_x : degree_two_x.totalDegree ≤ 2 :=
    degree_mul (degree_numeral 2) h_wn2
  let degree_two_x_plus_one := degree_two_x + 1
  have h_degree_two_x_plus_one : degree_two_x_plus_one.totalDegree ≤ 2 :=
    degree_add h_degree_two_x (degree_numeral 1)
  let degree_y_square := sn2 * sn2
  have h_degree_y_square : degree_y_square.totalDegree ≤ 8 :=
    degree_mul h_sn2 h_sn2
  let degree_xy_square := degree_two_x_plus_one * degree_y_square
  have h_degree_xy_square : degree_xy_square.totalDegree ≤ 10 :=
    degree_mul h_degree_two_x_plus_one h_degree_y_square
  let degree_inner := degree_xy_square + a4m5
  have h_degree_inner : degree_inner.totalDegree ≤ 10 :=
    degree_add h_degree_xy_square h_a4m5
  let degree_first := degree_inner * c2
  have h_degree_first : degree_first.totalDegree ≤ 20 :=
    degree_mul h_degree_inner h_c2
  let degree_E_square := UM * UM
  have h_degree_E_square : degree_E_square.totalDegree ≤ 12 :=
    degree_mul h_UM h_UM
  let degree_E_eta := degree_E_square * eta
  have h_degree_E_eta : degree_E_eta.totalDegree ≤ 13 :=
    degree_mul h_degree_E_square h_eta
  let degree_two_kY := 2 * ksn2
  have h_degree_two_kY : degree_two_kY.totalDegree ≤ 5 :=
    degree_mul (degree_numeral 2) h_ksn2
  let degree_two_kY_eta := degree_two_kY + eta
  have h_degree_two_kY_eta : degree_two_kY_eta.totalDegree ≤ 5 :=
    degree_add h_degree_two_kY h_eta
  let degree_second := degree_E_eta * degree_two_kY_eta
  have h_degree_second : degree_second.totalDegree ≤ 18 :=
    degree_mul h_degree_E_eta h_degree_two_kY_eta
  let degree_n := wn2 * degree_y_square
  have h_degree_n : degree_n.totalDegree ≤ 10 :=
    degree_mul h_wn2 h_degree_y_square
  let degree_k_square := R10b * R10b
  have h_degree_k_square : degree_k_square.totalDegree ≤ 2 :=
    degree_mul h_R10b h_R10b
  let degree_third := degree_n * degree_k_square
  have h_degree_third : degree_third.totalDegree ≤ 12 :=
    degree_mul h_degree_n h_degree_k_square
  let degree_sum := degree_first + degree_second
  have h_degree_sum : degree_sum.totalDegree ≤ 20 :=
    degree_add h_degree_first h_degree_second
  let degree_diff := degree_sum - degree_third
  have h_degree_diff : degree_diff.totalDegree ≤ 20 :=
    degree_sub h_degree_sum h_degree_third
  let degree_plus_tau := degree_diff + tau_square
  have h_degree_plus_tau : degree_plus_tau.totalDegree ≤ 20 :=
    degree_add h_degree_diff h_tau_square
  let degree_corrected := degree_plus_tau - 1
  have h_degree_corrected : degree_corrected.totalDegree ≤ 20 :=
    degree_sub h_degree_plus_tau (degree_numeral 1)
  have correction_identity : strong_corrected_main = degree_corrected := by
    dsimp [strong_corrected_main, Ac2, A, a_square, a4m5, a4, R12, c2, R10a,
      residual_first, norm_first, first_product, first_root_base, first_next,
      ksn2, UM, tau_square, degree_corrected, degree_plus_tau, degree_diff,
      degree_sum, degree_first, degree_inner, degree_xy_square, degree_two_x_plus_one,
      degree_two_x, degree_y_square, degree_second, degree_E_eta, degree_E_square,
      degree_two_kY_eta, degree_two_kY, degree_third, degree_n, degree_k_square]
    ring
  have h_strong_corrected_main : strong_corrected_main.totalDegree ≤ 20 := by
    rw [correction_identity]
    exact h_degree_corrected
  let strong_square_scaled := strong_coefficient * strong_corrected_main
  have h_strong_square_scaled : strong_square_scaled.totalDegree ≤ 32 :=
    degree_mul h_strong_coefficient h_strong_corrected_main
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
  let residual_aux := norm_aux - 1
  have h_residual_aux : residual_aux.totalDegree ≤ 28 :=
    degree_sub h_norm_aux (degree_numeral 1)
  let residual_strong := aux_f2_minus_one - strong_square_scaled
  have h_residual_strong : residual_strong.totalDegree ≤ 32 :=
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
  have h_residual_strong_square : residual_strong_square.totalDegree ≤ 64 :=
    degree_mul h_residual_strong h_residual_strong
  let residual_main_index_transport_square := residual_main_index_transport * residual_main_index_transport
  have h_residual_main_index_transport_square : residual_main_index_transport_square.totalDegree ≤ 62 :=
    degree_mul h_residual_main_index_transport h_residual_main_index_transport
  let sum_1 := residual_first_square + residual_aux_square
  have h_sum_1 : sum_1.totalDegree ≤ 56 :=
    degree_add h_residual_first_square h_residual_aux_square
  let sum_2 := sum_1 + residual_strong_square
  have h_sum_2 : sum_2.totalDegree ≤ 64 :=
    degree_add h_sum_1 h_residual_strong_square
  let polynomial := sum_2 + residual_main_index_transport_square
  have h_polynomial : polynomial.totalDegree ≤ 64 :=
    degree_add h_sum_2 h_residual_main_index_transport_square
  change (value (fun j => MvPolynomial.C (p j)) MvPolynomial.X).totalDegree ≤ 64
  rw [← literalValue_eq_value]
  change polynomial.totalDegree ≤ 64
  exact h_polynomial
-- END GENERATED P76 DEGREE CERTIFICATE

end DiophantineConsistency.ShortReducedStrong
