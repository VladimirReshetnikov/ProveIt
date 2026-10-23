import DiophantineConsistency.ShortSystem

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

private theorem degree_main_norm {a c x g h : MvPolynomial (Fin 15) ℤ}
    (ha : a.totalDegree ≤ 6) (hc : c.totalDegree ≤ 5) (hx : x.totalDegree ≤ 2)
    (hg : g.totalDegree ≤ 7) (hh : h.totalDegree ≤ 6) :
    ((a * c + x + g) ^ 2 - (a ^ 2 + h) * c ^ 2).totalDegree ≤ 18 := by
  have he : (a * c + x + g) ^ 2 - (a ^ 2 + h) * c ^ 2 =
      x ^ 2 + 2 * (a * c) * (x + g) + 2 * x * g + g ^ 2 - h * c ^ 2 := by ring
  rw [he]
  have htwo := degree_numeral 2
  have hxx := degree_mul hx hx
  have hacxg := degree_mul (degree_mul htwo (degree_mul ha hc)) (degree_add hx hg)
  have hxg := degree_mul (degree_mul htwo hx) hg
  have hgg := degree_mul hg hg
  have hhcc := degree_mul hh (degree_mul hc hc)
  simpa [pow_two] using
    degree_sub (degree_add (degree_add (degree_add hxx hacxg) hxg) hgg) hhcc

-- BEGIN GENERATED P73 DEGREE CERTIFICATE
theorem polynomial_totalDegree_le (p : Fin 4 → ℤ) :
    (polynomial p).totalDegree ≤ 80 := by
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
  have h_norm_main : norm_main.totalDegree ≤ 18 := by
    have hform : norm_main = (R12 * R10a + wn2 + gam) ^ 2 - (R12 ^ 2 + a4m5) * R10a ^ 2 := by
      dsimp only [norm_main, L15, R14, D1, cam2, Ac2, A, a_square, c2]
      ring
    rw [hform]
    exact degree_main_norm h_R12 h_R10a h_wn2 h_gam h_a4m5
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
  let first_main := norm_first * norm_main
  have h_first_main : first_main.totalDegree ≤ 40 :=
    degree_mul h_norm_first h_norm_main
  let aux_index := norm_aux * norm_index
  have h_aux_index : aux_index.totalDegree ≤ 35 :=
    degree_mul h_norm_aux h_norm_index
  let aux_index_transport := aux_index * norm_transport
  have h_aux_index_transport : aux_index_transport.totalDegree ≤ 37 :=
    degree_mul h_aux_index h_norm_transport
  let residual_first_main := first_main - 1
  have h_residual_first_main : residual_first_main.totalDegree ≤ 40 :=
    degree_sub h_first_main (degree_numeral 1)
  let residual_aux_index_transport := aux_index_transport - 1
  have h_residual_aux_index_transport : residual_aux_index_transport.totalDegree ≤ 37 :=
    degree_sub h_aux_index_transport (degree_numeral 1)
  let residual_strong := aux_f2_minus_one - strong_square_scaled
  have h_residual_strong : residual_strong.totalDegree ≤ 34 :=
    degree_sub h_aux_f2_minus_one h_strong_square_scaled
  let first_main_square := residual_first_main * residual_first_main
  have h_first_main_square : first_main_square.totalDegree ≤ 80 :=
    degree_mul h_residual_first_main h_residual_first_main
  let aux_index_transport_square := residual_aux_index_transport * residual_aux_index_transport
  have h_aux_index_transport_square : aux_index_transport_square.totalDegree ≤ 74 :=
    degree_mul h_residual_aux_index_transport h_residual_aux_index_transport
  let strong_residual_square := residual_strong * residual_strong
  have h_strong_residual_square : strong_residual_square.totalDegree ≤ 68 :=
    degree_mul h_residual_strong h_residual_strong
  let partial_sum := first_main_square + aux_index_transport_square
  have h_partial_sum : partial_sum.totalDegree ≤ 80 :=
    degree_add h_first_main_square h_aux_index_transport_square
  let polynomial := partial_sum + strong_residual_square
  have h_polynomial : polynomial.totalDegree ≤ 80 :=
    degree_add h_partial_sum h_strong_residual_square
  change (value (fun j => MvPolynomial.C (p j)) MvPolynomial.X).totalDegree ≤ 80
  rw [← literalValue_eq_value]
  change polynomial.totalDegree ≤ 80
  exact h_polynomial
-- END GENERATED P73 DEGREE CERTIFICATE

end DiophantineConsistency.ShortFrontier
