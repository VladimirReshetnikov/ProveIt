import DiophantineConsistency.Mixed121.Short15Root
import DiophantineConsistency.Compact44.P64Norm

/-! # Fifteen-positive forms: unit splits and norm exclusions

In the ring of differences of a model of `𝗜𝚺₁` (discrete, with reduction modulo
four):

* the excluded values: `N0 ≠ −1` (consecutive-product negative Pell,
  `ModelArithmetic.consecutive_ne_neg_one`), `N1 ≠ −1` and the normalized
  strong norm `≠ −1` (`Δ = (a+2)² − 1`, modulo four), `Na ≠ −1` and
  `S + 1 ≠ −1` (modulo four: `Aaux = Δ(f² − 1)` is `0` or `1`);
* the excluded zeros: `N0 ≠ 0` and `N1 ≠ 0` (`ModelArithmetic.near_square_ne_zero`),
  and `Na ≠ 0` at `y = V + e` once `S² ≤ 3` (`P64Norm.na_ne_zero` for `f ≥ 2`;
  for `f = 1`, `S = (ic²)² ≥ 81`);
* the splits: a product of six units, and sums of four or five squares. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
noncomputable section
namespace Short15Units
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency
open AdaptiveEquationSyntax2011 ModelDifferenceRing DiscreteOrderedRingFacts
open Short15Graph Short15Root
open P72Root (ι_tsub)
open P72Aux (ι_absdiff_sq)
open DiophantineConsistency.ArithmeticPellHalfIndex (absdiff)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## Units -/

theorem unit_pm {x y : DiffRing V} (h : x * y = 1 ∨ x * y = -1) :
    (x = 1 ∨ x = -1) ∧ (y = 1 ∨ y = -1) := by
  rcases h with h | h
  · exact ⟨eq_one_or_neg_one_of_mul_eq_one ModelArithmetic.model_discrete h,
      eq_one_or_neg_one_of_mul_eq_one ModelArithmetic.model_discrete (by rw [mul_comm]; exact h)⟩
  · have h' : x * (-y) = 1 := by rw [mul_neg, h, neg_neg]
    refine ⟨eq_one_or_neg_one_of_mul_eq_one ModelArithmetic.model_discrete h', ?_⟩
    rcases eq_one_or_neg_one_of_mul_eq_one ModelArithmetic.model_discrete
        (show (-y) * x = 1 by rw [mul_comm]; exact h') with h1 | h1
    · right; linear_combination -h1
    · left; linear_combination -h1

theorem sign_of_mul {x y : DiffRing V} (h : x * y = 1) :
    (x = 1 ∧ y = 1) ∨ (x = -1 ∧ y = -1) := by
  rcases eq_one_or_neg_one_of_mul_eq_one ModelArithmetic.model_discrete h with h1 | h1
  · left; rw [h1, one_mul] at h; exact ⟨h1, h⟩
  · right; refine ⟨h1, ?_⟩; rw [h1] at h; linear_combination -h

/-- A product of six units with four of them `≠ −1`. -/
theorem prod6_split {n0 n1 na nk nt ns : DiffRing V} (h : n0 * n1 * na * nk * nt * ns = 1)
    (h0 : n0 ≠ -1) (h1 : n1 ≠ -1) (ha : na ≠ -1) (hs : ns ≠ -1) :
    n0 = 1 ∧ n1 = 1 ∧ na = 1 ∧ ns = 1 ∧ ((nk = 1 ∧ nt = 1) ∨ (nk = -1 ∧ nt = -1)) := by
  have u5 := unit_pm (Or.inl h)
  have u4 := unit_pm u5.1
  have u3 := unit_pm u4.1
  have u2 := unit_pm u3.1
  have u1 := unit_pm u2.1
  have e0 : n0 = 1 := u1.1.resolve_right h0
  have e1 : n1 = 1 := u1.2.resolve_right h1
  have ea : na = 1 := u2.2.resolve_right ha
  have es : ns = 1 := u5.2.resolve_right hs
  rw [e0, e1, ea, es] at h
  have hk : nk * nt = 1 := by simpa only [one_mul, mul_one] using h
  exact ⟨e0, e1, ea, es, sign_of_mul hk⟩

/-! ## Excluded values modulo four -/

theorem na_ne_neg (p : Fin 4 → ℤ) (w : Fin 15 → DiffRing V) (Vr y : DiffRing V) :
    rNa (vals p w).Aaux Vr y ≠ -1 := by
  intro h
  have hA : (vals p w).Aaux = ((vals p w).a * (vals p w).a + (4 * (vals p w).a + 3)) * (w 4 * w 4 - 1) :=
    rfl
  rw [rNa, hA] at h
  have hm := congrArg ModelArithmetic.mod4 h
  simp only [map_add, map_mul, map_sub, map_one, map_neg, map_ofNat] at hm
  have bad : ∀ a f x y : ZMod 4,
      (a * a + (4 * a + 3)) * (f * f - 1) * (x * x - y * y) + y * y ≠ -1 := by decide
  exact bad _ _ _ _ hm

theorem ns_ne_neg (p : Fin 4 → ℤ) (w : Fin 15 → DiffRing V) (i : DiffRing V) :
    rS p w i + 1 ≠ -1 := by
  intro h
  have hA : (vals p w).Aaux = ((vals p w).a * (vals p w).a + (4 * (vals p w).a + 3)) * (w 4 * w 4 - 1) :=
    rfl
  rw [rS, hA] at h
  have hm := congrArg ModelArithmetic.mod4 h
  simp only [map_add, map_mul, map_sub, map_one, map_neg, map_ofNat] at hm
  have bad : ∀ a f t : ZMod 4, t * t - (a * a + (4 * a + 3)) * (f * f - 1) + 1 ≠ -1 := by decide
  exact bad _ _ _ hm

/-- `f² − ((a+2)² − 1)t² ≠ −1`, modulo four. -/
theorem pell_ne_neg (a f t : DiffRing V) : f * f - (a * a + (4 * a + 3)) * (t * t) ≠ -1 := by
  intro h
  have hm := congrArg ModelArithmetic.mod4 h
  simp only [map_add, map_mul, map_sub, map_one, map_neg, map_ofNat] at hm
  have bad : ∀ a f t : ZMod 4, f * f - (a * a + (4 * a + 3)) * (t * t) ≠ -1 := by decide
  exact bad _ _ _ hm

theorem n1_ne_neg (p : Fin 4 → ℤ) (w : Fin 15 → DiffRing V) : rN1 p w ≠ -1 := by
  have hΔ : (vals p w).Delta = (vals p w).a * (vals p w).a + (4 * (vals p w).a + 3) := rfl
  rw [rN1, hΔ]
  exact pell_ne_neg _ _ _

theorem nn_ne_neg (p : Fin 4 → ℤ) (w : Fin 15 → DiffRing V) (i : DiffRing V) :
    w 4 * w 4 - (vals p w).Delta * ((i * ((vals p w).c * (vals p w).c)) * (i * ((vals p w).c * (vals p w).c))) ≠
      -1 := by
  have hΔ : (vals p w).Delta = (vals p w).a * (vals p w).a + (4 * (vals p w).a + 3) := rfl
  rw [hΔ]
  exact pell_ne_neg _ _ _

/-! ## Excluded values in the model -/

theorem q_two (p : Fin 4 → ℕ) (v : Fin 15 → V) (hv : ∀ j, 0 < v j) (hb : 0 < (p 0 : V)) :
    (2 : V) ≤ qV p v := by
  have h1 : 1 ≤ (p 0 : V) * v 0 :=
    one_le_mul_of_one_le_of_one_le (pos_iff_one_le.mp hb) (pos_iff_one_le.mp (hv 0))
  simpa [qV, one_add_one_eq_two] using (add_le_add_iff_right (1 : V)).mpr h1

theorem n_two (p : Fin 4 → ℕ) (v : Fin 15 → V) (hv : ∀ j, 0 < v j) (hb : 0 < (p 0 : V)) :
    (2 : V) ≤ EV p v * YV p v := by
  have hq2 := q_two p v hv hb
  have hq0 : 0 < qV p v := lt_of_lt_of_le (by norm_num) hq2
  have hY0 : 0 < YV p v := mul_pos (hv 8) (mul_pos (mul_pos hq0 hq0) hq0)
  have hX2 : 2 ≤ XV p v :=
    le_trans hq2 (le_mul_of_one_le_left (Arithmetic.zero_le _) (pos_iff_one_le.mp (hv 9)))
  show 2 ≤ XV p v * YV p v * YV p v
  rw [mul_assoc]
  exact le_trans hX2 (le_mul_of_one_le_right (Arithmetic.zero_le _)
    (one_le_mul_of_one_le_of_one_le (pos_iff_one_le.mp hY0) (pos_iff_one_le.mp hY0)))

private theorem hell (p : Fin 4 → ℕ) (v : Fin 15 → V) :
    ι (ellV p v) = ι (EV p v * YV p v) * ι (kV v) := by
  simp only [ellV, map_mul]; ring

theorem n0_ne_neg (p : Fin 4 → ℕ) (v : Fin 15 → V) (hv : ∀ j, 0 < v j) (hb : 0 < (p 0 : V))
    (τ : DiffRing V) : rN0 (fun j => (p j : ℤ)) (fun j => ι (v j)) τ ≠ -1 := by
  intro hneg
  apply ModelArithmetic.consecutive_ne_neg_one (ι (EV p v * YV p v)) τ (ι (kV v))
    (ModelArithmetic.two_le_ι (n_two p v hv hb))
  rw [rN0, c_ell, c_k, hell] at hneg
  linear_combination hneg

theorem n0_ne_zero (p : Fin 4 → ℕ) (v : Fin 15 → V) (hv : ∀ j, 0 < v j) (hb : 0 < (p 0 : V))
    (τ : DiffRing V) : rN0 (fun j => (p j : ℤ)) (fun j => ι (v j)) τ ≠ 0 := by
  intro h0
  have hn := ModelArithmetic.two_le_ι (n_two p v hv hb)
  have hk : ι (kV v) ≠ 0 := ne_of_gt (ι_pos' (add_pos (hv 11) (hv 12)))
  apply ModelArithmetic.near_square_ne_zero (2 * ι (EV p v * YV p v) + 1) (2 * τ) (ι (kV v))
    (by linarith) hk
  rw [rN0, c_ell, c_k, hell] at h0
  linear_combination 4 * h0

theorem n1_ne_zero (p : Fin 4 → ℕ) (v : Fin 15 → V) (hv : ∀ j, 0 < v j) :
    rN1 (fun j => (p j : ℤ)) (fun j => ι (v j)) ≠ 0 := by
  intro h0
  have hc0 : 0 < cV p v := add_pos_of_nonneg_of_pos (Arithmetic.zero_le _) (hv 11)
  have hc : ι (cV p v) ≠ 0 := ne_of_gt (ι_pos' hc0)
  have ha := ι_nonneg (aV p v)
  apply ModelArithmetic.near_square_ne_zero (ι (aV p v) + 2) (ι (DV p v)) (ι (cV p v)) (by linarith) hc
  rw [rN1, c_D, c_Delta, c_c] at h0
  have hΔ : ι (ΔV p v) = ι (aV p v) * ι (aV p v) + (4 * ι (aV p v) + 3) := by
    simp only [ΔV, HV, map_add, map_mul, map_ofNat]
  rw [hΔ] at h0
  linear_combination h0

/-- `Na ≠ 0` at `y = V + e`, once the strong residual is small. -/
theorem na_ne_zero (p : Fin 4 → ℕ) (v : Fin 15 → V) (hv : ∀ j, 0 < v j) (hb : 0 < (p 0 : V))
    (Vr : DiffRing V)
    (hsmall : rS (fun j => (p j : ℤ)) (fun j => ι (v j)) (ι (v 6)) *
      rS (fun j => (p j : ℤ)) (fun j => ι (v j)) (ι (v 6)) ≤ 3) :
    rNa (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).Aaux Vr (Vr + ι (v 13)) ≠ 0 := by
  intro h0
  have hf1 : 1 ≤ v 4 * v 4 :=
    one_le_mul_of_one_le_of_one_le (pos_iff_one_le.mp (hv 4)) (pos_iff_one_le.mp (hv 4))
  have hq2 := q_two p v hv hb
  have hq0 : 0 < qV p v := lt_of_lt_of_le (by norm_num) hq2
  have hY0 : 0 < YV p v := mul_pos (hv 8) (mul_pos (mul_pos hq0 hq0) hq0)
  set A : V := ΔV p v * (v 4 * v 4 - 1) with hA
  have cA : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).Aaux = ι A := by
    rw [c_Aaux, c_Delta, hA, map_mul, ι_tsub hf1, map_mul, map_one]
  obtain ⟨P0, N0, hPN⟩ := exists_mk Vr
  rw [mk_eq_sub] at hPN
  have hna : rNa (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).Aaux Vr (Vr + ι (v 13)) =
      ι A * (ι (absdiff P0 N0) * ι (absdiff P0 N0) -
        ι (absdiff (P0 + v 13) N0) * ι (absdiff (P0 + v 13) N0)) +
        ι (absdiff (P0 + v 13) N0) * ι (absdiff (P0 + v 13) N0) := by
    rw [rNa, cA, hPN, ι_absdiff_sq, ι_absdiff_sq, map_add]; ring
  rcases (pos_iff_one_le.mp (hv 4)).lt_or_eq with hf2 | hf1'
  · -- f ≥ 2: A ≥ 2
    have hA2 : 2 ≤ A := by
      have hΔ3 : 3 ≤ ΔV p v := by
        show 3 ≤ aV p v * aV p v + (4 * aV p v + 3)
        exact le_add_self.trans' le_add_self
      have hff : 4 ≤ v 4 * v 4 := by
        have h2 : 2 ≤ v 4 := by simpa [one_add_one_eq_two] using lt_iff_succ_le.mp hf2
        calc (4 : V) = 2 * 2 := by norm_num
          _ ≤ v 4 * v 4 := mul_le_mul h2 h2 (by norm_num) (Arithmetic.zero_le _)
      have hf3 : 3 ≤ v 4 * v 4 - 1 := by
        apply (add_le_add_iff_right (1 : V)).mp
        rw [tsub_add_cancel_of_le hf1]
        calc (3 : V) + 1 = 4 := by norm_num
          _ ≤ v 4 * v 4 := hff
      calc (2 : V) ≤ 3 * 3 := by norm_num
        _ ≤ ΔV p v * (v 4 * v 4 - 1) := mul_le_mul hΔ3 hf3 (by norm_num) (Arithmetic.zero_le _)
    apply P64Norm.na_ne_zero A P0 N0 (v 13) hA2 (hv 13)
    apply ι_injective
    simp only [map_add, map_mul]
    rw [hna] at h0
    linear_combination h0
  · -- f = 1: the strong residual is too large
    have hA0 : A = 0 := by rw [hA, ← hf1', mul_one, tsub_self, mul_zero]
    have hc3 : (3 : V) ≤ cV p v := by
      have hk2 : 2 ≤ kV v := by
        simpa [kV, one_add_one_eq_two] using
          add_le_add (pos_iff_one_le.mp (hv 11)) (pos_iff_one_le.mp (hv 12))
      calc (3 : V) = 2 * 1 + 1 := by norm_num
        _ ≤ kV v * YV p v + v 11 := add_le_add (mul_le_mul hk2 (pos_iff_one_le.mp hY0)
            (by norm_num) (Arithmetic.zero_le _)) (pos_iff_one_le.mp (hv 11))
    have hI : (9 : V) ≤ v 6 * (cV p v * cV p v) := by
      calc (9 : V) = 1 * (3 * 3) := by norm_num
        _ ≤ v 6 * (cV p v * cV p v) := mul_le_mul (pos_iff_one_le.mp (hv 6))
            (mul_le_mul hc3 hc3 (by norm_num) (Arithmetic.zero_le _)) (by norm_num) (Arithmetic.zero_le _)
    have hS : rS (fun j => (p j : ℤ)) (fun j => ι (v j)) (ι (v 6)) =
        ι (v 6 * (cV p v * cV p v)) * ι (v 6 * (cV p v * cV p v)) := by
      rw [rS, cA, hA0, map_zero, _root_.sub_zero, c_c]; simp only [map_mul]
    have hI' : (9 : DiffRing V) ≤ ι (v 6 * (cV p v * cV p v)) := by
      have h := (ι_le_ι (V := V)).mpr hI; rwa [map_ofNat] at h
    rw [hS] at hsmall
    set I : DiffRing V := ι (v 6 * (cV p v * cV p v)) with hIdef
    have hII : (81 : DiffRing V) ≤ I * I := by nlinarith
    nlinarith

/-! ## Sums of squares -/

private theorem one_le_sq {x : DiffRing V} (hx : x ≠ 0) : 1 ≤ x * x := by
  have h1 : 1 ≤ |x| := abs_ge_one ModelArithmetic.model_discrete hx
  have := abs_mul_abs_self x
  nlinarith [abs_nonneg x]

private theorem pm_of_sq {x : DiffRing V} (h : x * x = 1) : x = 1 ∨ x = -1 :=
  eq_one_or_neg_one_of_mul_eq_one ModelArithmetic.model_discrete h

theorem sos4_split {n0 na u ws : DiffRing V} (h : n0 * n0 + na * na + u * u + ws * ws - 2 = 0)
    (h0 : n0 ≠ 0) (ha : na ≠ 0) :
    (n0 = 1 ∨ n0 = -1) ∧ (na = 1 ∨ na = -1) ∧ u = 0 ∧ ws = 0 := by
  have e0 := one_le_sq h0
  have ea := one_le_sq ha
  have hu := mul_self_nonneg u
  have hw := mul_self_nonneg ws
  exact ⟨pm_of_sq (by linarith), pm_of_sq (by linarith), mul_self_eq_zero.mp (by linarith),
    mul_self_eq_zero.mp (by linarith)⟩

theorem sos5_split {n0 n1 na u ws : DiffRing V}
    (h : n0 * n0 + n1 * n1 + na * na + u * u + ws * ws - 3 = 0)
    (h0 : n0 ≠ 0) (h1 : n1 ≠ 0) (ha : na ≠ 0) :
    (n0 = 1 ∨ n0 = -1) ∧ (n1 = 1 ∨ n1 = -1) ∧ (na = 1 ∨ na = -1) ∧ u = 0 ∧ ws = 0 := by
  have e0 := one_le_sq h0
  have e1 := one_le_sq h1
  have ea := one_le_sq ha
  have hu := mul_self_nonneg u
  have hw := mul_self_nonneg ws
  exact ⟨pm_of_sq (by linarith), pm_of_sq (by linarith), pm_of_sq (by linarith),
    mul_self_eq_zero.mp (by linarith), mul_self_eq_zero.mp (by linarith)⟩

end Short15Units

#print axioms Short15Units.prod6_split
#print axioms Short15Units.na_ne_neg
#print axioms Short15Units.ns_ne_neg
#print axioms Short15Units.n1_ne_neg
#print axioms Short15Units.nn_ne_neg
#print axioms Short15Units.n0_ne_neg
#print axioms Short15Units.n0_ne_zero
#print axioms Short15Units.n1_ne_zero
#print axioms Short15Units.na_ne_zero
#print axioms Short15Units.sos4_split
#print axioms Short15Units.sos5_split
