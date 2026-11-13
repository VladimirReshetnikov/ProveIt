import DiophantineConsistency.Compact44.P72Root

/-! # P13, section 6 (first part): the main root

Write `J = 3j+1`, so that `q = 1 + βJ`. Put:

* `R = G(q²−1) + (MC + q·MF)J`, with `G = (q−1)(q−F) + α`;
* `S = 4qY` and `M = qS`;
* `Dstar = M(X+ac) + H(Mγ + SX + R + 1) − Hk`.

The scaled registers satisfy `Rhat = βR`, `Sb = βS`, `Mb = βM` and
`Dhat = β·Dstar`, so `A1 = 0` reads `Dstar² = M²(1+Δc²)`. `Dstar` is positive,
since `M·a·c ≥ Hk` once `q³ ∣ Y`. Hence `Dstar = M·g` with `g² = 1 + Δc²`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace P72Main
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency
open AdaptiveEquationSyntax2011 ModelDifferenceRing ArithmeticSignedPairs
open ArithmeticAdaptiveQuotients2011 P72Graph P72Root
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem ι_pos' {x : V} (h : 0 < x) : (0 : DiffRing V) < ι x := by
  simpa using (ι_lt_ι (V := V)).mpr h

private theorem ι_ge {n : ℕ} {x : V} (h : (n : V) ≤ x) : ((n : ℕ) : DiffRing V) ≤ ι x := by
  simpa using (ι_le_ι (V := V)).mpr h

section Bounds

private theorem cube_bound {q s : DiffRing V} (hq : 2 ≤ q) (hs : 1 ≤ s) : (3 : DiffRing V) ≤ q * (q * q) * s := by
  have h4 : (4 : DiffRing V) ≤ q * q := by nlinarith
  have h8 : (8 : DiffRing V) ≤ q * (q * q) := by nlinarith
  nlinarith

private theorem scale_bound {Y q : DiffRing V} (hY : 0 ≤ Y) (hq : 1 ≤ q) : 4 * Y ≤ 4 * (Y * q) * q := by
  have h1 : Y ≤ Y * q := le_mul_of_one_le_right hY hq
  have h2 : Y * q ≤ Y * q * q := le_mul_of_one_le_right (le_trans hY h1) hq
  nlinarith

private theorem hk_bound {H M a c k Y : DiffRing V} (hH : H = 3 + 4 * a) (hM : 4 * Y ≤ M)
    (hc : k * Y ≤ c) (ha : 3 ≤ a) (hY : 3 ≤ Y) (hk : 0 < k) : H * k ≤ M * (a * c) := by
  have ha0 : 0 ≤ a := by linarith
  have hY0 : 0 ≤ Y := by linarith
  have h1 : (4 * Y) * (a * (k * Y)) ≤ M * (a * c) :=
    mul_le_mul hM (mul_le_mul_of_nonneg_left hc ha0) (by positivity) (by linarith)
  have hYY : (9 : DiffRing V) ≤ Y * Y := by nlinarith
  have hak : 0 ≤ a * k := by positivity
  have h2 : (4 * Y) * (a * (k * Y)) = 4 * (a * k) * (Y * Y) := by ring
  rw [hH]
  nlinarith

private theorem D0_bound {H k M a c X G S R : DiffRing V} (h : H * k ≤ M * (a * c))
    (hM : 0 ≤ M) (hX : 0 ≤ X) (hH : 0 ≤ H) (hG : 0 ≤ G) (hS : 0 ≤ S) (hR : 0 ≤ R) :
    H * k ≤ M * (X + a * c) + H * (M * G + S * X + R + 1) := by
  have h1 : 0 ≤ M * X := mul_nonneg hM hX
  have h2 : 0 ≤ H * (M * G + S * X + R + 1) := by positivity
  nlinarith

end Bounds

/-- §6: the main residual yields the main Pell root `g` and the exact carrier
relation `M·g + H·k = M(X+ac) + H(Mγ + SX + R + 1)`. -/
theorem main_root (p : Fin 4 → ℕ) (v : Fin 13 → V) (hv : ∀ j, 0 < v j)
    (hb : 0 < (p 0 : V)) (J : V)
    (hJ : v 0 + (v 2 + v 1) = 1 + (p 0 : V) * J)
    (hY : (v 0 + (v 2 + v 1)) * ((v 0 + (v 2 + v 1)) * (v 0 + (v 2 + v 1))) ∣ v 7)
    (hz : InternalZero (graph (fun j => (p j : ℤ))).A1 v) :
    let q : V := v 0 + (v 2 + v 1)
    let k : V := v 9 + v 10
    let c : V := v 9 + v 7 * k
    let a : V := v 6 * v 7 + v 7
    let H : V := 3 + 4 * a
    let Δ : V := H + a * a
    let R : V := ((q - 1) * (q - v 0) + v 1) * (q * q - 1) + ((p 2 : V) + (p 3 : V) * q) * J
    let S : V := 4 * (v 7 * q)
    let M : V := S * q
    ∃ g : V, g * g = 1 + Δ * (c * c) ∧
      M * g + H * k = M * (v 6 + a * c) + H * (M * v 12 + S * v 6 + R + 1) := by
  intro q k c a H Δ R S M
  let β : V := p 0
  set w : Fin 13 → DiffRing V := fun j => ι (v j) with hw
  have hq1 : 1 ≤ q := pos_iff_one_le.mp (add_pos_of_pos_of_nonneg (hv 0) (Arithmetic.zero_le _))
  have hqF : v 0 ≤ q := le_add_of_nonneg_right (Arithmetic.zero_le _)
  have hqq1 : 1 ≤ q * q := one_le_mul_of_one_le_of_one_le hq1 hq1
  -- casts of the registers
  have cq : (vals (fun j => (p j : ℤ)) w).q = ι q := by simp only [vals, hw, q, map_add]
  have cβ : (((fun j => (p j : ℤ)) 0 : ℤ) : DiffRing V) = ι β := cast_port p 0
  have cqm : ι q - 1 = ι β * ι J := by
    have h : ι q = ι (1 + β * J) := congrArg ι hJ
    rw [h]; simp [map_add, map_mul]
  have cR : (vals (fun j => (p j : ℤ)) w).Rhat = ι β * ι R := by
    have e1 : ι (q - 1) = ι q - 1 := by simpa using ι_tsub (V := V) hq1
    have e2 : ι (q - v 0) = ι q - ι (v 0) := ι_tsub hqF
    have e3 : ι (q * q - 1) = ι (q * q) - 1 := by simpa using ι_tsub (V := V) hqq1
    simp only [vals, R, map_add, map_mul, e1, e2, e3, cast_port]
    rw [← cq]
    simp only [vals, hw]
    rw [show ι (v 0) + (ι (v 2) + ι (v 1)) - 1 = ι β * ι J from by
      rw [← cqm, ← cq]; simp only [vals, hw]]
    ring
  have cHk : (vals (fun j => (p j : ℤ)) w).H = ι H ∧ (vals (fun j => (p j : ℤ)) w).k = ι k ∧
      (vals (fun j => (p j : ℤ)) w).c = ι c ∧ (vals (fun j => (p j : ℤ)) w).a = ι a ∧
      (vals (fun j => (p j : ℤ)) w).Delta = ι Δ := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [vals, hw, H, k, c, a, Δ, map_add, map_mul, map_ofNat]
  obtain ⟨cH, ck, cc, ca, cD⟩ := cHk
  have cSb : (vals (fun j => (p j : ℤ)) w).Sb = ι β * ι S := by
    simp only [vals, S, map_mul, map_ofNat, cast_port]; rw [← cq]; simp only [vals, hw]; ring
  have cMb : (vals (fun j => (p j : ℤ)) w).Mb = ι β * ι M := by
    simp only [vals, M, S, map_mul, map_ofNat, cast_port]; rw [← cq]; simp only [vals, hw]; ring
  let Dr : DiffRing V := ι M * (ι (v 6) + ι a * ι c) +
    ι H * (ι M * ι (v 12) + ι S * ι (v 6) + ι R + 1) - ι H * ι k
  have cD' : (vals (fun j => (p j : ℤ)) w).Dhat = ι β * Dr := by
    have hD := show (vals (fun j => (p j : ℤ)) w).Dhat =
        (vals (fun j => (p j : ℤ)) w).Mb * (w 6 + (vals (fun j => (p j : ℤ)) w).a *
          (vals (fun j => (p j : ℤ)) w).c) + (vals (fun j => (p j : ℤ)) w).H *
          ((vals (fun j => (p j : ℤ)) w).Rhat + (((vals (fun j => (p j : ℤ)) w).Mb * w 12 +
            (vals (fun j => (p j : ℤ)) w).Sb * w 6) - ι β * ((vals (fun j => (p j : ℤ)) w).k - 1)))
      from by simp only [vals, cast_port, β]
    rw [hD, cMb, ca, cc, cH, cR, cSb, ck]
    simp only [Dr, hw]
    ring
  rw [internalZero_iff, A1_eval, cD', cMb, cD, cc] at hz
  have hβ : (0 : DiffRing V) < ι β := ι_pos' hb
  have hDr : Dr * Dr = (ι M * ι M) * (1 + ι Δ * (ι c * ι c)) := by
    have h2 : ι β * ι β ≠ 0 := ne_of_gt (mul_pos hβ hβ)
    apply mul_left_cancel₀ h2
    linear_combination hz
  -- positivity of Dstar
  have hk : (0 : DiffRing V) < ι k := ι_pos' (add_pos (hv 9) (hv 10))
  have hY0 : (0 : DiffRing V) ≤ ι (v 7) := ι_nonneg _
  have hY3 : (3 : DiffRing V) ≤ ι (v 7) := by
    obtain ⟨s, hs⟩ := hY
    have hs0 : 1 ≤ s := by
      rcases (Arithmetic.zero_le s).lt_or_eq with h | h
      · exact pos_iff_one_le.mp h
      · exfalso; rw [← h, mul_zero] at hs; exact (ne_of_gt (hv 7)) hs
    have hq2 : (2 : DiffRing V) ≤ ι q := by
      have : (2 : V) ≤ q := by
        have h := add_le_add (pos_iff_one_le.mp (hv 0)) (pos_iff_one_le.mp (add_pos (hv 2) (hv 1)))
        simpa [one_add_one_eq_two] using h
      have h := (ι_le_ι (V := V)).mpr this
      rwa [map_ofNat] at h
    have hs1 : (1 : DiffRing V) ≤ ι s := by simpa using (ι_le_ι (V := V)).mpr hs0
    have he : ι (v 7) = ι q * (ι q * ι q) * ι s := by rw [hs]; simp only [map_mul]; rfl
    rw [he]
    exact cube_bound hq2 hs1
  have ha3 : (3 : DiffRing V) ≤ ι a := by
    have : ι a = ι (v 6) * ι (v 7) + ι (v 7) := by simp [a, map_add, map_mul]
    rw [this]; exact le_trans hY3 (le_add_of_nonneg_left (mul_nonneg (ι_nonneg _) hY0))
  have hc' : ι k * ι (v 7) ≤ ι c := by
    have : ι c = ι (v 9) + ι (v 7) * ι k := by simp [c, k, map_add, map_mul]
    rw [this, mul_comm (ι k)]; exact le_add_of_nonneg_left (ι_nonneg _)
  have hM : 4 * ι (v 7) ≤ ι M := by
    have : ι M = 4 * (ι (v 7) * ι q) * ι q := by simp [M, S, map_mul, map_ofNat]
    have hq1' : (1 : DiffRing V) ≤ ι q := by simpa using (ι_le_ι (V := V)).mpr hq1
    rw [this]; exact scale_bound hY0 hq1'
  have hHk : ι H * ι k ≤ ι M * (ι a * ι c) :=
    hk_bound (by simp [H, map_add, map_mul, map_ofNat]) hM hc' ha3 hY3 hk
  -- the natural Dstar
  let D0 : V := M * (v 6 + a * c) + H * (M * v 12 + S * v 6 + R + 1)
  have hle : H * k ≤ D0 := by
    apply (ι_le_ι (V := V)).mp
    have : ι D0 = ι M * (ι (v 6) + ι a * ι c) + ι H * (ι M * ι (v 12) + ι S * ι (v 6) + ι R + 1) := by
      simp [D0, map_add, map_mul]
    rw [this, map_mul]
    exact D0_bound hHk (ι_nonneg M) (ι_nonneg (v 6)) (ι_nonneg H) (ι_nonneg (v 12)) (ι_nonneg S) (ι_nonneg R)
  let Ds : V := D0 - H * k
  have cDs : ι Ds = Dr := by
    rw [ι_tsub hle]; simp [D0, Dr, map_add, map_mul]
  have hDsV : Ds * Ds = M * M * (1 + Δ * (c * c)) := by
    apply ι_injective
    simp only [map_mul, map_add, map_one, cDs]
    rw [hDr]
  have hMpos : 0 < M := by
    apply (ι_lt_ι (V := V)).mp; simp only [map_zero]
    exact lt_of_lt_of_le (by linarith) hM
  obtain ⟨g, hg, hgg⟩ := scaled_quotient M Ds (1 + Δ * (c * c)) hMpos hDsV
  refine ⟨g, hgg, ?_⟩
  rw [← hg]
  exact tsub_add_cancel_of_le hle

end P72Main

#print axioms P72Main.main_root
