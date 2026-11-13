import DiophantineConsistency.Compact44.P57Units
import DiophantineConsistency.Compact44.P72Root
import DiophantineConsistency.ArithmeticAdaptiveQuotients2011

/-! # Package 57: the factors in a model

After the unit guard (`P57Units.units`), at a positive valuation of a model of
`𝗜𝚺₁`:

* `transport`: `Nt = 1` gives `F + α < q` and `(K0 + w)C + q = 1 + F + z(q−1)`;
* `four_root`: `N = 0` restores the main root `g` and the first root `τ`.
  - `P = W² + U²G − S²A` has `P² = (2WU)²G`, so `|P| = 2WU·g` with `g² = G`.
  - If `P ≥ 0` then `(W − Ug)² = S²A`, so `|W − Ug| = Sτ` with `τ² = A`.
  - If `P < 0` then `W + Ug = Sτ` with `τ² = A`. But `W + Ug > S(ℓ + k)`
    (using `g > ac`, `c ≥ 8k`), so `τ > ℓ + k` and `τ² > A`, impossible.
  - The carrier is returned as a natural-number identity in each sign of
    `W − Ug`;
* `strong_aux`: `J_M = 0` restores the normalized strong root `f`.
  - `Z² = (2vb)²D`, so `|Z| = 2vb·f` with `f² = D = 1 + ΔI²`.
  - The identity `QZ = Q(Dv² + b²) − 1 − (Q−1)(Qy − 1)²` then gives the
    auxiliary norm `Q·V² − (Q−1)·y₀² = 1` with `y₀ = Qy − 1`.
  - `V = vf − b` (the ordinary-blank ordinate) or `V = vf + b`, according to
    the sign of `Z`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
noncomputable section
namespace P57Root
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency
open AdaptiveEquationSyntax2011 ModelDifferenceRing ArithmeticAdaptiveQuotients2011 P57Graph
open P72Root (ι_tsub)
open P72Aux (ι_absdiff_sq)
open DiophantineConsistency.ArithmeticPellHalfIndex (absdiff)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem ι_pos' {x : V} (h : 0 < x) : (0 : DiffRing V) < ι x := by
  simpa using (ι_lt_ι (V := V)).mpr h

private theorem ι_one_le {x : V} (h : 0 < x) : (1 : DiffRing V) ≤ ι x := by
  simpa using (ι_le_ι (V := V)).mpr (pos_iff_one_le.mp h)

theorem cast_nat (n : ℕ) : (((n : ℤ)) : DiffRing V) = ι (n : V) := by
  rw [Int.cast_natCast, map_natCast]

section Values
variable (p : Fin 4 → ℕ) (v : Fin 12 → V)

def qV : V := (p 0 : V) * v 0 + 1
def XV : V := v 7 * qV p v
def YV : V := v 6 * ((qV p v * qV p v) * qV p v)
def EV : V := XV p v * YV p v
def kV : V := v 8 + v 9
def cV : V := kV v * YV p v + v 8
def aV : V := EV p v + YV p v
def HV : V := 4 * aV p v + 3
def ΔV : V := aV p v * aV p v + HV p v
def ellV : V := EV p v * (kV v * YV p v)
def AV : V := ellV p v * (ellV p v + kV v) + 1
def GV : V := ΔV p v * (cV p v * cV p v) + 1
def UV : V := 4 * ((qV p v * qV p v) * (qV p v * qV p v))
def SV : V := UV p v * HV p v
def IV : V := v 4 * (cV p v * cV p v)
def QV : V := (ΔV p v * IV p v) * (ΔV p v * IV p v)
def DV : V := (ΔV p v * IV p v) * IV p v + 1
def vV : V := cV p v * v 5
def RV : V := ((p 0 : V) * v 0 * (qV p v - v 1) + v 2) * (qV p v * qV p v - 1) +
  ((p 2 : V) + qV p v * (p 3 : V)) * v 0
def bV : V := cV p v + RV p v * DV p v

theorem c_qm : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).qm = ι ((p 0 : V) * v 0) := by
  simp only [vals, map_mul, cast_nat]
theorem c_q : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).q = ι (qV p v) := by
  simp only [vals, qV, map_add, map_mul, map_one, cast_nat]
theorem c_X : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).X = ι (XV p v) := by
  simp only [vals, XV, qV, map_add, map_mul, map_one, cast_nat]
theorem c_Y : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).Y = ι (YV p v) := by
  simp only [vals, YV, qV, map_add, map_mul, map_one, cast_nat]
theorem c_k : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).k = ι (kV v) := by
  simp only [vals, kV, map_add]
theorem c_c : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).c = ι (cV p v) := by
  simp only [vals, cV, kV, YV, qV, map_add, map_mul, map_one, cast_nat]
theorem c_a : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).a = ι (aV p v) := by
  simp only [vals, aV, EV, XV, YV, qV, map_add, map_mul, map_one, cast_nat]
theorem c_H : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).H = ι (HV p v) := by
  simp only [vals, HV, aV, EV, XV, YV, qV, map_add, map_mul, map_one, map_ofNat, cast_nat]
theorem c_Delta : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).Delta = ι (ΔV p v) := by
  simp only [vals, ΔV, HV, aV, EV, XV, YV, qV, map_add, map_mul, map_one, map_ofNat, cast_nat]
theorem c_ell : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).ell = ι (ellV p v) := by
  simp only [vals, ellV, EV, XV, YV, kV, qV, map_add, map_mul, map_one, cast_nat]
theorem c_A : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).A = ι (AV p v) := by
  simp only [vals, AV, ellV, EV, XV, YV, kV, qV, map_add, map_mul, map_one, cast_nat]
theorem c_G : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).G = ι (GV p v) := by
  simp only [vals, GV, ΔV, HV, aV, EV, XV, YV, cV, kV, qV, map_add, map_mul, map_one, map_ofNat, cast_nat]
theorem c_U : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).U = ι (UV p v) := by
  simp only [vals, UV, qV, map_add, map_mul, map_one, map_ofNat, cast_nat]
theorem c_S : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).S = ι (SV p v) := by
  rw [show (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).S =
    (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).U * (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).H
    from rfl, c_U, c_H, SV, map_mul]
theorem c_I : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).I = ι (IV p v) := by
  rw [show (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).I =
    ι (v 4) * ((vals (fun j => (p j : ℤ)) (fun j => ι (v j))).c *
      (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).c) from rfl, c_c, IV, map_mul, map_mul]
theorem c_Q : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).Q = ι (QV p v) := by
  rw [show (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).Q =
    ((vals (fun j => (p j : ℤ)) (fun j => ι (v j))).Delta * (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).I) *
    ((vals (fun j => (p j : ℤ)) (fun j => ι (v j))).Delta * (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).I)
    from rfl, c_Delta, c_I, QV]
  simp only [map_mul]
theorem c_D : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).D = ι (DV p v) := by
  rw [show (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).D =
    ((vals (fun j => (p j : ℤ)) (fun j => ι (v j))).Delta * (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).I) *
      (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).I + 1 from rfl, c_Delta, c_I, DV]
  simp only [map_mul, map_add, map_one]
theorem c_v : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).v = ι (vV p v) := by
  rw [show (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).v =
    (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).c * ι (v 5) from rfl, c_c, vV, map_mul]
theorem c_RR (hF : v 1 ≤ qV p v) :
    (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).RR = ι (RV p v) := by
  have hq1 : 1 ≤ qV p v * qV p v := one_le_mul_of_one_le_of_one_le le_add_self le_add_self
  have e1 : ι (qV p v - v 1) = ι (qV p v) - ι (v 1) := ι_tsub hF
  have e2 : ι (qV p v * qV p v - 1) = ι (qV p v) * ι (qV p v) - 1 := by
    rw [ι_tsub hq1, map_mul, map_one]
  rw [show (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).RR =
      ((vals (fun j => (p j : ℤ)) (fun j => ι (v j))).qm *
        ((vals (fun j => (p j : ℤ)) (fun j => ι (v j))).q - ι (v 1)) + ι (v 2)) *
        ((vals (fun j => (p j : ℤ)) (fun j => ι (v j))).q * (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).q - 1) +
      (((p 2 : ℕ) : ℤ) + (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).q * (((p 3 : ℕ) : ℤ) : DiffRing V)) * ι (v 0)
    from rfl, c_qm, c_q]
  simp only [RV, map_add, map_mul, e1, e2, cast_nat]
theorem c_b (hF : v 1 ≤ qV p v) :
    (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).baux = ι (bV p v) := by
  rw [show (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).baux =
    (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).c +
      (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).RR * (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).D
    from rfl, c_c, c_RR p v hF, c_D, bV, map_add, map_mul]

end Values

/-- `Nt = 1`: the positive gap and the transport identity. -/
theorem transport (p : Fin 4 → ℕ) (v : Fin 12 → V) (hv : ∀ j, 0 < v j)
    (hNt : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).Nt = 1) :
    v 1 + v 2 < qV p v ∧
      ((p 1 : V) + v 7) * (qV p v - (v 1 + v 2)) + qV p v = 1 + v 1 + v 3 * ((p 0 : V) * v 0) := by
  have e : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).Nt =
      (((((p 1 : ℕ) : ℤ) : DiffRing V) + ι (v 7)) *
          (((vals (fun j => (p j : ℤ)) (fun j => ι (v j))).q - ι (v 1)) - ι (v 2)) +
        ((vals (fun j => (p j : ℤ)) (fun j => ι (v j))).q - ι (v 1))) -
      ι (v 3) * (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).qm := rfl
  rw [e, c_q, c_qm, cast_nat] at hNt
  have hqq : ι (qV p v) = ι ((p 0 : V) * v 0) + 1 := by simp [qV, map_add]
  have hF : (1 : DiffRing V) ≤ ι (v 1) := ι_one_le (hv 1)
  have hz : (1 : DiffRing V) ≤ ι (v 3) := ι_one_le (hv 3)
  have hb : (0 : DiffRing V) ≤ ι ((p 0 : V) * v 0) := ι_nonneg _
  have hKw : (0 : DiffRing V) ≤ ι (p 1 : V) + ι (v 7) := add_nonneg (ι_nonneg _) (ι_nonneg _)
  set Cr : DiffRing V := ι (qV p v) - ι (v 1) - ι (v 2) with hCr
  have hC : 0 < Cr := by
    by_contra hneg
    have hle : Cr ≤ 0 := le_of_not_gt hneg
    have h1 : (ι (p 1 : V) + ι (v 7)) * Cr ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hKw hle
    have h2 : ι ((p 0 : V) * v 0) ≤ ι (v 3) * ι ((p 0 : V) * v 0) := le_mul_of_one_le_left hb hz
    linarith
  have hlt : v 1 + v 2 < qV p v := by
    apply (ι_lt_ι (V := V)).mp
    rw [map_add]; linarith
  refine ⟨hlt, ?_⟩
  apply ι_injective
  rw [map_add, map_mul, ι_tsub (le_of_lt hlt)]
  simp only [Cr, map_add, map_mul, map_one] at hNt ⊢
  linear_combination hNt

/-- `N = 0` restores the main root `g` and the first root `τ`, given `R + 1 < U`. -/
theorem four_root (p : Fin 4 → ℕ) (v : Fin 12 → V) (hv : ∀ j, 0 < v j) (hb : 0 < (p 0 : V))
    (hF : v 1 ≤ qV p v) (hRU : RV p v + 1 < UV p v)
    (hN : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).N = 0) :
    ∃ g τ : V, g * g = GV p v ∧ τ * τ = AV p v ∧
      (UV p v * (XV p v + aV p v * cV p v) + HV p v * (UV p v * (v 11 + ellV p v) + kV v) =
          UV p v * g + SV p v * τ + HV p v * (RV p v + 1) ∨
        UV p v * (XV p v + aV p v * cV p v) + HV p v * (UV p v * (v 11 + ellV p v) + kV v) + SV p v * τ =
          UV p v * g + HV p v * (RV p v + 1)) := by
  set Wr := vals (fun j => (p j : ℤ)) (fun j => ι (v j)) with hWr
  set U := UV p v
  set X := XV p v
  set a := aV p v
  set c := cV p v
  set H := HV p v
  set k := kV v
  set R := RV p v
  set S := SV p v
  set G := GV p v
  set A := AV p v
  set ell := ellV p v
  set Wplus : V := U * (X + a * c) + H * (U * (v 11 + ell) + k)
  -- W is a positive natural
  have hU0 : 0 < U := mul_pos (by norm_num) (mul_pos (mul_pos (lt_of_lt_of_le (by simp) le_add_self)
    (lt_of_lt_of_le (by simp) le_add_self)) (mul_pos (lt_of_lt_of_le (by simp) le_add_self)
    (lt_of_lt_of_le (by simp) le_add_self)))
  have hH0 : 0 < H := add_pos_of_nonneg_of_pos (Arithmetic.zero_le _) (by norm_num)
  have hle : H * (R + 1) < Wplus := by
    calc H * (R + 1) < H * U := mul_lt_mul_of_pos_left hRU hH0
      _ ≤ H * (U * (v 11 + ell)) := mul_le_mul_of_nonneg_left
          (le_mul_of_one_le_right (Arithmetic.zero_le _) (le_trans (pos_iff_one_le.mp (hv 11)) le_self_add))
          (Arithmetic.zero_le _)
      _ ≤ H * (U * (v 11 + ell) + k) := mul_le_mul_of_nonneg_left le_self_add (Arithmetic.zero_le _)
      _ ≤ Wplus := le_add_self
  set Wv : V := Wplus - H * (R + 1) with hWv
  have hW0 : 0 < Wv := tsub_pos_of_lt hle
  have cW : Wr.W = ι Wv := by
    rw [show Wr.W = Wr.U * (Wr.X + Wr.a * Wr.c) + Wr.H * (Wr.U * (ι (v 11) + Wr.ell) + ((Wr.k - Wr.RR) - 1))
      from rfl, c_U, c_X, c_a, c_c, c_H, c_ell, c_k, c_RR p v hF, hWv, ι_tsub (le_of_lt hle)]
    simp only [Wplus, map_add, map_mul, map_one]; ring
  have eN : Wr.N = ((Wr.W * Wr.W + (Wr.U * Wr.U) * Wr.G) - (Wr.S * Wr.S) * Wr.A) *
      ((Wr.W * Wr.W + (Wr.U * Wr.U) * Wr.G) - (Wr.S * Wr.S) * Wr.A) - 4 * ((Wr.W * Wr.W) * ((Wr.U * Wr.U) * Wr.G)) := rfl
  rw [eN, cW, c_U, c_G, c_S, c_A] at hN
  -- the main root
  obtain ⟨P1, P2, hP⟩ := exists_mk (ι Wv * ι Wv + (ι U * ι U) * ι G - (ι S * ι S) * ι A)
  rw [mk_eq_sub] at hP
  have hPsq : absdiff P1 P2 * absdiff P1 P2 = (2 * Wv * U) * (2 * Wv * U) * G := by
    apply ι_injective
    rw [map_mul, ι_absdiff_sq, ← hP]
    simp only [map_mul, map_ofNat]
    linear_combination hN
  have hm0 : 0 < 2 * Wv * U := mul_pos (mul_pos (by norm_num) hW0) hU0
  obtain ⟨g, hg, hgg⟩ := scaled_quotient (2 * Wv * U) (absdiff P1 P2) G hm0 hPsq
  have hGg : ι G = ι g * ι g := by rw [← map_mul, hgg]
  rcases le_total P2 P1 with hP12 | hP12
  · -- P = 2WUg: (W − Ug)² = S²A
    have hpos : ι (absdiff P1 P2) = ι P1 - ι P2 := by
      rw [show absdiff P1 P2 = P1 - P2 by simp [absdiff, tsub_eq_zero_of_le hP12], ι_tsub hP12]
    have h' : ι Wv * ι Wv + (ι U * ι U) * ι G - (ι S * ι S) * ι A = ι (2 * Wv * U * g) :=
      hP.trans (hpos.symm.trans (congrArg ι hg))
    simp only [map_mul, map_ofNat] at h'
    rcases le_total (U * g) Wv with hUg | hUg
    · have hsq : (Wv - U * g) * (Wv - U * g) = S * S * A := by
        apply ι_injective
        simp only [map_mul, ι_tsub hUg]
        rw [hGg] at h'
        linear_combination h'
      have hS0 : 0 < S := mul_pos hU0 hH0
      obtain ⟨τ, hτ, hττ⟩ := scaled_quotient S (Wv - U * g) A hS0 hsq
      refine ⟨g, τ, hgg, hττ, Or.inl ?_⟩
      have h1 : Wv = U * g + S * τ := by rw [← hτ]; exact (add_tsub_cancel_of_le hUg).symm
      rw [hWv] at h1
      calc Wplus = (Wplus - H * (R + 1)) + H * (R + 1) := (tsub_add_cancel_of_le (le_of_lt hle)).symm
        _ = U * g + S * τ + H * (R + 1) := by rw [h1]
    · have hsq : (U * g - Wv) * (U * g - Wv) = S * S * A := by
        apply ι_injective
        simp only [map_mul, ι_tsub hUg]
        rw [hGg] at h'
        linear_combination h'
      have hS0 : 0 < S := mul_pos hU0 hH0
      obtain ⟨τ, hτ, hττ⟩ := scaled_quotient S (U * g - Wv) A hS0 hsq
      refine ⟨g, τ, hgg, hττ, Or.inr ?_⟩
      have h1 : Wv + S * τ = U * g := by rw [← hτ]; exact add_tsub_cancel_of_le hUg
      rw [hWv] at h1
      calc Wplus + S * τ = ((Wplus - H * (R + 1)) + H * (R + 1)) + S * τ := by
            rw [tsub_add_cancel_of_le (le_of_lt hle)]
        _ = ((Wplus - H * (R + 1)) + S * τ) + H * (R + 1) := by ring
        _ = U * g + H * (R + 1) := by rw [h1]
  · -- P = −2WUg: W + Ug = Sτ, impossible
    exfalso
    have hneg : ι (absdiff P1 P2) = ι P2 - ι P1 := by
      rw [show absdiff P1 P2 = P2 - P1 by simp [absdiff, tsub_eq_zero_of_le hP12], ι_tsub hP12]
    have h0 : ι P2 - ι P1 = ι (2 * Wv * U * g) := hneg.symm.trans (congrArg ι hg)
    have h' : ι Wv * ι Wv + (ι U * ι U) * ι G - (ι S * ι S) * ι A = -ι (2 * Wv * U * g) := by
      rw [hP]; linear_combination -h0
    simp only [map_mul, map_ofNat] at h'
    have hsq : (Wv + U * g) * (Wv + U * g) = S * S * A := by
      apply ι_injective
      simp only [map_mul, map_add]
      rw [hGg] at h'
      linear_combination h'
    have hS0 : 0 < S := mul_pos hU0 hH0
    obtain ⟨τ, hτ, hττ⟩ := scaled_quotient S (Wv + U * g) A hS0 hsq
    -- bounds
    have hq2 : (2 : V) ≤ qV p v := by
      have h1 : 1 ≤ (p 0 : V) * v 0 :=
        one_le_mul_of_one_le_of_one_le (pos_iff_one_le.mp hb) (pos_iff_one_le.mp (hv 0))
      simpa [qV, one_add_one_eq_two] using (add_le_add_iff_right (1 : V)).mpr h1
    have hY8 : (8 : V) ≤ YV p v := by
      show 8 ≤ v 6 * ((qV p v * qV p v) * qV p v)
      calc (8 : V) = 1 * ((2 * 2) * 2) := by norm_num
        _ ≤ v 6 * ((qV p v * qV p v) * qV p v) := mul_le_mul (pos_iff_one_le.mp (hv 6))
            (mul_le_mul (mul_le_mul hq2 hq2 (by norm_num) (Arithmetic.zero_le _)) hq2 (by norm_num)
              (Arithmetic.zero_le _)) (by norm_num) (Arithmetic.zero_le _)
    have hc8 : 8 * k ≤ c := by
      show 8 * k ≤ k * YV p v + v 8
      calc 8 * k ≤ k * YV p v := by rw [mul_comm]; exact mul_le_mul_of_nonneg_left hY8 (Arithmetic.zero_le _)
        _ ≤ k * YV p v + v 8 := le_self_add
    have hk2 : 2 ≤ k := by
      simpa [k, kV, one_add_one_eq_two] using add_le_add (pos_iff_one_le.mp (hv 8)) (pos_iff_one_le.mp (hv 9))
    have ha1 : 1 ≤ a := le_trans (le_trans (by norm_num) hY8) le_add_self
    have hgac : a * c < g := by
      have hG' : g * g = (a * a + (4 * a + 3)) * (c * c) + 1 := hgg
      by_contra hle'
      have h1 : g ≤ a * c := le_of_not_gt hle'
      have h2 : g * g ≤ (a * c) * (a * c) := mul_le_mul h1 h1 (Arithmetic.zero_le _) (Arithmetic.zero_le _)
      have h3 : (a * c) * (a * c) < (a * a + (4 * a + 3)) * (c * c) + 1 := by
        calc (a * c) * (a * c) = (a * a) * (c * c) := by ring
          _ ≤ (a * a + (4 * a + 3)) * (c * c) := mul_le_mul_of_nonneg_right le_self_add (Arithmetic.zero_le _)
          _ < _ := lt_add_one _
      rw [← hG'] at h3
      exact absurd h2 (not_le_of_gt h3)
    -- S(ℓ + k) < W + Ug
    have hbig : S * (ell + k) < Wv + U * g := by
      apply (ι_lt_ι (V := V)).mp
      have hWι : ι Wv = ι Wplus - ι (H * (R + 1)) := ι_tsub (le_of_lt hle)
      rw [map_add, hWι]
      simp only [Wplus, S, SV, map_add, map_mul, map_one]
      have hRUι : ι R + 1 < ι U := by
        have h := (ι_lt_ι (V := V)).mpr hRU; rwa [map_add, map_one] at h
      have ht1 : (1 : DiffRing V) ≤ ι (v 11) := ι_one_le (hv 11)
      have hgacι : ι a * ι c < ι g := by
        have h := (ι_lt_ι (V := V)).mpr hgac; rwa [map_mul] at h
      have hc8ι : 8 * ι k ≤ ι c := by
        have h := (ι_le_ι (V := V)).mpr hc8; rwa [map_mul, map_ofNat] at h
      have ha1ι : (1 : DiffRing V) ≤ ι a := by simpa using (ι_le_ι (V := V)).mpr ha1
      have hk0 : (0 : DiffRing V) ≤ ι k := ι_nonneg _
      have hU0ι : (0 : DiffRing V) < ι U := ι_pos' hU0
      have hX0 : (0 : DiffRing V) ≤ ι X := ι_nonneg _
      have hell0 : (0 : DiffRing V) ≤ ι ell := ι_nonneg _
      have hH : ι H = 4 * ι a + 3 := by simp only [H, HV, map_add, map_mul, map_ofNat]; rfl
      rw [hH]
      have key : (4 * ι a + 3) * ι k ≤ ι a * ι c + ι g := by nlinarith
      nlinarith [mul_nonneg hU0ι.le hX0, mul_nonneg hU0ι.le hell0, mul_le_mul_of_nonneg_left key hU0ι.le,
        mul_le_mul_of_nonneg_left ht1 (mul_nonneg (by linarith : (0:DiffRing V) ≤ 4 * ι a + 3) hU0ι.le)]
    have hτbig : ell + k < τ := by
      by_contra hle'
      have h1 : τ ≤ ell + k := le_of_not_gt hle'
      have h2 : S * τ ≤ S * (ell + k) := mul_le_mul_of_nonneg_left h1 (Arithmetic.zero_le _)
      rw [← hτ] at h2
      exact absurd hbig (not_lt_of_ge h2)
    have hAlt : A < (ell + k) * (ell + k) := by
      show ell * (ell + k) + 1 < (ell + k) * (ell + k)
      have : (ell + k) * (ell + k) = ell * (ell + k) + (ell * k + k * k) := by ring
      rw [this]
      apply (add_lt_add_iff_left _).mpr
      calc (1 : V) < 2 * 2 := by norm_num
        _ ≤ k * k := mul_le_mul hk2 hk2 (by norm_num) (Arithmetic.zero_le _)
        _ ≤ ell * k + k * k := le_add_self
    have h2 : (ell + k) * (ell + k) < τ * τ := mul_lt_mul'' hτbig hτbig (Arithmetic.zero_le _) (Arithmetic.zero_le _)
    rw [hττ] at h2
    exact absurd (lt_trans hAlt h2) (_root_.lt_irrefl _)

/-- `J_M = 0` restores the normalized strong root and the auxiliary norm. -/
theorem strong_aux (p : Fin 4 → ℕ) (v : Fin 12 → V) (hv : ∀ j, 0 < v j) (hF : v 1 ≤ qV p v)
    (hJ : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).inner = 0) :
    ∃ f y0 : V, f * f = DV p v ∧ 0 < f ∧ 0 < y0 ∧
      (QV p v * absdiff (cV p v * v 5 * f) (f * f * RV p v + cV p v) *
          absdiff (cV p v * v 5 * f) (f * f * RV p v + cV p v) + y0 * y0 = 1 + QV p v * y0 * y0 ∨
        QV p v * (cV p v * v 5 * f + (f * f * RV p v + cV p v)) *
          (cV p v * v 5 * f + (f * f * RV p v + cV p v)) + y0 * y0 = 1 + QV p v * y0 * y0) := by
  set Wr := vals (fun j => (p j : ℤ)) (fun j => ι (v j)) with hWr
  set Q := QV p v
  set D := DV p v
  set vv := vV p v
  set b := bV p v
  set c := cV p v
  set R := RV p v
  have eJ : Wr.inner = Wr.Z * Wr.Z - 4 * ((Wr.D * (Wr.v * Wr.v)) * (Wr.baux * Wr.baux)) := rfl
  have eZ : Wr.Z = ((Wr.D * (Wr.v * Wr.v) + Wr.baux * Wr.baux) - 1) +
      ((Wr.Q - 1) * ι (v 10)) * (2 - Wr.Q * ι (v 10)) := rfl
  rw [eJ, c_D, c_v, c_b p v hF] at hJ
  rw [c_D, c_v, c_b p v hF, c_Q] at eZ
  -- positivity
  have hc0 : 0 < c := add_pos_of_nonneg_of_pos (Arithmetic.zero_le _) (hv 8)
  have hv0 : 0 < vv := mul_pos hc0 (hv 5)
  have hb0 : 0 < b := add_pos_of_pos_of_nonneg hc0 (Arithmetic.zero_le _)
  -- the strong root
  obtain ⟨Z1, Z2, hZ⟩ := exists_mk Wr.Z
  rw [mk_eq_sub] at hZ
  have hZsq : absdiff Z1 Z2 * absdiff Z1 Z2 = (2 * vv * b) * (2 * vv * b) * D := by
    apply ι_injective
    rw [map_mul, ι_absdiff_sq, ← hZ]
    simp only [map_mul, map_ofNat]
    linear_combination hJ
  have hm0 : 0 < 2 * vv * b := mul_pos (mul_pos (by norm_num) hv0) hb0
  obtain ⟨f, hf, hff⟩ := scaled_quotient (2 * vv * b) (absdiff Z1 Z2) D hm0 hZsq
  have hf0 : 0 < f := by
    rcases (Arithmetic.zero_le f).lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h, mul_zero] at hff
      exact absurd hff.symm (ne_of_gt (lt_of_lt_of_le (by simp) le_add_self))
  -- Q ≥ 2 and y0
  have hQ2 : 2 ≤ Q := by
    have hI : 1 ≤ IV p v := one_le_mul_of_one_le_of_one_le (pos_iff_one_le.mp (hv 4))
      (one_le_mul_of_one_le_of_one_le (pos_iff_one_le.mp hc0) (pos_iff_one_le.mp hc0))
    have hΔ : 3 ≤ ΔV p v := le_trans (by norm_num) (le_add_self.trans' le_add_self)
    have hDI : 3 ≤ ΔV p v * IV p v := le_trans hΔ (le_mul_of_one_le_right (Arithmetic.zero_le _) hI)
    show 2 ≤ (ΔV p v * IV p v) * (ΔV p v * IV p v)
    exact le_trans (by norm_num) (le_trans hDI (le_mul_of_one_le_right (Arithmetic.zero_le _)
      (le_trans (by norm_num) hDI)))
  have hQy : 1 ≤ Q * v 10 := le_trans (le_trans (by norm_num) hQ2)
    (le_mul_of_one_le_right (Arithmetic.zero_le _) (pos_iff_one_le.mp (hv 10)))
  set y0 : V := Q * v 10 - 1 with hy0def
  have hy0 : 0 < y0 := by
    apply tsub_pos_of_lt
    exact lt_of_lt_of_le (by norm_num : (1 : V) < 2) (le_trans hQ2
      (le_mul_of_one_le_right (Arithmetic.zero_le _) (pos_iff_one_le.mp (hv 10))))
  have hy0ι : ι y0 = ι Q * ι (v 10) - 1 := by rw [hy0def, ι_tsub hQy, map_mul, map_one]
  -- identity (25): QZ = Q(Dv² + b²) − 1 − (Q−1)y0²
  have h25 : ι Q * Wr.Z = ι Q * (ι D * (ι vv * ι vv) + ι b * ι b) - 1 - (ι Q - 1) * (ι y0 * ι y0) := by
    rw [eZ, hy0ι]; ring
  have hDf : ι D = ι f * ι f := by rw [← map_mul, hff]
  have hbD : b = c + R * (f * f) := by rw [hff]; rfl
  refine ⟨f, y0, hff, hf0, hy0, ?_⟩
  rcases le_total Z2 Z1 with hZ12 | hZ12
  · -- Z = 2vbf: Q(vf − b)² − (Q−1)y0² = 1
    left
    have hpos : ι (absdiff Z1 Z2) = ι Z1 - ι Z2 := by
      rw [show absdiff Z1 Z2 = Z1 - Z2 by simp [absdiff, tsub_eq_zero_of_le hZ12], ι_tsub hZ12]
    have hZv : Wr.Z = ι (2 * vv * b * f) := hZ.trans (hpos.symm.trans (congrArg ι hf))
    apply ι_injective
    simp only [map_add, map_mul, map_one]
    rw [mul_assoc (ι Q), ι_absdiff_sq]
    rw [hZv] at h25
    simp only [map_mul, map_ofNat] at h25
    rw [hDf, hbD] at h25
    simp only [vv, vV, map_add, map_mul] at h25 ⊢
    linear_combination -h25
  · -- Z = −2vbf: Q(vf + b)² − (Q−1)y0² = 1
    right
    have hneg : ι (absdiff Z1 Z2) = ι Z2 - ι Z1 := by
      rw [show absdiff Z1 Z2 = Z2 - Z1 by simp [absdiff, tsub_eq_zero_of_le hZ12], ι_tsub hZ12]
    have h0 : ι Z2 - ι Z1 = ι (2 * vv * b * f) := hneg.symm.trans (congrArg ι hf)
    have hZv : Wr.Z = -ι (2 * vv * b * f) := by rw [hZ]; linear_combination -h0
    apply ι_injective
    simp only [map_add, map_mul, map_one]
    rw [hZv] at h25
    simp only [map_mul, map_ofNat] at h25
    rw [hDf, hbD] at h25
    simp only [vv, vV, map_add, map_mul] at h25 ⊢
    linear_combination -h25

end P57Root

#print axioms P57Root.transport
#print axioms P57Root.four_root
#print axioms P57Root.strong_aux
