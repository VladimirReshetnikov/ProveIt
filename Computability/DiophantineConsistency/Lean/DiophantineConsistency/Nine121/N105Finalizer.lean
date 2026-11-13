import DiophantineConsistency.Nine121.N9Finalizer

/-! # Package 105's local Laurent finalizer in every model of `𝗜𝚺₁`

`value R N b g t h s w C i j n` is the finalizer of
`105-bootstrap-certificates/nine/PROOF.md` (§3), with the prefix outputs `R, N, t` as inputs. Its
ratio and saturated-Pell registers are those of `N9Finalizer.value` (`U, Y, M, P, K, A, B₁, W, J,
Q, m, Ω, E₀, V₀, a₀, D, r = iJC², F, Λ, G, Z, H, I`); only the second majorant changes:

  `T = iC²(AJ(2D − C²) + 3C² − 4)`, `V₁ = TGH`, `a₁ = 4DFI`,

and the norm is `norm2 (E₀ − Ω(V₀ + V₁)) Ω a₀ a₁`. The JSON circuit evaluates it at `C = c + 1`.

* `majorant`: for `A, C ≥ 2`, `i ≥ 1` in an ordered ring, `T > 0` and `4DF < T²` (PROOF.md §4:
  `T² − 4DF = i²t²Q(A, t) − 4D` with `t = C²`, and `Q(x + 2, y + 4) − (x + 2)²` has nonnegative
  coefficients);
* `sound`: a zero at positive model naturals with `C ≥ 2` gives `N² ∣ C(2R, R)`, `b = 2ᵏ` and
  `g < 4t`, in the audited order of `N9Finalizer.sound` (strict majorants first, then `m > 0`,
  the separation `a₀ < a₁`, the roots, `J ∣ Q`, `2 ∣ √a₁` hence `DFI` square, `SatPell.psi_of_sat`,
  Lemma 2.25);
* `complete`: from `N² ∣ C(2R, R)`, `b = 2ᵏ` and `g < t`, a zero with `C ≥ 2` and the other six
  unknowns positive, using `T ≥ AD` (so `n = m(V₀ + V₁ + z₀ + 2z₁) − W² − Q/J > 0`);
* `sound_succ`, `complete_succ`: the same at `C = c + 1` with `c > 0`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
noncomputable section
namespace Nine121.N105Finalizer
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ModelDifferenceRing ModelArithmetic NinePolynomial ArithmeticPellRecurrence ArithmeticBinomPascal
open ModelNineRatio
open N9Norm
open N9Finalizer hiding value value_eq sound complete a1 V1

section Ring
variable {A : Type*} [CommRing A]

/-- Package 105's local Laurent finalizer. -/
def value (R N b g t h s w C i j n : A) : A :=
  let U := N ^ 2 * w
  let Y := N ^ 2 * s
  let M := R * Y
  let P := 2 * M ^ 2 * U
  let K := R + 1 + h * (P - 1)
  let Am := M * (U + 1)
  let B1 := 2 * R + 1
  let W1 := b * w
  let J := 4 * Am - 5
  let Qr := 3 * W1 * C - 2 * (W1 ^ 2 - 1)
  let m := K ^ 2 * (4 * t - g) - 16 * t * (C - K * Y) ^ 2
  let Ω := J * m
  let E0 := J * (n + W1 ^ 2) + Qr
  let V0 := P * K
  let a0 := (P ^ 2 - 1) * K ^ 2 + 1
  let D := (Am ^ 2 - 1) * C ^ 2 + 1
  let r0 := i * J * C ^ 2
  let F := (Am ^ 2 - 1) * D * r0 ^ 2 + 1
  let Λ := C * D + 1 - Am
  let G := Am + F * Λ
  let Z := B1 + (j - 1) * C
  let H1 := C + F * Z
  let I := (G ^ 2 - 1) * H1 ^ 2 + 1
  let a1 := 4 * (D * F * I)
  let T := i * C ^ 2 * (Am * J * (2 * D - C ^ 2) + (3 * C ^ 2 - 4))
  let V1 := T * G * H1
  norm2 (E0 - Ω * (V0 + V1)) Ω a0 a1

end Ring


variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### The new majorant -/

section Majorant

/-- `Q(x + 2, y + 4) − (x + 2)² ≥ 0` for `x, y ≥ 0` (all twelve coefficients are positive). -/
theorem Qpos (x y : DiffRing V) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ 1344 + 816 * y + 117 * y ^ 2 + x * (3580 + 2188 * y + 318 * y ^ 2) +
      x ^ 2 * (2975 + 1852 * y + 277 * y ^ 2) + x ^ 3 * (640 + 400 * y + 60 * y ^ 2) := by
  have h1 : 0 ≤ 3580 + 2188 * y + 318 * y ^ 2 := by linarith [pow_nonneg hy 2]
  have h2 : 0 ≤ 2975 + 1852 * y + 277 * y ^ 2 := by linarith [pow_nonneg hy 2]
  have h3 : 0 ≤ 640 + 400 * y + 60 * y ^ 2 := by linarith [pow_nonneg hy 2]
  have h0 : 0 ≤ 1344 + 816 * y + 117 * y ^ 2 := by linarith [pow_nonneg hy 2]
  have := mul_nonneg hx h1
  have := mul_nonneg (pow_nonneg hx 2) h2
  have := mul_nonneg (pow_nonneg hx 3) h3
  linarith

/-- **The local Laurent majorant** (PROOF.md §4): `T > 0` and `4DF < T²`. -/
theorem majorant (a c i : DiffRing V) (ha : 2 ≤ a) (hc : 2 ≤ c) (hi : 1 ≤ i) :
    0 < i * c ^ 2 * (a * (4 * a - 5) * (2 * ((a ^ 2 - 1) * c ^ 2 + 1) - c ^ 2) + (3 * c ^ 2 - 4)) ∧
    4 * ((a ^ 2 - 1) * c ^ 2 + 1) * ((a ^ 2 - 1) * ((a ^ 2 - 1) * c ^ 2 + 1) *
      (i * (4 * a - 5) * c ^ 2) ^ 2 + 1) <
      (i * c ^ 2 * (a * (4 * a - 5) * (2 * ((a ^ 2 - 1) * c ^ 2 + 1) - c ^ 2) + (3 * c ^ 2 - 4))) ^ 2 := by
  obtain ⟨t, ht⟩ : ∃ t, t = c ^ 2 := ⟨_, rfl⟩
  have ht4 : 4 ≤ t := by rw [ht]; nlinarith
  rw [← ht]
  have hQ := Qpos (a - 2) (t - 4) (by linarith) (by linarith)
  have hQa : 20 * t * (3 * t - 4) * a ^ 3 - t * (83 * t - 116) * a ^ 2 - 10 * (7 * t ^ 2 - 14 * t + 8) * a +
      109 * t ^ 2 - 224 * t + 116 - a ^ 2 =
      1344 + 816 * (t - 4) + 117 * (t - 4) ^ 2 + (a - 2) * (3580 + 2188 * (t - 4) + 318 * (t - 4) ^ 2) +
      (a - 2) ^ 2 * (2975 + 1852 * (t - 4) + 277 * (t - 4) ^ 2) +
      (a - 2) ^ 3 * (640 + 400 * (t - 4) + 60 * (t - 4) ^ 2) := by ring
  obtain ⟨Q, hQd⟩ : ∃ Q, Q = 20 * t * (3 * t - 4) * a ^ 3 - t * (83 * t - 116) * a ^ 2 -
      10 * (7 * t ^ 2 - 14 * t + 8) * a + 109 * t ^ 2 - 224 * t + 116 := ⟨_, rfl⟩
  have hQ' : a ^ 2 ≤ Q := by rw [hQd]; linarith
  have hid : (i * t * (a * (4 * a - 5) * (2 * ((a ^ 2 - 1) * t + 1) - t) + (3 * t - 4))) ^ 2 -
      4 * ((a ^ 2 - 1) * t + 1) * ((a ^ 2 - 1) * ((a ^ 2 - 1) * t + 1) * (i * (4 * a - 5) * t) ^ 2 + 1) =
      i ^ 2 * t ^ 2 * Q - 4 * ((a ^ 2 - 1) * t + 1) := by rw [hQd]; ring
  have hi2 : 1 ≤ i ^ 2 := by nlinarith
  have ht2 : 0 ≤ t ^ 2 := sq_nonneg t
  have ha2 : 0 ≤ a ^ 2 := sq_nonneg a
  have hQ0 : 0 ≤ Q := le_trans ha2 hQ'
  have h1 : t ^ 2 * a ^ 2 ≤ i ^ 2 * t ^ 2 * Q := by
    have e1 : t ^ 2 * a ^ 2 ≤ t ^ 2 * Q := mul_le_mul_of_nonneg_left hQ' ht2
    have e2 : t ^ 2 * Q ≤ i ^ 2 * (t ^ 2 * Q) := le_mul_of_one_le_left (mul_nonneg ht2 hQ0) hi2
    linarith [show i ^ 2 * (t ^ 2 * Q) = i ^ 2 * t ^ 2 * Q by ring]
  have h2 : 12 ≤ t ^ 2 * a ^ 2 - 4 * ((a ^ 2 - 1) * t + 1) := by
    have e : t ^ 2 * a ^ 2 - 4 * ((a ^ 2 - 1) * t + 1) = a ^ 2 * t * (t - 4) + 4 * t - 4 := by ring
    rw [e]
    have : 0 ≤ a ^ 2 * t * (t - 4) := mul_nonneg (mul_nonneg ha2 (by linarith)) (by linarith)
    linarith
  refine ⟨?_, by linarith⟩
  have hD : 0 ≤ 2 * ((a ^ 2 - 1) * t + 1) - t := by
    have : 3 ≤ a ^ 2 - 1 := by nlinarith
    nlinarith
  have hJ : 0 < 4 * a - 5 := by linarith
  have h3 : 0 ≤ a * (4 * a - 5) * (2 * ((a ^ 2 - 1) * t + 1) - t) :=
    mul_nonneg (mul_nonneg (by linarith) hJ.le) hD
  have h4 : 0 < a * (4 * a - 5) * (2 * ((a ^ 2 - 1) * t + 1) - t) + (3 * t - 4) := by linarith
  exact mul_pos (mul_pos (by linarith) (by linarith)) h4

end Majorant

/-! ### The new registers in `V` -/

/-- The majorant `T = iC²(AJ(2D − C²) + (3C² − 4))` as a model natural. -/
def Tm (A C i J : V) : V := i * C * C * (A * J * (2 * S.D A C - C * C) + (3 * C * C - 4))

/-- `a₁ = 4DFI`. -/
def a1 (R N s w C i j : V) : V :=
  4 * (S.D (Q.A R N s w) C * S.F (Q.A R N s w) C i (Q.J R N s w) *
    S.I (Q.A R N s w) C i (Q.J R N s w) j (Q.B' R))

/-- `V₁ = TGH`. -/
def V1 (R N s w C i j : V) : V :=
  Tm (Q.A R N s w) C i (Q.J R N s w) * S.G (Q.A R N s w) C i (Q.J R N s w) *
    S.H (Q.A R N s w) C i (Q.J R N s w) j (Q.B' R)

theorem C2_le_2D (A C : V) (hA : 2 ≤ A) : C * C ≤ 2 * S.D A C := by
  unfold S.D
  have hA1 : 1 ≤ A * A - 1 := by
    apply le_tsub_of_add_le_left
    calc (1 : V) + 1 = 2 := one_add_one_eq_two
      _ ≤ 2 * 2 := by norm_num
      _ ≤ A * A := mul_le_mul hA hA (by norm_num) (Arithmetic.zero_le _)
  calc C * C = 1 * C * C := by ring
    _ ≤ (A * A - 1) * C * C := by
        rw [mul_assoc, mul_assoc]; exact mul_le_mul_of_nonneg_right hA1 (Arithmetic.zero_le _)
    _ ≤ (A * A - 1) * C * C + 1 := le_self_add
    _ ≤ 2 * ((A * A - 1) * C * C + 1) := le_mul_of_one_le_left (Arithmetic.zero_le _) (by norm_num)

theorem four_le_3C2 (C : V) (hC : 2 ≤ C) : 4 ≤ 3 * C * C := by
  calc (4 : V) = 1 * 2 * 2 := by norm_num
    _ ≤ 3 * C * C := mul_le_mul (mul_le_mul (by norm_num) hC (by norm_num) (by norm_num)) hC
        (by norm_num) (Arithmetic.zero_le _)

theorem ι_Tm (A C i J : V) (hA : 2 ≤ A) (hC : 2 ≤ C) :
    ι (Tm A C i J) = ι i * ι C ^ 2 * (ι A * ι J * (2 * ι (S.D A C) - ι C ^ 2) + (3 * ι C ^ 2 - 4)) := by
  unfold Tm
  simp only [map_mul, map_add, ι_sub_of_le (four_le_3C2 C hC), ι_sub_of_le (C2_le_2D A C hA), map_ofNat]
  ring

/-- All registers of the finalizer as images of model naturals; `Θ` and `Ω` stay signed. -/
theorem value_eq {R N b g t h s w C i j n : V} (hR : 8 ≤ R) (hN : 8 ≤ N) (hs : 0 < s)
    (hw : 0 < w) (hC : 2 ≤ C) (hj : 0 < j) :
    value (ι R) (ι N) (ι b) (ι g) (ι t) (ι h) (ι s) (ι w) (ι C) (ι i) (ι j) (ι n) =
      norm2 (ι (Q.J R N s w) * (ι n + ι (Q.W b w) ^ 2) + Qr b w C -
          ι (Q.J R N s w) * marg R N b g t h s w C * (ι (V0 R N h s w) + ι (V1 R N s w C i j)))
        (ι (Q.J R N s w) * marg R N b g t h s w C) (ι (a0 R N h s w)) (ι (a1 R N s w C i j)) := by
  obtain ⟨hP1, hA2⟩ := ModelNineRatio.sizes hR hN hs hw
  have hA1 : 1 ≤ Q.A R N s w * Q.A R N s w := ModelNineRatio.one_le_sq_of_two_le hA2
  have hA5 : 5 ≤ 4 * Q.A R N s w := ModelNineRatio.five_le_four_mul hA2
  have hC1 : 1 ≤ C := le_trans one_le_two hC
  have hj1 : 1 ≤ j := pos_iff_one_le.mp hj
  have hDA : Q.A R N s w ≤ C * S.D (Q.A R N s w) C + 1 := by
    unfold S.D
    calc Q.A R N s w ≤ Q.A R N s w * Q.A R N s w :=
          le_mul_of_one_le_left (Arithmetic.zero_le _) (le_trans one_le_two hA2)
      _ = (Q.A R N s w * Q.A R N s w - 1) + 1 := (tsub_add_cancel_of_le hA1).symm
      _ ≤ C * ((Q.A R N s w * Q.A R N s w - 1) * C * C + 1) + 1 := by
          refine add_le_add ?_ (le_refl 1)
          calc Q.A R N s w * Q.A R N s w - 1 ≤ (Q.A R N s w * Q.A R N s w - 1) * C * C := by
                rw [mul_assoc]; exact le_mul_of_one_le_right (Arithmetic.zero_le _)
                  (one_le_mul_of_one_le_of_one_le hC1 hC1)
            _ ≤ (Q.A R N s w * Q.A R N s w - 1) * C * C + 1 := le_self_add
            _ ≤ C * ((Q.A R N s w * Q.A R N s w - 1) * C * C + 1) :=
                le_mul_of_one_le_left (Arithmetic.zero_le _) hC1
  have hG1 : 1 ≤ S.G (Q.A R N s w) C i (Q.J R N s w) * S.G (Q.A R N s w) C i (Q.J R N s w) := by
    have : 1 ≤ S.G (Q.A R N s w) C i (Q.J R N s w) :=
      le_trans (le_trans one_le_two hA2) (le_add_of_nonneg_right (Arithmetic.zero_le _))
    exact one_le_mul_of_one_le_of_one_le this this
  have hPP : 1 ≤ Q.P R N s w * Q.P R N s w := one_le_mul_of_one_le_of_one_le hP1 hP1
  -- the casts
  have eY : ι N ^ 2 * ι s = ι (Q.Y N s) := by simp only [Q.Y, map_mul]; ring
  have eU : ι N ^ 2 * ι w = ι (Q.U N w) := by simp only [Q.U, map_mul]; ring
  have eM : ι R * ι (Q.Y N s) = ι (Q.M R N s) := by simp only [Q.M, map_mul]
  have eP : 2 * ι (Q.M R N s) ^ 2 * ι (Q.U N w) = ι (Q.P R N s w) := by
    simp only [Q.P, map_mul, map_ofNat]; ring
  have eK : ι R + 1 + ι h * (ι (Q.P R N s w) - 1) = ι (Q.K R N h s w) := by
    simp only [Q.K, map_add, map_mul, map_one, ι_sub_of_le hP1]
  have eA : ι (Q.M R N s) * (ι (Q.U N w) + 1) = ι (Q.A R N s w) := by
    simp only [Q.A, map_add, map_mul, map_one]
  have eW : ι b * ι w = ι (Q.W b w) := by simp only [Q.W, map_mul]
  have eB : 2 * ι R + 1 = ι (Q.B' R) := by simp only [Q.B', map_add, map_mul, map_one, map_ofNat]
  have eJ : 4 * ι (Q.A R N s w) - 5 = ι (Q.J R N s w) := by
    simp only [Q.J, ι_sub_of_le hA5, map_mul, map_ofNat]
  have eD : (ι (Q.A R N s w) ^ 2 - 1) * ι C ^ 2 + 1 = ι (S.D (Q.A R N s w) C) := by
    simp only [S.D, map_add, map_mul, map_one, ι_sub_of_le hA1]; ring
  have er : ι i * ι (Q.J R N s w) * ι C ^ 2 = ι (S.r C i (Q.J R N s w)) := by
    simp only [S.r, map_mul]; ring
  have eF : (ι (Q.A R N s w) ^ 2 - 1) * ι (S.D (Q.A R N s w) C) * ι (S.r C i (Q.J R N s w)) ^ 2 + 1 =
      ι (S.F (Q.A R N s w) C i (Q.J R N s w)) := by
    simp only [S.F, map_add, map_mul, map_one, ι_sub_of_le hA1]; ring
  have eL : ι C * ι (S.D (Q.A R N s w) C) + 1 - ι (Q.A R N s w) =
      ι (C * S.D (Q.A R N s w) C + 1 - Q.A R N s w) := by
    rw [ι_sub_of_le hDA]; simp only [map_add, map_mul, map_one]
  have eG : ι (Q.A R N s w) + ι (S.F (Q.A R N s w) C i (Q.J R N s w)) *
      ι (C * S.D (Q.A R N s w) C + 1 - Q.A R N s w) = ι (S.G (Q.A R N s w) C i (Q.J R N s w)) := by
    simp only [S.G, map_add, map_mul]
  have eZ : ι (Q.B' R) + (ι j - 1) * ι C = ι (Q.B' R + (j - 1) * C) := by
    simp only [map_add, map_mul, ι_sub_of_le hj1, map_one]
  have eH : ι C + ι (S.F (Q.A R N s w) C i (Q.J R N s w)) * ι (Q.B' R + (j - 1) * C) =
      ι (S.H (Q.A R N s w) C i (Q.J R N s w) j (Q.B' R)) := by
    simp only [S.H, map_add, map_mul]
  have eI : (ι (S.G (Q.A R N s w) C i (Q.J R N s w)) ^ 2 - 1) *
      ι (S.H (Q.A R N s w) C i (Q.J R N s w) j (Q.B' R)) ^ 2 + 1 =
      ι (S.I (Q.A R N s w) C i (Q.J R N s w) j (Q.B' R)) := by
    simp only [S.I, map_add, map_mul, map_one, ι_sub_of_le hG1]; ring
  have ea0 : (ι (Q.P R N s w) ^ 2 - 1) * ι (Q.K R N h s w) ^ 2 + 1 = ι (a0 R N h s w) := by
    simp only [a0, map_add, map_mul, map_one, ι_sub_of_le hPP]; ring
  have eT : ι i * ι C ^ 2 * (ι (Q.A R N s w) * ι (Q.J R N s w) * (2 * ι (S.D (Q.A R N s w) C) -
      ι C ^ 2) + (3 * ι C ^ 2 - 4)) = ι (Tm (Q.A R N s w) C i (Q.J R N s w)) :=
    (ι_Tm _ _ _ _ hA2 hC).symm
  simp only [value]
  rw [eY, eU, eM, eP, eK, eA, eW, eB, eJ, eD, er, eF, eL, eG, eZ, eH, eI, ea0, eT]
  simp only [marg, Qr, a1, V0, V1, map_mul, map_ofNat]

/-! ### Soundness -/

set_option maxHeartbeats 8000000 in
/-- **Soundness**: a positive zero (with `C ≥ 2`) gives the binomial calibration, the binary
base and the cap. -/
theorem sound {R N b g t h s w C i j n : V} (hR : 8 ≤ R) (hN : 8 ≤ N) (hbR : b ≤ R) (hb : 0 < b)
    (hbN : b ≤ N) (ht : 0 < t) (hh : 0 < h) (hs : 0 < s) (hw : 0 < w) (hC2 : 2 ≤ C)
    (hi : 0 < i) (hj : 0 < j)
    (hz : value (ι R) (ι N) (ι b) (ι g) (ι t) (ι h) (ι s) (ι w) (ι C) (ι i) (ι j) (ι n) = 0) :
    N * N ∣ binom (2 * R) R ∧ (∃ k, b = Exp.exp k) ∧ g < 4 * t := by
  have hC : 0 < C := lt_of_lt_of_le (by norm_num) hC2
  rw [value_eq hR hN hs hw hC2 hj] at hz
  obtain ⟨hY64, hRPK, hWP, hPA, hJ3, hr1, hP1⟩ := register_sizes hR hN hb hbR hh hs hw hC hi hj
  obtain ⟨-, hA2⟩ := ModelNineRatio.sizes hR hN hs hw
  have hA1 : 1 ≤ Q.A R N s w * Q.A R N s w := ModelNineRatio.one_le_sq_of_two_le hA2
  have hj1 : 1 ≤ j := pos_iff_one_le.mp hj
  -- DiffRing atoms
  set p : DiffRing V := ι (Q.P R N s w) with hp
  set k : DiffRing V := ι (Q.K R N h s w) with hk
  set a : DiffRing V := ι (Q.A R N s w) with ha
  set J : DiffRing V := ι (Q.J R N s w) with hJ
  set y : DiffRing V := ι (Q.Y N s) with hy
  set W : DiffRing V := ι (Q.W b w) with hW
  set c : DiffRing V := ι C with hc
  set d : DiffRing V := ι (S.D (Q.A R N s w) C) with hd
  set r : DiffRing V := ι (S.r C i (Q.J R N s w)) with hrr
  set f : DiffRing V := ι (S.F (Q.A R N s w) C i (Q.J R N s w)) with hf
  set G : DiffRing V := ι (S.G (Q.A R N s w) C i (Q.J R N s w)) with hG
  set H : DiffRing V := ι (S.H (Q.A R N s w) C i (Q.J R N s w) j (Q.B' R)) with hH
  set I : DiffRing V := ι (S.I (Q.A R N s w) C i (Q.J R N s w) j (Q.B' R)) with hI
  set T : DiffRing V := ι (Tm (Q.A R N s w) C i (Q.J R N s w)) with hT
  -- the defining relations
  have ed : d = (a ^ 2 - 1) * c ^ 2 + 1 := by
    rw [hd, ha, hc]; simp only [S.D, map_add, map_mul, map_one, ι_sub_of_le hA1]; ring
  have ef : f = (a ^ 2 - 1) * d * r ^ 2 + 1 := by
    rw [hf, ha, hd, hrr]; simp only [S.F, map_add, map_mul, map_one, ι_sub_of_le hA1]; ring
  have hG1 : 1 ≤ S.G (Q.A R N s w) C i (Q.J R N s w) * S.G (Q.A R N s w) C i (Q.J R N s w) := by
    have : 1 ≤ S.G (Q.A R N s w) C i (Q.J R N s w) :=
      le_trans (le_trans one_le_two hA2) (le_add_of_nonneg_right (Arithmetic.zero_le _))
    exact one_le_mul_of_one_le_of_one_le this this
  have eI : I = (G ^ 2 - 1) * H ^ 2 + 1 := by
    rw [hI, hG, hH]; simp only [S.I, map_add, map_mul, map_one, ι_sub_of_le hG1]; ring
  have hA5 : 5 ≤ 4 * Q.A R N s w := ModelNineRatio.five_le_four_mul hA2
  have eJd : J = 4 * a - 5 := by
    rw [hJ, ha]; simp only [Q.J, ι_sub_of_le hA5, map_mul, map_ofNat]
  have er : r = ι i * J * c ^ 2 := by
    rw [hrr, hJ, hc]; simp only [S.r, map_mul]; ring
  have eT : T = ι i * c ^ 2 * (a * J * (2 * d - c ^ 2) + (3 * c ^ 2 - 4)) := by
    rw [hT, ι_Tm _ _ _ _ hA2 hC2]
  have ea0 : ι (a0 R N h s w) = (p ^ 2 - 1) * k ^ 2 + 1 := by
    have hPP : 1 ≤ Q.P R N s w * Q.P R N s w := one_le_mul_of_one_le_of_one_le hP1 hP1
    rw [hp, hk]; simp only [a0, map_add, map_mul, map_one, ι_sub_of_le hPP]; ring
  have ea1 : ι (a1 R N s w C i j) = 4 * (d * f * I) := by
    simp only [a1, map_mul, map_ofNat, hd, hf, hI]
  have eV0 : ι (V0 R N h s w) = p * k := by simp only [V0, map_mul, hp, hk]
  have eV1 : ι (V1 R N s w C i j) = T * G * H := by simp only [V1, map_mul, hT, hG, hH]
  rw [ea0, ea1, eV0, eV1] at hz
  -- bounds on the atoms
  have hK9 : (9 : V) ≤ Q.K R N h s w :=
    le_trans (by calc (9 : V) = 8 + 1 := by norm_num
                    _ ≤ R + 1 := add_le_add hR (le_refl 1))
      (le_trans (add_le_add (le_refl R) hP1) hRPK)
  have hk9 : (9 : DiffRing V) ≤ k := by have hh := (ι_le_ι (V := V)).mpr hK9; simp only [map_one, map_ofNat] at hh; exact hh
  have hp1 : (1 : DiffRing V) ≤ p := by have hh := (ι_le_ι (V := V)).mpr hP1; simp only [map_one, map_ofNat] at hh; exact hh
  have hpa : p + 1 ≤ a ^ 2 := by
    have h' := (ι_le_ι (V := V)).mpr hPA
    simp only [map_add, map_mul, map_one] at h'
    rw [pow_two]; exact h'
  have ha2 : (2 : DiffRing V) ≤ a := by have hh := (ι_le_ι (V := V)).mpr hA2; simp only [map_one, map_ofNat] at hh; exact hh
  have hJ3' : (3 : DiffRing V) ≤ J := by have hh := (ι_le_ι (V := V)).mpr hJ3; simp only [map_one, map_ofNat] at hh; exact hh
  have hy64 : (64 : DiffRing V) ≤ y := by have hh := (ι_le_ι (V := V)).mpr hY64; simp only [map_one, map_ofNat] at hh; exact hh
  have hc2 : (2 : DiffRing V) ≤ c := by have hh := (ι_le_ι (V := V)).mpr hC2; simp only [map_one, map_ofNat] at hh; exact hh
  have hc1 : (1 : DiffRing V) ≤ c := by linarith
  have hi1 : (1 : DiffRing V) ≤ ι i := by have hh := (ι_le_ι (V := V)).mpr (pos_iff_one_le.mp hi); simp only [map_one] at hh; exact hh
  have hr1' : (1 : DiffRing V) ≤ r := by have hh := (ι_le_ι (V := V)).mpr hr1; simp only [map_one, map_ofNat] at hh; exact hh
  have hW0 : (0 : DiffRing V) ≤ W := ι_nonneg _
  have hWp : W < p := (ι_lt_ι (V := V)).mpr hWP
  have hRk : ι R + p ≤ k := by
    have h' := (ι_le_ι (V := V)).mpr hRPK; rwa [map_add] at h'
  have hR8 : (8 : DiffRing V) ≤ ι R := by have hh := (ι_le_ι (V := V)).mpr hR; simp only [map_one, map_ofNat] at hh; exact hh
  have hd1 : p * c ^ 2 + 1 ≤ d := by
    rw [ed]
    have : p * c ^ 2 ≤ (a ^ 2 - 1) * c ^ 2 := mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg c)
    linarith
  have hd2 : (2 : DiffRing V) ≤ d := by
    have : (1 : DiffRing V) ≤ p * c ^ 2 := one_le_mul_of_one_le_of_one_le hp1 (one_le_pow₀ hc1)
    linarith
  have hf1 : d + 1 ≤ f := by
    rw [ef]
    have h1 : (3 : DiffRing V) ≤ a ^ 2 - 1 := by nlinarith
    have h2 : (1 : DiffRing V) ≤ r ^ 2 := one_le_pow₀ hr1'
    have h3 : d ≤ (a ^ 2 - 1) * d * r ^ 2 := by
      have : d ≤ (a ^ 2 - 1) * d := le_mul_of_one_le_left (by linarith) (by linarith)
      exact le_trans this (le_mul_of_one_le_right (by nlinarith) h2)
    linarith
  have hG1' : (1 : DiffRing V) ≤ G := by
    have h := (ι_le_ι (V := V)).mpr (le_trans (le_trans one_le_two hA2)
      (le_add_of_nonneg_right (Arithmetic.zero_le _)) :
        1 ≤ S.G (Q.A R N s w) C i (Q.J R N s w))
    simp only [map_one] at h; exact h
  have hH1 : (1 : DiffRing V) ≤ H := by
    have h := (ι_le_ι (V := V)).mpr (le_trans (pos_iff_one_le.mp hC) le_self_add :
        1 ≤ S.H (Q.A R N s w) C i (Q.J R N s w) j (Q.B' R))
    simp only [map_one] at h; exact h
  -- the new majorant
  obtain ⟨hT0, hTdf⟩ := majorant a c (ι i) ha2 hc2 hi1
  rw [← eJd, ← ed] at hT0 hTdf
  rw [← er, ← ef] at hTdf
  rw [← eT] at hT0 hTdf
  -- the two strict majorants
  have hV0 : (p ^ 2 - 1) * k ^ 2 + 1 < (p * k) ^ 2 := by nlinarith
  have hV1 : 4 * (d * f * I) < (T * G * H) ^ 2 := by
    have e : (T * G * H) ^ 2 - 4 * (d * f * I) =
        (T ^ 2 - 4 * d * f) * G ^ 2 * H ^ 2 + 4 * d * f * (H ^ 2 - 1) := by
      rw [eI]; ring
    have hG2 : (1 : DiffRing V) ≤ G ^ 2 := one_le_pow₀ hG1'
    have hH2 : (1 : DiffRing V) ≤ H ^ 2 := one_le_pow₀ hH1
    have h1 : 0 < (T ^ 2 - 4 * d * f) * G ^ 2 * H ^ 2 :=
      mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
    have h2 : 0 ≤ 4 * d * f * (H ^ 2 - 1) :=
      mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
    linarith
  have hE0 : 0 < J * (ι n + W ^ 2) + Qr b w C := by
    simp only [Qr]
    rw [← hW, ← hc]
    have hn0 := ι_nonneg n
    have h1 : 0 ≤ J * ι n := mul_nonneg (by linarith) hn0
    have h2 : 0 ≤ (J - 2) * W ^ 2 := mul_nonneg (by linarith) (sq_nonneg W)
    have h3 : 0 ≤ 3 * W * c := mul_nonneg (mul_nonneg (by norm_num) hW0) (by linarith)
    nlinarith
  have hI0 : (0 : DiffRing V) ≤ I := by
    rw [eI]
    have hG2 : (1 : DiffRing V) ≤ G ^ 2 := one_le_pow₀ hG1'
    have : 0 ≤ (G ^ 2 - 1) * H ^ 2 := mul_nonneg (by linarith) (sq_nonneg H)
    linarith
  -- the margin is positive
  set m := marg R N b g t h s w C with hm
  have hm0 : 0 < m := by
    by_contra hneg
    have hm' : m ≤ 0 := le_of_not_gt hneg
    have hJm : J * m ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hm'
    have hpos := norm2_pos_of_nonpos_scale (U := p * k) (W := T * G * H)
      (by have := mul_nonneg (by nlinarith : (0 : DiffRing V) ≤ p ^ 2 - 1) (sq_nonneg k); linarith)
      (mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg (by linarith) (by linarith)) hI0))
      (mul_pos (by linarith) (by linarith))
      (mul_pos (mul_pos hT0 (by linarith)) (by linarith)) hV0 hV1 hJm hE0
    rw [hz] at hpos
    exact _root_.lt_irrefl _ hpos
  have hmd : m = k ^ 2 * (4 * ι t - ι g) - 16 * ι t * (c - k * y) ^ 2 := by
    rw [hm, hk, hc, hy]; rfl
  have ht0 : (0 : DiffRing V) < ι t := by have hh := (ι_lt_ι (V := V)).mpr ht; simp only [map_zero, map_one, map_ofNat] at hh; exact hh
  have hg0 := ι_nonneg g
  have hsq0 : 0 ≤ 16 * ι t * (c - k * y) ^ 2 := mul_nonneg (mul_nonneg (by norm_num) ht0.le) (sq_nonneg _)
  have hcap : ι g < 4 * ι t := by
    by_contra hn
    have : 4 * ι t - ι g ≤ 0 := by linarith
    have : k ^ 2 * (4 * ι t - ι g) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg k) this
    linarith
  have hgt : g < 4 * t := by
    apply (ι_lt_ι (V := V)).mp; rw [map_mul, map_ofNat]; exact hcap
  have hB3 : 4 * (c - k * y) ^ 2 < k ^ 2 := by
    have h1 : 16 * ι t * (c - k * y) ^ 2 < k ^ 2 * (4 * ι t - ι g) := by linarith
    have h2 : k ^ 2 * (4 * ι t - ι g) ≤ k ^ 2 * (4 * ι t) :=
      mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg k)
    have h3 : (4 * ι t) * (4 * (c - k * y) ^ 2) < (4 * ι t) * k ^ 2 := by nlinarith
    exact lt_of_mul_lt_mul_left h3 (by linarith)
  -- `C > KY − K/2`, hence `C > 2R + 1` and `C > K`
  have hck : k * y - k < 2 * c := by
    by_contra hn
    have hle : 2 * c ≤ k * y - k := le_of_not_gt hn
    have h1 : k ≤ 2 * (k * y - c) := by linarith
    have h2 : k ^ 2 ≤ (2 * (k * y - c)) ^ 2 := by
      have hk0 : 0 ≤ k := by linarith
      have := mul_le_mul h1 h1 hk0 (by linarith)
      nlinarith
    nlinarith
  have hky : k * 64 ≤ k * y := mul_le_mul_of_nonneg_left hy64 (by linarith)
  have hcK : k < c := by linarith
  have hcB : 2 * ι R + 1 < c := by linarith
  -- separation of the radicands
  have hsep0 : (p ^ 2 - 1) * k ^ 2 + 1 < d * f * I := by
    have hk0 : 0 ≤ k := by linarith
    have h1 : (p ^ 2 - 1) * k ^ 2 + 1 ≤ p ^ 2 * k ^ 2 := by nlinarith
    have hkc : k ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ hk0 hcK.le 2
    have hc2' : c ^ 2 ≤ c ^ 2 * c ^ 2 := le_mul_of_one_le_right (sq_nonneg c) (one_le_pow₀ hc1)
    have h2 : p ^ 2 * k ^ 2 ≤ (p * c ^ 2) ^ 2 := by
      have := mul_le_mul_of_nonneg_left (le_trans hkc hc2') (sq_nonneg p)
      nlinarith
    have hpc0 : 0 ≤ p * c ^ 2 := mul_nonneg (by linarith) (sq_nonneg c)
    have h3 : (p * c ^ 2) ^ 2 < d * d := by
      have := mul_lt_mul'' (lt_of_lt_of_le (lt_add_one _) hd1) (lt_of_lt_of_le (lt_add_one _) hd1) hpc0 hpc0
      nlinarith
    have h4 : d * d < d * f := mul_lt_mul_of_pos_left (by linarith) (by linarith)
    have h5 : d * f ≤ d * f * I := by
      have hI1 : (1 : DiffRing V) ≤ I := by
        rw [eI]
        have hG2 : (1 : DiffRing V) ≤ G ^ 2 := one_le_pow₀ hG1'
        have : 0 ≤ (G ^ 2 - 1) * H ^ 2 := mul_nonneg (by linarith) (sq_nonneg H)
        linarith
      exact le_mul_of_one_le_right (mul_nonneg (by linarith) (by linarith)) hI1
    linarith
  have hsep : (p ^ 2 - 1) * k ^ 2 + 1 < 4 * (d * f * I) := by
    have : 0 ≤ d * f * I := mul_nonneg (mul_nonneg (by linarith) (by linarith)) hI0
    linarith
  -- the roots
  have hΩ : J * m ≠ 0 := ne_of_gt (mul_pos (by linarith) hm0)
  obtain ⟨z0, z1, hz0, hz1, hθ⟩ := roots_of_norm2_zero hΩ (ne_of_lt hsep) hz
  -- `J ∣ Q`
  have hJQ : J ∣ Qr b w C := by
    refine ⟨m * (p * k + T * G * H + z0 + z1) - (ι n + W ^ 2), ?_⟩
    linear_combination hθ
  -- `2 ∣ z₁`, so `DFI` is a square of a model natural
  obtain ⟨u1, hu1⟩ : (2 : DiffRing V) ∣ z1 := by
    refine ModelRelationCombining.sq_dvd_sq 2 z1 two_ne_zero ⟨d * f * I, ?_⟩
    rw [← hz1]; ring
  have hdfI : d * f * I = u1 ^ 2 := by
    have e : (4 : DiffRing V) * (d * f * I) = 4 * u1 ^ 2 := by rw [hz1, hu1]; ring
    have h4 : (4 : DiffRing V) ≠ 0 := by norm_num
    exact mul_left_cancel₀ h4 e
  have ha1sq : ∃ u : V, S.D (Q.A R N s w) C * S.F (Q.A R N s w) C i (Q.J R N s w) *
      S.I (Q.A R N s w) C i (Q.J R N s w) j (Q.B' R) = u * u := by
    apply (isSquare_ι _).mp
    refine ⟨u1, ?_⟩
    rw [map_mul, map_mul, ← hd, ← hf, ← hI, hdfI]; ring
  -- the saturated ProductPell theorem: `C = ψ_A(2R + 1)`
  have hBC : Q.B' R ≤ C := by
    apply (ι_le_ι (V := V)).mp
    simp only [Q.B', map_add, map_mul, map_one, map_ofNat]; rw [← hc]; linarith
  have hB1 : 1 < Q.B' R := by
    have : (1 : V) < 2 * 8 + 1 := by norm_num
    exact lt_of_lt_of_le this (by simp only [Q.B']; exact add_le_add (mul_le_mul_of_nonneg_left hR (by simp)) le_rfl)
  have hDA : Q.A R N s w ≤ C * S.D (Q.A R N s w) C + 1 := by
    apply (ι_le_ι (V := V)).mp
    simp only [map_add, map_mul, map_one]
    rw [← hd, ← hc, ← ha]
    have had : a ≤ d := by
      rw [ed]
      have : (a ^ 2 - 1) * 1 ≤ (a ^ 2 - 1) * c ^ 2 :=
        mul_le_mul_of_nonneg_left (one_le_pow₀ hc1) (by nlinarith)
      nlinarith
    have hdc : d ≤ c * d := le_mul_of_one_le_left (by linarith) hc1
    linarith
  have hsat : SatPell.SatConds (Q.A R N s w - 2 + 2) (Q.B' R) C (Q.J R N s w) i j
      (S.D (Q.A R N s w) C) (S.F (Q.A R N s w) C i (Q.J R N s w))
      (S.G (Q.A R N s w) C i (Q.J R N s w)) (S.H (Q.A R N s w) C i (Q.J R N s w) j (Q.B' R))
      (S.I (Q.A R N s w) C i (Q.J R N s w) j (Q.B' R)) := by
    rw [tsub_add_cancel_of_le hA2]
    refine ⟨ha1sq, ?_, ?_, ?_, ?_, ?_⟩
    · apply ι_injective
      simp only [S.D, map_add, map_mul, map_one, ι_sub_of_le hA1]; ring
    · apply ι_injective
      simp only [S.F, S.r, map_add, map_mul, map_one, ι_sub_of_le hA1]; ring
    · apply ι_injective
      simp only [S.G, map_add, map_mul, ι_sub_of_le hDA]; ring
    · apply ι_injective
      simp only [S.H, map_add, map_mul, ι_sub_of_le hj1, map_one]; ring
    · apply ι_injective
      simp only [S.I, map_add, map_mul, map_one, ι_sub_of_le hG1]; ring
  have hψ : C = ycoord (Q.B' R) (Q.A R N s w - 2) :=
    SatPell.psi_of_sat (Q.A R N s w - 2) (Q.B' R) C (Q.J R N s w) i j _ _ _ _ _ hB1 hBC
      (Or.inr (ModelNineRatio.odd_B' R)) (lt_of_lt_of_le (by norm_num) hJ3) hi hsat
  -- Lemma 2.25
  obtain ⟨φ, hφ⟩ : ∃ φ : V, C = Q.B' R + φ := ⟨C - Q.B' R, (add_tsub_cancel_of_le hBC).symm⟩
  have hφ0 : 0 < φ := by
    have h' : Q.B' R < C := by
      apply (ι_lt_ι (V := V)).mp
      simp only [Q.B', map_add, map_mul, map_one, map_ofNat]; rw [← hc]; exact hcB
    rcases (Arithmetic.zero_le φ).lt_or_eq with h0 | h0
    · exact h0
    · exfalso; rw [← h0, add_zero] at hφ; rw [hφ] at h'; exact _root_.lt_irrefl _ h'
  have hcore : ModelRatio.B25core R N b h s w φ (Q.A R N s w) (Q.B' R) C (Q.K R N h s w)
      (Q.M R N s) (Q.P R N s w) (Q.U N w) 2 (Q.W b w) (Q.Y N s) := by
    refine ⟨rfl, ?_, hB3, rfl, rfl, rfl, rfl, hφ, rfl, rfl, rfl, rfl, hψ⟩
    have hPP : 1 ≤ Q.P R N s w * Q.P R N s w := one_le_mul_of_one_le_of_one_le hP1 hP1
    have e : ι ((Q.P R N s w * Q.P R N s w - 1) * Q.K R N h s w * Q.K R N h s w + 1) = z0 ^ 2 := by
      rw [← hz0, hp, hk]; simp only [map_add, map_mul, map_one, ι_sub_of_le hPP]; ring
    obtain ⟨u, hu⟩ := (isSquare_ι _).mp ⟨z0, by rw [e]; ring⟩
    exact ⟨u, hu.symm⟩
  have hB13 : (2 * ι (Q.A R N s w) * ι (2 : V) - ι (2 : V) * ι (2 : V) - 1 : DiffRing V) ∣
      ι (2 : V) * (ι (Q.W b w) ^ 2 - 1) - (ι (2 : V) ^ 2 - 1) * ι (Q.W b w) * ι C := by
    have e1 : (2 * ι (Q.A R N s w) * ι (2 : V) - ι (2 : V) * ι (2 : V) - 1 : DiffRing V) = J := by
      rw [eJd, ← ha, map_ofNat]; ring
    have e2 : ι (2 : V) * (ι (Q.W b w) ^ 2 - 1) - (ι (2 : V) ^ 2 - 1) * ι (Q.W b w) * ι C =
        -Qr b w C := by
      simp only [Qr, map_ofNat]; ring
    rw [e1, e2]; exact (dvd_neg).mpr hJQ
  obtain ⟨hdvd, hpow⟩ := (ModelRatio.lemma_2_25 R N b hR hN hbR hb hbN).mpr
    ⟨h, s, w, φ, _, _, _, _, _, _, _, _, _, _, hh, hs, hw, hφ0, hcore, hB13⟩
  exact ⟨hdvd, hpow, hgt⟩

/-! ### Completeness -/

set_option maxHeartbeats 8000000 in
/-- **Completeness**: from the calibration, a binary base and `g < t`, a zero with `C ≥ 2`. -/
theorem complete {R N b g t : V} (hR : 8 ≤ R) (hN : 8 ≤ N) (hbR : b ≤ R) (hb : 0 < b)
    (hbN : b ≤ N) (hgt : g < t) (hdvd : N * N ∣ binom (2 * R) R) (hpow : ∃ k, b = Exp.exp k) :
    ∃ h s w C i j n : V, 0 < h ∧ 0 < s ∧ 0 < w ∧ 2 ≤ C ∧ 0 < i ∧ 0 < j ∧ 0 < n ∧
      value (ι R) (ι N) (ι b) (ι g) (ι t) (ι h) (ι s) (ι w) (ι C) (ι i) (ι j) (ι n) = 0 := by
  obtain ⟨h, s, w, φ, A, B', C, K, M, P, U, V', W, Y, hh, hs, hw, -, hcore, hWe, hBWC, hB3s⟩ :=
    ModelRatio.exists_B25core R N b hR hN hbR hb hbN hdvd hpow
  obtain ⟨B1, ⟨z0, hz0⟩, -, B4, B5, B6, B7, B8, B9, B10, B11, -, B14⟩ := hcore
  subst B1 B4 B5 B6 B7 B9 B10 B11
  obtain ⟨hP1, hA2⟩ := ModelNineRatio.sizes hR hN hs hw
  have hA1 : 1 ≤ Q.A R N s w * Q.A R N s w := ModelNineRatio.one_le_sq_of_two_le hA2
  have hA5 : 5 ≤ 4 * Q.A R N s w := ModelNineRatio.five_le_four_mul hA2
  have hJ0 : 0 < Q.J R N s w := by
    simp only [Q.J]
    exact lt_tsub_of_add_lt_left (lt_of_lt_of_le (by norm_num : (5 : V) + 0 < 8)
      (le_trans (by norm_num : (8 : V) ≤ 4 * 2) (mul_le_mul_of_nonneg_left hA2 (by simp))))
  have hB1 : 1 < Q.B' R := by
    have : (1 : V) < 2 * 8 + 1 := by norm_num
    exact lt_of_lt_of_le this (by simp only [Q.B']; exact add_le_add (mul_le_mul_of_nonneg_left hR (by simp)) le_rfl)
  have hψ : C = ycoord (Q.B' R) (Q.A R N s w - 2) := B14
  have hC2 : 2 ≤ C := by
    rw [hψ]
    have h2 : 2 ≤ Q.B' R := by
      have := lt_iff_succ_le.mp hB1; rwa [one_add_one_eq_two] at this
    exact le_trans h2 (ArithmeticPellRecurrence.time_le_y _ _)
  have hC0 : 0 < C := lt_of_lt_of_le (by norm_num) hC2
  have hWlt : b * w < C := lt_of_le_of_lt le_add_self hBWC
  -- the saturated witnesses
  obtain ⟨i, j, D, F, G, H, I, hi, hj, hsat⟩ := SatPell.exists_sat (Q.A R N s w - 2) (Q.B' R)
    (Q.J R N s w) hB1 hJ0
  rw [tsub_add_cancel_of_le hA2, ← hψ] at hsat
  obtain ⟨⟨z1, hz1⟩, A2, A4, A5, A6, A7⟩ := hsat
  have hj1 : 1 ≤ j := pos_iff_one_le.mp hj
  -- identification with the saturated registers
  have eD : S.D (Q.A R N s w) C = D := by
    apply add_right_cancel (b := C * C)
    rw [A2]; unfold S.D
    rw [show (Q.A R N s w * Q.A R N s w - 1) * C * C + 1 + C * C =
        ((Q.A R N s w * Q.A R N s w - 1) + 1) * C * C + 1 by ring, tsub_add_cancel_of_le hA1]
  have eF : S.F (Q.A R N s w) C i (Q.J R N s w) = F := by
    apply add_right_cancel (b := D * (i * Q.J R N s w * C * C) * (i * Q.J R N s w * C * C))
    rw [A4]; unfold S.F S.r; rw [eD]
    rw [show (Q.A R N s w * Q.A R N s w - 1) * D * (i * Q.J R N s w * C * C) *
          (i * Q.J R N s w * C * C) + 1 + D * (i * Q.J R N s w * C * C) * (i * Q.J R N s w * C * C) =
        ((Q.A R N s w * Q.A R N s w - 1) + 1) * D * (i * Q.J R N s w * C * C) *
          (i * Q.J R N s w * C * C) + 1 by ring, tsub_add_cancel_of_le hA1]
  have hDA : Q.A R N s w ≤ C * D + 1 := by
    rw [← eD]; unfold S.D
    calc Q.A R N s w ≤ Q.A R N s w * Q.A R N s w :=
          le_mul_of_one_le_left (Arithmetic.zero_le _) (le_trans one_le_two hA2)
      _ = (Q.A R N s w * Q.A R N s w - 1) + 1 := (tsub_add_cancel_of_le hA1).symm
      _ ≤ C * ((Q.A R N s w * Q.A R N s w - 1) * C * C + 1) + 1 := by
          refine add_le_add ?_ (le_refl 1)
          have hC1 : 1 ≤ C := pos_iff_one_le.mp hC0
          calc Q.A R N s w * Q.A R N s w - 1 ≤ (Q.A R N s w * Q.A R N s w - 1) * C * C := by
                rw [mul_assoc]; exact le_mul_of_one_le_right (Arithmetic.zero_le _)
                  (one_le_mul_of_one_le_of_one_le hC1 hC1)
            _ ≤ (Q.A R N s w * Q.A R N s w - 1) * C * C + 1 := le_self_add
            _ ≤ C * ((Q.A R N s w * Q.A R N s w - 1) * C * C + 1) :=
                le_mul_of_one_le_left (Arithmetic.zero_le _) hC1
  have eG : S.G (Q.A R N s w) C i (Q.J R N s w) = G := by
    apply add_right_cancel (b := F * Q.A R N s w)
    rw [A5]; unfold S.G; rw [eF, eD]
    rw [show Q.A R N s w + F * (C * D + 1 - Q.A R N s w) + F * Q.A R N s w =
        Q.A R N s w + F * (C * D + 1 - Q.A R N s w + Q.A R N s w) by ring, tsub_add_cancel_of_le hDA]
  have eH : S.H (Q.A R N s w) C i (Q.J R N s w) j (Q.B' R) = H := by
    apply add_right_cancel (b := F * C)
    rw [A6]; unfold S.H; rw [eF]
    rw [show C + F * (Q.B' R + (j - 1) * C) + F * C = C + F * (Q.B' R + ((j - 1) + 1) * C) by ring,
      tsub_add_cancel_of_le hj1]
  have hG1 : 1 ≤ G * G := by
    rw [← eG]
    have : 1 ≤ S.G (Q.A R N s w) C i (Q.J R N s w) :=
      le_trans (le_trans one_le_two hA2) (le_add_of_nonneg_right (Arithmetic.zero_le _))
    exact one_le_mul_of_one_le_of_one_le this this
  have eI : S.I (Q.A R N s w) C i (Q.J R N s w) j (Q.B' R) = I := by
    apply add_right_cancel (b := H * H)
    rw [A7]; unfold S.I; rw [eG, eH]
    rw [show (G * G - 1) * H * H + 1 + H * H = ((G * G - 1) + 1) * H * H + 1 by ring,
      tsub_add_cancel_of_le hG1]
  -- `J ∣ Q`, with `Q > 0`
  have hJQ : (ι (Q.J R N s w) : DiffRing V) ∣ Qr b w C := by
    have hpc := ModelExponentialCongruence.pow_congruence (Q.A R N s w - 2) (Q.B' R)
    have hJd : (4 * ι (Q.A R N s w - 2) + 3 : DiffRing V) = ι (Q.J R N s w) := by
      simp only [Q.J, ι_sub_of_le hA5, ι_sub_of_le hA2, map_mul, map_ofNat]; ring
    have hWe' : Q.W b w = Exp.exp (Q.B' R) := hWe
    rw [hJd, ← hψ, ← hWe'] at hpc
    exact hpc
  have hQ0 : (0 : DiffRing V) < Qr b w C := by
    simp only [Qr]
    have h1 : ι (Q.W b w) + 1 ≤ ι C := by
      have := (ι_le_ι (V := V)).mpr (lt_iff_succ_le.mp hWlt); simpa [Q.W] using this
    have h0 := ι_nonneg (Q.W b w)
    nlinarith
  obtain ⟨q', hq'⟩ := hJQ
  have hq'0 : 0 ≤ q' := by
    by_contra hneg
    have : ι (Q.J R N s w) * q' < 0 :=
      mul_neg_of_pos_of_neg (by have hh := (ι_lt_ι (V := V)).mpr hJ0; simp only [map_zero] at hh; exact hh)
        (lt_of_not_ge hneg)
    linarith
  obtain ⟨qv, hqv⟩ := nonneg_iff.mp hq'0
  -- the margin
  have hm0 : (0 : DiffRing V) < marg R N b g t h s w C := by
    simp only [marg]
    have hK1 : (1 : DiffRing V) ≤ ι (Q.K R N h s w) := by
      have : 1 ≤ Q.K R N h s w := le_trans (by norm_num : (1 : V) ≤ 8 + 1)
        (le_add_of_le_of_nonneg (add_le_add hR le_rfl) (by simp))
      simpa only [map_one] using (ι_le_ι (V := V)).mpr this
    have hgt' : ι g < ι t := (ι_lt_ι (V := V)).mpr hgt
    have hg0 := ι_nonneg g
    have hB3 : (4096 : DiffRing V) * (ι C - ι (Q.K R N h s w) * ι (Q.Y N s)) ^ 2 ≤
        625 * ι (Q.K R N h s w) ^ 2 := hB3s
    have ht0 : (0 : DiffRing V) ≤ ι t := ι_nonneg t
    have h1 := mul_le_mul_of_nonneg_left hB3 ht0
    have hK2 : 0 < ι (Q.K R N h s w) ^ 2 := pow_pos (lt_of_lt_of_le one_pos hK1) 2
    have h2 : 3 * ι t * ι (Q.K R N h s w) ^ 2 < (4 * ι t - ι g) * ι (Q.K R N h s w) ^ 2 := by
      have := mul_pos (sub_pos.2 hgt') hK2
      nlinarith
    have h3 : 0 < ι t := lt_of_le_of_lt hg0 hgt'
    have h4 : 0 < ι t * ι (Q.K R N h s w) ^ 2 := mul_pos h3 hK2
    nlinarith
  obtain ⟨mv, hmv⟩ := nonneg_iff.mp hm0.le
  -- the final coordinate: `V₁ ≥ T ≥ AD`
  have hV1D : ι (Q.A R N s w * D) ≤ ι (V1 R N s w C i j) := by
    rw [← eD]
    apply (ι_le_ι (V := V)).mpr
    unfold V1 Tm
    have hC1 : 1 ≤ C := le_trans one_le_two hC2
    have hiC : 1 ≤ i * C * C := one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (pos_iff_one_le.mp hi) hC1) hC1
    have hDD : S.D (Q.A R N s w) C ≤ 2 * S.D (Q.A R N s w) C - C * C := by
      apply le_tsub_of_add_le_left
      have : C * C ≤ S.D (Q.A R N s w) C := by
        have h2 := C2_le_2D (Q.A R N s w) C hA2
        unfold S.D at h2 ⊢
        have hA1' : 1 ≤ Q.A R N s w * Q.A R N s w - 1 := by
          apply le_tsub_of_add_le_left
          calc (1 : V) + 1 = 2 := one_add_one_eq_two
            _ ≤ 2 * 2 := by norm_num
            _ ≤ Q.A R N s w * Q.A R N s w := mul_le_mul hA2 hA2 (by norm_num) (Arithmetic.zero_le _)
        calc C * C = 1 * C * C := by ring
          _ ≤ (Q.A R N s w * Q.A R N s w - 1) * C * C := by
              rw [mul_assoc, mul_assoc]; exact mul_le_mul_of_nonneg_right hA1' (Arithmetic.zero_le _)
          _ ≤ _ := le_self_add
      calc C * C + S.D (Q.A R N s w) C ≤ S.D (Q.A R N s w) C + S.D (Q.A R N s w) C :=
            add_le_add this le_rfl
        _ = 2 * S.D (Q.A R N s w) C := by ring
    have hJ1 : 1 ≤ Q.J R N s w := pos_iff_one_le.mp hJ0
    have hG' : 1 ≤ S.G (Q.A R N s w) C i (Q.J R N s w) :=
      le_trans (le_trans one_le_two hA2) (le_add_of_nonneg_right (Arithmetic.zero_le _))
    have hH' : 1 ≤ S.H (Q.A R N s w) C i (Q.J R N s w) j (Q.B' R) :=
      le_trans (pos_iff_one_le.mp hC0) le_self_add
    calc Q.A R N s w * S.D (Q.A R N s w) C
        ≤ Q.A R N s w * Q.J R N s w * (2 * S.D (Q.A R N s w) C - C * C) := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (le_trans hDD (le_mul_of_one_le_left (Arithmetic.zero_le _) hJ1))
            (Arithmetic.zero_le _)
      _ ≤ Q.A R N s w * Q.J R N s w * (2 * S.D (Q.A R N s w) C - C * C) + (3 * C * C - 4) := le_self_add
      _ ≤ i * C * C * (Q.A R N s w * Q.J R N s w * (2 * S.D (Q.A R N s w) C - C * C) + (3 * C * C - 4)) :=
          le_mul_of_one_le_left (Arithmetic.zero_le _) hiC
      _ ≤ i * C * C * (Q.A R N s w * Q.J R N s w * (2 * S.D (Q.A R N s w) C - C * C) + (3 * C * C - 4)) *
            S.G (Q.A R N s w) C i (Q.J R N s w) := le_mul_of_one_le_right (Arithmetic.zero_le _) hG'
      _ ≤ _ := le_mul_of_one_le_right (Arithmetic.zero_le _) hH'
  have hbig : ι (Q.W b w) ^ 2 + Qr b w C + 1 ≤ ι (Q.A R N s w * D) := by
    simp only [Qr, map_mul]
    rw [← eD]
    simp only [S.D, map_add, map_mul, map_one, ι_sub_of_le hA1]
    have hWC : ι (Q.W b w) + 1 ≤ ι C := by
      have := (ι_le_ι (V := V)).mpr (lt_iff_succ_le.mp hWlt); simpa [Q.W] using this
    have hW0 := ι_nonneg (Q.W b w)
    have ha2 : (2 : DiffRing V) ≤ ι (Q.A R N s w) := by have hh := (ι_le_ι (V := V)).mpr hA2; simp only [map_one, map_ofNat] at hh; exact hh
    have hc1 : (1 : DiffRing V) ≤ ι C := le_trans (by linarith) hWC
    have hC2' : (1 : DiffRing V) ≤ ι C * ι C := one_le_mul_of_one_le_of_one_le hc1 hc1
    have hWC2 : ι (Q.W b w) * ι C ≤ ι C * ι C := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    have hA3 : (3 : DiffRing V) ≤ ι (Q.A R N s w) * ι (Q.A R N s w) - 1 := by nlinarith
    have hD' : 3 * (ι C * ι C) + 1 ≤ (ι (Q.A R N s w) * ι (Q.A R N s w) - 1) * ι C * ι C + 1 := by
      have := mul_le_mul_of_nonneg_right hA3 (by linarith : (0 : DiffRing V) ≤ ι C * ι C)
      nlinarith
    have hAD : 2 * ((ι (Q.A R N s w) * ι (Q.A R N s w) - 1) * ι C * ι C + 1) ≤
        ι (Q.A R N s w) * ((ι (Q.A R N s w) * ι (Q.A R N s w) - 1) * ι C * ι C + 1) :=
      mul_le_mul_of_nonneg_right ha2 (by linarith)
    have hWsq : 0 ≤ ι (Q.W b w) ^ 2 := sq_nonneg _
    nlinarith
  have hJ1 : (1 : DiffRing V) ≤ ι (Q.J R N s w) := by
    have hh := (ι_le_ι (V := V)).mpr (pos_iff_one_le.mp hJ0); simp only [map_one] at hh; exact hh
  have hqQ : ι qv ≤ Qr b w C := by
    rw [hq', hqv]
    have := ι_nonneg qv
    nlinarith
  have hm1 : (1 : DiffRing V) ≤ ι mv := by
    rw [← hmv]; exact model_discrete _ hm0
  have hz0' : ι (a0 R N h s w) = ι z0 ^ 2 := by rw [← map_pow, pow_two, hz0]; rfl
  have hz1' : ι (a1 R N s w C i j) = ι (2 * z1) ^ 2 := by
    rw [← map_pow]; unfold a1; rw [eD, eF, eI, hz1]; congr 1; ring
  have hnpos : ι (Q.W b w) ^ 2 + ι qv <
      ι mv * (ι (V0 R N h s w) + ι (V1 R N s w C i j) + ι z0 + ι (2 * z1)) := by
    have h0 := ι_nonneg (V0 R N h s w); have h0' := ι_nonneg z0; have h0'' := ι_nonneg (2 * z1)
    have hV1 := le_trans hbig hV1D
    have hsum : ι (V1 R N s w C i j) ≤ ι (V0 R N h s w) + ι (V1 R N s w C i j) + ι z0 + ι (2 * z1) := by
      linarith
    have hS0 : 0 ≤ ι (V0 R N h s w) + ι (V1 R N s w C i j) + ι z0 + ι (2 * z1) := by
      have := ι_nonneg (V1 R N s w C i j); linarith
    have hmS := mul_le_mul_of_nonneg_right hm1 hS0
    linarith
  have hn0 : (0 : DiffRing V) ≤
      ι mv * (ι (V0 R N h s w) + ι (V1 R N s w C i j) + ι z0 + ι (2 * z1)) - ι (Q.W b w) ^ 2 - ι qv := by
    linarith
  obtain ⟨n, hn⟩ := nonneg_iff.mp hn0
  refine ⟨h, s, w, C, i, j, n, hh, hs, hw, hC2, hi, hj, ?_, ?_⟩
  · apply (ι_lt_ι (V := V)).mp
    rw [map_zero, ← hn]; linarith
  · rw [value_eq hR hN hs hw hC2 hj, hz0', hz1', hmv]
    rw [show ι (Q.J R N s w) * (ι n + ι (Q.W b w) ^ 2) + Qr b w C -
        ι (Q.J R N s w) * ι mv * (ι (V0 R N h s w) + ι (V1 R N s w C i j)) =
        ι (Q.J R N s w) * ι mv * (ι z0 + ι (2 * z1)) by rw [← hn, hq', ← hqv]; ring]
    exact norm2_zero_of_root _ _ _

/-! ### The successor coordinate `C = c + 1` -/

theorem sound_succ {R N b g t h s w c i j n : V} (hR : 8 ≤ R) (hN : 8 ≤ N) (hbR : b ≤ R)
    (hb : 0 < b) (hbN : b ≤ N) (ht : 0 < t) (hh : 0 < h) (hs : 0 < s) (hw : 0 < w) (hc : 0 < c)
    (hi : 0 < i) (hj : 0 < j)
    (hz : value (ι R) (ι N) (ι b) (ι g) (ι t) (ι h) (ι s) (ι w) (ι c + 1) (ι i) (ι j) (ι n) = 0) :
    N * N ∣ binom (2 * R) R ∧ (∃ k, b = Exp.exp k) ∧ g < 4 * t := by
  have hC2 : 2 ≤ c + 1 := by
    rw [← one_add_one_eq_two]; exact add_le_add (pos_iff_one_le.mp hc) le_rfl
  have hz' : value (ι R) (ι N) (ι b) (ι g) (ι t) (ι h) (ι s) (ι w) (ι (c + 1)) (ι i) (ι j) (ι n) = 0 := by
    rwa [map_add, map_one]
  exact sound hR hN hbR hb hbN ht hh hs hw hC2 hi hj hz'

theorem complete_succ {R N b g t : V} (hR : 8 ≤ R) (hN : 8 ≤ N) (hbR : b ≤ R) (hb : 0 < b)
    (hbN : b ≤ N) (hgt : g < t) (hdvd : N * N ∣ binom (2 * R) R) (hpow : ∃ k, b = Exp.exp k) :
    ∃ h s w c i j n : V, 0 < h ∧ 0 < s ∧ 0 < w ∧ 0 < c ∧ 0 < i ∧ 0 < j ∧ 0 < n ∧
      value (ι R) (ι N) (ι b) (ι g) (ι t) (ι h) (ι s) (ι w) (ι c + 1) (ι i) (ι j) (ι n) = 0 := by
  obtain ⟨h, s, w, C, i, j, n, hh, hs, hw, hC2, hi, hj, hn, hz⟩ :=
    complete hR hN hbR hb hbN hgt hdvd hpow
  have hC1 : 1 ≤ C := le_trans one_le_two hC2
  refine ⟨h, s, w, C - 1, i, j, n, hh, hs, hw, ?_, hi, hj, hn, ?_⟩
  · exact lt_tsub_iff_left.mpr (by rw [add_zero]; exact lt_of_lt_of_le one_lt_two hC2)
  · rw [← map_one ι, ← map_add, tsub_add_cancel_of_le hC1]; exact hz

end Nine121.N105Finalizer

#print axioms Nine121.N105Finalizer.majorant
#print axioms Nine121.N105Finalizer.value_eq
#print axioms Nine121.N105Finalizer.sound_succ
#print axioms Nine121.N105Finalizer.complete_succ
