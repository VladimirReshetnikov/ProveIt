import DiophantineConsistency.Nine121.N9Finalizer
import DiophantineConsistency.Nine121.N1057Majorant

/-! # Package 101's complete-radical finalizer in every model of `𝗜𝚺₁`

`value R N b g t h s w C i j n` is the complete-radical finalizer of
`101-constructive-reductions/nine/report_section.tex` (the 1,057-operation
`equations/boundary_complete.json`), with the prefix outputs `R, N, t` as inputs. Its ratio and
saturated-Pell registers are those of `N9Finalizer.value` (`U, Y, M, P, K, A, B₁, W, J, Q, m, Ω,
E₀, V₀, a₀, D, r = iJC², F, Λ, G, Z, H, I`); only the second radicand and majorant change:

  `σ = 1024C⁵i`, `a₁ = DFI·σ²`, `V₁ = Π(A, C, i, Z)` (the 333-term `N1057Majorant.PiR`),

and the norm is `norm2 (E₀ − Ω(V₀ + V₁)) Ω a₀ a₁`.

* `sound`: a zero at positive model naturals with `N ≥ 32` gives `N² ∣ C(2R, R)`, `b = 2ᵏ` and
  `g < 4t`, in the audited order of `N9Finalizer.sound`: the strict majorants (`a₀ < V₀²`, and
  `DFIσ² < Π²`, `Π > AD` from `N1057Majorant.majorant`, which needs `A ≥ 2²⁰`, i.e. `N ≥ 32`) give
  `m > 0`; the separation `a₀ < a₁`; the roots; `J ∣ Q`; `σ ∣ √a₁` (`sq_dvd_sq`), hence `DFI` is a
  square; `SatPell.psi_of_sat`; Lemma 2.25.
* `complete`: from `N² ∣ C(2R, R)`, `b = 2ᵏ` and `g < t` (and `N ≥ 32`), a positive zero, using
  `Π > AD` (so `n = m(V₀ + V₁ + z₀ + σz₁) − W² − Q/J > 0`). -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
noncomputable section
namespace Nine121.N1057Finalizer
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ModelDifferenceRing ModelArithmetic NinePolynomial ArithmeticPellRecurrence ArithmeticBinomPascal
open ModelNineRatio
open N9Norm
open N9Finalizer hiding value value_eq sound complete V1 a1

section Ring
variable {A : Type*} [CommRing A]

/-- Package 101's complete-radical finalizer. -/
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
  let σ := 1024 * C ^ 5 * i
  let a1 := D * F * I * (σ * σ)
  let V1 := N1057Majorant.PiR Am C i Z
  norm2 (E0 - Ω * (V0 + V1)) Ω a0 a1

end Ring

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### The new registers -/

/-- `σ = 1024C⁵i`. -/
def sg (C i : V) : V := 1024 * (C * C * C * C * C) * i

/-- `a₁ = DFI·σ²`. -/
def a1 (R N s w C i j : V) : V := N9Finalizer.a1 R N s w C i j * (sg C i * sg C i)

/-- `Z = B₁ + (j − 1)C`. -/
def Zr (R C j : V) : V := Q.B' R + (j - 1) * C

/-- `V₁ = Π(A, C, i, Z)`, a signed value. -/
def V1 (R N s w C i j : V) : DiffRing V :=
  N1057Majorant.PiR (ι (Q.A R N s w)) (ι C) (ι i) (ι (Zr R C j))

theorem ι_sg (C i : V) : ι (sg C i) = 1024 * ι C ^ 5 * ι i := by
  simp only [sg, map_mul, map_ofNat]; ring

/-- `A ≥ 2²⁰` once `N ≥ 32`. -/
theorem A_big {R N s w : V} (hR : 8 ≤ R) (hN : 32 ≤ N) (hs : 0 < s) (hw : 0 < w) :
    1048576 ≤ Q.A R N s w := by
  have hNN : (1024 : V) ≤ N * N := calc
    (1024 : V) = 32 * 32 := by norm_num
    _ ≤ N * N := mul_le_mul hN hN (by simp) (by simp)
  have hY : (1024 : V) ≤ Q.Y N s := le_trans hNN (le_mul_of_one_le_right (by simp) (pos_iff_one_le.mp hs))
  have hU : (1024 : V) ≤ Q.U N w := le_trans hNN (le_mul_of_one_le_right (by simp) (pos_iff_one_le.mp hw))
  have hM : (8192 : V) ≤ Q.M R N s := calc
    (8192 : V) = 8 * 1024 := by norm_num
    _ ≤ R * Q.Y N s := mul_le_mul hR hY (by simp) (by simp)
  unfold Q.A
  calc (1048576 : V) ≤ 8192 * 1025 := by norm_num
    _ ≤ Q.M R N s * (Q.U N w + 1) :=
        mul_le_mul hM (by calc (1025 : V) = 1024 + 1 := by norm_num
                            _ ≤ Q.U N w + 1 := add_le_add hU le_rfl) (by simp) (by simp)

theorem one_le_Zr (R C j : V) : 1 ≤ Zr R C j :=
  le_trans (le_add_self : (1 : V) ≤ 2 * R + 1) le_self_add

/-- All registers of the finalizer as images of model naturals; `Θ`, `Ω` and `V₁` stay signed. -/
theorem value_eq {R N b g t h s w C i j n : V} (hR : 8 ≤ R) (hN : 8 ≤ N) (hs : 0 < s)
    (hw : 0 < w) (hC : 0 < C) (hj : 0 < j) :
    value (ι R) (ι N) (ι b) (ι g) (ι t) (ι h) (ι s) (ι w) (ι C) (ι i) (ι j) (ι n) =
      norm2 (ι (Q.J R N s w) * (ι n + ι (Q.W b w) ^ 2) + Qr b w C -
          ι (Q.J R N s w) * marg R N b g t h s w C * (ι (V0 R N h s w) + V1 R N s w C i j))
        (ι (Q.J R N s w) * marg R N b g t h s w C) (ι (a0 R N h s w)) (ι (a1 R N s w C i j)) := by
  obtain ⟨hP1, hA2⟩ := ModelNineRatio.sizes hR hN hs hw
  have hA1 : 1 ≤ Q.A R N s w * Q.A R N s w := ModelNineRatio.one_le_sq_of_two_le hA2
  have hA5 : 5 ≤ 4 * Q.A R N s w := ModelNineRatio.five_le_four_mul hA2
  have hC1 : 1 ≤ C := pos_iff_one_le.mp hC
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
  have eσ : 1024 * ι C ^ 5 * ι i = ι (sg C i) := (ι_sg C i).symm
  simp only [value]
  rw [eY, eU, eM, eP, eK, eA, eW, eB, eJ, eD, er, eF, eL, eG, eZ, eH, eI, ea0, eσ]
  simp only [marg, Qr, a1, N9Finalizer.a1, V0, V1, Zr, map_mul]

/-! ### Soundness -/

set_option maxHeartbeats 8000000 in
/-- **Soundness**: a positive zero gives the binomial calibration, the binary base and the cap. -/
theorem sound {R N b g t h s w C i j n : V} (hR : 8 ≤ R) (hN : 32 ≤ N) (hbR : b ≤ R) (hb : 0 < b)
    (hbN : b ≤ N) (ht : 0 < t) (hh : 0 < h) (hs : 0 < s) (hw : 0 < w) (hC : 0 < C)
    (hi : 0 < i) (hj : 0 < j)
    (hz : value (ι R) (ι N) (ι b) (ι g) (ι t) (ι h) (ι s) (ι w) (ι C) (ι i) (ι j) (ι n) = 0) :
    N * N ∣ binom (2 * R) R ∧ (∃ k, b = Exp.exp k) ∧ g < 4 * t := by
  have hN8 : 8 ≤ N := le_trans (by norm_num) hN
  rw [value_eq hR hN8 hs hw hC hj] at hz
  obtain ⟨hY64, hRPK, hWP, hPA, hJ3, hr1, hP1⟩ := register_sizes hR hN8 hb hbR hh hs hw hC hi hj
  obtain ⟨-, hA2⟩ := ModelNineRatio.sizes hR hN8 hs hw
  have hA1 : 1 ≤ Q.A R N s w * Q.A R N s w := ModelNineRatio.one_le_sq_of_two_le hA2
  have hA5 : 5 ≤ 4 * Q.A R N s w := ModelNineRatio.five_le_four_mul hA2
  have hj1 : 1 ≤ j := pos_iff_one_le.mp hj
  have hDA : Q.A R N s w ≤ C * S.D (Q.A R N s w) C + 1 := by
    have hC1 : 1 ≤ C := pos_iff_one_le.mp hC
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
  set zz : DiffRing V := ι (Zr R C j) with hzz
  set σ : DiffRing V := ι (sg C i) with hσ
  set PP : DiffRing V := V1 R N s w C i j with hPPd
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
  have eJd : J = 4 * a - 5 := by
    rw [hJ, ha]; simp only [Q.J, ι_sub_of_le hA5, map_mul, map_ofNat]
  have er : r = ι i * J * c ^ 2 := by
    rw [hrr, hJ, hc]; simp only [S.r, map_mul]; ring
  have eG : G = a + f * (c * d + 1 - a) := by
    rw [hG, ha, hf, hc, hd]; simp only [S.G, map_add, map_mul, map_one, ι_sub_of_le hDA]
  have eH : H = c + f * zz := by
    rw [hH, hc, hf, hzz]; simp only [S.H, Zr, map_add, map_mul]
  have ea0 : ι (a0 R N h s w) = (p ^ 2 - 1) * k ^ 2 + 1 := by
    have hPP : 1 ≤ Q.P R N s w * Q.P R N s w := one_le_mul_of_one_le_of_one_le hP1 hP1
    rw [hp, hk]; simp only [a0, map_add, map_mul, map_one, ι_sub_of_le hPP]; ring
  have ea1 : ι (a1 R N s w C i j) = d * f * I * (σ * σ) := by
    simp only [a1, N9Finalizer.a1, map_mul, hd, hf, hI, hσ]
  have eV0 : ι (V0 R N h s w) = p * k := by simp only [V0, map_mul, hp, hk]
  rw [ea0, ea1, eV0] at hz
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
  have haB : (1048576 : DiffRing V) ≤ a := by
    have hh := (ι_le_ι (V := V)).mpr (A_big hR hN hs hw); simp only [map_ofNat] at hh; exact hh
  have hJ3' : (3 : DiffRing V) ≤ J := by have hh := (ι_le_ι (V := V)).mpr hJ3; simp only [map_one, map_ofNat] at hh; exact hh
  have hy64 : (64 : DiffRing V) ≤ y := by have hh := (ι_le_ι (V := V)).mpr hY64; simp only [map_one, map_ofNat] at hh; exact hh
  have hc1 : (1 : DiffRing V) ≤ c := by have hh := (ι_le_ι (V := V)).mpr (pos_iff_one_le.mp hC); simp only [map_one, map_ofNat] at hh; exact hh
  have hi1 : (1 : DiffRing V) ≤ ι i := by have hh := (ι_le_ι (V := V)).mpr (pos_iff_one_le.mp hi); simp only [map_one] at hh; exact hh
  have hz1' : (1 : DiffRing V) ≤ zz := by have hh := (ι_le_ι (V := V)).mpr (one_le_Zr R C j); simp only [map_one] at hh; exact hh
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
  have hσ1 : (1 : DiffRing V) ≤ σ := by
    rw [hσ, ι_sg, ← hc]
    have : (1 : DiffRing V) ≤ c ^ 5 := one_le_pow₀ hc1
    nlinarith
  have hI0 : (0 : DiffRing V) ≤ I := by
    rw [eI]
    have hG2 : (1 : DiffRing V) ≤ G ^ 2 := one_le_pow₀ hG1'
    have : 0 ≤ (G ^ 2 - 1) * H ^ 2 := mul_nonneg (by linarith) (sq_nonneg H)
    linarith
  -- the complete-radical majorant
  obtain ⟨hmaj, hgap⟩ := N1057Majorant.majorant haB hc1 hi1 hz1'
  have hDr : N1057Majorant.Dr a c = d := by rw [ed]; rfl
  have hFr : N1057Majorant.Fr a c (ι i) = f := by
    unfold N1057Majorant.Fr; rw [hDr, ef, er, eJd]
  have hGr : N1057Majorant.Gr a c (ι i) = G := by
    unfold N1057Majorant.Gr; rw [hDr, hFr, eG]
  have hHr : N1057Majorant.Hr a c (ι i) zz = H := by
    unfold N1057Majorant.Hr; rw [hFr, eH]
  have hIr : N1057Majorant.Ir a c (ι i) zz = I := by
    unfold N1057Majorant.Ir; rw [hGr, hHr, eI]
  have hsig : N1057Majorant.sig c (ι i) = σ := by
    unfold N1057Majorant.sig; rw [hσ, ι_sg]
  have hPi : N1057Majorant.PiR a c (ι i) zz = PP := rfl
  rw [hDr, hFr, hIr, hsig, hPi] at hmaj
  rw [hDr, hPi] at hgap
  -- the two strict majorants
  have hV0 : (p ^ 2 - 1) * k ^ 2 + 1 < (p * k) ^ 2 := by nlinarith
  have hV1 : d * f * I * (σ * σ) < PP ^ 2 := by
    have : σ * σ = σ ^ 2 := by ring
    rw [this]; exact hmaj
  have had0 : 0 ≤ a * d := mul_nonneg (by linarith) (by linarith)
  have hPP0 : 0 < PP := by linarith
  have hE0 : 0 < J * (ι n + W ^ 2) + Qr b w C := by
    simp only [Qr]
    rw [← hW, ← hc]
    have hn0 := ι_nonneg n
    have h1 : 0 ≤ J * ι n := mul_nonneg (by linarith) hn0
    have h2 : 0 ≤ (J - 2) * W ^ 2 := mul_nonneg (by linarith) (sq_nonneg W)
    have h3 : 0 ≤ 3 * W * c := mul_nonneg (mul_nonneg (by norm_num) hW0) (by linarith)
    nlinarith
  have ha10 : 0 ≤ d * f * I * (σ * σ) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by linarith) (by linarith)) hI0) (mul_nonneg (by linarith) (by linarith))
  -- the margin is positive
  set m := marg R N b g t h s w C with hm
  have hm0 : 0 < m := by
    by_contra hneg
    have hm' : m ≤ 0 := le_of_not_gt hneg
    have hJm : J * m ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hm'
    have hpos := norm2_pos_of_nonpos_scale (U := p * k) (W := PP)
      (by have := mul_nonneg (by nlinarith : (0 : DiffRing V) ≤ p ^ 2 - 1) (sq_nonneg k); linarith)
      ha10 (mul_pos (by linarith) (by linarith)) hPP0 hV0 hV1 hJm hE0
    rw [hz] at hpos
    exact _root_.lt_irrefl _ hpos
  have ht0 : (0 : DiffRing V) < ι t := by have hh := (ι_lt_ι (V := V)).mpr ht; simp only [map_zero, map_one, map_ofNat] at hh; exact hh
  have hg0 := ι_nonneg g
  have hmd : m = k ^ 2 * (4 * ι t - ι g) - 16 * ι t * (c - k * y) ^ 2 := by
    rw [hm, hk, hc, hy]; rfl
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
    have hc2 : c ^ 2 ≤ c ^ 2 * c ^ 2 := le_mul_of_one_le_right (sq_nonneg c) (one_le_pow₀ hc1)
    have h2 : p ^ 2 * k ^ 2 ≤ (p * c ^ 2) ^ 2 := by
      have := mul_le_mul_of_nonneg_left (le_trans hkc hc2) (sq_nonneg p)
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
  have hsep : (p ^ 2 - 1) * k ^ 2 + 1 < d * f * I * (σ * σ) := by
    have hσσ : (1 : DiffRing V) ≤ σ * σ := one_le_mul_of_one_le_of_one_le hσ1 hσ1
    have : d * f * I ≤ d * f * I * (σ * σ) :=
      le_mul_of_one_le_right (mul_nonneg (mul_nonneg (by linarith) (by linarith)) hI0) hσσ
    linarith
  -- the roots
  have hΩ : J * m ≠ 0 := ne_of_gt (mul_pos (by linarith) hm0)
  obtain ⟨z0, z1, hz0, hz1, hθ⟩ := roots_of_norm2_zero hΩ (ne_of_lt hsep) hz
  -- `J ∣ Q`
  have hJQ : J ∣ Qr b w C := by
    refine ⟨m * (p * k + PP + z0 + z1) - (ι n + W ^ 2), ?_⟩
    linear_combination hθ
  -- `σ ∣ z₁`, so `DFI` is a square of a model natural
  have hσ0 : σ ≠ 0 := ne_of_gt (lt_of_lt_of_le one_pos hσ1)
  obtain ⟨u1, hu1⟩ : σ ∣ z1 := by
    refine ModelRelationCombining.sq_dvd_sq σ z1 hσ0 ⟨d * f * I, ?_⟩
    rw [← hz1]; ring
  have hdfI : d * f * I = u1 ^ 2 := by
    have e : σ ^ 2 * (d * f * I) = σ ^ 2 * u1 ^ 2 := by
      have := hz1; rw [hu1] at this; linear_combination this
    exact mul_left_cancel₀ (pow_ne_zero 2 hσ0) e
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
  obtain ⟨hdvd, hpow⟩ := (ModelRatio.lemma_2_25 R N b hR hN8 hbR hb hbN).mpr
    ⟨h, s, w, φ, _, _, _, _, _, _, _, _, _, _, hh, hs, hw, hφ0, hcore, hB13⟩
  exact ⟨hdvd, hpow, hgt⟩

/-! ### Completeness -/

set_option maxHeartbeats 8000000 in
/-- **Completeness**: from the calibration, a binary base and `g < t`, a positive zero. -/
theorem complete {R N b g t : V} (hR : 8 ≤ R) (hN : 32 ≤ N) (hbR : b ≤ R) (hb : 0 < b)
    (hbN : b ≤ N) (hgt : g < t) (hdvd : N * N ∣ binom (2 * R) R) (hpow : ∃ k, b = Exp.exp k) :
    ∃ h s w C i j n : V, 0 < h ∧ 0 < s ∧ 0 < w ∧ 0 < C ∧ 0 < i ∧ 0 < j ∧ 0 < n ∧
      value (ι R) (ι N) (ι b) (ι g) (ι t) (ι h) (ι s) (ι w) (ι C) (ι i) (ι j) (ι n) = 0 := by
  have hN8 : 8 ≤ N := le_trans (by norm_num) hN
  obtain ⟨h, s, w, φ, A, B', C, K, M, P, U, V', W, Y, hh, hs, hw, -, hcore, hWe, hBWC, hB3s⟩ :=
    ModelRatio.exists_B25core R N b hR hN8 hbR hb hbN hdvd hpow
  obtain ⟨B1, ⟨z0, hz0⟩, -, B4, B5, B6, B7, B8, B9, B10, B11, -, B14⟩ := hcore
  subst B1 B4 B5 B6 B7 B9 B10 B11
  obtain ⟨hP1, hA2⟩ := ModelNineRatio.sizes hR hN8 hs hw
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
  have hC0 : 0 < C := by
    rw [hψ]; exact lt_of_lt_of_le (lt_trans (by norm_num) hB1) (ArithmeticPellRecurrence.time_le_y _ _)
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
  -- the final coordinate: `V₁ = Π > AD`
  have hV1D : ι (Q.A R N s w * D) ≤ V1 R N s w C i j := by
    have haB : (1048576 : DiffRing V) ≤ ι (Q.A R N s w) := by
      have hh := (ι_le_ι (V := V)).mpr (A_big hR hN hs hw); simp only [map_ofNat] at hh; exact hh
    have hc1 : (1 : DiffRing V) ≤ ι C := by
      have hh := (ι_le_ι (V := V)).mpr (pos_iff_one_le.mp hC0); simp only [map_one] at hh; exact hh
    have hi1 : (1 : DiffRing V) ≤ ι i := by
      have hh := (ι_le_ι (V := V)).mpr (pos_iff_one_le.mp hi); simp only [map_one] at hh; exact hh
    have hz1' : (1 : DiffRing V) ≤ ι (Zr R C j) := by
      have hh := (ι_le_ι (V := V)).mpr (one_le_Zr R C j); simp only [map_one] at hh; exact hh
    obtain ⟨-, hgap⟩ := N1057Majorant.majorant haB hc1 hi1 hz1'
    have hDr : N1057Majorant.Dr (ι (Q.A R N s w)) (ι C) = ι D := by
      rw [← eD]; unfold N1057Majorant.Dr
      simp only [S.D, map_add, map_mul, map_one, ι_sub_of_le hA1]; ring
    rw [hDr] at hgap
    rw [map_mul]; exact hgap.le
  have hbig : ι (Q.W b w) ^ 2 + Qr b w C + 1 ≤ ι (Q.A R N s w * D) := by
    simp only [Qr, map_mul]
    rw [← eD]
    simp only [S.D, map_add, map_mul, map_one, ι_sub_of_le hA1]
    have hWC : ι (Q.W b w) + 1 ≤ ι C := by
      have := (ι_le_ι (V := V)).mpr (lt_iff_succ_le.mp hWlt); simpa [Q.W] using this
    have hW0 := ι_nonneg (Q.W b w)
    have ha2 : (2 : DiffRing V) ≤ ι (Q.A R N s w) := by have hh := (ι_le_ι (V := V)).mpr hA2; simp only [map_one, map_ofNat] at hh; exact hh
    have hc1 : (1 : DiffRing V) ≤ ι C := le_trans (by linarith) hWC
    have hC2 : (1 : DiffRing V) ≤ ι C * ι C := one_le_mul_of_one_le_of_one_le hc1 hc1
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
  have hz1' : ι (a1 R N s w C i j) = (ι (sg C i) * ι z1) ^ 2 := by
    have e1 : ι (N9Finalizer.a1 R N s w C i j) = ι z1 ^ 2 := by
      rw [← map_pow, pow_two, ← hz1]; unfold N9Finalizer.a1; rw [eD, eF, eI]
    rw [a1, map_mul, map_mul, e1]; ring
  have hσ0 : (0 : DiffRing V) ≤ ι (sg C i) * ι z1 := mul_nonneg (ι_nonneg _) (ι_nonneg _)
  have hnpos : ι (Q.W b w) ^ 2 + ι qv <
      ι mv * (ι (V0 R N h s w) + V1 R N s w C i j + ι z0 + ι (sg C i) * ι z1) := by
    have h0 := ι_nonneg (V0 R N h s w); have h0' := ι_nonneg z0
    have hV1 := le_trans hbig hV1D
    have hAD0 : (0 : DiffRing V) ≤ ι (Q.A R N s w * D) := ι_nonneg _
    have hsum : V1 R N s w C i j ≤ ι (V0 R N h s w) + V1 R N s w C i j + ι z0 + ι (sg C i) * ι z1 := by
      linarith
    have hS0 : 0 ≤ ι (V0 R N h s w) + V1 R N s w C i j + ι z0 + ι (sg C i) * ι z1 := by linarith
    have hmS := mul_le_mul_of_nonneg_right hm1 hS0
    linarith
  have hn0 : (0 : DiffRing V) ≤
      ι mv * (ι (V0 R N h s w) + V1 R N s w C i j + ι z0 + ι (sg C i) * ι z1) - ι (Q.W b w) ^ 2 -
        ι qv := by
    linarith
  obtain ⟨n, hn⟩ := nonneg_iff.mp hn0
  refine ⟨h, s, w, C, i, j, n, hh, hs, hw, hC0, hi, hj, ?_, ?_⟩
  · apply (ι_lt_ι (V := V)).mp
    rw [map_zero, ← hn]; linarith
  · rw [value_eq hR hN8 hs hw hC0 hj, hz0', hz1', hmv]
    rw [show ι (Q.J R N s w) * (ι n + ι (Q.W b w) ^ 2) + Qr b w C -
        ι (Q.J R N s w) * ι mv * (ι (V0 R N h s w) + V1 R N s w C i j) =
        ι (Q.J R N s w) * ι mv * (ι z0 + ι (sg C i) * ι z1) by rw [← hn, hq', ← hqv]; ring]
    exact norm2_zero_of_root _ _ _

end Nine121.N1057Finalizer

#print axioms Nine121.N1057Finalizer.value_eq
#print axioms Nine121.N1057Finalizer.sound
#print axioms Nine121.N1057Finalizer.complete
