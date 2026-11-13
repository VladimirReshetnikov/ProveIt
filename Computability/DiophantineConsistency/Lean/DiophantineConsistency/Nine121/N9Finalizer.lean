import DiophantineConsistency.ModelNineRatio
import DiophantineConsistency.Nine121.SatPell
import DiophantineConsistency.Nine121.N9Norm

/-! # Package 101's saturated simple finalizer in every model of `𝗜𝚺₁`

`value R N b g t h s w C i j n` is the finalizer of
`101-constructive-reductions/nine/report_section.tex` (and
`inherited/FULL_NINE_SOUNDNESS.md`), with the prefix outputs `R, N, t` as inputs:
`U = N²w, Y = N²s, M = RY, P = 2M²U, K = R + 1 + h(P − 1), A = M(U + 1),
B₁ = 2R + 1, W = bw, J = 4A − 5, Q = 3WC − 2(W² − 1),
m = K²(4t − g) − 16t(C − KY)², D = (A² − 1)C² + 1, r = iJC², F = (A² − 1)Dr² + 1,
G = A + F(CD + 1 − A), H = C + F(B₁ + (j − 1)C), I = (G² − 1)H² + 1`, and the
norm `norm2 (J(n + W²) + Q − Jm(PK + ADrGH)) (Jm) ((P² − 1)K² + 1) (DFI)`.

* `sound`: a zero at positive model naturals gives `N² ∣ C(2R, R)`, `b = 2ᵏ` and
  `g < 4t`. The proof order is the audited one: strict majorants give `m > 0`
  before any root is used; then `C > B₁ + W` and the radicands separate;
  `N9Norm.roots_of_norm2_zero` gives the two squares and `J ∣ Q`;
  `SatPell.psi_of_sat` gives `C = ψ_A(B₁)`; Jones's old certificate
  (`ModelProductPell.exists_ProductPellConds`) rebuilds the conditions of
  `ModelNineRatio.ratio_sound` at `G = 32t`.
* `complete`: from `N² ∣ C(2R, R)`, `b = 2ᵏ` and `g < t`, the core of
  `ModelRatio.exists_B25core`, `SatPell.exists_sat` and
  `n = m(V₀ + V₁ + z₀ + z₁) − W² − Q/J` give a positive zero. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
noncomputable section
namespace Nine121.N9Finalizer
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ModelDifferenceRing ModelArithmetic NinePolynomial ArithmeticPellRecurrence ArithmeticBinomPascal
open ModelNineRatio
open N9Norm

section Ring
variable {A : Type*} [CommRing A]

/-- Package 101's saturated simple finalizer. -/
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
  let a1 := D * F * I
  let V1 := Am * D * r0 * G * H1
  norm2 (E0 - Ω * (V0 + V1)) Ω a0 a1

end Ring

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### The saturated registers in `V` -/

namespace S
variable (A C i J j B : V)
def D : V := (A * A - 1) * C * C + 1
def r : V := i * J * C * C
def F : V := (A * A - 1) * D A C * r C i J * r C i J + 1
def G : V := A + F A C i J * (C * D A C + 1 - A)
def H : V := C + F A C i J * (B + (j - 1) * C)
def I : V := (G A C i J * G A C i J - 1) * H A C i J j B * H A C i J j B + 1
end S

/-- The signed margin `m = K²(4t − g) − 16t(C − KY)²`. -/
def marg (R N b g t h s w C : V) : DiffRing V :=
  ι (Q.K R N h s w) ^ 2 * (4 * ι t - ι g) - 16 * ι t * (ι C - ι (Q.K R N h s w) * ι (Q.Y N s)) ^ 2

/-- The signed `Q = 3WC − 2(W² − 1)`. -/
def Qr (b w C : V) : DiffRing V := 3 * ι (Q.W b w) * ι C - 2 * (ι (Q.W b w) ^ 2 - 1)

/-- The two radicands and majorants, as model naturals. -/
def a0 (R N h s w : V) : V := (Q.P R N s w * Q.P R N s w - 1) * Q.K R N h s w * Q.K R N h s w + 1
def a1 (R N s w C i j : V) : V :=
  S.D (Q.A R N s w) C * S.F (Q.A R N s w) C i (Q.J R N s w) *
    S.I (Q.A R N s w) C i (Q.J R N s w) j (Q.B' R)
def V0 (R N h s w : V) : V := Q.P R N s w * Q.K R N h s w
def V1 (R N s w C i j : V) : V :=
  Q.A R N s w * S.D (Q.A R N s w) C * S.r C i (Q.J R N s w) * S.G (Q.A R N s w) C i (Q.J R N s w) *
    S.H (Q.A R N s w) C i (Q.J R N s w) j (Q.B' R)

/-- All registers of the finalizer as images of model naturals; `Θ` and `Ω`
stay signed. -/
theorem value_eq {R N b g t h s w C i j n : V} (hR : 8 ≤ R) (hN : 8 ≤ N) (hs : 0 < s)
    (hw : 0 < w) (hC : 0 < C) (hj : 0 < j) :
    value (ι R) (ι N) (ι b) (ι g) (ι t) (ι h) (ι s) (ι w) (ι C) (ι i) (ι j) (ι n) =
      norm2 (ι (Q.J R N s w) * (ι n + ι (Q.W b w) ^ 2) + Qr b w C -
          ι (Q.J R N s w) * marg R N b g t h s w C * (ι (V0 R N h s w) + ι (V1 R N s w C i j)))
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
  simp only [value]
  rw [eY, eU, eM, eP, eK, eA, eW, eB, eJ, eD, er, eF, eL, eG, eZ, eH, eI, ea0]
  simp only [marg, Qr, a1, V0, V1, map_mul]

/-! ### Register sizes -/

theorem register_sizes {R N b h s w C i j : V} (hR : 8 ≤ R) (hN : 8 ≤ N) (hb : 0 < b) (hbR : b ≤ R)
    (hh : 0 < h) (hs : 0 < s) (hw : 0 < w) (hC : 0 < C) (hi : 0 < i) (hj : 0 < j) :
    64 ≤ Q.Y N s ∧ R + Q.P R N s w ≤ Q.K R N h s w ∧ Q.W b w < Q.P R N s w ∧
      Q.P R N s w + 1 ≤ Q.A R N s w * Q.A R N s w ∧ 3 ≤ Q.J R N s w ∧
      1 ≤ S.r C i (Q.J R N s w) ∧ 1 ≤ Q.P R N s w := by
  obtain ⟨hP1, hA2⟩ := ModelNineRatio.sizes hR hN hs hw
  have hNN : 64 ≤ N * N := calc
    (64 : V) = 8 * 8 := by norm_num
    _ ≤ N * N := mul_le_mul hN hN (by simp) (by simp)
  have hY : 64 ≤ Q.Y N s := le_trans hNN (le_mul_of_one_le_right (by simp) (pos_iff_one_le.mp hs))
  have hU : 1 ≤ Q.U N w := le_trans (le_trans (by norm_num) hNN)
    (le_mul_of_one_le_right (by simp) (pos_iff_one_le.mp hw))
  have hK : R + Q.P R N s w ≤ Q.K R N h s w := by
    unfold Q.K
    have e : R + Q.P R N s w = R + 1 + 1 * (Q.P R N s w - 1) := by
      rw [one_mul, add_assoc, add_tsub_cancel_of_le hP1]
    rw [e]
    exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_right (pos_iff_one_le.mp hh) (Arithmetic.zero_le _))
  have hM : b ≤ Q.M R N s := le_trans hbR (le_mul_of_one_le_right (Arithmetic.zero_le _)
    (le_trans (by norm_num) hY))
  have hUw : w ≤ Q.U N w := le_mul_of_one_le_left (Arithmetic.zero_le _) (le_trans (by norm_num) hNN)
  have hM1 : 1 ≤ Q.M R N s := le_trans (pos_iff_one_le.mp hb) hM
  have hPW : Q.W b w < Q.P R N s w := by
    unfold Q.P Q.W
    have h1 : b * w ≤ Q.M R N s * Q.U N w := mul_le_mul hM hUw (Arithmetic.zero_le _) (Arithmetic.zero_le _)
    have h2 : Q.M R N s * Q.U N w ≤ Q.M R N s * Q.M R N s * Q.U N w := by
      rw [mul_assoc]; exact le_mul_of_one_le_left (Arithmetic.zero_le _) hM1
    have h3 : 0 < b * w := mul_pos hb hw
    calc b * w < b * w + b * w := lt_add_of_pos_right _ h3
      _ ≤ 2 * Q.M R N s * Q.M R N s * Q.U N w := by
          calc b * w + b * w ≤ Q.M R N s * Q.M R N s * Q.U N w + Q.M R N s * Q.M R N s * Q.U N w :=
                add_le_add (h1.trans h2) (h1.trans h2)
            _ = 2 * Q.M R N s * Q.M R N s * Q.U N w := by ring
  have hPA : Q.P R N s w + 1 ≤ Q.A R N s w * Q.A R N s w := by
    unfold Q.P Q.A
    have hU0 : 0 ≤ Q.U N w := Arithmetic.zero_le _
    calc 2 * Q.M R N s * Q.M R N s * Q.U N w + 1
        ≤ 2 * Q.M R N s * Q.M R N s * Q.U N w + Q.M R N s * Q.M R N s * (Q.U N w * Q.U N w + 1) := by
          exact add_le_add (le_refl _) (le_trans (one_le_mul_of_one_le_of_one_le hM1 hM1)
            (le_mul_of_one_le_right (Arithmetic.zero_le _) le_add_self))
      _ = Q.M R N s * (Q.U N w + 1) * (Q.M R N s * (Q.U N w + 1)) := by ring
  have hJ3 : 3 ≤ Q.J R N s w := by
    unfold Q.J
    apply le_tsub_of_add_le_left
    calc (5 : V) + 3 = 4 * 2 := by norm_num
      _ ≤ 4 * Q.A R N s w := mul_le_mul_of_nonneg_left hA2 (by simp)
  have hr : 1 ≤ S.r C i (Q.J R N s w) := by
    unfold S.r
    have := mul_pos (mul_pos (mul_pos hi (lt_of_lt_of_le (by norm_num) hJ3)) hC) hC
    exact pos_iff_one_le.mp this
  exact ⟨hY, hK, hPW, hPA, hJ3, hr, hP1⟩

/-! ### Soundness -/

set_option maxHeartbeats 8000000 in
/-- **Soundness**: a positive zero gives the binomial calibration, the binary base and the cap. -/
theorem sound {R N b g t h s w C i j n : V} (hR : 8 ≤ R) (hN : 8 ≤ N) (hbR : b ≤ R) (hb : 0 < b)
    (hbN : b ≤ N) (ht : 0 < t) (hh : 0 < h) (hs : 0 < s) (hw : 0 < w) (hC : 0 < C)
    (hi : 0 < i) (hj : 0 < j)
    (hz : value (ι R) (ι N) (ι b) (ι g) (ι t) (ι h) (ι s) (ι w) (ι C) (ι i) (ι j) (ι n) = 0) :
    N * N ∣ binom (2 * R) R ∧ (∃ k, b = Exp.exp k) ∧ g < 4 * t := by
  rw [value_eq hR hN hs hw hC hj] at hz
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
  have ea0 : ι (a0 R N h s w) = (p ^ 2 - 1) * k ^ 2 + 1 := by
    have hPP : 1 ≤ Q.P R N s w * Q.P R N s w := one_le_mul_of_one_le_of_one_le hP1 hP1
    rw [hp, hk]; simp only [a0, map_add, map_mul, map_one, ι_sub_of_le hPP]; ring
  have ea1 : ι (a1 R N s w C i j) = d * f * I := by simp only [a1, map_mul, hd, hf, hI]
  have eV0 : ι (V0 R N h s w) = p * k := by simp only [V0, map_mul, hp, hk]
  have eV1 : ι (V1 R N s w C i j) = a * d * r * G * H := by simp only [V1, map_mul, ha, hd, hrr, hG, hH]
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
  have hc1 : (1 : DiffRing V) ≤ c := by have hh := (ι_le_ι (V := V)).mpr (pos_iff_one_le.mp hC); simp only [map_one, map_ofNat] at hh; exact hh
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
  -- the two strict majorants
  have hV0 : (p ^ 2 - 1) * k ^ 2 + 1 < (p * k) ^ 2 := by nlinarith
  have hV1 : d * f * I < (a * d * r * G * H) ^ 2 := by
    have e : (a * d * r * G * H) ^ 2 - d * f * I =
        d * (d * r ^ 2 - 1) * G ^ 2 * H ^ 2 + d * f * (H ^ 2 - 1) := by
      rw [eI, ef]; ring
    have h1 : 0 < d * (d * r ^ 2 - 1) * G ^ 2 * H ^ 2 := by
      have hr2 : (1 : DiffRing V) ≤ r ^ 2 := one_le_pow₀ hr1'
      have hdr : (1 : DiffRing V) ≤ d * r ^ 2 - 1 := by nlinarith
      have hG2 : (1 : DiffRing V) ≤ G ^ 2 := one_le_pow₀ hG1'
      have hH2 : (1 : DiffRing V) ≤ H ^ 2 := one_le_pow₀ hH1
      exact mul_pos (mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)) (by linarith)
    have h2 : 0 ≤ d * f * (H ^ 2 - 1) := by
      have hH2 : (1 : DiffRing V) ≤ H ^ 2 := one_le_pow₀ hH1
      exact mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
    linarith
  have hE0 : 0 < J * (ι n + W ^ 2) + Qr b w C := by
    simp only [Qr]
    rw [← hW, ← hc]
    have hn0 := ι_nonneg n
    have h1 : 0 ≤ J * ι n := mul_nonneg (by linarith) hn0
    have h2 : 0 ≤ (J - 2) * W ^ 2 := mul_nonneg (by linarith) (sq_nonneg W)
    have h3 : 0 ≤ 3 * W * c := mul_nonneg (mul_nonneg (by norm_num) hW0) (by linarith)
    nlinarith
  -- the margin is positive
  set m := marg R N b g t h s w C with hm
  have hm0 : 0 < m := by
    by_contra hneg
    have hm' : m ≤ 0 := le_of_not_gt hneg
    have hJm : J * m ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hm'
    have hI0 : (0 : DiffRing V) ≤ I := by
      rw [eI]
      have hG2 : (1 : DiffRing V) ≤ G ^ 2 := one_le_pow₀ hG1'
      have : 0 ≤ (G ^ 2 - 1) * H ^ 2 := mul_nonneg (by linarith) (sq_nonneg H)
      linarith
    have hpos := norm2_pos_of_nonpos_scale (U := p * k) (W := a * d * r * G * H)
      (by have := mul_nonneg (by nlinarith : (0 : DiffRing V) ≤ p ^ 2 - 1) (sq_nonneg k); linarith)
      (mul_nonneg (mul_nonneg (by linarith) (by linarith)) hI0)
      (mul_pos (by linarith) (by linarith))
      (mul_pos (mul_pos (mul_pos (mul_pos (by linarith) (by linarith)) (by linarith))
        (by linarith)) (by linarith)) hV0 hV1 hJm hE0
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
  have hsep : (p ^ 2 - 1) * k ^ 2 + 1 < d * f * I := by
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
  -- the roots
  have hΩ : J * m ≠ 0 := ne_of_gt (mul_pos (by linarith) hm0)
  obtain ⟨z0, z1, hz0, hz1, hθ⟩ := roots_of_norm2_zero hΩ (ne_of_lt hsep) hz
  -- `J ∣ Q`
  have hJQ : J ∣ Qr b w C := by
    refine ⟨m * (p * k + a * d * r * G * H + z0 + z1) - (ι n + W ^ 2), ?_⟩
    linear_combination hθ
  -- `DFI` is a square of a model natural
  have ha1sq : ∃ u : V, S.D (Q.A R N s w) C * S.F (Q.A R N s w) C i (Q.J R N s w) *
      S.I (Q.A R N s w) C i (Q.J R N s w) j (Q.B' R) = u * u := by
    apply (isSquare_ι _).mp
    refine ⟨z1, ?_⟩
    rw [map_mul, map_mul, ← hd, ← hf, ← hI, hz1]; ring
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
    have hJd : J = 4 * a - 5 := by
      have hA5 : 5 ≤ 4 * Q.A R N s w := ModelNineRatio.five_le_four_mul hA2
      rw [hJ, ha]; simp only [Q.J, ι_sub_of_le hA5, map_mul, map_ofNat]
    have e1 : (2 * ι (Q.A R N s w) * ι (2 : V) - ι (2 : V) * ι (2 : V) - 1 : DiffRing V) = J := by
      rw [hJd, ← ha, map_ofNat]; ring
    have e2 : ι (2 : V) * (ι (Q.W b w) ^ 2 - 1) - (ι (2 : V) ^ 2 - 1) * ι (Q.W b w) * ι C =
        -Qr b w C := by
      simp only [Qr, map_ofNat]; ring
    rw [e1, e2]; exact (dvd_neg).mpr hJQ
  obtain ⟨hdvd, hpow⟩ := (ModelRatio.lemma_2_25 R N b hR hN hbR hb hbN).mpr
    ⟨h, s, w, φ, _, _, _, _, _, _, _, _, _, _, hh, hs, hw, hφ0, hcore, hB13⟩
  exact ⟨hdvd, hpow, hgt⟩

/-! ### Completeness -/

set_option maxHeartbeats 8000000 in
/-- **Completeness**: from the calibration, a binary base and `g < t`, a positive zero. -/
theorem complete {R N b g t : V} (hR : 8 ≤ R) (hN : 8 ≤ N) (hbR : b ≤ R) (hb : 0 < b)
    (hbN : b ≤ N) (hgt : g < t) (hdvd : N * N ∣ binom (2 * R) R) (hpow : ∃ k, b = Exp.exp k) :
    ∃ h s w C i j n : V, 0 < h ∧ 0 < s ∧ 0 < w ∧ 0 < C ∧ 0 < i ∧ 0 < j ∧ 0 < n ∧
      value (ι R) (ι N) (ι b) (ι g) (ι t) (ι h) (ι s) (ι w) (ι C) (ι i) (ι j) (ι n) = 0 := by
  obtain ⟨h, s, w, φ, A, B', C, K, M, P, U, V', W, Y, hh, hs, hw, -, hcore, hWe, hBWC, hB3s⟩ :=
    ModelRatio.exists_B25core R N b hR hN hbR hb hbN hdvd hpow
  obtain ⟨B1, ⟨z0, hz0⟩, -, B4, B5, B6, B7, B8, B9, B10, B11, -, B14⟩ := hcore
  subst B1 B4 B5 B6 B7 B9 B10 B11
  -- the quantities are the `Q` quantities
  have eP : 2 * (R * (N * N * s)) * (R * (N * N * s)) * (N * N * w) = Q.P R N s w := rfl
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
  -- the final coordinate
  have hV1D : ι (Q.A R N s w * D) ≤ ι (V1 R N s w C i j) := by
    rw [← eD]
    apply (ι_le_ι (V := V)).mpr
    unfold V1
    have hr : 1 ≤ S.r C i (Q.J R N s w) := by
      unfold S.r
      exact pos_iff_one_le.mp (mul_pos (mul_pos (mul_pos hi hJ0) hC0) hC0)
    have hG' : 1 ≤ S.G (Q.A R N s w) C i (Q.J R N s w) :=
      le_trans (le_trans one_le_two hA2) (le_add_of_nonneg_right (Arithmetic.zero_le _))
    have hH' : 1 ≤ S.H (Q.A R N s w) C i (Q.J R N s w) j (Q.B' R) :=
      le_trans (pos_iff_one_le.mp hC0) le_self_add
    calc Q.A R N s w * S.D (Q.A R N s w) C
        ≤ Q.A R N s w * S.D (Q.A R N s w) C * S.r C i (Q.J R N s w) :=
          le_mul_of_one_le_right (Arithmetic.zero_le _) hr
      _ ≤ Q.A R N s w * S.D (Q.A R N s w) C * S.r C i (Q.J R N s w) *
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
  have hz1' : ι (a1 R N s w C i j) = ι z1 ^ 2 := by
    rw [← map_pow, pow_two, ← hz1]; unfold a1; rw [eD, eF, eI]
  have hnpos : ι (Q.W b w) ^ 2 + ι qv < ι mv * (ι (V0 R N h s w) + ι (V1 R N s w C i j) + ι z0 + ι z1) := by
    have h0 := ι_nonneg (V0 R N h s w); have h0' := ι_nonneg z0; have h0'' := ι_nonneg z1
    have hV1 := le_trans hbig hV1D
    have hsum : ι (V1 R N s w C i j) ≤ ι (V0 R N h s w) + ι (V1 R N s w C i j) + ι z0 + ι z1 := by
      linarith
    have hS0 : 0 ≤ ι (V0 R N h s w) + ι (V1 R N s w C i j) + ι z0 + ι z1 := by
      have := ι_nonneg (V1 R N s w C i j); linarith
    have hmS := mul_le_mul_of_nonneg_right hm1 hS0
    linarith
  have hn0 : (0 : DiffRing V) ≤
      ι mv * (ι (V0 R N h s w) + ι (V1 R N s w C i j) + ι z0 + ι z1) - ι (Q.W b w) ^ 2 - ι qv := by
    linarith
  obtain ⟨n, hn⟩ := nonneg_iff.mp hn0
  refine ⟨h, s, w, C, i, j, n, hh, hs, hw, hC0, hi, hj, ?_, ?_⟩
  · apply (ι_lt_ι (V := V)).mp
    rw [map_zero, ← hn]; linarith
  · rw [value_eq hR hN hs hw hC0 hj, hz0', hz1', hmv]
    rw [show ι (Q.J R N s w) * (ι n + ι (Q.W b w) ^ 2) + Qr b w C -
        ι (Q.J R N s w) * ι mv * (ι (V0 R N h s w) + ι (V1 R N s w C i j)) =
        ι (Q.J R N s w) * ι mv * (ι z0 + ι z1) by rw [← hn, hq', ← hqv]; ring]
    exact norm2_zero_of_root _ _ _

end Nine121.N9Finalizer

#print axioms Nine121.N9Finalizer.value_eq
#print axioms Nine121.N9Finalizer.sound
#print axioms Nine121.N9Finalizer.complete