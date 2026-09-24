import Diophantine.Paper1982.Ratio
import Diophantine.Paper1982.ProductPell

/-!
# Jones 1982, §3: `N² ∣ C(2R, R)`, `b` pow 2 and the ceiling for `g` as four conditions

With `R, N, b` and the ceiling `G` given, the conditions of Lemma 2.25 (with (B8') and `V = 2`)
and of Lemma 2.27 (with `J = 2AV − V² − 1 = 4A − 5`) leave the unknowns `h, s, w, φ, i, j`
and four conditions:

* `(P² − 1)K² + 1 = □` (B2),
* `DFI = □` (A1),
* `JF ∣ QF + J(H − C)` with `Q = (V² − 1)WC − V(W² − 1)` ((B13) and `F ∣ H − C` combined, (M18)),
* `4(C − KY)²G + 8gK² < K²G` ((B3) stacked with the ceiling for `g`, (B3')).

The stacking uses the estimate `|C − KY| ≤ (25/64)K` of the necessity proof of Lemma 2.25.
Sufficiency gives `8g < G`; necessity needs `32g < G`.
-/

namespace Jones1982.Nine

open Pell Diophantine JSWW1976 Jones1978

/-- The free quantities. -/
structure Vars where
  (R N b g G h s w φ i j : ℤ)

namespace Vars

variable (v : Vars)

def U : ℤ := v.N ^ 2 * v.w
def Y : ℤ := v.N ^ 2 * v.s
def M : ℤ := v.R * v.Y
def P : ℤ := 2 * v.M ^ 2 * v.U
def K : ℤ := v.R + 1 + v.h * (v.P - 1)
def A : ℤ := v.M * (v.U + 1)
def B' : ℤ := 2 * v.R + 1
def W : ℤ := v.b * v.w
def C : ℤ := v.B' + v.W + v.φ
def J : ℤ := 4 * v.A - 5
def Q : ℤ := 3 * v.W * v.C - 2 * (v.W ^ 2 - 1)
def D : ℤ := (v.A ^ 2 - 1) * v.C ^ 2 + 1
def E : ℤ := v.i * v.J * v.D * v.C ^ 2
def F : ℤ := (v.A ^ 2 - 1) * v.E ^ 2 + 1
def Gp : ℤ := v.A + v.F * (v.C * v.D + 1 - v.A)
def H : ℤ := v.B' + v.j * v.C
def I : ℤ := (v.Gp ^ 2 - 1) * v.H ^ 2 + 1

/-- The four conditions. -/
def Conds : Prop :=
  IsSquare ((v.P ^ 2 - 1) * v.K ^ 2 + 1) ∧ IsSquare (v.D * v.F * v.I) ∧
    v.J * v.F ∣ v.Q * v.F + v.J * (v.H - v.C) ∧
    0 < v.K ^ 2 * v.G - 4 * (v.C - v.K * v.Y) ^ 2 * v.G - 8 * v.g * v.K ^ 2

/-- The quantities at natural values. -/
def ofNat (R N b g G h s w φ i j : ℕ) : Vars := ⟨R, N, b, g, G, h, s, w, φ, i, j⟩

end Vars

/-- `F ≡ 1 (mod J)`, hence `F ⊥ J`. -/
theorem isCoprime_F_J (v : Vars) : IsCoprime v.F v.J := by
  refine ⟨1, -((v.A ^ 2 - 1) * v.i ^ 2 * v.J * v.D ^ 2 * v.C ^ 4), ?_⟩
  simp only [Vars.F, Vars.E]
  ring

theorem natCast_isSquare {n : ℕ} {m : ℤ} (h : (n : ℤ) = m) : IsSquare m ↔ IsSquare n := by
  rw [← h, Int.isSquare_natCast_iff]

/-! ### The quantities at natural values -/

namespace NatQ

variable (R N b h s w φ i j : ℕ)

def U : ℕ := N ^ 2 * w
def Y : ℕ := N ^ 2 * s
def M : ℕ := R * Y N s
def P : ℕ := 2 * M R N s ^ 2 * U N w
def K : ℕ := R + 1 + h * (P R N s w - 1)
def A : ℕ := M R N s * (U N w + 1)
def B' : ℕ := 2 * R + 1
def W : ℕ := b * w
def C : ℕ := B' R + W b w + φ
def J : ℕ := 2 * A R N s w * 2 - 2 * 2 - 1
def D : ℕ := (A R N s w ^ 2 - 1) * C R b w φ ^ 2 + 1
def E : ℕ := i * J R N s w * D R N b s w φ * C R b w φ ^ 2
def F : ℕ := (A R N s w ^ 2 - 1) * E R N b s w φ i ^ 2 + 1
def Gp : ℕ := A R N s w + F R N b s w φ i * (C R b w φ * D R N b s w φ + 1 - A R N s w)
def H : ℕ := B' R + j * C R b w φ
def I : ℕ := (Gp R N b s w φ i ^ 2 - 1) * H R b w φ j ^ 2 + 1

end NatQ

section Casts

variable {R N b g G h s w φ i j : ℕ}

local notation "𝒱" => Vars.ofNat R N b g G h s w φ i j

theorem sizes_nat (hR : 8 ≤ R) (hN : 8 ≤ N) (hs : 0 < s) (hw : 0 < w) :
    1 ≤ NatQ.P R N s w ∧ 2 ≤ NatQ.A R N s w := by
  have hN2 : 64 ≤ N ^ 2 := by nlinarith
  have hU : 64 ≤ NatQ.U N w := by rw [NatQ.U]; nlinarith
  have hY : 64 ≤ NatQ.Y N s := by rw [NatQ.Y]; nlinarith
  have hM : 1 ≤ NatQ.M R N s := by rw [NatQ.M]; nlinarith
  exact ⟨by rw [NatQ.P]; nlinarith, by rw [NatQ.A]; nlinarith⟩

theorem cU : (𝒱).U = (NatQ.U N w : ℤ) := by simp only [Vars.U, Vars.ofNat, NatQ.U]; push_cast; ring
theorem cY : (𝒱).Y = (NatQ.Y N s : ℤ) := by simp only [Vars.Y, Vars.ofNat, NatQ.Y]; push_cast; ring
theorem cM : (𝒱).M = (NatQ.M R N s : ℤ) := by
  simp only [Vars.M, cY]; simp only [Vars.ofNat, NatQ.M]; push_cast; ring
theorem cP : (𝒱).P = (NatQ.P R N s w : ℤ) := by
  simp only [Vars.P, cM, cU, NatQ.P]; push_cast; ring
theorem cK (hP : 1 ≤ NatQ.P R N s w) : (𝒱).K = (NatQ.K R N h s w : ℤ) := by
  simp only [Vars.K, cP, NatQ.K]; simp only [Vars.ofNat]; push_cast [Nat.cast_sub hP]; ring
theorem cA : (𝒱).A = (NatQ.A R N s w : ℤ) := by
  simp only [Vars.A, cM, cU, NatQ.A]; push_cast; ring
theorem cB : (𝒱).B' = (NatQ.B' R : ℤ) := by
  simp only [Vars.B', Vars.ofNat, NatQ.B']; push_cast; ring
theorem cW : (𝒱).W = (NatQ.W b w : ℤ) := by
  simp only [Vars.W, Vars.ofNat, NatQ.W]; push_cast; ring
theorem cC : (𝒱).C = (NatQ.C R b w φ : ℤ) := by
  simp only [Vars.C, cB, cW, NatQ.C]; simp only [Vars.ofNat]; push_cast; ring
theorem cJ (hA : 2 ≤ NatQ.A R N s w) : (𝒱).J = (NatQ.J R N s w : ℤ) := by
  simp only [Vars.J, cA, NatQ.J]
  have h5 : 2 * 2 + 1 ≤ 2 * NatQ.A R N s w * 2 := by omega
  rw [show 2 * NatQ.A R N s w * 2 - 2 * 2 - 1 = 2 * NatQ.A R N s w * 2 - (2 * 2 + 1) by omega]
  push_cast [Nat.cast_sub h5]; ring
theorem cQ : (𝒱).Q = 3 * (NatQ.W b w : ℤ) * NatQ.C R b w φ - 2 * ((NatQ.W b w : ℤ) ^ 2 - 1) := by
  simp only [Vars.Q, cW, cC]
theorem cD (hA : 2 ≤ NatQ.A R N s w) : (𝒱).D = (NatQ.D R N b s w φ : ℤ) := by
  have h1 : 1 ≤ NatQ.A R N s w ^ 2 := Nat.one_le_pow _ _ (by omega)
  simp only [Vars.D, cA, cC, NatQ.D]; push_cast [Nat.cast_sub h1]; ring
theorem cE (hA : 2 ≤ NatQ.A R N s w) : (𝒱).E = (NatQ.E R N b s w φ i : ℤ) := by
  simp only [Vars.E, cJ hA, cD hA, cC, NatQ.E]; simp only [Vars.ofNat]; push_cast; ring
theorem cF (hA : 2 ≤ NatQ.A R N s w) : (𝒱).F = (NatQ.F R N b s w φ i : ℤ) := by
  have h1 : 1 ≤ NatQ.A R N s w ^ 2 := Nat.one_le_pow _ _ (by omega)
  simp only [Vars.F, cA, cE hA, NatQ.F]; push_cast [Nat.cast_sub h1]; ring

theorem A_le_CD (hA : 2 ≤ NatQ.A R N s w) :
    NatQ.A R N s w ≤ NatQ.C R b w φ * NatQ.D R N b s w φ + 1 := by
  have h1 : NatQ.A R N s w ≤ NatQ.A R N s w ^ 2 := Nat.le_self_pow (by norm_num) _
  have h2 : 1 ≤ NatQ.C R b w φ := by simp only [NatQ.C, NatQ.B']; omega
  have h3 : NatQ.A R N s w ^ 2 ≤ NatQ.D R N b s w φ := by
    simp only [NatQ.D]
    have : 1 ≤ NatQ.C R b w φ ^ 2 := Nat.one_le_pow _ _ (by omega)
    have : NatQ.A R N s w ^ 2 - 1 ≤ (NatQ.A R N s w ^ 2 - 1) * NatQ.C R b w φ ^ 2 :=
      Nat.le_mul_of_pos_right _ (by omega)
    omega
  nlinarith

theorem cG (hA : 2 ≤ NatQ.A R N s w) : (𝒱).Gp = (NatQ.Gp R N b s w φ i : ℤ) := by
  have h := A_le_CD (b := b) (φ := φ) hA
  simp only [Vars.Gp, cA, cF hA, cC, cD hA, NatQ.Gp]; push_cast [Nat.cast_sub h]; ring
theorem cH : (𝒱).H = (NatQ.H R b w φ j : ℤ) := by
  simp only [Vars.H, cB, cC, NatQ.H]; simp only [Vars.ofNat]; push_cast; ring

theorem one_le_Gp (hA : 2 ≤ NatQ.A R N s w) : 1 ≤ NatQ.Gp R N b s w φ i := by
  simp only [NatQ.Gp]; omega

theorem cI (hA : 2 ≤ NatQ.A R N s w) : (𝒱).I = (NatQ.I R N b s w φ i j : ℤ) := by
  have h1 : 1 ≤ NatQ.Gp R N b s w φ i ^ 2 := Nat.one_le_pow _ _ (one_le_Gp hA)
  simp only [Vars.I, cG hA, cH, NatQ.I]; push_cast [Nat.cast_sub h1]; ring

end Casts

set_option maxHeartbeats 1000000 in
/-- **Sufficiency.** -/
theorem ratio_sound {R N b g G h s w φ i j : ℕ} (hR : 8 ≤ R) (hN : 8 ≤ N) (hbR : b ≤ R)
    (hb : 0 < b) (hbN : b ≤ N) (hG : 0 < G) (hh : 0 < h) (hs : 0 < s) (hw : 0 < w)
    (hi : 0 < i) (hj : 0 < j) (hc : (Vars.ofNat R N b g G h s w φ i j).Conds) :
    N ^ 2 ∣ (2 * R).choose R ∧ (∃ k, b = 2 ^ k) ∧ 8 * g < G := by
  obtain ⟨hP1, hA2⟩ := sizes_nat hR hN hs hw
  obtain ⟨sq1, sq2, hdvd, hpos⟩ := hc
  rw [cP, cK hP1] at sq1
  rw [cD hA2, cF hA2, cI hA2] at sq2
  rw [cJ hA2, cF hA2, cQ, cH, cC] at hdvd
  rw [cK hP1, cY, cC] at hpos
  simp only [Vars.ofNat] at hpos
  set U := NatQ.U N w with hU
  set Y := NatQ.Y N s with hY
  set M := NatQ.M R N s with hM
  set Pn := NatQ.P R N s w with hPn
  set K := NatQ.K R N h s w with hK
  set A := NatQ.A R N s w with hA
  set B' := NatQ.B' R with hB'
  set W := NatQ.W b w with hW
  set C := NatQ.C R b w φ with hC
  set J := NatQ.J R N s w with hJ
  set D := NatQ.D R N b s w φ with hD
  set E := NatQ.E R N b s w φ i with hE
  set F := NatQ.F R N b s w φ i with hF
  set Gn := NatQ.Gp R N b s w φ i with hGn
  set H := NatQ.H R b w φ j with hH
  set I := NatQ.I R N b s w φ i j with hI
  have hGz : (0 : ℤ) < G := by exact_mod_cast hG
  have hK9 : 9 ≤ K := by rw [hK, NatQ.K]; omega
  have hKz : (0 : ℤ) < (K : ℤ) ^ 2 := by positivity
  -- (B3) and the ceiling
  have hB3 : 4 * ((C : ℤ) - K * Y) ^ 2 < (K : ℤ) ^ 2 := by
    have h1 : 0 ≤ 8 * (g : ℤ) * (K : ℤ) ^ 2 := by positivity
    have h2 : 4 * ((C : ℤ) - K * Y) ^ 2 * G < (K : ℤ) ^ 2 * G := by linarith
    exact lt_of_mul_lt_mul_right h2 hGz.le
  have hgG : 8 * g < G := by
    have h1 : 0 ≤ 4 * ((C : ℤ) - K * Y) ^ 2 * G := by positivity
    have h2 : 8 * (g : ℤ) * (K : ℤ) ^ 2 < (G : ℤ) * (K : ℤ) ^ 2 := by linarith
    exact_mod_cast lt_of_mul_lt_mul_right h2 hKz.le
  -- the two divisibilities
  have hcop := isCoprime_F_J (Vars.ofNat R N b g G h s w φ i j)
  rw [cF hA2, cJ hA2] at hcop
  have hFHC : (F : ℤ) ∣ (H : ℤ) - C := by
    have h2 : (F : ℤ) ∣ (3 * (W : ℤ) * C - 2 * ((W : ℤ) ^ 2 - 1)) * F + J * ((H : ℤ) - C) :=
      (Dvd.intro_left _ rfl).trans hdvd
    have h1 : (F : ℤ) ∣ (J : ℤ) * ((H : ℤ) - C) := (dvd_add_right (Dvd.intro_left _ rfl)).1 h2
    exact hcop.dvd_of_dvd_mul_left h1
  have hJQ : (J : ℤ) ∣ 3 * (W : ℤ) * C - 2 * ((W : ℤ) ^ 2 - 1) := by
    have h2 : (J : ℤ) ∣ (3 * (W : ℤ) * C - 2 * ((W : ℤ) ^ 2 - 1)) * F + J * ((H : ℤ) - C) :=
      (Dvd.intro _ rfl).trans hdvd
    have h1 : (J : ℤ) ∣ (3 * (W : ℤ) * C - 2 * ((W : ℤ) ^ 2 - 1)) * F :=
      (dvd_add_left (Dvd.intro _ rfl)).1 h2
    exact hcop.symm.dvd_of_dvd_mul_right h1
  -- Lemma 2.27
  have hA1 : 1 < A := by omega
  have hJ0 : 0 < J := by rw [hJ, NatQ.J]; omega
  have hB1 : 1 < B' := by rw [hB', NatQ.B']; omega
  have hBC : B' ≤ C := by rw [hC, NatQ.C]; omega
  have hA1' : 1 ≤ A ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hCD := A_le_CD (b := b) (φ := φ) hA2
  have hG1 : 1 ≤ Gn ^ 2 := Nat.one_le_pow _ _ (one_le_Gp hA2)
  have hpp : ProductPellConds A B' C J i j D E F Gn H I := by
    refine ⟨(natCast_isSquare (by push_cast; ring)).1 sq2, (productPell_congr_iff F H C).2 hFHC,
      ?_, rfl, ?_, ?_, rfl, ?_⟩
    · have eD : D = (A ^ 2 - 1) * C ^ 2 + 1 := rfl
      rw [eD]; zify [hA1']; ring
    · have eF : F = (A ^ 2 - 1) * E ^ 2 + 1 := rfl
      rw [eF]; zify [hA1']; ring
    · have eG : Gn = A + F * (C * D + 1 - A) := rfl
      have hCD' : A ≤ C * D + 1 := hCD
      rw [eG]; zify [hCD']; ring
    · have eI : I = (Gn ^ 2 - 1) * H ^ 2 + 1 := rfl
      rw [eI]; zify [hG1]; ring
  have hψ : C = ψ hA1 B' :=
    (lemma_2_27 hA1 hB1 hBC (Or.inr ⟨R, by rw [hB', NatQ.B']⟩) hJ0).2
      ⟨i, j, D, E, F, Gn, H, I, hi, hj, hpp⟩
  -- Lemma 2.25
  have hPn2 : 1 ≤ Pn ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hcore : B25core R N b h s w (W + φ) A B' C K M Pn U 2 W Y :=
    ⟨rfl, (natCast_isSquare (by push_cast [Nat.cast_sub hPn2]; ring)).1 sq1,
      hB3, rfl, rfl, rfl, rfl, by rw [hC, NatQ.C]; ring, rfl, rfl, rfl, rfl, fun _ => hψ⟩
  have hW1 : 1 ≤ W := by rw [hW, NatQ.W]; nlinarith
  have hB13 : (2 ^ 2 - 1) * W * C ≡ 2 * (W ^ 2 - 1) [MOD 2 * A * 2 - 2 * 2 - 1] := by
    rw [Nat.ModEq.comm, Nat.modEq_iff_dvd]
    have hW2 : 1 ≤ W ^ 2 := Nat.one_le_pow _ _ (by omega)
    have hJeq : ((2 * A * 2 - 2 * 2 - 1 : ℕ) : ℤ) = J := by rw [hJ, NatQ.J]
    have e : (((2 ^ 2 - 1) * W * C : ℕ) : ℤ) - ((2 * (W ^ 2 - 1) : ℕ) : ℤ) =
        3 * (W : ℤ) * C - 2 * ((W : ℤ) ^ 2 - 1) := by push_cast [hW2]; ring
    rw [hJeq, e]; exact hJQ
  obtain ⟨hdvd', hpow⟩ := (lemma_2_25 hR hN hbR hb hbN).2
    ⟨h, s, w, W + φ, A, B', C, K, M, Pn, U, 2, W, Y, hh, hs, hw, by omega, hcore, hB13⟩
  exact ⟨hdvd', hpow, hgG⟩

set_option maxHeartbeats 1000000 in
/-- **Necessity.** -/
theorem ratio_complete {R N b g G : ℕ} (hR : 8 ≤ R) (hN : 8 ≤ N) (hbR : b ≤ R)
    (hb : 0 < b) (hbN : b ≤ N) (hgG : 32 * g < G)
    (hdvd : N ^ 2 ∣ (2 * R).choose R) (hpow : ∃ k, b = 2 ^ k) :
    ∃ h s w φ i j : ℕ, 0 < h ∧ 0 < s ∧ 0 < w ∧ 0 < i ∧ 0 < j ∧
      (Vars.ofNat R N b g G h s w φ i j).Conds := by
  obtain ⟨h, s, w, φ₀, A, B', C, K, M, Pn, U, V, W, Y, hh, hs, hw, -, hcore, hW, hBWC, hB3s⟩ :=
    exists_B25core hR hN hbR hb hbN hdvd hpow
  obtain ⟨-, -, -, hA33, hA1, -, -, -, hVA, -⟩ := hcore.sizes hR hN hs hw
  obtain ⟨B1, B2, -, B4, B5, B6, B7, B8, B9, B10, B11, B12, B14⟩ := hcore
  subst B12
  have hJ0 : 0 < 2 * A * 2 - 2 * 2 - 1 := by omega
  have hB1 : 1 < B' := by omega
  have hBC : B' ≤ C := by omega
  obtain ⟨i, j, D, E, F, Gn, H, I, hi, hj, hpp⟩ :=
    (lemma_2_27 hA1 hB1 hBC (Or.inr ⟨R, by omega⟩) hJ0).1 (B14 hA1)
  refine ⟨h, s, w, C - B' - W, i, j, hh, hs, hw, hi, hj, ?_⟩
  obtain ⟨sq2, congr, A2, A3, A4, A5, A6, A7⟩ := hpp
  have hsz := sizes_nat hR hN hs hw
  -- identify the natural quantities
  have eU : NatQ.U N w = U := by rw [NatQ.U, B9]
  have eY : NatQ.Y N s = Y := by rw [NatQ.Y, B10]
  have eM : NatQ.M R N s = M := by rw [NatQ.M, eY, B5]
  have eP : NatQ.P R N s w = Pn := by rw [NatQ.P, eM, eU, B1]
  have eK : NatQ.K R N h s w = K := by rw [NatQ.K, eP, B4]
  have eA : NatQ.A R N s w = A := by rw [NatQ.A, eM, eU, B6]
  have eB : NatQ.B' R = B' := by rw [NatQ.B', B7]
  have eW : NatQ.W b w = W := by rw [NatQ.W, B11]
  have eC : NatQ.C R b w (C - B' - W) = C := by rw [NatQ.C, eB, eW]; omega
  have eJ : NatQ.J R N s w = 2 * A * 2 - 2 * 2 - 1 := by rw [NatQ.J, eA]
  have hA1' : 1 ≤ A ^ 2 := Nat.one_le_pow _ _ (by omega)
  have eD : NatQ.D R N b s w (C - B' - W) = D := by
    rw [NatQ.D, eA, eC]; zify [hA1'] at A2 ⊢; linarith
  have eE : NatQ.E R N b s w (C - B' - W) i = E := by rw [NatQ.E, eJ, eD, eC, A3]
  have eF : NatQ.F R N b s w (C - B' - W) i = F := by
    rw [NatQ.F, eA, eE]; zify [hA1'] at A4 ⊢; linarith
  have hCD := A_le_CD (b := b) (φ := C - B' - W) (hsz.2)
  rw [eA, eC, eD] at hCD
  have eG : NatQ.Gp R N b s w (C - B' - W) i = Gn := by
    rw [NatQ.Gp, eA, eF, eC, eD]; zify [hCD] at A5 ⊢; linarith
  have eH : NatQ.H R b w (C - B' - W) j = H := by rw [NatQ.H, eB, eC, A6]
  have hG1 : 1 ≤ Gn ^ 2 := by rw [← eG]; exact Nat.one_le_pow _ _ (one_le_Gp hsz.2)
  have eI : NatQ.I R N b s w (C - B' - W) i j = I := by
    rw [NatQ.I, eG, eH]; zify [hG1] at A7 ⊢; linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [cP, cK hsz.1, eP, eK]
    have hPn2 : 1 ≤ Pn ^ 2 := Nat.one_le_pow _ _ (by rw [← eP]; exact hsz.1)
    exact (natCast_isSquare (n := (Pn ^ 2 - 1) * K ^ 2 + 1)
      (by push_cast [Nat.cast_sub hPn2]; ring)).2 B2
  · rw [cD hsz.2, cF hsz.2, cI hsz.2, eD, eF, eI]
    exact (natCast_isSquare (n := D * F * I) (by push_cast; ring)).2 sq2
  · rw [cJ hsz.2, cF hsz.2, cQ, cH, cC, eJ, eF, eW, eH, eC]
    have hB13 := lemma_2_22_iii hA1 (by norm_num : 0 < 2) hVA.le (2 * R + 1)
    rw [← hW, ← B7, ← B14 hA1] at hB13
    have hJQ : ((2 * A * 2 - 2 * 2 - 1 : ℕ) : ℤ) ∣ 3 * (W : ℤ) * C - 2 * ((W : ℤ) ^ 2 - 1) := by
      rw [Nat.ModEq.comm, Nat.modEq_iff_dvd] at hB13
      have hW2 : 1 ≤ W ^ 2 := Nat.one_le_pow _ _ (by rw [hW]; positivity)
      have e : (((2 ^ 2 - 1) * W * C : ℕ) : ℤ) - ((2 * (W ^ 2 - 1) : ℕ) : ℤ) =
          3 * (W : ℤ) * C - 2 * ((W : ℤ) ^ 2 - 1) := by push_cast [hW2]; ring
      rwa [e] at hB13
    have hFHC : (F : ℤ) ∣ (H : ℤ) - C := (productPell_congr_iff F H C).1 congr
    exact dvd_add (mul_dvd_mul hJQ (dvd_refl _)) (mul_dvd_mul_left _ hFHC)
  · rw [cK hsz.1, cY, cC, eK, eY, eC]
    simp only [Vars.ofNat]
    have hK1 : 1 ≤ K := by rw [← eK, NatQ.K]; omega
    have hKz : (0 : ℤ) < (K : ℤ) ^ 2 := by positivity
    have hGz : (0 : ℤ) < G := by exact_mod_cast (by omega : 0 < G)
    have h1 : 4096 * (4 * ((C : ℤ) - K * Y) ^ 2 * G) ≤ 2500 * ((K : ℤ) ^ 2 * G) := by
      have := mul_le_mul_of_nonneg_right hB3s hGz.le
      linarith
    have h2 : 32 * (g : ℤ) * (K : ℤ) ^ 2 < (G : ℤ) * (K : ℤ) ^ 2 :=
      mul_lt_mul_of_pos_right (by exact_mod_cast hgG) hKz
    have h3 : 0 < (K : ℤ) ^ 2 * G := by positivity
    linarith

end Jones1982.Nine
