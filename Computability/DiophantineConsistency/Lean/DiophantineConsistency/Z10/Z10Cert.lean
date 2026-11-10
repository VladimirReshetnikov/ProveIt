import DiophantineConsistency.Z10.Z10Lucas
import DiophantineConsistency.P138.P138Rank
import DiophantineConsistency.ZRows.CoprimeSquares
import DiophantineConsistency.ArithmeticPellClassification
import DiophantineConsistency.ArithmeticPellStrongDivisibility
import DiophantineConsistency.ArithmeticPellIndexDivisibility
import DiophantineConsistency.ArithmeticPellCongruences
import DiophantineConsistency.ArithmeticPellPeriodicity

/-! # The signed square certificate of the ten-integer forms

Soundness step S8 of the ten-integer route: Sun's certificate `C = ψ_A(B)` from one square
`D F I = □`, in the ring of differences `DiffRing V` of a model `V` of `IΣ₁`.

The certificate is stated over plain variables with equational hypotheses, so that the
registers stay opaque in the proof. With `A = 2 A₁`:

* `D' = (A₁² − 1) C² + 1` (so `D = 4 D'`), `F = 1 + 4 D' K` with
  `K = 16 (A₁² − 1) C⁴ ξ²`, `G = (A₁ − 1)(F − 1) − 1`,
  `H = C + F (B − C + C W)`, `I = (G² − 1) H² + 1`.

Hypotheses: `|A₁| = a + 2`, `0 ≤ B < a + 2`, `|C| > 1`, `ξ ≠ 0`, `4 D' F I = s₁²`. Then
`|C| = ψ_a(B)` (`cert_abs`), and with `3 ∣ A₁`, `3 ∣ C + 1`, `B = 4 j + 3` the sign is fixed:
`C = ψ_a(B)` (`cert`). Here `ψ_a(n) = ycoord n a` is the Lucas sequence of the Pell equation
`x² − ((a+2)² − 1) y² = 1`.

Steps of the proof:

* `mod_F`: `F ∣ G² − A₁²` and `F ∣ I − D'`.
* `three_squares`: `4 D'`, `F`, `I` are pairwise coprime by explicit Bezout pairs, so each
  is a square up to sign (`ZRowsCoprimeSquares.abs_squares_of_mul_mul_square`).
* The three Pell equations give indices `t₀`, `t'`, `t''` with `|C| = ψ_a(t₀)`,
  `F = χ_a(t')²`, `|H| = ψ_γ(t'')`, `|G| = γ + 2`; `ordinate_dvd_index`: `|C| ∣ t'`.
* `index_transfer`: modulo `χ_a(t')` the abscissae at doubled indices agree; the base
  `γ + 2 ≡ ±(a + 2)` enters only through its square (`Z10Lucas.double_x_of_sq`), and
  `doubled_step_down` gives `t'' ≡ ±t₀ (mod t')`.
* `residue_pm`: modulo `|C|`, `G ≡ −1` gives `ψ_γ(n) ≡ ±n`; with `H ≡ B (mod C)` this
  yields `t₀ ≡ ±B (mod |C|)`, and the sizes `2 t₀ ≤ |C|`, `2 B < |C|` force `t₀ = B`. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.Z10Cert

section Ring
variable {R : Type*} [CommRing R]

/-- Modulo `F`: `G ≡ −A₁` and `H ≡ C`, hence `G² ≡ A₁²` and `I ≡ D'`. -/
theorem mod_F {A1 C D' F G H I Wh : R}
    (hD' : D' = (A1 * A1 - 1) * (C * C) + 1)
    (hG : G = (A1 - 1) * (F - 1) - 1) (hH : H = C + F * Wh)
    (hI : I = (G * G - 1) * (H * H) + 1) :
    F ∣ G * G - A1 * A1 ∧ F ∣ I - D' := by
  have hGA : G + A1 = (A1 - 1) * F := by rw [hG]; ring
  have hHC : H - C = F * Wh := by rw [hH]; ring
  refine ⟨⟨(G - A1) * (A1 - 1), ?_⟩,
    ⟨(G - A1) * (A1 - 1) * (H * H) + (A1 * A1 - 1) * (H + C) * Wh, ?_⟩⟩
  · linear_combination (G - A1) * hGA
  · linear_combination hI - hD' + (G - A1) * (H * H) * hGA + (A1 * A1 - 1) * (H + C) * hHC

end Ring

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ModelDifferenceRing ZRowsCoprimeSquares ModelProductPell
open ArithmeticPellRecurrence Z10Lucas

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- `4 D'`, `F` and `I` are squares up to sign. -/
theorem three_squares {A1 C D' K F G H I Wh s1 : DiffRing V}
    (hD' : D' = (A1 * A1 - 1) * (C * C) + 1)
    (hF : F = 1 + 4 * D' * K)
    (hG : G = (A1 - 1) * (F - 1) - 1) (hH : H = C + F * Wh)
    (hI : I = (G * G - 1) * (H * H) + 1)
    (hsq : 4 * D' * F * I = s1 * s1) :
    (∃ d : V, |4 * D'| = ι d * ι d) ∧ (∃ e : V, |F| = ι e * ι e) ∧
      ∃ f : V, |I| = ι f * ι f := by
  obtain ⟨-, k, hk⟩ := mod_F hD' hG hH hI
  have hG1 : G + 1 = (A1 - 1) * (4 * D' * K) := by rw [hG, hF]; ring
  refine abs_squares_of_mul_mul_square ⟨-K, 1, ?_⟩
    ⟨-((G - 1) * (A1 - 1) * K * (H * H)), 1, ?_⟩ ⟨1 + 4 * K * k, -(4 * K), ?_⟩ hsq
  · linear_combination hF
  · linear_combination hI + H * H * (G - 1) * hG1
  · linear_combination hF - 4 * K * hk

/-- If `ψ(t₀)² ∣ ψ(t')` then `ψ(t₀) ∣ t'`. -/
theorem ordinate_dvd_index (a t₀ t' q : V)
    (h : ycoord t' a = ycoord t₀ a * ycoord t₀ a * q) : ycoord t₀ a ∣ t' := by
  have h1 : t₀ ∣ t' := (ArithmeticPellStrongDivisibility.y_dvd_iff a t₀ t').mp
    ⟨ycoord t₀ a * q, by rw [h]; ring⟩
  exact ArithmeticPellIndexDivisibility.ordinate_divides_index a t₀ t' h1
    ⟨delta a * q, by rw [h]; ring⟩

/-- Transfer of the index modulo `χ_a(t')`: the bases agree up to sign and the norms agree. -/
theorem index_transfer (a γ t₀ t' t'' : V) (hp : 0 < t₀) (hpm : 2 * t₀ ≤ t')
    (h1 : (ι (xcoord t' a) : DiffRing V) ∣ ι (γ + 2) * ι (γ + 2) - ι (a + 2) * ι (a + 2))
    (h2 : (ι (xcoord t' a) : DiffRing V) ∣
      ι (delta γ * ycoord t'' γ * ycoord t'' γ) - ι (delta a * ycoord t₀ a * ycoord t₀ a)) :
    t'' % t' = t₀ % t' ∨ (t'' + t₀) % t' = 0 := by
  have he : 0 < xcoord t' a := lt_of_lt_of_le (by simp) (one_le_x t' a)
  have hsq : ((γ + 2) * (γ + 2)) % xcoord t' a = ((a + 2) * (a + 2)) % xcoord t' a :=
    P138Rank.mod_eq_of_ι_dvd he (by simpa only [map_mul] using h1)
  have hx : xcoord (2 * t'') γ % xcoord t' a = xcoord (2 * t₀) a % xcoord t' a := by
    apply P138Rank.mod_eq_of_ι_dvd he
    obtain ⟨w, hw⟩ := h2
    refine ⟨2 * w, ?_⟩
    have e1 := congrArg (ι (V := V)) (ArithmeticPellPeriodicity.double_x_add_one t'' γ)
    have e2 := congrArg (ι (V := V)) (ArithmeticPellPeriodicity.double_x_add_one t₀ a)
    have e3 := congrArg (ι (V := V)) (norm t'' γ)
    have e4 := congrArg (ι (V := V)) (norm t₀ a)
    simp only [map_add, map_mul, map_one, map_ofNat] at e1 e2 e3 e4 hw ⊢
    linear_combination e1 - e2 + 2 * e3 - 2 * e4 + 2 * hw
  have hg := (double_x_of_sq γ a _ he hsq t'').symm
  exact ArithmeticPellResidueClasses.doubled_step_down a t' t₀ t'' hp hpm
    (Or.inl (hg.trans hx))

/-- Modulo a divisor of `G + 1` with `|G| = γ + 2`: `ψ_γ(n) ≡ ±n`. -/
theorem residue_pm (γ c n : V) (hc : 0 < c) {G : DiffRing V}
    (hG : G = ι (γ + 2) ∨ G = -ι (γ + 2)) (hd : (ι c : DiffRing V) ∣ G + 1) :
    (ι c : DiffRing V) ∣ ι (ycoord n γ) - ι n ∨ (ι c : DiffRing V) ∣ ι (ycoord n γ) + ι n := by
  rcases hG with hG | hG
  · refine P138FirstIndex.alt_sign γ c hc ?_ n
    apply ι_dvd_iff.mp
    have e : (ι (γ + 3) : DiffRing V) = ι (γ + 2) + 1 := by
      simp only [map_add, map_ofNat]; ring
    rw [e, ← hG]; exact hd
  · left
    have hd' : c ∣ γ + 1 := by
      apply ι_dvd_iff.mp
      have e : (ι (γ + 1) : DiffRing V) = -(-ι (γ + 2) + 1) := by
        simp only [map_add, map_one, map_ofNat]; ring
      rw [e, ← hG]; exact (dvd_neg).mpr hd
    obtain ⟨_, s, _, hs⟩ := ArithmeticPellCongruences.residue_quotients n γ c hd'
    refine ⟨ι s, ?_⟩
    rw [hs, map_add, map_mul]; ring

/-- The certificate up to sign: `|C| = ψ_a(B)`. -/
theorem cert_abs {A1 C ξ W D' K F G H I s1 : DiffRing V} (a Bn : V)
    (hA : |A1| = ι (a + 2)) (hB : Bn < a + 2) (hC : 1 < |C|) (hξ : ξ ≠ 0)
    (hD' : D' = (A1 * A1 - 1) * (C * C) + 1)
    (hK : K = 16 * (A1 * A1 - 1) * (C * C * (C * C)) * (ξ * ξ))
    (hF : F = 1 + 4 * D' * K)
    (hG : G = (A1 - 1) * (F - 1) - 1)
    (hH : H = C + F * (ι Bn - C + C * W))
    (hI : I = (G * G - 1) * (H * H) + 1)
    (hsq : 4 * D' * F * I = s1 * s1) :
    |C| = ι (ycoord Bn a) := by
  -- naturals for `|C|`, `|ξ|`, and the squares
  obtain ⟨c, hc⟩ := abs_eq_ι C
  obtain ⟨xn, hxn⟩ := abs_eq_ι ξ
  have hCC : C * C = ι c * ι c := by rw [← hc]; exact (abs_mul_abs_self C).symm
  have hξξ : ξ * ξ = ι xn * ι xn := by rw [← hxn]; exact (abs_mul_abs_self ξ).symm
  have hAA : A1 * A1 = ι (a + 2) * ι (a + 2) := by
    rw [← hA]; exact (abs_mul_abs_self A1).symm
  have hA1 : A1 * A1 - 1 = ι (delta a) := by
    rw [hAA]; unfold delta; simp only [map_add, map_mul, map_one, map_ofNat]; ring
  have hδ3 : (3 : DiffRing V) ≤ A1 * A1 - 1 := by
    have e : (ι (delta a) : DiffRing V) = ι a * ι a + 4 * ι a + 3 := by
      unfold delta; simp only [map_add, map_mul, map_one, map_ofNat]; ring
    rw [hA1, e]; linarith [_root_.mul_self_nonneg (ι a : DiffRing V), ι_nonneg a]
  have hCne : C ≠ 0 := by
    intro h; rw [h, abs_zero] at hC; exact absurd hC (by norm_num)
  have hCCpos : 0 < C * C := _root_.mul_self_pos.mpr hCne
  have hξξpos : 0 < ξ * ξ := _root_.mul_self_pos.mpr hξ
  have hD'1 : 1 ≤ D' := by
    have := _root_.mul_nonneg (show (0 : DiffRing V) ≤ A1 * A1 - 1 by linarith) hCCpos.le
    rw [hD']; linarith
  have hKpos : 0 < K := by
    rw [hK]
    exact _root_.mul_pos (_root_.mul_pos (by linarith) (_root_.mul_pos hCCpos hCCpos)) hξξpos
  have hF4 : 4 ≤ F - 1 := by
    have h1 := P138Bootstrap.one_le_of_pos' (_root_.mul_pos (show (0 : DiffRing V) < D' by linarith) hKpos)
    have e : F - 1 = 4 * (D' * K) := by rw [hF]; ring
    rw [e]; linarith
  -- three squares and three Pell indices
  obtain ⟨⟨d, hd⟩, ⟨e, he⟩, ⟨f, hf⟩⟩ := three_squares hD' hF hG hH hI hsq
  have hD'n : D' = ι (1 + delta a * c * c) := by
    rw [hD', hA1, hCC]; simp only [map_add, map_mul, map_one]; ring
  have hdd : d * d = 4 * (1 + delta a * c * c) := by
    apply ι_injective (V := V)
    simp only [map_mul, map_ofNat]
    rw [← hd, abs_of_nonneg (by linarith : (0 : DiffRing V) ≤ 4 * D'), hD'n]
  obtain ⟨s, -, hs⟩ := even_of_sq d _ hdd
  obtain ⟨t₀, -, -, hy0⟩ := ArithmeticPellClassification.solution_index a s c hs
  have hFn : F = ι (1 + delta a * (8 * c * c * s * xn) * (8 * c * c * s * xn)) := by
    rw [hF, hK, hD'n, hA1, hCC, hξξ, ← hs]
    simp only [map_add, map_mul, map_one, map_ofNat]; ring
  have hF0 : 0 ≤ F := by linarith
  have hFe : F = ι e * ι e := by rw [← he, abs_of_nonneg hF0]
  have hee : e * e = 1 + delta a * (8 * c * c * s * xn) * (8 * c * c * s * xn) := by
    apply ι_injective (V := V)
    rw [← hFn, map_mul]; exact hFe.symm
  obtain ⟨t', -, hxt, hyt⟩ := ArithmeticPellClassification.solution_index a e _ hee
  -- `|G| = γ + 2`
  have hG1 : G + 1 = (A1 - 1) * (F - 1) := by rw [hG]; ring
  have hA1ne : A1 - 1 ≠ 0 := by
    intro h
    have h1 : A1 = 1 := by linarith
    rw [h1] at hδ3; norm_num at hδ3
  have h3G : (3 : DiffRing V) ≤ |G + 1| := by
    have hP := P138Bootstrap.one_le_abs hA1ne
    have hM : (0 : DiffRing V) ≤ F - 1 := by linarith
    have hnn := _root_.mul_nonneg (_root_.sub_nonneg.mpr hP) hM
    have e' : |A1 - 1| * (F - 1) = (|A1 - 1| - 1) * (F - 1) + (F - 1) := by ring
    rw [hG1, _root_.abs_mul, abs_of_nonneg hM, e']; linarith
  have hG2 : (2 : DiffRing V) ≤ |G| := by
    rcases _root_.le_abs.mp h3G with h | h
    · exact _root_.le_abs.mpr (Or.inl (by linarith))
    · exact _root_.le_abs.mpr (Or.inr (by linarith))
  obtain ⟨γ, hγ⟩ := nonneg_iff.mp (show (0 : DiffRing V) ≤ |G| - 2 by linarith)
  have hGγ : |G| = ι (γ + 2) := by rw [map_add, map_ofNat]; linarith
  have hGG : G * G = ι (γ + 2) * ι (γ + 2) := by
    rw [← hGγ]; exact (abs_mul_abs_self G).symm
  -- `|H| = ψ_γ(t'')`
  obtain ⟨η, hη⟩ := abs_eq_ι H
  have hHH : H * H = ι η * ι η := by rw [← hη]; exact (abs_mul_abs_self H).symm
  have hIn : I = ι (1 + delta γ * η * η) := by
    rw [hI, hGG, hHH]; unfold delta; simp only [map_add, map_mul, map_one, map_ofNat]; ring
  have hI0 : 0 ≤ I := by rw [hIn]; exact ι_nonneg _
  have hff : f * f = 1 + delta γ * η * η := by
    apply ι_injective (V := V)
    rw [← hIn, map_mul, ← hf, abs_of_nonneg hI0]
  obtain ⟨t'', -, -, hy2⟩ := ArithmeticPellClassification.solution_index γ f η hff
  -- sizes of the indices
  have hct' : c ∣ t' := by
    have h1 := ordinate_dvd_index a t₀ t' (8 * s * xn) (by rw [hyt, hy0]; ring)
    rwa [hy0] at h1
  have hc1 : (1 : V) < c := by
    apply ι_lt_ι.mp; rw [map_one, ← hc]; exact hC
  have hc0 : (0 : V) < c := lt_of_lt_of_le (by simp) hc1.le
  have ht2 : 2 ≤ t₀ := by
    by_contra hlt
    have h1 : t₀ ≤ 1 :=
      le_iff_lt_succ.mpr (by rw [one_add_one_eq_two]; exact not_le.mp hlt)
    have h2 : ycoord t₀ a ≤ ycoord 1 a := (ordinate_strictMono a).monotone h1
    rw [hy0, y_one] at h2
    exact absurd hc1 (not_lt.mpr h2)
  have ht0 : 0 < t₀ := lt_of_lt_of_le (by simp) ht2
  have h2t : 2 * t₀ ≤ c := by
    have h1 := pp_two_mul_le_y a t₀ ht2
    rwa [hy0] at h1
  have ht'0 : 0 < t' := by
    by_contra hn
    have h0 : t' = 0 := le_antisymm (not_lt.mp hn) (by simp)
    rw [h0, x_zero] at hxt
    rw [← hxt, map_one, mul_one] at hFe
    linarith
  have hpm : 2 * t₀ ≤ t' := le_trans h2t (Arithmetic.le_of_dvd ht'0 hct')
  -- transfer modulo `χ_a(t')`
  obtain ⟨⟨q1, hq1⟩, ⟨q2, hq2⟩⟩ := mod_F hD' hG hH hI
  have eI : (ι (delta γ * η * η) : DiffRing V) = I - 1 := by
    rw [hIn, map_add, map_one]; ring
  have eD : (ι (delta a * c * c) : DiffRing V) = D' - 1 := by
    rw [hD'n, map_add, map_one]; ring
  have hT := index_transfer a γ t₀ t' t'' ht0 hpm
    ⟨ι e * q1, by rw [hxt, ← hGG, ← hAA, hq1, hFe]; ring⟩
    ⟨ι e * q2, by rw [hxt, hy2, hy0, eI, eD]; linear_combination hq2 + q2 * hFe⟩
  have hT' : (ι c : DiffRing V) ∣ ι t'' - ι t₀ ∨ (ι c : DiffRing V) ∣ ι t'' + ι t₀ := by
    rcases hT with h | h
    · left
      apply P138Rank.ι_dvd_of_mod_eq
      have e1 := ArithmeticPellResidueClasses.mod_reduce t'' c t' hc0 hct'
      have e2 := ArithmeticPellResidueClasses.mod_reduce t₀ c t' hc0 hct'
      rw [← e1, ← e2, h]
    · right
      have h1 : (ι c : DiffRing V) ∣ ι (t'' + t₀) :=
        ι_dvd_iff.mpr (dvd_trans hct' (mod_eq_zero_iff_dvd.mp h))
      rwa [map_add] at h1
  -- residues modulo `|C|`
  have hcC : (ι c : DiffRing V) ∣ C := by
    rcases eq_or_eq_neg_abs C with h | h
    · exact ⟨1, by rw [mul_one, ← hc]; exact h⟩
    · exact ⟨-1, by rw [← hc]; linear_combination h⟩
  obtain ⟨Kc, hKc⟩ : ∃ Kc, F - 1 = C * Kc :=
    ⟨4 * D' * (16 * (A1 * A1 - 1) * (C * (C * C)) * (ξ * ξ)), by rw [hF, hK]; ring⟩
  have hGpm : G = ι (γ + 2) ∨ G = -ι (γ + 2) := by rw [← hGγ]; exact eq_or_eq_neg_abs G
  have hY := residue_pm γ c t'' hc0 hGpm
    (dvd_trans hcC ⟨(A1 - 1) * Kc, by rw [hG1, hKc]; ring⟩)
  rw [hy2] at hY
  have hHB : (ι c : DiffRing V) ∣ H - ι Bn :=
    dvd_trans hcC ⟨Kc * (ι Bn - C) + F * W, by linear_combination hH + (ι Bn - C) * hKc⟩
  have hB' : (ι c : DiffRing V) ∣ ι η - ι Bn ∨ (ι c : DiffRing V) ∣ ι η + ι Bn := by
    rcases eq_or_eq_neg_abs H with h | h
    · left; rw [h, hη] at hHB; exact hHB
    · right
      have h1 := (dvd_neg).mpr hHB
      rw [h, hη] at h1
      rwa [show -(-ι η - ι Bn) = (ι η : DiffRing V) + ι Bn by ring] at h1
  have hfin := pm_trans (pm_symm hT') (pm_trans (pm_symm hY) hB')
  -- sizes: `2 t₀ ≤ |C|` and `2 B < |C|`
  have b1 : 2 * ι t₀ ≤ (ι c : DiffRing V) := by
    have h1 := ι_le_ι.mpr h2t
    rwa [map_mul, map_ofNat] at h1
  have b2 : 2 * ι Bn < (ι c : DiffRing V) := by
    have h1 : (ι Bn : DiffRing V) < ι (a + 2) := ι_lt_ι.mpr hB
    have h2 : (ι (ycoord 2 a) : DiffRing V) ≤ ι (ycoord t₀ a) :=
      ι_le_ι.mpr ((ordinate_strictMono a).monotone ht2)
    rw [y_two, hy0, map_mul, map_ofNat] at h2
    linarith
  have hB0 : (0 : DiffRing V) ≤ ι Bn := ι_nonneg Bn
  have ht00 : (0 : DiffRing V) ≤ ι t₀ := ι_nonneg t₀
  have heq : (ι t₀ : DiffRing V) = ι Bn := by
    rcases hfin with h | h
    · have h0 := P138FirstIndex.eq_zero_of_dvd_small h
        (_root_.abs_lt.mpr ⟨by linarith, by linarith⟩)
      linarith
    · have h0 := P138FirstIndex.eq_zero_of_dvd_small h
        (_root_.abs_lt.mpr ⟨by linarith, by linarith⟩)
      exact le_antisymm (by linarith) (by linarith)
  rw [hc, ← hy0, ι_injective heq]

/-- Sun's signed certificate: `C = ψ_a(B)`. -/
theorem cert {A1 C ξ W D' K F G H I s1 : DiffRing V} (a Bn j : V)
    (hA : |A1| = ι (a + 2)) (hB : Bn < a + 2) (hB4 : Bn = 4 * j + 3)
    (h3A : (3 : DiffRing V) ∣ A1) (h3C : (3 : DiffRing V) ∣ C + 1)
    (hC : 1 < |C|) (hξ : ξ ≠ 0)
    (hD' : D' = (A1 * A1 - 1) * (C * C) + 1)
    (hK : K = 16 * (A1 * A1 - 1) * (C * C * (C * C)) * (ξ * ξ))
    (hF : F = 1 + 4 * D' * K)
    (hG : G = (A1 - 1) * (F - 1) - 1)
    (hH : H = C + F * (ι Bn - C + C * W))
    (hI : I = (G * G - 1) * (H * H) + 1)
    (hsq : 4 * D' * F * I = s1 * s1) :
    C = ι (ycoord Bn a) := by
  have habs := cert_abs a Bn hA hB hC hξ hD' hK hF hG hH hI hsq
  rcases eq_or_eq_neg_abs C with h | h
  · exact h.trans habs
  · exfalso
    have e3 : (ι (3 : V) : DiffRing V) = 3 := map_ofNat ι 3
    have h3 : (3 : V) ∣ a + 2 := by
      apply ι_dvd_iff.mp
      rw [e3, ← hA]; exact (dvd_abs _ _).mpr h3A
    obtain ⟨w, hw⟩ := h3
    obtain ⟨r, hr⟩ := three_dvd_y a w hw j
    obtain ⟨q, hq⟩ := h3C
    rw [← hB4] at hr
    have er := congrArg (ι (V := V)) hr
    simp only [map_add, map_mul, map_one, map_ofNat] at er
    rw [habs] at h
    have hd : (ι (3 : V) : DiffRing V) ∣ 2 := by
      refine ⟨ι r + q, ?_⟩
      rw [e3]; linear_combination er + hq - h
    have h0 := P138FirstIndex.eq_zero_of_dvd_small hd
      (by rw [abs_of_pos (by norm_num : (0 : DiffRing V) < 2), map_ofNat]; norm_num)
    exact absurd h0 (by norm_num)

#print axioms mod_F
#print axioms three_squares
#print axioms index_transfer
#print axioms residue_pm
#print axioms cert_abs
#print axioms cert

end DiophantineConsistency.Z10Cert
