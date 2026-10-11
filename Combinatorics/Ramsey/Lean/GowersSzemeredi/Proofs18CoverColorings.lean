import GowersSzemeredi.Proofs18CoverTightBase
import GowersSzemeredi.Proofs18Consequences

/-! **Corollary 18.7 with sharper thresholds** (Notes L.15b).

Corollary 18.7 is Theorem 18.2 at density one half, and at `δ = 1/2` the
parameterized Szemerédi threshold has the shape of the two-colour threshold:
`szemerediThresholdAt c (1/2) k = twoColorThresholdAt c k`, the five-level
tower with `k + c` on top (`szemerediThresholdAt_half`). So:
* `Corollary187AtSharp c k`, the catalogue's `Corollary187At k` at `c = 9`
  (`corollary187AtSharp_nine_iff`);
* `Theorem182AtSharp.corollary_18_7`;
* `corollary_18_7_sharper_of_profiles_cover` (`L + 6`, every `L ≥ 6`) and
  `corollary_18_7_L5_of_profiles_cover` (`L + 5`, every `L ≥ 11`). -/
set_option autoImplicit false
noncomputable section
open Finset
namespace LeanProofs.GowersSzemeredi

/-- The two-colour threshold with `k + c` in place of the printed `k + 9`. -/
def twoColorThresholdAt (c k : Nat) : Real :=
  (2 : Real) ^ ((2 : Real) ^ ((2 : Real) ^
    ((2 : Real) ^ ((2 : Real) ^ (k + c : Nat)))))

/-- Corollary 18.7 at length `k` with the threshold `twoColorThresholdAt c`. -/
def Corollary187AtSharp (c k : Nat) : Prop :=
  ∀ N : Nat, twoColorThresholdAt c k ≤ N → ∀ color : Nat → Fin 2, HasMonochromaticAP N 2 color k

theorem corollary187AtSharp_nine_iff (k : Nat) : Corollary187AtSharp 9 k ↔ Corollary187At k :=
  Iff.rfl

theorem szemerediThresholdAt_half (c k : Nat) :
    szemerediThresholdAt c (1 / 2 : Real) k = twoColorThresholdAt c k := by
  simp only [szemerediThresholdAt, twoColorThresholdAt]
  norm_num

/-- One of the two colour classes has at least half of `[1, N]`. -/
theorem two_color_class_half (N : Nat) (color : Nat → Fin 2) :
    ∃ c : Fin 2,
      (N : Real) / 2 ≤ (((Finset.Icc 1 N).filter fun x => color x = c).card : Real) := by
  classical
  let S := Finset.Icc 1 N
  let A0 := S.filter fun x => color x = (0 : Fin 2)
  let A1 := S.filter fun x => color x = (1 : Fin 2)
  have hnot : S.filter (fun x => ¬ color x = (0 : Fin 2)) = A1 := by
    ext x
    simp only [Finset.mem_filter, A1]
    constructor
    · rintro ⟨hx, hne⟩
      refine ⟨hx, ?_⟩
      apply Fin.ext
      have hlt := (color x).isLt
      have hneval : (color x).val ≠ 0 := by
        intro hv
        apply hne
        apply Fin.ext
        simpa using hv
      omega
    · rintro ⟨hx, hone⟩
      refine ⟨hx, ?_⟩
      simp [hone]
  have hsumNat : A0.card + A1.card = S.card := by
    simpa [A0, hnot] using
      (Finset.card_filter_add_card_filter_not (s := S) (fun x => color x = (0 : Fin 2)))
  have hScard : S.card = N := by simp [S]
  have hsum : (A0.card : Real) + A1.card = N := by
    exact_mod_cast hsumNat.trans hScard
  by_cases h0 : (N : Real) / 2 ≤ A0.card
  · exact ⟨0, by simpa [A0, S] using h0⟩
  · refine ⟨1, ?_⟩
    have h0lt : (A0.card : Real) < (N : Real) / 2 := lt_of_not_ge h0
    have h1 : (N : Real) / 2 ≤ A1.card := by linarith
    simpa [A1, S] using h1

/-- **Theorem 18.2 at a length and constant gives Corollary 18.7 there.** -/
theorem Theorem182AtSharp.corollary_18_7 {c k : Nat} (h : Theorem182AtSharp c k) :
    Corollary187AtSharp c k := by
  intro N hN color
  obtain ⟨col, hcol⟩ := two_color_class_half N color
  let A := (Finset.Icc 1 N).filter fun x => color x = col
  have hthreshold : szemerediThresholdAt c (1 / 2 : Real) k ≤ N := by
    rw [szemerediThresholdAt_half]; exact hN
  have hAsub : A ⊆ Finset.Icc 1 N := Finset.filter_subset _ _
  have hAcard : (1 / 2 : Real) * N ≤ A.card := by
    simpa [A, div_eq_mul_inv, mul_comm] using hcol
  obtain ⟨a, d, hd, hmem⟩ := h (1 / 2 : Real) N (by norm_num) (by norm_num) hthreshold A hAsub hAcard
  refine ⟨a, d, col, hd, ?_⟩
  intro i hi
  have hai := hmem i hi
  have haiA : a + i * d ∈ A := hai
  have hfilter := Finset.mem_filter.mp haiA
  exact ⟨hfilter.1, hfilter.2⟩

/-- **Corollary 18.7 at every length `L ≥ 6` with `L + 6`**, from the profiles. -/
theorem corollary_18_7_sharper_of_profiles_cover (Kc pc : Nat → Nat) (hK : ∀ k, 2 ≤ Kc k)
    (hp : ∀ k, 0 < pc k)
    (hrec : ∀ k, 1 ≤ k →
      Section16RecurrenceProfileWith k (familyRecThr k (Kc k) (pc k)) (familyRecExp k (pc k)))
    (hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 5))))
    {L : Nat} (hL6 : 6 ≤ L) : Corollary187AtSharp 6 L :=
  (theorem_18_2_sharper_of_profiles_cover Kc pc hK hp hrec hconst hL6).corollary_18_7

/-- **Corollary 18.7 at every length `L ≥ 11` with `L + 5`**, from the profiles. -/
theorem corollary_18_7_L5_of_profiles_cover (Kc pc : Nat → Nat) (hK : ∀ k, 2 ≤ Kc k)
    (hp : ∀ k, 0 < pc k)
    (hrec : ∀ k, 1 ≤ k →
      Section16RecurrenceProfileWith k (familyRecThr k (Kc k) (pc k)) (familyRecExp k (pc k)))
    (hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 5))))
    {L : Nat} (hL11 : 11 ≤ L) : Corollary187AtSharp 5 L :=
  (theorem_18_2_L5_of_profiles_cover Kc pc hK hp hrec hconst hL11).corollary_18_7

end LeanProofs.GowersSzemeredi
