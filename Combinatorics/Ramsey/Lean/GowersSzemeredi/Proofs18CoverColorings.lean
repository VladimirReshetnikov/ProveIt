import GowersSzemeredi.Proofs18CoverTightBase
import GowersSzemeredi.Proofs18SharpInterfaces

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
