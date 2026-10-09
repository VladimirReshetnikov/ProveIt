import GowersSzemeredi.Proofs16DenseColumnEightFamily
import GowersSzemeredi.Proofs16UniformColumnRepSystem
import GowersSzemeredi.Proofs16SharedWitnessZeros

/-! Construct a dense column witness system from the original dense
Freiman bihomomorphism, with density-only numerical parameters. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- Global density supplies the column maps and their robust witness
system. No column or witness extraction oracle is assumed. -/
theorem dense_bihom_column_witness_system {N : Nat} [NeZero N] [Fact N.Prime]
    (A : Finset (ZMod N × ZMod N)) (phi : ZMod N × ZMod N → ZMod N)
    {alpha : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (hA : alpha * (N : Real)^2 ≤ A.card) (hphi : IsEBihomomorphism A phi {0}) :
    let beta := columnEightDensity alpha
    let d := columnSpectrumCap beta
    let c := columnWitnessDensity beta
    ∃ (X : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
      (L : ZMod N → ZMod N → ZMod N) (W : ZMod N → Finset (Fin 4 → ZMod N)),
      (alpha / (2 - alpha)) * N ≤ X.card ∧
      IsColumnWitnessSystem A phi X T L W (1 / (4 * Real.pi)) ∧
      (∀ x ∈ X, (T x).card ≤ d) ∧
      (∀ x ∈ X, IsFreimanLinearOn (bohr (T x) (1 / (4 * Real.pi))) (L x)) ∧
      (∀ x ∈ X, L x 0 = 0) ∧ (∀ x ∈ X, c * (N : Real)^4 ≤ (W x).card) := by
  obtain ⟨X, B, hX, hB⟩ := dense_column_eight_family A phi ha ha1 hA hphi
  let T (x : ZMod N) := commonLargeSpectrum (B x) (B x) (Real.sqrt (((B x).card / (N : Real))^3) / 4)
  let L (x : ZMod N) := repMap (B x) (fun y => phi (x, y))
  let W (x : ZMod N) := columnWitnesses (B x) (T x)
  have hdata (x : ZMod N) (hx : x ∈ X) := column_rep_system_uniform (B x) (fun y => phi (x, y))
    (hB x hx).2.2 (columnEightDensity_pos ha) (hB x hx).2.1
  refine ⟨X, T, L, W, hX, ?_, (fun x hx => (hdata x hx).1),
    (fun x hx => (hdata x hx).2.1), (fun x hx => (hdata x hx).2.2.1),
    (fun x hx => (hdata x hx).2.2.2)⟩
  intro x hx z hz
  have hz' : (∀ j, z j ∈ B x) ∧ fourSum z ∈ bohr (T x) (1 / (4 * Real.pi)) := by
    simpa only [W, columnWitnesses, Finset.mem_filter, Finset.mem_univ, true_and] using hz
  refine ⟨?_, hz'.2, repMap_spec (hB x hx).2.2 hz'.1⟩
  intro j
  exact (Finset.mem_filter.mp ((hB x hx).1 (hz'.1 j))).2

end LeanProofs.GowersSzemeredi
