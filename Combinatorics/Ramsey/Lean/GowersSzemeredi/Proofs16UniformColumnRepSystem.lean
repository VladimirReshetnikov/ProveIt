import GowersSzemeredi.Proofs16ColumnRepSystem

/-! Uniform numerical bounds for represented column maps and witnesses. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def columnSpectrumCap (beta : Real) : Nat := ⌈16 / beta^2⌉₊
def columnWitnessDensity (beta : Real) : Real := beta^4 / (4 * (13 : Real)^columnSpectrumCap beta)

theorem columnWitnessDensity_pos {beta : Real} (hb : 0 < beta) : 0 < columnWitnessDensity beta := by
  unfold columnWitnessDensity
  positivity

/-- The represented map is normalized on every nonempty source set. -/
theorem repMap_zero {N : Nat} {B : Finset (ZMod N)} {f : ZMod N → ZMod N}
    (hf : FreimanHom 8 B f) (hB : B.Nonempty) : repMap B f 0 = 0 := by
  obtain ⟨b, hb⟩ := hB
  have h := repMap_spec hf (q := fun _ => b) (fun _ => hb)
  simpa only [fourSum, repFourValue, add_sub_cancel_right, sub_self] using h

/-- Rank, normalization, and witness density depend only on a lower bound
for the source density, not its actual cardinality. -/
theorem column_rep_system_uniform {N : Nat} [NeZero N] (B : Finset (ZMod N))
    (f : ZMod N → ZMod N) (hf : FreimanHom 8 B f) {beta : Real} (hb : 0 < beta)
    (hcard : beta * N ≤ B.card) :
    let mu : Real := B.card / N
    let S := commonLargeSpectrum B B (Real.sqrt (mu^3) / 4)
    S.card ≤ columnSpectrumCap beta ∧
      IsFreimanLinearOn (bohr S (1 / (4 * Real.pi))) (repMap B f) ∧ repMap B f 0 = 0 ∧
      columnWitnessDensity beta * (N : Real)^4 ≤ (columnWitnesses B S).card := by
  let mu : Real := B.card / N
  let S := commonLargeSpectrum B B (Real.sqrt (mu^3) / 4)
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hB : B.Nonempty := Finset.card_pos.mp (by exact_mod_cast (mul_pos hb hN).trans_le hcard)
  have hmu : beta ≤ mu := (le_div_iff₀ hN).mpr hcard
  have hmu0 : 0 < mu := hb.trans_le hmu
  obtain ⟨hS, hlin, hrep⟩ := column_rep_system B f hf hB
  have hScap : S.card ≤ columnSpectrumCap beta := by
    have hr : (S.card : Real) ≤ 16 / beta^2 := hS.trans
      (div_le_div_of_nonneg_left (by norm_num) (by positivity) (pow_le_pow_left₀ hb.le hmu 2))
    exact_mod_cast hr.trans (Nat.le_ceil _)
  refine ⟨hScap, hlin, repMap_zero hf hB, ?_⟩
  have hcount := column_witness_card_ge B S hrep (by positivity : 0 ≤ mu^4 * (N : Real)^3 / 4)
  have hpow : (13 : Real)^S.card ≤ (13 : Real)^columnSpectrumCap beta :=
    pow_le_pow_right₀ (by norm_num) hScap
  have hW : (0 : Real) ≤ (columnWitnesses B S).card := Nat.cast_nonneg _
  have hcount' := hcount.trans (mul_le_mul_of_nonneg_right hpow hW)
  have hbeta : beta^4 * (N : Real)^4 ≤ mu^4 * (N : Real)^4 := by gcongr
  change beta^4 / (4 * (13 : Real)^columnSpectrumCap beta) * (N : Real)^4 ≤ _
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith only [hcount', hbeta]

end LeanProofs.GowersSzemeredi
