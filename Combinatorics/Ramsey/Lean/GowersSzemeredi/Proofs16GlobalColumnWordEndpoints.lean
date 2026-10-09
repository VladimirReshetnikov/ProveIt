import GowersSzemeredi.Proofs16GlobalColumnWords
import GowersSzemeredi.Proofs16ExactRelationWordTransfer

/-! Endpoint identities for the direct global column BSG construction.
The maps retain their original bihomomorphism witness system. The kernel
cost is charged to only finitely many endpoint and auxiliary spectra per
word, rather than to a packed global model family. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem refinementKernelCap_mono_dimensions {d e D E : Nat} {rho r : Real}
    (hrho : 0 < rho) (hr : 0 < r) (hd : d ≤ D) (he : e ≤ E) :
    refinementKernelCap d e rho r ≤ refinementKernelCap D E rho r := by
  unfold refinementKernelCap
  apply Nat.mul_le_mul
  · exact Nat.pow_le_pow_right (Nat.ceil_pos.mpr (by positivity)) hd
  · exact Nat.pow_le_pow_right (Nat.ceil_pos.mpr (by positivity)) (Nat.add_le_add hd he)

theorem refinementKernelRadius_anti_dimensions {d e D E : Nat} {rho r : Real}
    (hrho : 0 < rho) (hr : 0 < r) (hd : d ≤ D) (he : e ≤ E) :
    refinementKernelRadius D E rho r ≤ refinementKernelRadius d e rho r := by
  unfold refinementKernelRadius
  apply div_le_div_of_nonneg_left (by positivity)
    (by exact_mod_cast refinementKernelCap_pos d e hrho hr)
  exact_mod_cast refinementKernelCap_mono_dimensions hrho hr hd he

/-- A ladder relation is the local-map identity needed for exact word transfer. -/
theorem columnZeroQ_exact_relation {N D : Nat} [NeZero N]
    (X : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (rho r : Real) (n : Nat)
    {a b c d : ZMod N} (h : columnZeroQ X T L D rho r (n+1) a b c d) :
    ∀ y, y ∈ bohr (T a) (zeroLadderRadius D rho r n) →
      y ∈ bohr (T b) (zeroLadderRadius D rho r n) →
      y ∈ bohr (T c) (zeroLadderRadius D rho r n) →
      y ∈ bohr (T d) (zeroLadderRadius D rho r n) → columnQuadDefect L a b c d y = 0 := by
  intro y ha hb hc hd
  have hdom : y ∈ bohr (quadSpec T a b c d) (zeroLadderRadius D rho r n) := by
    simp only [quadSpec, bohr_union, Finset.mem_inter]
    exact ⟨⟨⟨ha, hb⟩, hc⟩, hd⟩
  exact h.2.2.2.2.2 y hdom

/-- The level-16 common radius of the direct global BSG ladder. -/
def globalColumnWordZeroRadius (alpha : Real) : Real :=
  zeroLadderRadius (columnSpectrumCap (columnEightDensity alpha))
    (1/(4*Real.pi)) (globalColumnIdentityRadius alpha) 15

/-- Endpoint radius for every global word of at most `k+1` triples. -/
def globalColumnWordEndpointRadius (alpha : Real) (k : Nat) : Real :=
  refinementKernelRadius (4*(k+1)*columnSpectrumCap (columnEightDensity alpha))
    (2*k*columnSpectrumCap (columnEightDensity alpha)) (1/(4*Real.pi))
    (globalColumnWordZeroRadius alpha)

/-- A modulus condition covering the global construction and endpoint removal. -/
def globalColumnWordEndpointModulusBound (alpha : Real) (k : Nat) : Nat :=
  max (globalColumnBSGModulusBound alpha)
    (refinementKernelCap (4*(k+1)*columnSpectrumCap (columnEightDensity alpha))
      (2*k*columnSpectrumCap (columnEightDensity alpha)) (1/(4*Real.pi))
      (globalColumnWordZeroRadius alpha)+1)

theorem globalColumnWordZeroRadius_pos {alpha : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1) :
    0 < globalColumnWordZeroRadius alpha :=
  zeroLadderRadius_pos (by positivity) (globalColumnIdentityRadius_pos ha ha1) 15

theorem globalColumnWordEndpointRadius_pos {alpha : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (k : Nat) : 0 < globalColumnWordEndpointRadius alpha k :=
  refinementKernelRadius_pos _ _ (by positivity) (globalColumnWordZeroRadius_pos ha ha1)

theorem global_column_word_endpoint_system {N : Nat} [NeZero N] [Fact N.Prime]
    (A : Finset (ZMod N × ZMod N)) (phi : ZMod N × ZMod N → ZMod N)
    {alpha : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (hA : alpha * (N : Real)^2 ≤ A.card) (hphi : IsEBihomomorphism A phi {0})
    (k : Nat) (hN : globalColumnWordEndpointModulusBound alpha k ≤ N) :
    ∃ (X : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N)
      (W : ZMod N → Finset (Fin 4 → ZMod N)) (B B' : Finset (ZMod N)),
      alpha / 2 * N ≤ X.card ∧
      IsColumnWitnessSystem A phi X T L W (1/(4*Real.pi)) ∧
      (∀ x ∈ X, columnWitnessDensity (columnEightDensity alpha)*(N : Real)^4 ≤ (W x).card) ∧
      (∀ x ∈ X, (T x).card ≤ columnSpectrumCap (columnEightDensity alpha) ∧
        IsFreimanLinearOn (bohr (T x) (1 / (4 * Real.pi))) (L x) ∧ L x 0 = 0) ∧
      B' ⊆ B ∧ B ⊆ X ∧
      absBsgEps (globalColumnQuadrupleDensity alpha) 1 * N ≤ (B'.card : Real) ∧
      ThresholdRelationRichness B
        (columnZeroQ X T L (columnSpectrumCap (columnEightDensity alpha)) (1 / (4 * Real.pi))
          (globalColumnIdentityRadius alpha) 16)
        (absBsgWordBeta (globalColumnQuadrupleDensity alpha) 1 k)
        (absBsgWordEta (globalColumnQuadrupleDensity alpha) 1) ∧
      ∀ a : ZMod N, ∀ as : List (ZMod N), (∀ x ∈ a :: as, x ∈ B') → as.length ≤ k →
        thresholdColumnWordDensity (absBsgWordLambda (globalColumnQuadrupleDensity alpha) 1)
            (absBsgWordEta (globalColumnQuadrupleDensity alpha) 1) as.length *
          (N : Real) ^ (3 * as.length + 2) ≤
        (relationWordRepresentations B
          (columnZeroQ X T L (columnSpectrumCap (columnEightDensity alpha)) (1 / (4 * Real.pi))
            (globalColumnIdentityRadius alpha) 16) (a :: as)).card ∧
        ∀ w ∈ relationWordRepresentations B
          (columnZeroQ X T L (columnSpectrumCap (columnEightDensity alpha)) (1/(4*Real.pi))
            (globalColumnIdentityRadius alpha) 16) (a::as),
          ColumnWordIdentity T L (globalColumnWordEndpointRadius alpha k) (a::as) w := by
  have hNbase : globalColumnBSGModulusBound alpha ≤ N := (le_max_left _ _).trans hN
  obtain ⟨X, T, L, W, B, B', hX, hsys, hW, hcol, hB'B, hBX, hsize, hrich, hwords⟩ :=
    global_column_word_witness_system A phi ha ha1 hA hphi hNbase k
  let d := columnSpectrumCap (columnEightDensity alpha)
  let r := globalColumnWordZeroRadius alpha
  let rho : Real := 1/(4*Real.pi)
  have hrho : 0 < rho := by dsimp [rho]; positivity
  have hr : 0 < r := globalColumnWordZeroRadius_pos ha ha1
  have hrle : r ≤ rho := zeroLadderRadius_le hrho (globalColumnIdentityRadius_pos ha ha1)
    (globalColumnIdentityRadius_le ha ha1) 15
  have hNcap : refinementKernelCap (4*(k+1)*d) (2*k*d) rho r < N :=
    Nat.lt_of_succ_le ((le_max_right _ _).trans hN)
  refine ⟨X, T, L, W, B, B', hX, hsys, hW, hcol, hB'B, hBX, hsize, hrich, ?_⟩
  intro a as has hlen
  refine ⟨hwords a as has hlen, ?_⟩
  intro w hw
  have hd : 4*(as.length+1)*d ≤ 4*(k+1)*d := by gcongr
  have he : 2*as.length*d ≤ 2*k*d := by gcongr
  have hcap := (refinementKernelCap_mono_dimensions hrho hr hd he).trans_lt hNcap
  have hident := relation_word_identity_remove_aux X B T L
    (columnZeroQ X T L d rho (globalColumnIdentityRadius alpha) 16) hrho hr hrle hBX
    (fun x hx => (hcol x hx).1) (fun x hx => (hcol x hx).2.1)
    (fun x hx => (hcol x hx).2.2)
    (fun a b c d h => columnZeroQ_exact_relation X T L rho (globalColumnIdentityRadius alpha) 15 h)
    a as (fun x hx => hB'B (has x hx)) w hw hcap
  have hrad := refinementKernelRadius_anti_dimensions hrho hr hd he
  intro y hyA hyW
  exact hident y (fun x hx => bohr_mono_radius _ hrad (hyA x hx))
    (fun x hx => bohr_mono_radius _ hrad (hyW x hx))

end LeanProofs.GowersSzemeredi
