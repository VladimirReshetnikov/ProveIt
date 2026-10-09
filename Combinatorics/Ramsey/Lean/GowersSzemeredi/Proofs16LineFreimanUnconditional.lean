import GowersSzemeredi.Proofs16DenseBihomPiece
import GowersSzemeredi.Proofs07AdditiveRestriction

/-! The line-wise Freiman input, unconditionally, from Gowers's Corollary 7.6.

`LineFreimanExtraction κ` (`Proofs16DenseBihomPiece`) was introduced as a
consequence of Theorem 2.26 of arXiv:2601.01682 (Sanders's bounds): energy
`≥ δN³` on a line set gives a Freiman sub-line of size `≥ κ(δ)N`. Gowers's
own Corollary 7.6, already proved in the corpus, gives exactly this with a
**polynomial** `κ`. From `γ(αN)³` respected quadruples on a set of density
`α`, it produces a Freiman 8-homomorphism on `≥ 2^(−1882)γ^1164·αN` points.

* `energy_eq_phiAdditiveCount`: with unit weights and one map, the weighted
  energy is the count of respected quadruples.
* `lineFreimanExtraction_holds`: `LineFreimanExtraction` with
  `κ(δ) = 2^(−1882)δ^1164`, taking `γ = δ/α³` and using `α ≤ 1`.
* `densePiece_energy_unconditional`: the energy route to `DenseBihomPiece`
  is unconditional as well.

The polynomial line extractor of `Proofs16LineExtractor` also needed no
Theorem 2.26; this is a second, independent route. Composed with Lemma 7.8
(Freiman maps on dense sets extend to Bohr sets), Corollary 7.6 is the
polynomial-bound analogue in `ℤ/N` of Theorem 17 of arXiv:2109.03093, the
engine of step 2 of the bilinear Bogolyubov argument. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

open Classical

/-- With unit weights and a single map, energy counts respected quadruples. -/
theorem energy_eq_phiAdditiveCount {N : Nat} [NeZero N] (E : Finset (ZMod N)) (f : ZMod N → ZMod N) :
    weightedSimultaneousAdditiveEnergy E (fun _ => 1) (fun _ : Fin 1 => f) =
      (phiAdditiveCount E f : Real) := by
  unfold weightedSimultaneousAdditiveEnergy phiAdditiveCount countWhere
  rw [Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro q _
  rw [Finset.prod_const_one]
  by_cases h : IsPhiAdditive E f q
  · have h' : (∀ t, q t ∈ E) ∧ IsAdditiveQuadruple q ∧
        ∀ i : Fin 1, IsAdditiveQuadruple (fun t => (fun _ : Fin 1 => f) i (q t)) :=
      ⟨h.1, h.2.1, fun _ => h.2.2⟩
    rw [if_pos h', if_pos h]
  · have h' : ¬ ((∀ t, q t ∈ E) ∧ IsAdditiveQuadruple q ∧
        ∀ i : Fin 1, IsAdditiveQuadruple (fun t => (fun _ : Fin 1 => f) i (q t))) :=
      fun h'' => h ⟨h''.1, h''.2.1, h''.2.2 0⟩
    rw [if_neg h', if_neg h]

/-- **The line-wise Freiman input holds**, with a polynomial `κ`. -/
theorem lineFreimanExtraction_holds :
    LineFreimanExtraction (fun δ => (2 : Real) ^ (-(1882 : Real)) * δ ^ 1164) := by
  refine ⟨fun δ hδ => by positivity, ?_⟩
  intro N _ _ E f δ hδ henergy
  have hNR : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  rw [energy_eq_phiAdditiveCount] at henergy
  -- `E` is nonempty
  have hEpos : 0 < E.card := by
    by_contra h0
    have hE : E = ∅ := Finset.card_eq_zero.mp (by omega)
    have : phiAdditiveCount E f = 0 := by
      unfold phiAdditiveCount countWhere
      apply Finset.card_eq_zero.mpr
      apply Finset.filter_eq_empty_iff.mpr
      intro q _ hq
      have := hq.1 0
      rw [hE] at this
      exact Finset.notMem_empty _ this
    rw [this] at henergy
    have : 0 < δ * (N : Real) ^ 3 := by positivity
    simp at henergy
    linarith
  obtain ⟨α, hαdef⟩ : ∃ α : Real, α = (E.card : Real) / N := ⟨_, rfl⟩
  have hα : 0 < α := by rw [hαdef]; exact div_pos (by exact_mod_cast hEpos) hNR
  have hα1 : α ≤ 1 := by
    rw [hαdef, div_le_one hNR]
    have : E.card ≤ N := by
      calc E.card ≤ (Finset.univ : Finset (ZMod N)).card := Finset.card_le_univ _
        _ = N := ZMod.card N
    exact_mod_cast this
  have hcard : (E.card : Real) = α * N := by rw [hαdef]; field_simp
  have hγ : 0 < δ / α ^ 3 := div_pos hδ (pow_pos hα 3)
  have hα3 : α ^ 3 ≠ 0 := (pow_pos hα 3).ne'
  have hcount : δ / α ^ 3 * (α * N) ^ 3 ≤ phiAdditiveCount E f := by
    have : δ / α ^ 3 * (α * N) ^ 3 = δ * (N : Real) ^ 3 * (α ^ 3 / α ^ 3) := by ring
    rw [this, div_self hα3, mul_one]
    exact henergy
  obtain ⟨B, hBE, hBcard, hBfreiman⟩ :=
    corollary_7_6_holds N E f α (δ / α ^ 3) (Fact.out : N.Prime) hα hγ hcard hcount
  refine ⟨B, hBE, ?_, ?_⟩
  · -- `(δ/α³)^1164 · α ≥ δ^1164` since `α ≤ 1`
    have hpow : δ ^ 1164 ≤ (δ / α ^ 3) ^ 1164 * α := by
      have hbig : 0 < α ^ 3492 := pow_pos hα 3492
      have hle : α ^ 3492 ≤ α := by
        calc α ^ 3492 ≤ α ^ 1 := pow_le_pow_of_le_one hα.le hα1 (by norm_num)
          _ = α := pow_one α
      have h1 : 1 ≤ α / α ^ 3492 := by rw [le_div_iff₀ hbig]; linarith
      have heq : (δ / α ^ 3) ^ 1164 * α = δ ^ 1164 * (α / α ^ 3492) := by
        rw [div_pow, ← pow_mul]
        ring
      rw [heq]
      calc δ ^ 1164 = δ ^ 1164 * 1 := (mul_one _).symm
        _ ≤ δ ^ 1164 * (α / α ^ 3492) := mul_le_mul_of_nonneg_left h1 (pow_pos hδ 1164).le
    calc (2 : Real) ^ (-(1882 : Real)) * δ ^ 1164 * N
        ≤ (2 : Real) ^ (-(1882 : Real)) * ((δ / α ^ 3) ^ 1164 * α) * N := by
          apply mul_le_mul_of_nonneg_right _ hNR.le
          exact mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = (2 : Real) ^ (-(1882 : Real)) * (δ / α ^ 3) ^ 1164 * α * N := by ring
      _ ≤ B.card := hBcard
  · intro y₁ y₂ y₃ y₄ h1 h2 h3 h4 hsum
    exact (hBfreiman.mono (by norm_num : 2 ≤ 8)).add_eq_add
      (by exact_mod_cast h1) (by exact_mod_cast h2) (by exact_mod_cast h3) (by exact_mod_cast h4) hsum

/-- The energy route to the single extraction step, now unconditional. -/
theorem densePiece_energy_unconditional :
    DenseBihomPiece (densePieceMass fun δ => (2 : Real) ^ (-(1882 : Real)) * δ ^ 1164) :=
  densePiece_of_lineExtraction lineFreimanExtraction_holds

end LeanProofs.GowersSzemeredi
