import GRHArticle.ProgressionFree.PolynomialBlocks
import GRHArticle.ProgressionFree.PolynomialRoughReplacement

/-!
# The infinite union for the 74-deficit polynomial replacement
-/

namespace GRHArticle.ProgressionFree

open Polynomial Filter Topology

/-- The set from gluing the modified degree balls with their uppermost layers. -/
noncomputable def polynomialReplacementUnion {F : Type*} [Field F] (R : ℕ) :
    Set (Polynomial F) :=
  polynomialBlockUnion (polynomialBlockCutoff (R+2))
    (fun j ↦ polynomialDeficitReplacement (polynomialBlockCutoff (R+2) j) R)

/-- Two consecutive ratio steps of positive degree cannot stay in the glued set. -/
theorem polynomialReplacementUnion_no_ratio_progression {F : Type*} [Field F] (R : ℕ)
    {f r : Polynomial F} (hr : 0 < r.natDegree) :
    ¬ (f ∈ polynomialReplacementUnion R ∧ f * r ∈ polynomialReplacementUnion R ∧
      f * r * r ∈ polynomialReplacementUnion R) :=
  polynomialBlockUnion_no_ratio_progression (fun ⦃_ _⦄ h ↦ polynomialBlockCutoff_gap _ h) _
    (fun _ h ↦ h.1 rfl) (fun _ _ _ ↦ polynomialDeficitReplacement_no_ratio_progression _ _) f r hr

/-- The construction contains the monomial at the top of every selected ball. -/
theorem polynomialReplacementUnion_infinite {F : Type*} [Field F] (R : ℕ) :
    (polynomialReplacementUnion (F := F) R).Infinite := by
  let N := polynomialBlockCutoff (R+2)
  let f (j : ℕ) : Polynomial F := X ^ N j
  have hdeg (j : ℕ) : (f j).natDegree = N j := natDegree_X_pow _
  have hinj : Function.Injective f := by
    intro i j hij
    apply (polynomialBlockCutoff_strictMono (R+2)).injective
    exact (hdeg i).symm.trans ((congrArg natDegree hij).trans (hdeg j))
  apply (Set.infinite_range_of_injective hinj).mono
  rintro _ ⟨j, rfl⟩
  have hw : 0 ∈ polynomialDeficitWitness := by decide
  refine ⟨j, ⟨pow_ne_zero _ X_ne_zero, (hdeg j).le, ?_, ?_⟩, ?_, (hdeg j).le⟩
  · intro _
    simpa [hdeg, N] using hw
  · intro _
    simpa [hdeg, N] using zero_mem_greedyExponents
  · change N j ≤ (f j).natDegree + j
    rw [hdeg]
    omega

/-- The upper density of the actual glued set dominates the limit of the
modified ball proportions whenever that limit is established. -/
theorem polynomialReplacementUnion_le_limsup {F : Type*} [Field F] [Fintype F]
    (R : ℕ) {d : ℝ}
    (hd : Tendsto (fun n ↦ polynomialBallProportion
      (polynomialDeficitReplacement (F := F) n R) n) atTop (𝓝 d)) :
    d ≤ limsup (polynomialBallProportion (polynomialReplacementUnion (F := F) R)) atTop :=
  polynomialBlockUnion_le_limsup (polynomialBlockCutoff_strictMono (R+2)) _
    (hd.comp (polynomialBlockCutoff_strictMono (R+2)).tendsto_atTop)

end GRHArticle.ProgressionFree
