import OAI.Combinatorics.Progressions.Probability.FiniteProductPointMass

namespace OAI

section

namespace Erdos3

variable {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X]

theorem finiteProductIntegral_section_free (s : I → Bool) (w : I → X → ℝ)
    (f : (I → X) → ℝ) (z : I → X) :
    finiteProductIntegral (fun i => finiteSectionWeight (w i) (s i) (z i)) f =
      finiteProductIntegral (fun i : {i // s i ≠ true} => w i)
        (fun v => f (finiteSplitPoint (fun i => s i = true) (fun i => z i) v)) := by
  classical
  rw [finiteProductIntegral_split (fun i => s i = true)]
  have hfix : (fun i : {i // s i = true} => finiteSectionWeight (w i) (s i) (z i)) =
      (fun i : {i // s i = true} => finiteSectionWeight (w i) true (z i)) := by
    funext i x
    rw [i.property]
  have hfree : (fun i : {i // s i ≠ true} => finiteSectionWeight (w i) (s i) (z i)) =
      (fun i : {i // s i ≠ true} => w i) := by
    funext i x
    have hi : s i = false := Bool.eq_false_iff.mpr i.property
    rw [hi, finiteSectionWeight_false]
  rw [hfix, hfree, finiteProductIntegral_pointMass]

theorem finiteSectionIntegral_free (w : ℕ → X → ℝ) (n : ℕ) (s : Fin n → Bool)
    (f : (Fin n → X) → ℝ) (z : Fin n → X) :
    finiteSectionIntegral w n s f z =
      finiteProductIntegral (fun i : {i : Fin n // s i ≠ true} => w i)
        (fun v => f (finiteSplitPoint (fun i => s i = true) (fun i => z i) v)) := by
  rw [finiteSectionIntegral_eq_product, finiteProductIntegral_section_free]

end Erdos3

end

section

namespace Erdos3

variable {X : Type*} [Fintype X]

theorem finiteSectionIntegral_orderedFree (w : ℕ → X → ℝ) (n : ℕ) (s : Fin n → Bool)
    (f : (Fin n → X) → ℝ) (z : Fin n → X) :
    finiteSectionIntegral w n s f z =
      finiteProductIntegral (fun i : Fin (n - finiteSectionCount s) => w (finiteSectionFreeOrder n s i))
        (fun v => f (finiteSectionFill n s z v)) := by
  rw [finiteSectionIntegral_free]
  exact (finiteProductIntegral_reindex (finiteSectionFreeOrder n s).toEquiv
    (fun i : {i : Fin n // s i ≠ true} => w i)
    (fun v => f (finiteSplitPoint (fun i => s i = true) (fun i => z i) v))).symm

theorem finiteSectionL2Norm_orderedFree (w : ℕ → X → ℝ) (n : ℕ) (s : Fin n → Bool)
    (f : (Fin n → X) → ℝ) (z : Fin n → X) :
    finiteSectionL2Norm w n s f z =
      Real.sqrt (finiteProductIntegral
        (fun i : Fin (n - finiteSectionCount s) => w (finiteSectionFreeOrder n s i))
        (fun v => f (finiteSectionFill n s z v) ^ 2)) := by
  rw [finiteSectionL2Norm, finiteSectionIntegral_orderedFree]

end Erdos3

end

end OAI
