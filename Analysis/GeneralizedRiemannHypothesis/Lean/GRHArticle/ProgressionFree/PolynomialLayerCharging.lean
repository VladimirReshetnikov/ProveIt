import GRHArticle.ProgressionFree.GreedyLengthThree
import GRHArticle.ProgressionFree.PolynomialPrimeDivisorTail
import GRHArticle.ProgressionFree.PolynomialDensitySupremum

/-!
# Charging nonpreferred polynomial layers to preferred layers

The uniqueness of a source layer for a fixed target layer and step needs
only three-term progression-freeness of the preferred indices. It holds
for any allowed choice of predecessors.
-/

namespace GRHArticle.ProgressionFree

open Polynomial Finset
open scoped Classical

/-- The two preceding layer indices at distance `d` are both preferred. -/
def PolynomialLayerStep (C : Set ℕ) (k d : ℕ) : Prop :=
  0 < d ∧ 2*d ≤ k ∧ k-2*d ∈ C ∧ k-d ∈ C

theorem exists_polynomialLayerStep_greedy {k : ℕ} (hk : k ∉ greedyExponents) :
    ∃ d, PolynomialLayerStep greedyExponents k d := by
  obtain ⟨a,b,ha,hb,hab,hbk,he⟩ := exists_threeAP_greedyExponents_of_notMem hk
  refine ⟨k-b,by omega,by omega,?_,?_⟩
  · rwa [show k - 2*(k-b) = a by omega]
  · rwa [show k-(k-b) = b by omega]

/-- Any preferred target index and any positive step identify at most
one source layer. Two different roles would give a three-term progression
entirely among the preferred indices. -/
theorem PolynomialLayerStep.source_unique {C : Set ℕ} (hC : ThreeAPFree C)
    {k l h d : ℕ} (hk : PolynomialLayerStep C k d) (hl : PolynomialLayerStep C l d)
    (h₁ : h = k-d ∨ h = k-2*d) (h₂ : h = l-d ∨ h = l-2*d) : k = l := by
  obtain ⟨hd,hk,ha,hb⟩ := hk
  obtain ⟨_,hl,hx,hy⟩ := hl
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
  · omega
  · have := hC ha hb hy (by omega)
    omega
  · have := hC hx hy hb (by omega)
    omega
  · omega

variable {F : Type*} [Field F]

/-- Send a polynomial to the first missing member of its progression, or
to the last member when the middle member is present. -/
noncomputable def polynomialMissingTarget (E : Set F[X]) (f p : F[X]) : F[X] :=
  if f*p ∈ E then f*p*p else f*p

theorem polynomialMissingTarget_notMem {E : Set F[X]} (hE : PolynomialRatioThreeGPFree E)
    {f p : F[X]} (hf : f ≠ 0) (hmem : f ∈ E) (hp : 0 < p.natDegree) :
    polynomialMissingTarget E f p ∉ E := by
  unfold polynomialMissingTarget
  split_ifs with hm
  · exact fun ht ↦ hE f p hf hp ⟨hmem,hm,ht⟩
  · exact hm

private theorem deficit_missingTarget {E : Set F[X]} {N d : ℕ} {C : Set ℕ} {f p : F[X]}
    (hf : f ≠ 0) (hp : p ≠ 0) (hd : p.natDegree = d)
    (hs : PolynomialLayerStep C (N-f.natDegree) d) :
    let h := N-(polynomialMissingTarget E f p).natDegree
    h = (N-f.natDegree)-d ∨ h = (N-f.natDegree)-2*d := by
  obtain ⟨_, hbudget, _, _⟩ := hs
  unfold polynomialMissingTarget
  split_ifs <;> simp only [natDegree_mul (mul_ne_zero hf hp) hp, natDegree_mul hf hp, hd] <;> omega

/-- The charge arriving at a fixed target and step comes from at most
one source for each distinct prime divisor of that degree. No choice of
canonical ternary predecessors is necessary. -/
theorem card_polynomialMissingTarget_fiber_le {E : Set F[X]} {C : Set ℕ} (hC : ThreeAPFree C)
    {N d : ℕ} (S : Finset F[X]) (D : Finset (F[X] × F[X]))
    (hS : ∀ p ∈ S, p ≠ 0 ∧ p.natDegree = d)
    (hD : ∀ x ∈ D, x.1 ≠ 0 ∧ x.1.natDegree ≤ N ∧ x.2 ∈ S ∧
      PolynomialLayerStep C (N-x.1.natDegree) d) (g : F[X]) :
    (D.filter (fun x ↦ polynomialMissingTarget E x.1 x.2 = g)).card ≤
      (S.filter (· ∣ g)).card := by
  apply Finset.card_le_card_of_injOn Prod.snd
  · intro x hx
    obtain ⟨hx,he⟩ := mem_filter.mp hx
    refine mem_filter.mpr ⟨(hD x hx).2.2.1,?_⟩
    rw [← he,polynomialMissingTarget]
    split_ifs <;> exact dvd_mul_left _ _
  · rintro ⟨f,p⟩ hx ⟨f',p'⟩ hy hp'
    change p = p' at hp'
    subst p'
    obtain ⟨hx,he⟩ := mem_filter.mp hx
    obtain ⟨hy,he'⟩ := mem_filter.mp hy
    obtain ⟨hf,hn,hpS,hs⟩ := hD _ hx
    obtain ⟨hf',hn',_,hs'⟩ := hD _ hy
    obtain ⟨hp,hd⟩ := hS _ hpS
    have h₁ := deficit_missingTarget (E := E) hf hp hd hs
    have h₂ := deficit_missingTarget (E := E) hf' hp hd hs'
    change polynomialMissingTarget E f p = g at he
    change polynomialMissingTarget E f' p = g at he'
    simp only [he] at h₁
    simp only [he'] at h₂
    have hkl := hs.source_unique hC hs' h₁ h₂
    have hfd : f.natDegree = f'.natDegree := by
      change N-f.natDegree = N-f'.natDegree at hkl
      change f.natDegree ≤ N at hn
      change f'.natDegree ≤ N at hn'
      omega
    have h := he.trans he'.symm
    have hpos := hs.1
    suffices hff : f = f' by exact congrArg (fun a ↦ (a,p)) hff
    unfold polynomialMissingTarget at h
    split_ifs at h
    · exact mul_right_cancel₀ hp (mul_right_cancel₀ hp h)
    · have heq := congrArg natDegree h
      simp only [natDegree_mul (mul_ne_zero hf hp) hp, natDegree_mul hf hp,
        natDegree_mul hf' hp, hd, hfd] at heq
      omega
    · have heq := congrArg natDegree h
      simp only [natDegree_mul (mul_ne_zero hf' hp) hp, natDegree_mul hf hp,
        natDegree_mul hf' hp, hd, hfd] at heq
      omega
    · exact mul_right_cancel₀ hp h

end GRHArticle.ProgressionFree
