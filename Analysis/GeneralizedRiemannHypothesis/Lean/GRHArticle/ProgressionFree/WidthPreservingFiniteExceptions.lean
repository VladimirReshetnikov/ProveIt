import GRHArticle.ProgressionFree.ExteriorPrimeBlockDensity

/-!
# Width bounds for finitely many exceptional blocks

Keep the specified finite family of exceptional blocks, and partition
all other primes into singletons. The resulting rule has the prescribed
width and agrees with the independent exterior rule everywhere else.
-/

namespace GRHArticle.ProgressionFree

open Finset
open scoped Classical

/-- Finite exceptional blocks with independently prescribed exterior
exponents retain any positive width bound satisfied by their blocks. -/
theorem integerBoundedPrimeBlockSet_finiteExceptionPrimeRule {d : ℕ} (hd : 0 < d)
    (S : Finset (Finset ℕ)) (rules : (P : Finset ℕ) → Set (↥P → ℕ)) (G : Set ℕ)
    (hNonempty : ∀ P ∈ S, P.Nonempty) (hpr : ∀ P ∈ S, ∀ p ∈ P, p.Prime)
    (hpair : (S : Set (Finset ℕ)).PairwiseDisjoint id)
    (hWidth : ∀ P ∈ S, P.card ≤ d) :
    IntegerBoundedPrimeBlockSet d (finiteExceptionPrimeRule S rules G) := by
  let U := S.biUnion id
  let out : Set (Finset ℕ) := {P | ∃ p : ℕ, p.Prime ∧ p ∉ U ∧ P = {p}}
  have hDis (P : Finset ℕ) (hP : P ∈ S) (Q : Finset ℕ) (hQ : Q ∈ out) : Disjoint P Q := by
    obtain ⟨q,_,hq,rfl⟩ := hQ
    exact disjoint_left.mpr fun p hp hpq ↦
      hq (mem_biUnion.mpr ⟨P,hP,(mem_singleton.mp hpq) ▸ hp⟩)
  have hNot (P : Finset ℕ) (hP : P ∈ out) : P ∉ S := by
    intro h
    obtain ⟨p,_,hp,rfl⟩ := hP
    exact hp (mem_biUnion.mpr ⟨{p},h,mem_singleton_self p⟩)
  let π : PrimeBlockPartition :=
    { blocks := (S : Set (Finset ℕ)) ∪ out
      nonempty := by
        intro P hP
        rcases hP with hP | ⟨p,_,_,rfl⟩
        · exact hNonempty P hP
        · exact singleton_nonempty p
      primes := by
        intro P hP
        rcases hP with hP | ⟨p,hp,_,rfl⟩
        · exact hpr P hP
        · exact fun q hq ↦ (mem_singleton.mp hq).symm ▸ hp
      covers := by
        intro p hp
        by_cases h : p ∈ U
        · obtain ⟨P,hP,hpP⟩ := mem_biUnion.mp h
          exact ⟨P,Or.inl hP,hpP⟩
        · exact ⟨{p},Or.inr ⟨p,hp,h,rfl⟩,mem_singleton_self _⟩
      pairwiseDisjoint := by
        intro P hP Q hQ hne
        rcases hP with hP | hP <;> rcases hQ with hQ | hQ
        · exact hpair hP hQ hne
        · exact hDis P hP Q hQ
        · exact (hDis Q hQ P hP).symm
        · obtain ⟨p,_,_,rfl⟩ := hP
          obtain ⟨q,_,_,rfl⟩ := hQ
          exact disjoint_singleton.mpr fun h ↦ hne (congrArg singleton h) }
  let R (P : Finset ℕ) : Set (↥P → ℕ) :=
    if P ∈ S then rules P else blockwiseIndependentRules (fun _ ↦ G) P
  refine ⟨π,R,?_,?_⟩
  · intro P hP
    rcases hP with hP | ⟨p,_,_,rfl⟩
    · exact hWidth P hP
    · rw [card_singleton]; omega
  · ext n
    constructor
    · rintro ⟨⟨hn,h⟩,hOut⟩
      refine ⟨hn,fun P hP ↦ ?_⟩
      rcases hP with hP | ⟨p,hp,hpU,rfl⟩
      · rw [show R P = rules P from if_pos hP]
        exact h P hP
      · rw [show R {p} = blockwiseIndependentRules (fun _ ↦ G) {p} from if_neg
          (hNot {p} ⟨p,hp,hpU,rfl⟩)]
        intro q
        change n.factorization q.val ∈ G
        rw [mem_singleton.mp q.property]
        exact hOut p hp hpU
    · rintro ⟨hn,h⟩
      refine ⟨⟨hn,fun P hP ↦ ?_⟩,fun p hp hpU ↦ ?_⟩
      · have ht := h P (Or.inl hP)
        rw [show R P = rules P from if_pos hP] at ht
        exact ht
      · have hOut : ({p} : Finset ℕ) ∈ out := ⟨p,hp,hpU,rfl⟩
        have ht := h {p} (Or.inr hOut)
        rw [show R {p} = blockwiseIndependentRules (fun _ ↦ G) {p} from if_neg
          (hNot {p} hOut)] at ht
        exact ht ⟨p,mem_singleton_self _⟩

end GRHArticle.ProgressionFree
