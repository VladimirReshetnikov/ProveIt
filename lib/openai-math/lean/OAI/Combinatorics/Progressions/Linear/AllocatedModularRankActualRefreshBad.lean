import OAI.Combinatorics.Progressions.Lattices.AllocatedModularRankIntegerDecay

namespace OAI

section

namespace Erdos3

theorem extend_restrict_disjoint_fiber {T A S K R : Type*} {U : T → Type*}
    (full : (Σ t, U t) ↪ K) (slot : ∀ t, A ↪ U t)
    (selected : S ↪ K) (reindex : T × A ≃ S)
    (hselected : ∀ t a, selected (reindex (t,a)) = full ⟨t, slot t a⟩)
    (f : K → R) (c : S → R) (t : T) (u : U t) :
    Function.extend selected c f (full ⟨t,u⟩) =
      Function.extend (slot t) (fun a => c (reindex (t,a)))
        (fun z => f (full ⟨t,z⟩)) u := by
  classical
  by_cases hu : ∃ a, slot t a = u
  · obtain ⟨a,rfl⟩ := hu
    rw [← hselected t a, selected.injective.extend_apply,
      (slot t).injective.extend_apply]
  · rw [Function.extend_apply' _ _ _ hu]
    apply Function.extend_apply'
    rintro ⟨z,hz⟩
    obtain ⟨⟨s,a⟩,rfl⟩ := reindex.surjective z
    rw [hselected] at hz
    have htu := full.injective hz
    have hst : s = t := congrArg Sigma.fst htu
    subst s
    have hlocal : slot t a = u := eq_of_heq (Sigma.mk.inj htu).2
    exact hu ⟨a,hlocal⟩

theorem map_extend_selected {A K R S : Type*} (slot : A ↪ K)
    (map : R → S) (fixed : K → R) (fresh : A → R) (k : K) :
    map (Function.extend slot fresh fixed k) =
      Function.extend slot (fun a => map (fresh a)) (fun z => map (fixed z)) k := by
  classical
  by_cases hk : ∃ a, slot a = k
  · obtain ⟨a,rfl⟩ := hk
    rw [slot.injective.extend_apply, slot.injective.extend_apply]
  · rw [Function.extend_apply' _ _ _ hk, Function.extend_apply' _ _ _ hk]

end Erdos3

namespace Erdos3.VectorPolynomial
open MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}

def allocatedCongruenceCoefficientReindex
    (inactive : LayerSamplerAxis I n → Prop) (L : ℕ) :
    ((Σ j : Fin m, AllocatedCongruenceRankOutput X E inactive j) × Fin L) ≃
      AllocatedCongruenceCoefficientIndex X E inactive L where
  toFun k := ⟨k.1.1, k.1.2, k.2⟩
  invFun k := (⟨k.1,k.2.1⟩,k.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

theorem allocatedActualRefresh_component {R : Type*}
    (inactive : LayerSamplerAxis I n → Prop)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ (j : Fin m) (a : AllocatedDegreeActiveAxis inactive j), Fin L ↪ B ⟨j, a.val⟩)
    (f : AllocatedActualCoefficientIndex G X I E n B → R)
    (c : AllocatedCongruenceCoefficientIndex X E inactive L → R)
    (j : Fin m) (o : AllocatedCongruenceRankOutput X E inactive j)
    (q : AllocatedRankComponentCoefficient (G := G) (B := B) inactive j o) :
    Function.extend (allocatedCongruenceActualCoefficientEmbedding inactive spatial kernel block)
      c f (allocatedRankComponentCoefficientEmbedding inactive ⟨⟨j,o⟩,q⟩) =
      Function.extend (allocatedRankComponentSelectedEmbedding inactive spatial kernel block j o)
        (fun l => c ⟨j,o,l⟩)
        (fun z => f (allocatedRankComponentCoefficientEmbedding inactive ⟨⟨j,o⟩,z⟩)) q := by
  exact extend_restrict_disjoint_fiber
    (allocatedRankComponentCoefficientEmbedding inactive)
    (fun t => allocatedRankComponentSelectedEmbedding inactive spatial kernel block t.1 t.2)
    (allocatedCongruenceActualCoefficientEmbedding inactive spatial kernel block)
    (allocatedCongruenceCoefficientReindex inactive L)
    (fun t l => (allocatedRankComponentCoefficientEmbedding_selected
      inactive spatial kernel block t.1 t.2 l).symm) f c ⟨j,o⟩ q

theorem allocatedActualRefresh_component_reduce
    (N : ℕ) (inactive : LayerSamplerAxis I n → Prop)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ (j : Fin m) (a : AllocatedDegreeActiveAxis inactive j), Fin L ↪ B ⟨j, a.val⟩)
    (f : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (c : AllocatedCongruenceCoefficientIndex X E inactive L → ℤ)
    (j : Fin m) (o : AllocatedCongruenceRankOutput X E inactive j)
    (q : AllocatedRankComponentCoefficient (G := G) (B := B) inactive j o) :
    ((Function.extend (allocatedCongruenceActualCoefficientEmbedding inactive spatial kernel block)
      c f (allocatedRankComponentCoefficientEmbedding inactive ⟨⟨j,o⟩,q⟩) : ℤ) : ZMod N) =
      Function.extend (allocatedRankComponentSelectedEmbedding inactive spatial kernel block j o)
        (fun l => (c ⟨j,o,l⟩ : ZMod N))
        (fun z => (f (allocatedRankComponentCoefficientEmbedding inactive ⟨⟨j,o⟩,z⟩) : ZMod N)) q := by
  rw [allocatedActualRefresh_component]
  exact map_extend_selected
    (allocatedRankComponentSelectedEmbedding inactive spatial kernel block j o)
    (fun z : ℤ => (z : ZMod N)) _ _ q

variable [Fintype G] [∀ j, Fintype (I j)] [∀ a, Fintype (B a)]

theorem allocatedActualRefresh_original_congruence
    (N : ℕ) (inactive : LayerSamplerAxis I n → Prop)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ (j : Fin m) (a : AllocatedDegreeActiveAxis inactive j), Fin L ↪ B ⟨j, a.val⟩)
    (f : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (c : AllocatedCongruenceCoefficientIndex X E inactive L → ℤ)
    (j : Fin m) (v : LayerSamplerVariables G I n B → ZMod N)
    (o : AllocatedCongruenceRankOutput X E inactive j) :
    let refreshed := fun z => ((Function.extend
      (allocatedCongruenceActualCoefficientEmbedding inactive spatial kernel block) c f z : ℤ) : ZMod N)
    let fixed := fun z => (f z : ZMod N)
    allocatedOriginalTaggedTop inactive j (allocatedReadNoise refreshed) (allocatedReadDeck refreshed)
      (fun a => allocatedReadProjection refreshed ⟨j,a.val⟩) v
      (allocatedCongruenceOutputEmbedding inactive j o) =
      allocatedCongruenceRankPolynomial inactive j (allocatedReadNoise fixed) (allocatedReadDeck fixed)
        (fun a => allocatedReadProjection fixed ⟨j,a.val⟩) spatial (kernel j) (block j)
        (fun z l => (c ⟨j,z,l⟩ : ZMod N)) v o := by
  dsimp only
  let fresh : AllocatedCongruenceRankOutput X E inactive j → Fin L → ZMod N :=
    fun z l => (c ⟨j,z,l⟩ : ZMod N)
  have hext (z : AllocatedCongruenceRankOutput X E inactive j) :
      Function.extend (allocatedCongruenceOutputEmbedding inactive j) fresh (fun _ _ => 0)
        (allocatedCongruenceOutputEmbedding inactive j z) = fresh z :=
    (allocatedCongruenceOutputEmbedding inactive j).injective.extend_apply _ _ z
  rcases o with x | i | a
  · have hx : Function.extend (allocatedCongruenceOutputEmbedding inactive j) fresh
        (fun _ _ => 0) (.inl x) = fresh (.inl x) := hext (.inl x)
    have hc := funext (allocatedActualRefresh_component_reduce N inactive spatial kernel block
      f c j (.inl x))
    change homogeneousComponent 1 (conditionPolynomial (allocatedLongEmbedding inactive)
      (allocatedLongEmbedding inactive).injective v (spatialRankPolynomial _)) = _
    unfold allocatedCongruenceRankPolynomial
    change _ = homogeneousComponent 1 (conditionPolynomial (allocatedLongEmbedding inactive)
      (allocatedLongEmbedding inactive).injective v (spatialRankPolynomial
        (Function.extend (spatialKernelRankSlot spatial)
          (Function.extend (allocatedCongruenceOutputEmbedding inactive j) fresh (fun _ _ => 0)
            (.inl x)) _)))
    rw [hx]
    exact congrArg (fun coefficients => homogeneousComponent 1
      (conditionPolynomial (allocatedLongEmbedding inactive)
        (allocatedLongEmbedding inactive).injective v (spatialRankPolynomial coefficients))) hc
  · have hi : Function.extend (allocatedCongruenceOutputEmbedding inactive j) fresh
        (fun _ _ => 0) (.inr (.inl i)) = fresh (.inr (.inl i)) := hext (.inr (.inl i))
    have hc := funext (allocatedActualRefresh_component_reduce N inactive spatial kernel block
      f c j (.inr (.inl i)))
    unfold allocatedCongruenceRankPolynomial
    simp only [allocatedCongruenceOutputEmbedding_deck, allocatedTaggedRankPolynomial,
      allocatedDegreeRankPolynomial, allocatedOriginalTaggedTop, modularDeckPolynomial,
      resampleCoefficientDeckCoordinate_apply]
    change _ = homogeneousComponent (j.val + 1)
      (conditionPolynomial (allocatedLongEmbedding inactive) (allocatedLongEmbedding inactive).injective v
        (modularBoundedCoefficientPolynomial (j.val + 1)
          (Function.extend (kernelRankCoefficientSlot (layerSamplerDegree I n) (kernel j))
            (Function.extend (allocatedCongruenceOutputEmbedding inactive j) fresh (fun _ _ => 0)
              (.inr (.inl i))) _)))
    rw [hi]
    exact congrArg (fun coefficients => homogeneousComponent (j.val + 1)
      (conditionPolynomial (allocatedLongEmbedding inactive)
        (allocatedLongEmbedding inactive).injective v
        (modularBoundedCoefficientPolynomial (j.val + 1) coefficients))) hc
  · have ha : Function.extend (allocatedCongruenceOutputEmbedding inactive j) fresh
        (fun _ _ => 0) (.inr (.inr (allocatedCongruenceIntegerEmbedding inactive j a))) =
          fresh (.inr (.inr a)) := hext (.inr (.inr a))
    have hc := funext (allocatedActualRefresh_component_reduce N inactive spatial kernel block
      f c j (.inr (.inr a)))
    unfold allocatedCongruenceRankPolynomial
    simp only [allocatedCongruenceOutputEmbedding_integer, allocatedTaggedRankPolynomial,
      allocatedDegreeRankPolynomial, allocatedOriginalTaggedTop]
    change _ = homogeneousComponent (j.val + 1)
      (conditionPolynomial (allocatedLongEmbedding inactive) (allocatedLongEmbedding inactive).injective v
        (modularBoundedCoefficientPolynomial (j.val + 1)
          (Function.extend (canonicalPrincipalSubblockSlot (layerSamplerDegree I n)
            ⟨j,.inr a.val⟩ (block j (allocatedCongruenceIntegerEmbedding inactive j a)))
            (Function.extend (allocatedCongruenceOutputEmbedding inactive j) fresh (fun _ _ => 0)
              (.inr (.inr (allocatedCongruenceIntegerEmbedding inactive j a)))) _)))
    rw [ha]
    exact congrArg (fun coefficients => homogeneousComponent (j.val + 1)
      (conditionPolynomial (allocatedLongEmbedding inactive)
        (allocatedLongEmbedding inactive).injective v
        (modularBoundedCoefficientPolynomial (j.val + 1) coefficients))) hc

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

variable (inactive : LayerSamplerAxis I n → Prop)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ (j : Fin m) (a : AllocatedDegreeActiveAxis inactive j), Fin L ↪ B ⟨j, a.val⟩)
    (f : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (c : AllocatedCongruenceCoefficientIndex X E inactive L → ℤ)

local notation "refreshed" => Function.extend
  (allocatedCongruenceActualCoefficientEmbedding inactive spatial kernel block) c f
local notation "selected" => allocatedCongruenceIntegerSelectedCoefficients inactive
  (allocatedReadNoise refreshed) (allocatedReadDeck refreshed)
  (fun j a => allocatedReadProjection refreshed (Sigma.mk j (Subtype.val a))) spatial kernel block

omit [Fintype X] [∀ j, Fintype (E j)] in

theorem allocatedActualRefresh_rank_polynomial
    (N : ℕ) (j : Fin m) (v : LayerSamplerVariables G I n B → ZMod N)
    (o : AllocatedCongruenceRankOutput X E inactive j) :
    allocatedCongruenceRankPolynomial inactive j
      (fun q => ((allocatedReadNoise refreshed q : ℤ) : ZMod N))
      (fun j q i => ((allocatedReadDeck refreshed j q i : ℤ) : ZMod N))
      (fun a q => ((allocatedReadProjection refreshed ⟨j,a.val⟩ q : ℤ) : ZMod N))
      spatial (kernel j) (block j) (fun z l => (selected ⟨j,z,l⟩ : ZMod N)) v o =
    allocatedCongruenceRankPolynomial inactive j
      (fun q => ((allocatedReadNoise f q : ℤ) : ZMod N))
      (fun j q i => ((allocatedReadDeck f j q i : ℤ) : ZMod N))
      (fun a q => ((allocatedReadProjection f ⟨j,a.val⟩ q : ℤ) : ZMod N))
      spatial (kernel j) (block j) (fun z l => (c ⟨j,z,l⟩ : ZMod N)) v o := by
  simp only [allocatedCongruenceIntegerSelectedCoefficients_reduce,
    allocatedCongruenceRankPolynomial_original]
  exact allocatedActualRefresh_original_congruence N inactive spatial kernel block f c j v o

theorem allocatedActualRefresh_rank_probability
    (N : ℕ) [NeZero N] (j : Fin m) (v : LayerSamplerVariables G I n B → ZMod N)
    (w : AllocatedCongruenceRankOutput X E inactive j → ZMod N) :
    allocatedCongruenceRankFailureProbability inactive j
      (fun q => ((allocatedReadNoise refreshed q : ℤ) : ZMod N))
      (fun j q i => ((allocatedReadDeck refreshed j q i : ℤ) : ZMod N))
      (fun a q => ((allocatedReadProjection refreshed ⟨j,a.val⟩ q : ℤ) : ZMod N))
      spatial (kernel j) (block j) (fun z l => (selected ⟨j,z,l⟩ : ZMod N)) v w =
    allocatedCongruenceRankFailureProbability inactive j
      (fun q => ((allocatedReadNoise f q : ℤ) : ZMod N))
      (fun j q i => ((allocatedReadDeck f j q i : ℤ) : ZMod N))
      (fun a q => ((allocatedReadProjection f ⟨j,a.val⟩ q : ℤ) : ZMod N))
      spatial (kernel j) (block j) (fun z l => (c ⟨j,z,l⟩ : ZMod N)) v w := by
  unfold allocatedCongruenceRankFailureProbability
  simp only [allocatedActualRefresh_rank_polynomial]

theorem allocatedActualRefresh_modulusBad
    (C : ℝ) (N : ℕ) [NeZero N] :
    allocatedCongruenceModulusBad inactive
      (allocatedReadNoise refreshed) (allocatedReadDeck refreshed)
      (fun j a => allocatedReadProjection refreshed ⟨j,a.val⟩) spatial kernel block
      C N (fun z => (selected z : ZMod N)) =
    allocatedCongruenceModulusBad inactive
      (allocatedReadNoise f) (allocatedReadDeck f)
      (fun j a => allocatedReadProjection f ⟨j,a.val⟩) spatial kernel block
      C N (fun z => (c z : ZMod N)) := by
  unfold allocatedCongruenceModulusBad
  simp only [allocatedActualRefresh_rank_probability]

theorem allocatedActualRefresh_rankBad
    (P : Finset ℕ) [∀ p : P, NeZero p.val] (C : ℝ) (p a : ℕ) :
    allocatedCongruenceRankBad inactive
      (allocatedReadNoise refreshed) (allocatedReadDeck refreshed)
      (fun j a => allocatedReadProjection refreshed ⟨j,a.val⟩) spatial kernel block
      P C p a selected =
    allocatedCongruenceRankBad inactive
      (allocatedReadNoise f) (allocatedReadDeck f)
      (fun j a => allocatedReadProjection f ⟨j,a.val⟩) spatial kernel block P C p a c := by
  unfold allocatedCongruenceRankBad smoothResiduePrimeBad
  apply propext
  apply exists_congr
  intro hp
  let : NeZero p := inferInstanceAs (NeZero (⟨p,hp⟩ : P).val)
  exact (allocatedActualRefresh_modulusBad inactive spatial kernel block f c C (p ^ a)).to_iff

theorem allocatedActualRefresh_badDepth
    (P : Finset ℕ) [∀ p : P, NeZero p.val] (A : ℕ → ℕ) (C : ℝ) (p : ℕ) :
    allocatedCongruenceBadDepth inactive
      (allocatedReadNoise refreshed) (allocatedReadDeck refreshed)
      (fun j a => allocatedReadProjection refreshed ⟨j,a.val⟩) spatial kernel block P A C p =
    largestTestedBadDepth A
      (allocatedCongruenceRankBad inactive
        (allocatedReadNoise f) (allocatedReadDeck f)
        (fun j a => allocatedReadProjection f ⟨j,a.val⟩) spatial kernel block P C) p c := by
  unfold allocatedCongruenceBadDepth largestTestedBadDepth
  simp only [allocatedActualRefresh_rankBad]

end Erdos3.VectorPolynomial

end

end OAI
