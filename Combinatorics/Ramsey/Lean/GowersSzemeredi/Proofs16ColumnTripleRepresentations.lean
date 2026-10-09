import GowersSzemeredi.Proofs16PopularColumnAnchors

/-! Exact quadruples at a fixed column are three-term representations,
with the same finite cardinality and a local value identity. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def columnTripleTuple {N : Nat} (a : ZMod N) (t : ZMod N × ZMod N × ZMod N) : Fin 4 → ZMod N :=
  ![a,t.2.1,t.1,t.2.2]

def columnTripleRepresentations {N : Nat} [NeZero N] (B : Finset (ZMod N))
    (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N)
    (r : Real) (a : ZMod N) : Finset (ZMod N × ZMod N × ZMod N) :=
  Finset.univ.filter (fun t => columnTripleTuple a t ∈ exactColumnQuadruples B T L r)

theorem columnTripleRepresentations_card {N : Nat} [NeZero N]
    (B : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (r : Real) (a : ZMod N) :
    (columnTripleRepresentations B T L r a).card = (exactColumnAnchor B T L r a).card := by
  apply Finset.card_bij (fun t _ => columnTripleTuple a t)
  · intro t ht
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp ht).2,rfl⟩
  · intro t ht u hu heq
    exact Prod.ext (congrFun heq 2) (Prod.ext (congrFun heq 1) (congrFun heq 3))
  · intro q hq
    obtain ⟨hqB,hqa⟩ := Finset.mem_filter.mp hq
    let t : ZMod N × ZMod N × ZMod N := (q 2,q 1,q 3)
    have heq : columnTripleTuple a t = q := by
      funext i; fin_cases i
      · exact hqa.symm
      · rfl
      · rfl
      · rfl
    refine ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq.symm ▸ hqB⟩, heq⟩

/-- A triple represents both the index and its column-map value. -/
theorem columnTripleRepresentations_spec {N : Nat} [NeZero N]
    (B : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (r : Real) {a : ZMod N}
    {t : ZMod N × ZMod N × ZMod N} (ht : t ∈ columnTripleRepresentations B T L r a) :
    a ∈ B ∧ t.1 ∈ B ∧ t.2.1 ∈ B ∧ t.2.2 ∈ B ∧ a = t.1-t.2.1+t.2.2 ∧
      (∀ y, y ∈ bohr (T a) r → y ∈ bohr (T t.1) r →
        y ∈ bohr (T t.2.1) r → y ∈ bohr (T t.2.2) r →
        L a y = L t.1 y-L t.2.1 y+L t.2.2 y) := by
  have hq := (Finset.mem_filter.mp ht).2
  obtain ⟨_,hB,hadd,hval⟩ := Finset.mem_filter.mp hq
  refine ⟨hB 0,hB 2,hB 1,hB 3,?_,?_⟩
  · change a+t.2.1 = t.1+t.2.2 at hadd
    linear_combination hadd
  · intro y ha h1 h2 h3
    have hy : ∀ i, y ∈ bohr (T (columnTripleTuple a t i)) r := by
      intro i; fin_cases i
      · exact ha
      · exact h2
      · exact h1
      · exact h3
    have h := hval y hy
    change L a y+L t.2.1 y = L t.1 y+L t.2.2 y at h
    linear_combination h

/-- The popular-anchor bound is exactly the triple-representation bound. -/
theorem popular_column_triple_count {N : Nat} [NeZero N]
    (B : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (r lambda : Real) {a : ZMod N}
    (ha : a ∈ popularColumnAnchors B T L r lambda) :
    lambda*(N : Real)^2 ≤ (columnTripleRepresentations B T L r a).card := by
  rw [columnTripleRepresentations_card]
  exact (Finset.mem_filter.mp ha).2

end LeanProofs.GowersSzemeredi
