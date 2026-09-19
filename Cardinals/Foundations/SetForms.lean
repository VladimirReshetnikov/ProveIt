/-
  FIRST-ORDER FORMULAS FOR A FEW SET-THEORETIC NOTIONS, with their meaning in a
  transitive, pair-closed set structure `(A, ∈)`:

  * `surjF f m S`   : `v_f` is (the graph of) a function from `v_m` onto `v_S`;
  * `sUnionF i j`   : `v_i = ⋃ v_j`;
  * `minSurjF`      : `v_0` is the least element of `v_1` that maps onto `v_2`
                      (used to define the cardinality of a small set of ordinals);
  * `interF i j k`  : `v_i = v_j ∩ v_k`.

  Nothing is admitted in this file.
-/
import Cardinals.Foundations.PairForm

universe u

namespace Cardinals

open ZFSet
open SetTheory (Form Sat scons)
open SetTheory.Form

variable {A : ZFSet.{u}}

/-! ### Surjections -/

/-- `∀ u ∈ v_m ∃ v ∈ v_S, ⟨u, v⟩ ∈ v_f`. -/
def totalF (f m S : ℕ) : Form :=
  fAll (fImp (fMem 0 (m + 1)) (fEx (fAnd (fMem 0 (S + 2)) (pairMemF 1 0 (f + 2)))))

/-- `v_f` is single valued. -/
def funcF (f : ℕ) : Form :=
  fAll (fAll (fAll (fImp (fAnd (pairMemF 2 1 (f + 3)) (pairMemF 2 0 (f + 3))) (fEq 1 0))))

/-- `∀ v ∈ v_S ∃ u ∈ v_m, ⟨u, v⟩ ∈ v_f`. -/
def ontoF (f m S : ℕ) : Form :=
  fAll (fImp (fMem 0 (S + 1)) (fEx (fAnd (fMem 0 (m + 2)) (pairMemF 0 1 (f + 2)))))

/-- `v_f` is a function from `v_m` onto `v_S`. -/
def surjF (f m S : ℕ) : Form := fAnd (totalF f m S) (fAnd (funcF f) (ontoF f m S))

/-- The meaning of `surjF` in `(A, ∈)`. -/
def SurjSem (A f m S : ZFSet.{u}) : Prop :=
  (∀ u ∈ m, ∃ v ∈ S, pair u v ∈ f) ∧
  (∀ u ∈ A, ∀ v ∈ A, ∀ v' ∈ A, pair u v ∈ f → pair u v' ∈ f → v = v') ∧
  (∀ v ∈ S, ∃ u ∈ m, pair u v ∈ f)

theorem totalF_spec (hA : IsTransitive A) (hP : PairClosed A) (e : ℕ → Carrier A) (f m S : ℕ) :
    Sat (memOn A) e (totalF f m S) ↔ ∀ u ∈ (e m).1, ∃ v ∈ (e S).1, pair u v ∈ (e f).1 := by
  unfold totalF
  simp only [Sat]
  constructor
  · intro h u hu
    obtain ⟨d', hd', hp⟩ := h ⟨u, hA.subset_of_mem (e m).2 hu⟩ hu
    rw [pairMemF_spec hA hP] at hp
    exact ⟨d'.1, hd', hp⟩
  · intro h d hd
    obtain ⟨v, hv, hp⟩ := h d.1 hd
    refine ⟨⟨v, hA.subset_of_mem (e S).2 hv⟩, hv, ?_⟩
    rw [pairMemF_spec hA hP]
    exact hp

theorem funcF_spec (hA : IsTransitive A) (hP : PairClosed A) (e : ℕ → Carrier A) (f : ℕ) :
    Sat (memOn A) e (funcF f) ↔
      ∀ u ∈ A, ∀ v ∈ A, ∀ v' ∈ A, pair u v ∈ (e f).1 → pair u v' ∈ (e f).1 → v = v' := by
  unfold funcF
  simp only [Sat]
  constructor
  · intro h u hu v hv v' hv' h1 h2
    have := h ⟨u, hu⟩ ⟨v, hv⟩ ⟨v', hv'⟩
      ⟨(pairMemF_spec hA hP _ 2 1 (f + 3)).mpr h1, (pairMemF_spec hA hP _ 2 0 (f + 3)).mpr h2⟩
    exact congrArg Subtype.val this
  · rintro h d₁ d₂ d₃ ⟨h1, h2⟩
    rw [pairMemF_spec hA hP] at h1 h2
    exact Subtype.ext (h d₁.1 d₁.2 d₂.1 d₂.2 d₃.1 d₃.2 h1 h2)

theorem ontoF_spec (hA : IsTransitive A) (hP : PairClosed A) (e : ℕ → Carrier A) (f m S : ℕ) :
    Sat (memOn A) e (ontoF f m S) ↔ ∀ v ∈ (e S).1, ∃ u ∈ (e m).1, pair u v ∈ (e f).1 := by
  unfold ontoF
  simp only [Sat]
  constructor
  · intro h v hv
    obtain ⟨d', hd', hp⟩ := h ⟨v, hA.subset_of_mem (e S).2 hv⟩ hv
    rw [pairMemF_spec hA hP] at hp
    exact ⟨d'.1, hd', hp⟩
  · intro h d hd
    obtain ⟨u, hu, hp⟩ := h d.1 hd
    refine ⟨⟨u, hA.subset_of_mem (e m).2 hu⟩, hu, ?_⟩
    rw [pairMemF_spec hA hP]
    exact hp

theorem surjF_spec (hA : IsTransitive A) (hP : PairClosed A) (e : ℕ → Carrier A) (f m S : ℕ) :
    Sat (memOn A) e (surjF f m S) ↔ SurjSem A (e f).1 (e m).1 (e S).1 := by
  unfold surjF SurjSem
  simp only [Sat]
  rw [totalF_spec hA hP, funcF_spec hA hP, ontoF_spec hA hP]

/-! ### The least element of `v_1` mapping onto `v_2` -/

/-- `v_0 ∈ v_1`, some function maps `v_0` onto `v_2`, and no element of `v_0` has this
property. -/
def minSurjF : Form :=
  fAnd (fMem 0 1) (fAnd (fEx (surjF 0 1 3))
    (fAll (fImp (fMem 0 1) (fImp (fEx (surjF 0 1 4)) fBot))))

theorem minSurjF_spec (hA : IsTransitive A) (hP : PairClosed A) (e : ℕ → Carrier A) :
    Sat (memOn A) e minSurjF ↔
      (e 0).1 ∈ (e 1).1 ∧ (∃ f ∈ A, SurjSem A f (e 0).1 (e 2).1) ∧
        ∀ ν ∈ (e 0).1, ¬ ∃ f ∈ A, SurjSem A f ν (e 2).1 := by
  unfold minSurjF
  simp only [Sat]
  refine and_congr Iff.rfl (and_congr ?_ ?_)
  · constructor
    · rintro ⟨d, hd⟩
      rw [surjF_spec hA hP] at hd
      exact ⟨d.1, d.2, hd⟩
    · rintro ⟨f, hf, h⟩
      refine ⟨⟨f, hf⟩, ?_⟩
      rw [surjF_spec hA hP]
      exact h
  · constructor
    · rintro h ν hν ⟨f, hf, hs⟩
      refine h ⟨ν, hA.subset_of_mem (e 0).2 hν⟩ hν ⟨⟨f, hf⟩, ?_⟩
      rw [surjF_spec hA hP]
      exact hs
    · rintro h d hd ⟨d', hd'⟩
      rw [surjF_spec hA hP] at hd'
      exact h d.1 hd ⟨d'.1, d'.2, hd'⟩

/-! ### Unions and intersections -/

/-- `v_i = ⋃ v_j`. -/
def sUnionF (i j : ℕ) : Form :=
  fAll (SetTheory.fIff (fMem 0 (i + 1)) (fEx (fAnd (fMem 0 (j + 2)) (fMem 1 0))))

theorem sUnionF_spec (hA : IsTransitive A) (e : ℕ → Carrier A) (i j : ℕ) :
    Sat (memOn A) e (sUnionF i j) ↔ (e i).1 = ⋃₀ (e j).1 := by
  unfold sUnionF
  simp only [Sat, SetTheory.Sat_fIff]
  constructor
  · intro h
    ext t
    rw [mem_sUnion]
    constructor
    · intro ht
      obtain ⟨b, hb, htb⟩ := (h ⟨t, hA.subset_of_mem (e i).2 ht⟩).mp ht
      exact ⟨b.1, hb, htb⟩
    · rintro ⟨b, hb, htb⟩
      have hbA : b ∈ A := hA.subset_of_mem (e j).2 hb
      exact (h ⟨t, hA.subset_of_mem hbA htb⟩).mpr ⟨⟨b, hbA⟩, hb, htb⟩
  · intro h d
    constructor
    · intro hd
      have hd0 : d.1 ∈ (e i).1 := hd
      have hd' : d.1 ∈ ⋃₀ (e j).1 := h ▸ hd0
      obtain ⟨b, hb, hdb⟩ := mem_sUnion.mp hd'
      exact ⟨⟨b, hA.subset_of_mem (e j).2 hb⟩, hb, hdb⟩
    · rintro ⟨b, hb, hdb⟩
      have : d.1 ∈ ⋃₀ (e j).1 := mem_sUnion.mpr ⟨b.1, hb, hdb⟩
      have h' : d.1 ∈ (e i).1 := h ▸ this
      exact h'

/-- `v_i = v_j ∩ v_k`. -/
def interF (i j k : ℕ) : Form :=
  fAll (SetTheory.fIff (fMem 0 (i + 1)) (fAnd (fMem 0 (j + 1)) (fMem 0 (k + 1))))

theorem interF_spec (hA : IsTransitive A) (e : ℕ → Carrier A) (i j k : ℕ) :
    Sat (memOn A) e (interF i j k) ↔ (e i).1 = (e j).1 ∩ (e k).1 := by
  unfold interF
  simp only [Sat, SetTheory.Sat_fIff]
  constructor
  · intro h
    ext t
    rw [mem_inter]
    constructor
    · intro ht
      exact (h ⟨t, hA.subset_of_mem (e i).2 ht⟩).mp ht
    · intro ht
      exact (h ⟨t, hA.subset_of_mem (e j).2 ht.1⟩).mpr ht
  · intro h d
    show d.1 ∈ (e i).1 ↔ d.1 ∈ (e j).1 ∧ d.1 ∈ (e k).1
    rw [h, mem_inter]

end Cardinals
