import Mathlib.Computability.TuringDegree

/-!
# Turing degrees of sets of natural numbers

Mathlib's `TuringDegree` is the antisymmetrization of Turing reducibility on
arbitrary partial functions `ℕ →. ℕ`.  The classical degrees discussed in the
literature are degrees of *sets*: an oracle for a set is its total
characteristic function.  This file supplies that page-faithful layer.
-/

noncomputable section

open scoped Classical Computability

namespace TuringDegrees

/-- The total `0`/`1` oracle associated with a set of natural numbers. -/
def characteristic (A : Set ℕ) : ℕ →. ℕ :=
  fun n => Part.some (if n ∈ A then 1 else 0)

@[simp]
theorem characteristic_apply (A : Set ℕ) (n : ℕ) :
    characteristic A n = Part.some (if n ∈ A then 1 else 0) :=
  rfl

@[simp]
theorem one_mem_characteristic {A : Set ℕ} {n : ℕ} :
    1 ∈ characteristic A n ↔ n ∈ A := by
  by_cases hn : n ∈ A <;> simp [characteristic, hn]

@[simp]
theorem zero_mem_characteristic {A : Set ℕ} {n : ℕ} :
    0 ∈ characteristic A n ↔ n ∉ A := by
  by_cases hn : n ∈ A <;> simp [characteristic, hn]

theorem characteristic_injective : Function.Injective characteristic := by
  intro A B equality
  ext n
  have pointwise := congrFun equality n
  by_cases hnA : n ∈ A <;> by_cases hnB : n ∈ B <;>
    simp [characteristic, hnA, hnB] at pointwise ⊢

/-- Turing reducibility of sets, via their total characteristic oracles. -/
def SetTuringReducible (A B : Set ℕ) : Prop :=
  characteristic A ≤ᵀ characteristic B

/-- Turing equivalence of sets. -/
def SetTuringEquivalent (A B : Set ℕ) : Prop :=
  SetTuringReducible A B ∧ SetTuringReducible B A

@[inherit_doc]
scoped[SetTuring] infix:50 " ≤ᵀₛ " => TuringDegrees.SetTuringReducible

@[inherit_doc]
scoped[SetTuring] infix:50 " ≡ᵀₛ " => TuringDegrees.SetTuringEquivalent

open scoped SetTuring

protected theorem SetTuringReducible.refl (A : Set ℕ) : A ≤ᵀₛ A :=
  TuringReducible.refl _

protected theorem SetTuringReducible.rfl {A : Set ℕ} : A ≤ᵀₛ A :=
  TuringReducible.refl _

protected theorem SetTuringReducible.trans {A B C : Set ℕ}
    (hAB : A ≤ᵀₛ B) (hBC : B ≤ᵀₛ C) : A ≤ᵀₛ C :=
  TuringReducible.trans hAB hBC

instance : IsPreorder (Set ℕ) SetTuringReducible where
  refl _ := .rfl
  trans _ _ _ := SetTuringReducible.trans

/-! Small closure lemmas for the oracle-recursive functions used below. -/

theorem recursiveIn_precomp {O : Set (ℕ →. ℕ)} {f : ℕ →. ℕ}
    (hf : RecursiveIn O f) {g : ℕ → ℕ} (hg : Computable g) :
    RecursiveIn O (fun n => f (g n)) := by
  rw [RecursiveIn.iff_nat] at hf ⊢
  apply Nat.RecursiveIn.of_eq
    (.comp hf (Nat.Partrec.recursiveIn (Partrec.nat_iff.mp hg.partrec)))
  intro n
  simp

theorem recursiveIn_map {O : Set (ℕ →. ℕ)} {f : ℕ →. ℕ}
    (hf : RecursiveIn O f) {g : ℕ → ℕ} (hg : Computable g) :
    RecursiveIn O (fun n => (f n).map g) := by
  rw [RecursiveIn.iff_nat] at hf ⊢
  apply Nat.RecursiveIn.of_eq
    (.comp (Nat.Partrec.recursiveIn (Partrec.nat_iff.mp hg.partrec)) hf)
  intro n
  exact Part.bind_some_eq_map g (f n)

theorem recursiveIn_pair {O : Set (ℕ →. ℕ)} {f g : ℕ →. ℕ}
    (hf : RecursiveIn O f) (hg : RecursiveIn O g) :
    RecursiveIn O (fun n => Nat.pair <$> f n <*> g n) := by
  rw [RecursiveIn.iff_nat] at hf hg ⊢
  exact .pair hf hg

theorem setTuringEquivalent_equivalence : Equivalence SetTuringEquivalent :=
  ⟨fun _ => ⟨SetTuringReducible.rfl, SetTuringReducible.rfl⟩,
    fun h => h.symm,
    fun hAB hBC => ⟨hAB.1.trans hBC.1, hBC.2.trans hAB.2⟩⟩

@[refl]
protected theorem SetTuringEquivalent.refl (A : Set ℕ) : A ≡ᵀₛ A :=
  Equivalence.refl setTuringEquivalent_equivalence A

@[symm]
protected theorem SetTuringEquivalent.symm {A B : Set ℕ}
    (h : A ≡ᵀₛ B) : B ≡ᵀₛ A :=
  Equivalence.symm setTuringEquivalent_equivalence h

@[trans]
protected theorem SetTuringEquivalent.trans {A B C : Set ℕ}
    (hAB : A ≡ᵀₛ B) (hBC : B ≡ᵀₛ C) : A ≡ᵀₛ C :=
  Equivalence.trans setTuringEquivalent_equivalence hAB hBC

/-- A Turing degree of sets is an equivalence class under mutual oracle
reducibility. -/
def SetTuringDegree : Type :=
  Quotient (⟨SetTuringEquivalent, setTuringEquivalent_equivalence⟩ : Setoid (Set ℕ))

namespace SetTuringDegree

/-- The Turing degree containing `A`. -/
def of (A : Set ℕ) : SetTuringDegree :=
  Quotient.mk'' A

@[elab_as_elim]
protected theorem ind_on {P : SetTuringDegree → Prop} (degree : SetTuringDegree)
    (h : ∀ A : Set ℕ, P (of A)) : P degree :=
  Quotient.inductionOn' degree h

/-- Lift a representative-invariant function to set Turing degrees. -/
protected abbrev liftOn {α : Sort*} (degree : SetTuringDegree)
    (f : Set ℕ → α) (h : ∀ A B, A ≡ᵀₛ B → f A = f B) : α :=
  Quotient.liftOn' degree f h

/-- Lift a representative-invariant binary function to set Turing degrees. -/
@[reducible]
protected def liftOn₂ {α : Sort*} (left right : SetTuringDegree)
    (f : Set ℕ → Set ℕ → α)
    (h : ∀ A A' B B', A ≡ᵀₛ A' → B ≡ᵀₛ B' → f A B = f A' B') : α :=
  left.liftOn
    (fun A => right.liftOn (f A) (fun B B' hB => h A A B B' (.refl A) hB))
    (by
      intro A A' hA
      induction right using SetTuringDegree.ind_on
      exact h A A' _ _ hA (.refl _))

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem of_eq_of {A B : Set ℕ} : of A = of B ↔ A ≡ᵀₛ B := by
  rw [of, of, Quotient.eq'']
  rfl

instance instLE : LE SetTuringDegree where
  le left right :=
    left.liftOn₂ right SetTuringReducible (by
      intro A A' B B' hA hB
      apply propext
      constructor
      · intro h
        exact hA.2.trans (h.trans hB.1)
      · intro h
        exact hA.1.trans (h.trans hB.2))

@[simp]
theorem of_le_of {A B : Set ℕ} : of A ≤ of B ↔ A ≤ᵀₛ B :=
  Iff.rfl

private theorem le_refl (degree : SetTuringDegree) : degree ≤ degree := by
  induction degree using SetTuringDegree.ind_on
  exact SetTuringReducible.rfl

private theorem le_trans {a b c : SetTuringDegree} : a ≤ b → b ≤ c → a ≤ c := by
  induction a using SetTuringDegree.ind_on
  induction b using SetTuringDegree.ind_on
  induction c using SetTuringDegree.ind_on
  exact SetTuringReducible.trans

private theorem le_antisymm {a b : SetTuringDegree} : a ≤ b → b ≤ a → a = b := by
  induction a using SetTuringDegree.ind_on
  induction b using SetTuringDegree.ind_on
  intro hab hba
  exact of_eq_of.mpr ⟨hab, hba⟩

instance instPartialOrder : PartialOrder SetTuringDegree where
  le_refl := le_refl
  le_trans _ _ _ := le_trans
  le_antisymm _ _ := le_antisymm

end SetTuringDegree

end TuringDegrees
