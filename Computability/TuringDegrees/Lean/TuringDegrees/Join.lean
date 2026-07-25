import TuringDegrees.Computable
import Mathlib.Data.Nat.Bits

/-!
# Joins of set Turing degrees

For sets `A` and `B`, their join places `A` on the even numbers and `B` on
the odd numbers.  Its degree is the least upper bound of their degrees.
-/

noncomputable section

open scoped Computability

namespace TuringDegrees

open scoped SetTuring

/-- Wikipedia's even/odd join of two sets:
`A ⊕ B = {2n | n ∈ A} ∪ {2n + 1 | n ∈ B}`. -/
def setJoin (A B : Set ℕ) : Set ℕ :=
  {n | match n.bodd with
    | false => n.div2 ∈ A
    | true => n.div2 ∈ B}

local infixl:65 " ⊕ₜ " => setJoin

/-- The embedding of an input into the even half of a join. -/
def evenCode (n : ℕ) : ℕ :=
  Nat.bit false n

/-- The embedding of an input into the odd half of a join. -/
def oddCode (n : ℕ) : ℕ :=
  Nat.bit true n

@[simp]
theorem evenCode_mem_join {A B : Set ℕ} {n : ℕ} :
    evenCode n ∈ A ⊕ₜ B ↔ n ∈ A := by
  simp [setJoin, evenCode]

@[simp]
theorem oddCode_mem_join {A B : Set ℕ} {n : ℕ} :
    oddCode n ∈ A ⊕ₜ B ↔ n ∈ B := by
  simp [setJoin, oddCode]

theorem computable_evenCode : Computable evenCode := by
  apply ((Primrec.nat_mul.comp (Primrec.const 2) Primrec.id).to_comp).of_eq
  intro n
  simp [evenCode, Nat.bit_val]

theorem computable_oddCode : Computable oddCode := by
  apply (Computable.succ.comp computable_evenCode).of_eq
  intro n
  simp [oddCode, evenCode, Nat.bit_val, Nat.add_comm]

theorem reducible_join_left (A B : Set ℕ) : A ≤ᵀₛ A ⊕ₜ B := by
  have queried : RecursiveIn {characteristic (A ⊕ₜ B)} (characteristic (A ⊕ₜ B)) :=
    RecursiveIn.oracle _ (by simp)
  apply (recursiveIn_precomp queried computable_evenCode).of_eq
  intro n
  by_cases hn : n ∈ A
  · have hjoin : evenCode n ∈ A ⊕ₜ B := evenCode_mem_join.mpr hn
    simp [characteristic, hn, hjoin]
  · have hjoin : evenCode n ∉ A ⊕ₜ B := by
      simpa only [evenCode_mem_join] using hn
    simp [characteristic, hn, hjoin]

theorem reducible_join_right (A B : Set ℕ) : B ≤ᵀₛ A ⊕ₜ B := by
  have queried : RecursiveIn {characteristic (A ⊕ₜ B)} (characteristic (A ⊕ₜ B)) :=
    RecursiveIn.oracle _ (by simp)
  apply (recursiveIn_precomp queried computable_oddCode).of_eq
  intro n
  by_cases hn : n ∈ B
  · have hjoin : oddCode n ∈ A ⊕ₜ B := oddCode_mem_join.mpr hn
    simp [characteristic, hn, hjoin]
  · have hjoin : oddCode n ∉ A ⊕ₜ B := by
      simpa only [oddCode_mem_join] using hn
    simp [characteristic, hn, hjoin]

/-- Decode an input packed as `(originalInput, (AAnswer, BAnswer))` and
select the answer appropriate to the parity of the original input. -/
def joinSelector (code : ℕ) : ℕ :=
  let outer := code.unpair
  let answers := outer.2.unpair
  bif outer.1.bodd then answers.2 else answers.1

theorem computable_joinSelector : Computable joinSelector := by
  have original : Primrec fun code : ℕ => code.unpair.1 :=
    Primrec.fst.comp Primrec.unpair
  have answers : Primrec fun code : ℕ => code.unpair.2.unpair :=
    Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)
  exact (Primrec.cond
    (Primrec.nat_bodd.comp original)
    (Primrec.snd.comp answers)
    (Primrec.fst.comp answers)).to_comp

/-- The even/odd join is reducible to every common upper bound. -/
theorem join_reducible {A B C : Set ℕ}
    (hA : A ≤ᵀₛ C) (hB : B ≤ᵀₛ C) : A ⊕ₜ B ≤ᵀₛ C := by
  have hAdiv : RecursiveIn {characteristic C}
      (fun n : ℕ => characteristic A (Nat.div2 n)) :=
    recursiveIn_precomp hA Computable.nat_div2
  have hBdiv : RecursiveIn {characteristic C}
      (fun n : ℕ => characteristic B (Nat.div2 n)) :=
    recursiveIn_precomp hB Computable.nat_div2
  have hAnswers : RecursiveIn {characteristic C} (fun n =>
      Nat.pair <$> characteristic A (Nat.div2 n) <*>
        characteristic B (Nat.div2 n)) :=
    recursiveIn_pair hAdiv hBdiv
  have hInput : RecursiveIn {characteristic C} (fun n => Part.some n) :=
    (Computable.id : Computable (fun n : ℕ => n)).partrec.recursiveIn
  have hPacked : RecursiveIn {characteristic C} (fun n =>
      Nat.pair <$> Part.some n <*>
        (Nat.pair <$> characteristic A (Nat.div2 n) <*>
          characteristic B (Nat.div2 n))) :=
    recursiveIn_pair hInput hAnswers
  have hSelected := recursiveIn_map hPacked computable_joinSelector
  apply hSelected.of_eq
  intro n
  cases hn : n.bodd
  · by_cases hmem : Nat.div2 n ∈ A
    · have hjoin : n ∈ A ⊕ₜ B := by simp [setJoin, hn, hmem]
      simp [characteristic, joinSelector, hn, hmem, hjoin, Seq.seq]
    · have hjoin : n ∉ A ⊕ₜ B := by simp [setJoin, hn, hmem]
      simp [characteristic, joinSelector, hn, hmem, hjoin, Seq.seq]
  · by_cases hmem : Nat.div2 n ∈ B
    · have hjoin : n ∈ A ⊕ₜ B := by simp [setJoin, hn, hmem]
      simp [characteristic, joinSelector, hn, hmem, hjoin, Seq.seq]
    · have hjoin : n ∉ A ⊕ₜ B := by simp [setJoin, hn, hmem]
      simp [characteristic, joinSelector, hn, hmem, hjoin, Seq.seq]

theorem join_reducible_iff {A B C : Set ℕ} :
    A ⊕ₜ B ≤ᵀₛ C ↔ A ≤ᵀₛ C ∧ B ≤ᵀₛ C := by
  constructor
  · intro h
    exact ⟨(reducible_join_left A B).trans h,
      (reducible_join_right A B).trans h⟩
  · rintro ⟨hA, hB⟩
    exact join_reducible hA hB

namespace SetTuringDegree

/-- Supremum induced by the even/odd join of representatives. -/
protected def sup (left right : SetTuringDegree) : SetTuringDegree :=
  left.liftOn₂ right (fun A B => of (A ⊕ₜ B)) (by
    intro A A' B B' hA hB
    apply of_eq_of.mpr
    constructor
    · apply join_reducible
      · exact hA.1.trans (reducible_join_left A' B')
      · exact hB.1.trans (reducible_join_right A' B')
    · apply join_reducible
      · exact hA.2.trans (reducible_join_left A B)
      · exact hB.2.trans (reducible_join_right A B))

@[simp]
theorem sup_of (A B : Set ℕ) :
    SetTuringDegree.sup (of A) (of B) = of (A ⊕ₜ B) :=
  rfl

instance instSemilatticeSup : SemilatticeSup SetTuringDegree where
  __ := instPartialOrder
  sup := SetTuringDegree.sup
  le_sup_left left right := by
    induction left using SetTuringDegree.ind_on
    induction right using SetTuringDegree.ind_on
    exact reducible_join_left _ _
  le_sup_right left right := by
    induction left using SetTuringDegree.ind_on
    induction right using SetTuringDegree.ind_on
    exact reducible_join_right _ _
  sup_le left right upper hleft hright := by
    induction left using SetTuringDegree.ind_on
    induction right using SetTuringDegree.ind_on
    induction upper using SetTuringDegree.ind_on
    exact join_reducible hleft hright

@[simp]
theorem of_join (A B : Set ℕ) :
    of (A ⊕ₜ B) = of A ⊔ of B :=
  rfl

end SetTuringDegree

/-! ## Complement invariance -/

/-- Flip a characteristic-oracle answer.  On `0`/`1` inputs this exchanges
false and true. -/
def flipBit (n : ℕ) : ℕ :=
  if n = 0 then 1 else 0

theorem computable_flipBit : Computable flipBit := by
  exact (Primrec.ite
    (Primrec.eq.comp Primrec.id (Primrec.const 0))
    (Primrec.const 1)
    (Primrec.const 0)).to_comp

theorem compl_reducible (A : Set ℕ) : Aᶜ ≤ᵀₛ A := by
  have queried : RecursiveIn {characteristic A} (characteristic A) :=
    RecursiveIn.oracle _ (by simp)
  apply (recursiveIn_map queried computable_flipBit).of_eq
  intro n
  by_cases hn : n ∈ A <;> simp [characteristic, flipBit, hn]

theorem reducible_compl (A : Set ℕ) : A ≤ᵀₛ Aᶜ := by
  have queried : RecursiveIn {characteristic Aᶜ} (characteristic Aᶜ) :=
    RecursiveIn.oracle _ (by simp)
  apply (recursiveIn_map queried computable_flipBit).of_eq
  intro n
  by_cases hn : n ∈ A <;> simp [characteristic, flipBit, hn]

theorem compl_equivalent (A : Set ℕ) : Aᶜ ≡ᵀₛ A :=
  ⟨compl_reducible A, reducible_compl A⟩

@[simp]
theorem SetTuringDegree.of_compl (A : Set ℕ) :
    SetTuringDegree.of Aᶜ = SetTuringDegree.of A :=
  SetTuringDegree.of_eq_of.mpr (compl_equivalent A)

end TuringDegrees
