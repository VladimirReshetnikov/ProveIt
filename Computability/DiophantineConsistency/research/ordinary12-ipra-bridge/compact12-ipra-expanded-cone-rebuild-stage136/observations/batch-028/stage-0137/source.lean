/-
  SetTheory.PAHF.AckermannHFCore

  Ackermann bit-coding of hereditary finite sets on `Nat`, the finite-set axioms that need only bit arithmetic, the (finite) adjunction models, and the semantic PA-in-HF round trip.  Reusable semantic core of the PA <-> HF bi-interpretation.
-/
import FirstOrder.Completeness

namespace SetTheory

/-! ## Ackermann-coded hereditary finite sets -/

namespace AckermannHF

open Form

/-- `Mem x y` means: in Ackermann's coding, the set coded by `x` is an element
of the set coded by `y`.  Equivalently, the `x`-th binary digit of `y` is set. -/
def Mem (x y : Nat) : Prop := y.testBit x = true

/-- The zero-th Ackermann member is present exactly when the code is odd; this
one-way form is the shape produced by a first binary-halving step. -/
theorem mem_zero_of_odd_double {set half : Nat}
    (hset : set = half + half + 1) : Mem 0 set := by
  rw [Mem, hset, Nat.testBit_zero]
  have hmod : (half + half + 1) % 2 = 1 := by omega
  simp [hmod]

/-- The zero-th Ackermann member is absent from an even code. -/
theorem not_mem_zero_of_double {set half : Nat}
    (hset : set = half + half) : ¬ Mem 0 set := by
  rw [Mem, hset, Nat.testBit_zero]
  have hmod : (half + half) % 2 = 0 := by omega
  simp [hmod]

/-- Doubling a code shifts every positive Ackermann member down by one bit. -/
theorem mem_succ_double_iff (x half : Nat) :
    Mem (x+1) (half + half) ↔ Mem x half := by
  unfold Mem
  rw [Nat.testBit_succ]
  have hdiv : (half + half) / 2 = half := by omega
  simp [hdiv]

/-- Odd doubling has the same positive-bit shift as doubling; only bit zero is
new. -/
theorem mem_succ_odd_double_iff (x half : Nat) :
    Mem (x+1) (half + half + 1) ↔ Mem x half := by
  unfold Mem
  rw [Nat.testBit_succ]
  have hdiv : (half + half + 1) / 2 = half := by omega
  simp [hdiv]

/-- Positive Ackermann membership in an even code survives incrementing the
set code.  The increment only changes bit zero; every bit `x+1` still reads
the corresponding bit of the half code. -/
theorem mem_succ_of_double_mem_succ
    {x set half : Nat} (hset : set = half + half)
    (hmem : Mem (x+1) set) :
    Mem (x+1) (set+1) := by
  subst set
  exact (mem_succ_odd_double_iff x half).mpr
    ((mem_succ_double_iff x half).mp hmem)

/-- A high-only bit remains high-only after the even/odd carry shift
`high ↦ 2*high`, `low ↦ 2*low+1`. -/
theorem mem_succ_double_not_mem_succ_odd_double_of_mem_not_mem
    {x high low : Nat} (hhigh : Mem x high) (hlow : ¬ Mem x low) :
    Mem (x+1) (high + high) ∧
      ¬ Mem (x+1) (low + low + 1) := by
  exact ⟨(mem_succ_double_iff x high).mpr hhigh,
    fun h => hlow ((mem_succ_odd_double_iff x low).mp h)⟩

/-- A high-only bit remains high-only after the even/even positive-bit shift
`high ↦ 2*high`, `low ↦ 2*low`. -/
theorem mem_succ_double_not_mem_succ_double_of_mem_not_mem
    {x high low : Nat} (hhigh : Mem x high) (hlow : ¬ Mem x low) :
    Mem (x+1) (high + high) ∧
      ¬ Mem (x+1) (low + low) := by
  exact ⟨(mem_succ_double_iff x high).mpr hhigh,
    fun h => hlow ((mem_succ_double_iff x low).mp h)⟩

/-- A high-only bit remains high-only after the odd/even positive-bit shift
`high ↦ 2*high+1`, `low ↦ 2*low`. -/
theorem mem_succ_odd_double_not_mem_succ_double_of_mem_not_mem
    {x high low : Nat} (hhigh : Mem x high) (hlow : ¬ Mem x low) :
    Mem (x+1) (high + high + 1) ∧
      ¬ Mem (x+1) (low + low) := by
  exact ⟨(mem_succ_odd_double_iff x high).mpr hhigh,
    fun h => hlow ((mem_succ_double_iff x low).mp h)⟩

/-- A high-only bit remains high-only after the odd/odd positive-bit shift
`high ↦ 2*high+1`, `low ↦ 2*low+1`. -/
theorem mem_succ_odd_double_not_mem_succ_odd_double_of_mem_not_mem
    {x high low : Nat} (hhigh : Mem x high) (hlow : ¬ Mem x low) :
    Mem (x+1) (high + high + 1) ∧
      ¬ Mem (x+1) (low + low + 1) := by
  exact ⟨(mem_succ_odd_double_iff x high).mpr hhigh,
    fun h => hlow ((mem_succ_odd_double_iff x low).mp h)⟩

/-- Nonmembership is the closed Boolean value `false` of the corresponding
Ackermann bit. -/
theorem testBit_false_of_not_mem {x y : Nat} (h : ¬ Mem x y) :
    y.testBit x = false := by
  cases hb : y.testBit x <;> simp [Mem, hb] at h ⊢

/-- The empty set is coded by `0`. -/
def empty : Nat := 0

/-- Adjunction/insert: add the element coded by `x` to the set coded by `a`. -/
def adjoin (a x : Nat) : Nat := a ||| 2 ^ x

theorem mem_empty (x : Nat) : ¬ Mem x empty := by
  simp [Mem, empty, Nat.zero_testBit]

theorem mem_adjoin (x a b : Nat) : Mem x (adjoin a b) ↔ Mem x a ∨ x = b := by
  unfold Mem adjoin
  rw [Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true]
  constructor
  · intro h
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr ((of_decide_eq_true h).symm)
  · intro h
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (decide_eq_true h.symm)

theorem ext {a b : Nat} (h : ∀ x, Mem x a ↔ Mem x b) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro x
  have hx := h x
  cases ha : a.testBit x <;> cases hb : b.testBit x <;>
    simp [Mem, ha, hb] at hx ⊢

theorem two_pow_le_of_mem {x y : Nat} (h : Mem x y) : 2 ^ x ≤ y := by
  apply Nat.le_of_testBit
  intro i hi
  rw [Nat.testBit_two_pow] at hi
  have hix : x = i := of_decide_eq_true hi
  subst hix
  exact h

theorem mem_lt {x y : Nat} (h : Mem x y) : x < y :=
  Nat.lt_of_lt_of_le Nat.lt_two_pow_self (two_pow_le_of_mem h)

/-- Set induction for the Ackermann-coded HF membership relation. -/
theorem induction (P : Nat → Prop)
    (step : ∀ a, (∀ x, Mem x a → P x) → P a) :
    ∀ a, P a := by
  intro a
  exact Nat.strongRecOn a (fun a ih =>
    step a (fun x hx => ih x (mem_lt hx)))

theorem eq_empty_iff_no_mem (a : Nat) : a = empty ↔ ∀ x, ¬ Mem x a := by
  constructor
  · intro h x
    rw [h]
    exact mem_empty x
  · intro h
    apply ext
    intro x
    constructor
    · exact fun hx => False.elim (h x hx)
    · exact fun hx => False.elim (mem_empty x hx)

theorem exists_mem_of_ne_empty {a : Nat} (ha : a ≠ empty) : ∃ x, Mem x a := by
  apply Classical.byContradiction
  intro h
  apply ha
  exact (eq_empty_iff_no_mem a).mpr (fun x hx => h ⟨x, hx⟩)

/-- If one Ackermann code is strictly below another, some bit is present in the
larger code and absent from the smaller one. -/
theorem exists_mem_not_mem_of_lt {low high : Nat} (hlt : low < high) :
    ∃ x, Mem x high ∧ ¬ Mem x low := by
  apply Classical.byContradiction
  intro h
  have hsubset : ∀ x, Mem x high → Mem x low := by
    intro x hx
    apply Classical.byContradiction
    intro hlow
    exact h ⟨x, hx, hlow⟩
  have hle : high ≤ low := by
    apply Nat.le_of_testBit
    intro x hx
    exact hsubset x hx
  omega

/-- Search for the largest bit below `n` that is present in `high` and absent
from `low`.  This is semantic data only; PA-side formulas and proofs consume
its specification through separate lemmas. -/
noncomputable def maxHighNotLowBelow (low high : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => by
      classical
      exact
        if Mem n high ∧ ¬ Mem n low then n
        else maxHighNotLowBelow low high n

theorem le_maxHighNotLowBelow_of_lt {x low high n : Nat}
    (hx : x < n) (hhigh : Mem x high) (hlow : ¬ Mem x low) :
    x ≤ maxHighNotLowBelow low high n := by
  classical
  induction n with
  | zero =>
      omega
  | succ n ih =>
      by_cases hn : Mem n high ∧ ¬ Mem n low
      · simp [maxHighNotLowBelow, hn]
        exact Nat.lt_succ_iff.mp hx
      · simp [maxHighNotLowBelow, hn]
        have hle : x ≤ n := Nat.lt_succ_iff.mp hx
        rcases Nat.lt_or_eq_of_le hle with hxlt | hxeq
        · exact ih hxlt
        · subst hxeq
          exact False.elim (hn ⟨hhigh, hlow⟩)

theorem maxHighNotLowBelow_spec_of_exists {low high n : Nat}
    (hex : ∃ x, x < n ∧ Mem x high ∧ ¬ Mem x low) :
    Mem (maxHighNotLowBelow low high n) high ∧
      ¬ Mem (maxHighNotLowBelow low high n) low := by
  classical
  induction n with
  | zero =>
      rcases hex with ⟨x, hx, _⟩
      omega
  | succ n ih =>
      by_cases hn : Mem n high ∧ ¬ Mem n low
      · simp [maxHighNotLowBelow, hn]
      · simp [maxHighNotLowBelow, hn]
        apply ih
        rcases hex with ⟨x, hx, hhigh, hlow⟩
        have hle : x ≤ n := Nat.lt_succ_iff.mp hx
        rcases Nat.lt_or_eq_of_le hle with hxlt | hxeq
        · exact ⟨x, hxlt, hhigh, hlow⟩
        · subst hxeq
          exact False.elim (hn ⟨hhigh, hlow⟩)

/-- Canonical semantic witness for `low < high`: the largest high-only bit
below `high`. -/
noncomputable def highNotLowWitness (low high : Nat) : Nat :=
  maxHighNotLowBelow low high high

theorem highNotLowWitness_spec_of_lt {low high : Nat} (hlt : low < high) :
    Mem (highNotLowWitness low high) high ∧
      ¬ Mem (highNotLowWitness low high) low := by
  rcases exists_mem_not_mem_of_lt hlt with ⟨x, hhigh, hlow⟩
  exact maxHighNotLowBelow_spec_of_exists
    (low := low) (high := high) (n := high)
    ⟨x, mem_lt hhigh, hhigh, hlow⟩

/-- Unequal Ackermann codes differ in at least one membership bit, in one
direction or the other. -/
theorem exists_mem_diff_of_ne {a b : Nat} (hne : a ≠ b) :
    (∃ x, Mem x a ∧ ¬ Mem x b) ∨
      (∃ x, Mem x b ∧ ¬ Mem x a) := by
  by_cases hab : a < b
  · exact Or.inr (exists_mem_not_mem_of_lt hab)
  · have hba : b < a := by omega
    exact Or.inl (exists_mem_not_mem_of_lt hba)

/-- Search for the largest member of `a` below `n`.  The default value at
`n = 0` is irrelevant; callers use the accompanying existence lemmas. -/
def maxMemberBelow (a : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => if a.testBit n then n else maxMemberBelow a n

theorem le_maxMemberBelow_of_lt {a y n : Nat}
    (hy : y < n) (hmem : Mem y a) : y ≤ maxMemberBelow a n := by
  induction n with
  | zero =>
      omega
  | succ n ih =>
      by_cases hn : Mem n a
      · have hbit : a.testBit n = true := hn
        simp [maxMemberBelow, hbit]
        exact Nat.lt_succ_iff.mp hy
      · have hbit : a.testBit n = false := by
          cases hb : a.testBit n <;> simp [Mem, hb] at hn ⊢
        simp [maxMemberBelow, hbit]
        have hyle : y ≤ n := Nat.lt_succ_iff.mp hy
        rcases Nat.lt_or_eq_of_le hyle with hylt | hyeq
        · exact ih hylt
        · subst hyeq
          exact False.elim (hn hmem)

theorem maxMemberBelow_mem_of_exists {a n : Nat}
    (hex : ∃ y, y < n ∧ Mem y a) : Mem (maxMemberBelow a n) a := by
  induction n with
  | zero =>
      rcases hex with ⟨y, hy, _⟩
      omega
  | succ n ih =>
      by_cases hn : Mem n a
      · have hbit : a.testBit n = true := hn
        simp [maxMemberBelow, hbit, Mem]
      · have hbit : a.testBit n = false := by
          cases hb : a.testBit n <;> simp [Mem, hb] at hn ⊢
        simp [maxMemberBelow, hbit]
        apply ih
        rcases hex with ⟨y, hy, hmem⟩
        have hyle : y ≤ n := Nat.lt_succ_iff.mp hy
        rcases Nat.lt_or_eq_of_le hyle with hylt | hyeq
        · exact ⟨y, hylt, hmem⟩
        · subst hyeq
          exact False.elim (hn hmem)

theorem exists_max_mem_of_ne_empty {a : Nat} (ha : a ≠ empty) :
    ∃ m, Mem m a ∧ ∀ y, Mem y a → y ≤ m := by
  obtain ⟨y, hy⟩ := exists_mem_of_ne_empty ha
  refine ⟨maxMemberBelow a a, ?_, ?_⟩
  · apply maxMemberBelow_mem_of_exists
    exact ⟨y, mem_lt hy, hy⟩
  · intro z hz
    exact le_maxMemberBelow_of_lt (mem_lt hz) hz

/-- The algebraic core shared by meta-level and first-order adjunction models.

It deliberately contains only extensionality, empty, and adjunction.  Induction
principles live in the stronger model bundles below, while finite-set and pair
constructions can be proved once against this reusable interface. -/
structure AdjunctionCore (α : Type u) where
  mem : α → α → Prop
  empty : α
  adjoin : α → α → α
  extensional :
    ∀ {a b}, (∀ x, mem x a ↔ mem x b) → a = b
  empty_spec :
    ∀ x, ¬ mem x empty
  adjoin_spec :
    ∀ x a b, mem x (adjoin a b) ↔ mem x a ∨ x = b

/-- A compact semantic bundle for the usual adjunction presentation of HF. -/
structure AdjunctionModel (α : Type) where
  mem : α → α → Prop
  empty : α
  adjoin : α → α → α
  extensional :
    ∀ {a b}, (∀ x, mem x a ↔ mem x b) → a = b
  empty_spec :
    ∀ x, ¬ mem x empty
  adjoin_spec :
    ∀ x a b, mem x (adjoin a b) ↔ mem x a ∨ x = b
  set_induction :
    ∀ P : α → Prop, (∀ a, (∀ x, mem x a → P x) → P a) → ∀ a, P a

/-- Forget the meta-level induction principle and retain the reusable
adjunction algebra. -/
abbrev AdjunctionModel.toCore {α : Type} (M : AdjunctionModel α) :
    AdjunctionCore α where
  mem := M.mem
  empty := M.empty
  adjoin := M.adjoin
  extensional := M.extensional
  empty_spec := M.empty_spec
  adjoin_spec := M.adjoin_spec

/-- The standard Ackermann-coded model of hereditary finite sets. -/
def standardModel : AdjunctionModel Nat where
  mem := Mem
  empty := empty
  adjoin := adjoin
  extensional := by
    intro a b h
    exact ext h
  empty_spec := mem_empty
  adjoin_spec := mem_adjoin
  set_induction := induction

/-- Membership in any adjunction model is irreflexive. -/
theorem AdjunctionModel.mem_irrefl {α : Type} (M : AdjunctionModel α) (a : α) :
    ¬ M.mem a a := by
  refine M.set_induction (fun x => ¬ M.mem x x) ?_ a
  intro x ih hxx
  exact ih x hxx hxx

/-! ## First-order HF axioms over the one-relation language -/

/-- A renaming used under two binders: keep the current object variable in
slot `0`, and move every parameter past the two locally-bound variables. -/
def rSkipParam : Nat → Nat
  | 0 => 0
  | n+1 => n+2

theorem Sat_rename_rSkipParam {α : Type u} {mem : α → α → Prop}
    (phi : Form) (e : Nat → α) (x y : α) :
    Sat mem (scons y (scons x e)) (rename rSkipParam phi) ↔
      Sat mem (scons y e) phi := by
  exact Sat_rename_ext phi rSkipParam _ _ (fun n => by cases n <;> rfl)

/-- In the finite-generation induction step, read `phi` at the old set slot
under the local binders for `a`, `b`, and `c = a ∪ {b}`. -/
def rAdjStepOld : Nat → Nat
  | 0 => 2
  | n+1 => n+3

/-- In the finite-generation induction step, read `phi` at the new adjunction
slot under the local binders for `a`, `b`, and `c = a ∪ {b}`. -/
def rAdjStepNew : Nat → Nat
  | 0 => 0
  | n+1 => n+3

theorem Sat_rename_rAdjStepOld {α : Type u} {mem : α → α → Prop}
    (phi : Form) (e : Nat → α) (a b c : α) :
    Sat mem (scons c (scons b (scons a e))) (rename rAdjStepOld phi) ↔
      Sat mem (scons a e) phi := by
  exact Sat_rename_ext phi rAdjStepOld _ _ (fun n => by cases n <;> rfl)

theorem Sat_rename_rAdjStepNew {α : Type u} {mem : α → α → Prop}
    (phi : Form) (e : Nat → α) (a b c : α) :
    Sat mem (scons c (scons b (scons a e))) (rename rAdjStepNew phi) ↔
      Sat mem (scons c e) phi := by
  exact Sat_rename_ext phi rAdjStepNew _ _ (fun n => by cases n <;> rfl)

/-- Under the local binders for a subset witness and its candidate element,
read a predicate at the candidate element while preserving the old parameters. -/
def rSepParam : Nat → Nat
  | 0 => 0
  | n+1 => n+2

theorem Sat_rename_rSepParam {α : Type u} {mem : α → α → Prop}
    (psi : Form) (e : Nat → α) (s x : α) :
    Sat mem (scons x (scons s e)) (rename rSepParam psi) ↔
      Sat mem (scons x e) psi := by
  exact Sat_rename_ext psi rSepParam _ _ (fun n => by cases n <;> rfl)

/-- The first-order empty-set axiom: some set has no elements. -/
def HF_empty_form : Form :=
  fEx (fAll (fImp (fMem 0 1) fBot))

/-- The first-order extensionality axiom. -/
def HF_extensionality_form : Form :=
  fAll (fAll
    (fImp
      (fAll (fIff (fMem 0 2) (fMem 0 1)))
      (fEq 1 0)))

/-- The first-order adjunction axiom:
for all `a b`, there is `c = a ∪ {b}`. -/
def HF_adjoin_form : Form :=
  fAll (fAll (fEx (fAll
    (fIff (fMem 0 1) (fOr (fMem 0 3) (fEq 0 2))))))

/-- Formula macro: slot `i` is empty. -/
def HF_emptyAt (i : Nat) : Form :=
  fAll (fImp (fMem 0 (i+1)) fBot)

theorem HF_emptyAt_spec {α : Type u} {mem : α → α → Prop}
    (e : Nat → α) (i : Nat) :
    Sat mem e (HF_emptyAt i) ↔ ∀ x, ¬ mem x (e i) :=
  Iff.rfl

namespace AdjunctionCore

theorem HF_emptyAt_empty {α : Type u} (M : AdjunctionCore α)
    (e : Nat → α) (i : Nat) :
    Sat M.mem e (HF_emptyAt i) ↔ e i = M.empty := by
  constructor
  · intro h
    apply M.extensional
    intro x
    constructor
    · exact fun hx => False.elim (h x hx)
    · exact fun hx => False.elim (M.empty_spec x hx)
  · intro h x hx
    have hx' : M.mem x (e i) := by
      simpa [Sat, scons] using hx
    rw [h] at hx'
    exact M.empty_spec x hx'

end AdjunctionCore

theorem HF_emptyAt_empty {α : Type} (M : AdjunctionModel α)
    (e : Nat → α) (i : Nat) :
    Sat M.mem e (HF_emptyAt i) ↔ e i = M.empty :=
  AdjunctionCore.HF_emptyAt_empty M.toCore e i

/-- Formula macro: slot `c` is the adjunction `a ∪ {b}`. -/
def HF_adjoinAt (c a b : Nat) : Form :=
  fAll (fIff (fMem 0 (c+1)) (fOr (fMem 0 (a+1)) (fEq 0 (b+1))))

theorem HF_adjoinAt_spec {α : Type u} {mem : α → α → Prop}
    (e : Nat → α) (c a b : Nat) :
    Sat mem e (HF_adjoinAt c a b) ↔
      ∀ x, mem x (e c) ↔ mem x (e a) ∨ x = e b := by
  constructor
  · intro h x
    exact (Sat_fIff (mem := mem)).mp (h x)
  · intro h x
    exact (Sat_fIff (mem := mem)).mpr (h x)

namespace AdjunctionCore

theorem HF_adjoinAt_adjoin {α : Type u} (M : AdjunctionCore α)
    (e : Nat → α) (c a b : Nat) :
    Sat M.mem e (HF_adjoinAt c a b) ↔ e c = M.adjoin (e a) (e b) := by
  constructor
  · intro h
    apply M.extensional
    intro x
    rw [(HF_adjoinAt_spec e c a b).mp h x, M.adjoin_spec x (e a) (e b)]
  · intro h
    apply (HF_adjoinAt_spec e c a b).mpr
    intro x
    rw [h, M.adjoin_spec x (e a) (e b)]

end AdjunctionCore

theorem HF_adjoinAt_adjoin {α : Type} (M : AdjunctionModel α)
    (e : Nat → α) (c a b : Nat) :
    Sat M.mem e (HF_adjoinAt c a b) ↔ e c = M.adjoin (e a) (e b) :=
  AdjunctionCore.HF_adjoinAt_adjoin M.toCore e c a b

/-- Formula macro: slot `s` is the finite-ordinal successor of slot `a`,
that is, `s = a ∪ {a}`. -/
def HF_succAt (s a : Nat) : Form := HF_adjoinAt s a a

theorem AdjunctionCore.HF_succAt_spec {α : Type u} (M : AdjunctionCore α)
    (e : Nat → α) (s a : Nat) :
    Sat M.mem e (HF_succAt s a) ↔ e s = M.adjoin (e a) (e a) :=
  HF_adjoinAt_adjoin M e s a a

theorem HF_succAt_spec {α : Type} (M : AdjunctionModel α)
    (e : Nat → α) (s a : Nat) :
    Sat M.mem e (HF_succAt s a) ↔ e s = M.adjoin (e a) (e a) :=
  AdjunctionCore.HF_succAt_spec M.toCore e s a

/-! ### HF-internal pair coding -/

namespace AdjunctionCore

/-- Singleton in any extensional empty-and-adjunction algebra. -/
def single {α : Type u} (M : AdjunctionCore α) (a : α) : α :=
  M.adjoin M.empty a

theorem single_spec {α : Type u} (M : AdjunctionCore α) (a x : α) :
    M.mem x (single M a) ↔ x = a := by
  rw [single, M.adjoin_spec]
  constructor
  · intro h
    rcases h with h | h
    · exact False.elim (M.empty_spec x h)
    · exact h
  · intro h
    exact Or.inr h

/-- Unordered pair inside any adjunction-style HF model. -/
def upair {α : Type u} (M : AdjunctionCore α) (a b : α) : α :=
  M.adjoin (single M a) b

theorem upair_spec {α : Type u} (M : AdjunctionCore α) (a b x : α) :
    M.mem x (upair M a b) ↔ x = a ∨ x = b := by
  rw [upair, M.adjoin_spec, single_spec]

/-- Kuratowski ordered pair inside any adjunction-style HF model. -/
def kpair {α : Type u} (M : AdjunctionCore α) (a b : α) : α :=
  upair M (single M a) (upair M a b)

theorem kpair_mem {α : Type u} (M : AdjunctionCore α) (a b q : α) :
    M.mem q (kpair M a b) ↔ q = single M a ∨ q = upair M a b := by
  unfold kpair
  rw [upair_spec]

theorem single_injective {α : Type u} (M : AdjunctionCore α) {a b : α}
    (h : single M a = single M b) : a = b := by
  have ha : M.mem a (single M a) := (single_spec M a a).mpr rfl
  rw [h] at ha
  exact (single_spec M b a).mp ha

theorem upair_eq_single {α : Type u} (M : AdjunctionCore α) {a b c : α}
    (h : upair M a b = single M c) : a = c ∧ b = c := by
  constructor
  · have ha : M.mem a (upair M a b) := (upair_spec M a b a).mpr (Or.inl rfl)
    rw [h] at ha
    exact (single_spec M c a).mp ha
  · have hb : M.mem b (upair M a b) := (upair_spec M a b b).mpr (Or.inr rfl)
    rw [h] at hb
    exact (single_spec M c b).mp hb

theorem kpair_injective {α : Type u} (M : AdjunctionCore α) {a b c d : α}
    (h : kpair M a b = kpair M c d) : a = c ∧ b = d := by
  have hac : a = c := by
    have hs : M.mem (single M a) (kpair M a b) :=
      (kpair_mem M a b (single M a)).mpr (Or.inl rfl)
    rw [h] at hs
    rcases (kpair_mem M c d (single M a)).mp hs with hs | hs
    · exact single_injective M hs
    · exact ((upair_eq_single M hs.symm).1).symm
  subst c
  constructor
  · rfl
  · have h1 : M.mem (upair M a b) (kpair M a b) :=
      (kpair_mem M a b (upair M a b)).mpr (Or.inr rfl)
    rw [h] at h1
    rcases (kpair_mem M a d (upair M a b)).mp h1 with h1 | h1
    · have hba : b = a := (upair_eq_single M h1).2
      have h2 : M.mem (upair M a d) (kpair M a d) :=
        (kpair_mem M a d (upair M a d)).mpr (Or.inr rfl)
      rw [← h] at h2
      rcases (kpair_mem M a b (upair M a d)).mp h2 with h2 | h2
      · have hda : d = a := (upair_eq_single M h2).2
        rw [hba, hda]
      · have hd : M.mem d (upair M a d) := (upair_spec M a d d).mpr (Or.inr rfl)
        rw [h2] at hd
        rcases (upair_spec M a b d).mp hd with hd | hd
        · rw [hba, hd]
        · exact hd.symm
    · have hb : M.mem b (upair M a b) := (upair_spec M a b b).mpr (Or.inr rfl)
      rw [h1] at hb
      rcases (upair_spec M a d b).mp hb with hb | hb
      · have hd : M.mem d (upair M a d) := (upair_spec M a d d).mpr (Or.inr rfl)
        rw [← h1] at hd
        rcases (upair_spec M a b d).mp hd with hd | hd
        · rw [hb, hd]
        · exact hd.symm
      · exact hb

end AdjunctionCore

/-- Backward-compatible singleton operation for a meta-level adjunction model. -/
abbrev single {α : Type} (M : AdjunctionModel α) (a : α) : α :=
  AdjunctionCore.single M.toCore a

theorem single_spec {α : Type} (M : AdjunctionModel α) (a x : α) :
    M.mem x (single M a) ↔ x = a :=
  AdjunctionCore.single_spec M.toCore a x

abbrev upair {α : Type} (M : AdjunctionModel α) (a b : α) : α :=
  AdjunctionCore.upair M.toCore a b

theorem upair_spec {α : Type} (M : AdjunctionModel α) (a b x : α) :
    M.mem x (upair M a b) ↔ x = a ∨ x = b :=
  AdjunctionCore.upair_spec M.toCore a b x

abbrev kpair {α : Type} (M : AdjunctionModel α) (a b : α) : α :=
  AdjunctionCore.kpair M.toCore a b

theorem kpair_mem {α : Type} (M : AdjunctionModel α) (a b q : α) :
    M.mem q (kpair M a b) ↔ q = single M a ∨ q = upair M a b :=
  AdjunctionCore.kpair_mem M.toCore a b q

theorem single_injective {α : Type} (M : AdjunctionModel α) {a b : α}
    (h : single M a = single M b) : a = b :=
  AdjunctionCore.single_injective M.toCore h

theorem upair_eq_single {α : Type} (M : AdjunctionModel α) {a b c : α}
    (h : upair M a b = single M c) : a = c ∧ b = c :=
  AdjunctionCore.upair_eq_single M.toCore h

theorem kpair_injective {α : Type} (M : AdjunctionModel α) {a b c d : α}
    (h : kpair M a b = kpair M c d) : a = c ∧ b = d :=
  AdjunctionCore.kpair_injective M.toCore h

/-- Formula macro: slot `i` is the singleton of slot `j`. -/
def HF_singleAt (i j : Nat) : Form :=
  fAll (fIff (fMem 0 (i+1)) (fEq 0 (j+1)))

theorem AdjunctionCore.HF_singleAt_spec {α : Type u} (M : AdjunctionCore α)
    (e : Nat → α) (i j : Nat) :
    Sat M.mem e (HF_singleAt i j) ↔ e i = M.single (e j) := by
  show (∀ x, (M.mem x (e i) → x = e j) ∧ (x = e j → M.mem x (e i))) ↔ _
  constructor
  · intro h
    apply M.extensional
    intro x
    rw [M.single_spec (e j) x]
    exact ⟨(h x).1, (h x).2⟩
  · intro h x
    rw [h, M.single_spec (e j) x]
    exact ⟨id, id⟩

theorem HF_singleAt_spec {α : Type} (M : AdjunctionModel α)
    (e : Nat → α) (i j : Nat) :
    Sat M.mem e (HF_singleAt i j) ↔ e i = single M (e j) :=
  M.toCore.HF_singleAt_spec e i j

/-- Formula macro: slot `i` is the unordered pair of slots `j` and `k`. -/
def HF_upairAt (i j k : Nat) : Form :=
  fAll (fIff (fMem 0 (i+1)) (fOr (fEq 0 (j+1)) (fEq 0 (k+1))))

theorem AdjunctionCore.HF_upairAt_spec {α : Type u} (M : AdjunctionCore α)
    (e : Nat → α) (i j k : Nat) :
    Sat M.mem e (HF_upairAt i j k) ↔ e i = M.upair (e j) (e k) := by
  show (∀ x, (M.mem x (e i) → (x = e j ∨ x = e k)) ∧
             ((x = e j ∨ x = e k) → M.mem x (e i))) ↔ _
  constructor
  · intro h
    apply M.extensional
    intro x
    rw [M.upair_spec (e j) (e k) x]
    exact ⟨(h x).1, (h x).2⟩
  · intro h x
    rw [h, M.upair_spec (e j) (e k) x]
    exact ⟨id, id⟩

theorem HF_upairAt_spec {α : Type} (M : AdjunctionModel α)
    (e : Nat → α) (i j k : Nat) :
    Sat M.mem e (HF_upairAt i j k) ↔ e i = upair M (e j) (e k) :=
  M.toCore.HF_upairAt_spec e i j k

/-- Formula macro: slot `p` is the Kuratowski ordered pair of slots `a` and
`b`. -/
def HF_kpairAt (p a b : Nat) : Form :=
  fAll (fIff (fMem 0 (p+1))
    (fOr (HF_singleAt 0 (a+1)) (HF_upairAt 0 (a+1) (b+1))))

theorem AdjunctionCore.HF_kpairAt_spec {α : Type u} (M : AdjunctionCore α)
    (e : Nat → α) (p a b : Nat) :
    Sat M.mem e (HF_kpairAt p a b) ↔ e p = M.kpair (e a) (e b) := by
  have hq : ∀ q : α,
      (Sat M.mem (scons q e) (HF_singleAt 0 (a+1)) ∨
       Sat M.mem (scons q e) (HF_upairAt 0 (a+1) (b+1)))
        ↔ (q = M.single (e a) ∨ q = M.upair (e a) (e b)) := by
    intro q
    rw [M.HF_singleAt_spec (scons q e) 0 (a+1),
        M.HF_upairAt_spec (scons q e) 0 (a+1) (b+1)]
    exact Iff.rfl
  constructor
  · intro h
    apply M.extensional
    intro q
    rw [M.kpair_mem (e a) (e b) q, ← hq q]
    exact ⟨(h q).1, (h q).2⟩
  · intro h q
    constructor
    · intro hq'
      have hqmem : M.mem q (e p) := hq'
      rw [h] at hqmem
      exact (hq q).mpr ((M.kpair_mem (e a) (e b) q).mp hqmem)
    · intro hs
      show M.mem q (e p)
      rw [h]
      exact (M.kpair_mem (e a) (e b) q).mpr ((hq q).mp hs)

theorem HF_kpairAt_spec {α : Type} (M : AdjunctionModel α)
    (e : Nat → α) (p a b : Nat) :
    Sat M.mem e (HF_kpairAt p a b) ↔ e p = kpair M (e a) (e b) :=
  M.toCore.HF_kpairAt_spec e p a b

/-- Formula macro: the ordered pair of slots `a` and `b` is a member of slot
`r`. -/
def HF_pairMemAt (a b r : Nat) : Form :=
  fEx (fAnd (HF_kpairAt 0 (a+1) (b+1)) (fMem 0 (r+1)))

theorem AdjunctionCore.HF_pairMemAt_spec {α : Type u} (M : AdjunctionCore α)
    (e : Nat → α) (a b r : Nat) :
    Sat M.mem e (HF_pairMemAt a b r) ↔
      M.mem (M.kpair (e a) (e b)) (e r) := by
  constructor
  · intro h
    rcases h with ⟨p, hp, hmem⟩
    have hp' : p = M.kpair (e a) (e b) :=
      (M.HF_kpairAt_spec (scons p e) 0 (a+1) (b+1)).mp hp
    have hmem' : M.mem p (e r) := hmem
    rwa [hp'] at hmem'
  · intro h
    refine ⟨M.kpair (e a) (e b), ?_, ?_⟩
    · exact (M.HF_kpairAt_spec (scons (M.kpair (e a) (e b)) e)
        0 (a+1) (b+1)).mpr rfl
    · exact h

theorem HF_pairMemAt_spec {α : Type} (M : AdjunctionModel α)
    (e : Nat → α) (a b r : Nat) :
    Sat M.mem e (HF_pairMemAt a b r) ↔
      M.mem (kpair M (e a) (e b)) (e r) :=
  M.toCore.HF_pairMemAt_spec e a b r

/-- A set of ordered pairs is single-valued in its second component. -/
def AdjunctionCore.PairFunctional {α : Type u} (M : AdjunctionCore α)
    (f : α) : Prop :=
  ∀ k y y', M.mem (M.kpair k y) f → M.mem (M.kpair k y') f → y = y'

/-- Every first component of a pair in `f` is a member of `m ∪ {m}`. -/
def AdjunctionCore.PairKeysBelowSucc {α : Type u} (M : AdjunctionCore α)
    (f m : α) : Prop :=
  ∀ k y, M.mem (M.kpair k y) f → M.mem k m ∨ k = m

/-- Every element of `m ∪ {m}` appears as the first component of some pair in
`f`. -/
def AdjunctionCore.PairTotalBelowSucc {α : Type u} (M : AdjunctionCore α)
    (f m : α) : Prop :=
  ∀ k, M.mem k m ∨ k = m → ∃ y, M.mem (M.kpair k y) f

/-- Successor-recursion step for a pair set `f` on the proper members of
`m`: if `f(k)=t`, then `f(k+1)=t+1`. -/
def AdjunctionCore.PairSuccStep {α : Type u} (M : AdjunctionCore α)
    (f m : α) : Prop :=
  ∀ k t y,
    M.mem k m →
    M.mem (M.kpair k t) f →
    M.mem (M.kpair (M.adjoin k k) y) f →
    y = M.adjoin t t

/-- Compatibility names specialized to a meta-level adjunction model. -/
abbrev PairFunctional {α : Type} (M : AdjunctionModel α) (f : α) : Prop :=
  M.toCore.PairFunctional f

abbrev PairKeysBelowSucc {α : Type} (M : AdjunctionModel α) (f m : α) : Prop :=
  M.toCore.PairKeysBelowSucc f m

abbrev PairTotalBelowSucc {α : Type} (M : AdjunctionModel α) (f m : α) : Prop :=
  M.toCore.PairTotalBelowSucc f m

abbrev PairSuccStep {α : Type} (M : AdjunctionModel α) (f m : α) : Prop :=
  M.toCore.PairSuccStep f m

/-- Formula macro: slot `f` is a single-valued relation represented by
Kuratowski pairs. -/
def HF_pairFunctionalAt (f : Nat) : Form :=
  fAll (fAll (fAll
    (fImp
      (fAnd (HF_pairMemAt 2 1 (f+3)) (HF_pairMemAt 2 0 (f+3)))
      (fEq 1 0))))

theorem AdjunctionCore.HF_pairFunctionalAt_spec {α : Type u}
    (M : AdjunctionCore α)
    (e : Nat → α) (f : Nat) :
    Sat M.mem e (HF_pairFunctionalAt f) ↔ M.PairFunctional (e f) := by
  constructor
  · intro h k y y' hky hky'
    exact h k y y'
      ⟨(M.HF_pairMemAt_spec (scons y' (scons y (scons k e))) 2 1 (f+3)).mpr hky,
       (M.HF_pairMemAt_spec (scons y' (scons y (scons k e))) 2 0 (f+3)).mpr hky'⟩
  · intro h k y y' hpairs
    exact h k y y'
      ((M.HF_pairMemAt_spec (scons y' (scons y (scons k e))) 2 1 (f+3)).mp hpairs.1)
      ((M.HF_pairMemAt_spec (scons y' (scons y (scons k e))) 2 0 (f+3)).mp hpairs.2)

theorem HF_pairFunctionalAt_spec {α : Type} (M : AdjunctionModel α)
    (e : Nat → α) (f : Nat) :
    Sat M.mem e (HF_pairFunctionalAt f) ↔ PairFunctional M (e f) :=
  M.toCore.HF_pairFunctionalAt_spec e f

/-- Formula macro: every key in relation slot `f` is in `m ∪ {m}`. -/
def HF_pairKeysBelowSuccAt (f m : Nat) : Form :=
  fAll (fAll
    (fImp
      (HF_pairMemAt 1 0 (f+2))
      (fOr (fMem 1 (m+2)) (fEq 1 (m+2)))))

theorem AdjunctionCore.HF_pairKeysBelowSuccAt_spec {α : Type u}
    (M : AdjunctionCore α)
    (e : Nat → α) (f m : Nat) :
    Sat M.mem e (HF_pairKeysBelowSuccAt f m) ↔
      M.PairKeysBelowSucc (e f) (e m) := by
  constructor
  · intro h k y hky
    exact h k y
      ((M.HF_pairMemAt_spec (scons y (scons k e)) 1 0 (f+2)).mpr hky)
  · intro h k y hky
    exact h k y
      ((M.HF_pairMemAt_spec (scons y (scons k e)) 1 0 (f+2)).mp hky)

theorem HF_pairKeysBelowSuccAt_spec {α : Type} (M : AdjunctionModel α)
    (e : Nat → α) (f m : Nat) :
    Sat M.mem e (HF_pairKeysBelowSuccAt f m) ↔
      PairKeysBelowSucc M (e f) (e m) :=
  M.toCore.HF_pairKeysBelowSuccAt_spec e f m

/-- Formula macro: every key in `m ∪ {m}` occurs in relation slot `f`. -/
def HF_pairTotalBelowSuccAt (f m : Nat) : Form :=
  fAll
    (fImp
      (fOr (fMem 0 (m+1)) (fEq 0 (m+1)))
      (fEx (HF_pairMemAt 1 0 (f+2))))

theorem AdjunctionCore.HF_pairTotalBelowSuccAt_spec {α : Type u}
    (M : AdjunctionCore α)
    (e : Nat → α) (f m : Nat) :
    Sat M.mem e (HF_pairTotalBelowSuccAt f m) ↔
      M.PairTotalBelowSucc (e f) (e m) := by
  constructor
  · intro h k hk
    rcases h k hk with ⟨y, hy⟩
    exact ⟨y, (M.HF_pairMemAt_spec (scons y (scons k e)) 1 0 (f+2)).mp hy⟩
  · intro h k hk
    rcases h k hk with ⟨y, hy⟩
    exact ⟨y, (M.HF_pairMemAt_spec (scons y (scons k e)) 1 0 (f+2)).mpr hy⟩

theorem HF_pairTotalBelowSuccAt_spec {α : Type} (M : AdjunctionModel α)
    (e : Nat → α) (f m : Nat) :
    Sat M.mem e (HF_pairTotalBelowSuccAt f m) ↔
      PairTotalBelowSucc M (e f) (e m) :=
  M.toCore.HF_pairTotalBelowSuccAt_spec e f m

/-- Formula macro: the represented relation advances by ordinal successor at
successive keys below `m`. -/
def HF_pairSuccStepAt (f m : Nat) : Form :=
  fAll (fAll (fAll
    (fImp
      (fMem 2 (m+3))
      (fImp
        (HF_pairMemAt 2 1 (f+3))
        (fAll
          (fImp
            (HF_succAt 0 3)
            (fImp
              (HF_pairMemAt 0 1 (f+4))
              (HF_succAt 1 2))))))))

theorem AdjunctionCore.HF_pairSuccStepAt_spec {α : Type u}
    (M : AdjunctionCore α)
    (e : Nat → α) (f m : Nat) :
    Sat M.mem e (HF_pairSuccStepAt f m) ↔ M.PairSuccStep (e f) (e m) := by
  constructor
  · intro h k t y hkm hkt hsy
    have hs := h k t y hkm
      ((M.HF_pairMemAt_spec (scons y (scons t (scons k e))) 2 1 (f+3)).mpr hkt)
      (M.adjoin k k)
      ((M.HF_succAt_spec
        (scons (M.adjoin k k) (scons y (scons t (scons k e)))) 0 3).mpr rfl)
      ((M.HF_pairMemAt_spec
        (scons (M.adjoin k k) (scons y (scons t (scons k e)))) 0 1 (f+4)).mpr hsy)
    exact (M.HF_succAt_spec
      (scons (M.adjoin k k) (scons y (scons t (scons k e)))) 1 2).mp hs
  · intro h k t y hkm hkt sk hsk hsky
    have hsk' : sk = M.adjoin k k :=
      (M.HF_succAt_spec (scons sk (scons y (scons t (scons k e)))) 0 3).mp hsk
    have hsky' : M.mem (M.kpair (M.adjoin k k) y) (e f) := by
      have hpair := (M.HF_pairMemAt_spec
        (scons sk (scons y (scons t (scons k e)))) 0 1 (f+4)).mp hsky
      rwa [hsk'] at hpair
    apply (M.HF_succAt_spec
      (scons sk (scons y (scons t (scons k e)))) 1 2).mpr
    exact h k t y hkm
      ((M.HF_pairMemAt_spec (scons y (scons t (scons k e))) 2 1 (f+3)).mp hkt)
      hsky'

theorem HF_pairSuccStepAt_spec {α : Type} (M : AdjunctionModel α)
    (e : Nat → α) (f m : Nat) :
    Sat M.mem e (HF_pairSuccStepAt f m) ↔ PairSuccStep M (e f) (e m) :=
  M.toCore.HF_pairSuccStepAt_spec e f m

/-- The base clause for successor recursion: `f(0)=s`. -/
def HF_pairBaseAt (f s : Nat) : Form :=
  fEx (fAnd (HF_emptyAt 0) (HF_pairMemAt 0 (s+1) (f+1)))

theorem AdjunctionCore.HF_pairBaseAt_spec {α : Type u} (M : AdjunctionCore α)
    (e : Nat → α) (f s : Nat) :
    Sat M.mem e (HF_pairBaseAt f s) ↔
      M.mem (M.kpair M.empty (e s)) (e f) := by
  constructor
  · intro h
    rcases h with ⟨z, hz, hpair⟩
    have hz' : z = M.empty := (M.HF_emptyAt_empty (scons z e) 0).mp hz
    have hpair' := (M.HF_pairMemAt_spec (scons z e) 0 (s+1) (f+1)).mp hpair
    rwa [hz'] at hpair'
  · intro h
    refine ⟨M.empty, ?_, ?_⟩
    · exact (M.HF_emptyAt_empty (scons M.empty e) 0).mpr rfl
    · exact (M.HF_pairMemAt_spec (scons M.empty e) 0 (s+1) (f+1)).mpr h

theorem HF_pairBaseAt_spec {α : Type} (M : AdjunctionModel α)
    (e : Nat → α) (f s : Nat) :
    Sat M.mem e (HF_pairBaseAt f s) ↔
      M.mem (kpair M M.empty (e s)) (e f) :=
  M.toCore.HF_pairBaseAt_spec e f s

/-- The base clause for zero-start recursion: `f(0)=0`. -/
def HF_pairZeroBaseAt (f : Nat) : Form :=
  fEx (fAnd (HF_emptyAt 0) (HF_pairMemAt 0 0 (f+1)))

theorem AdjunctionCore.HF_pairZeroBaseAt_spec {α : Type u}
    (M : AdjunctionCore α)
    (e : Nat → α) (f : Nat) :
    Sat M.mem e (HF_pairZeroBaseAt f) ↔
      M.mem (M.kpair M.empty M.empty) (e f) := by
  constructor
  · intro h
    rcases h with ⟨z, hz, hpair⟩
    have hz' : z = M.empty := (M.HF_emptyAt_empty (scons z e) 0).mp hz
    have hpair' := (M.HF_pairMemAt_spec (scons z e) 0 0 (f+1)).mp hpair
    rwa [hz'] at hpair'
  · intro h
    refine ⟨M.empty, ?_, ?_⟩
    · exact (M.HF_emptyAt_empty (scons M.empty e) 0).mpr rfl
    · exact (M.HF_pairMemAt_spec (scons M.empty e) 0 0 (f+1)).mpr h

theorem HF_pairZeroBaseAt_spec {α : Type} (M : AdjunctionModel α)
    (e : Nat → α) (f : Nat) :
    Sat M.mem e (HF_pairZeroBaseAt f) ↔
      M.mem (kpair M M.empty M.empty) (e f) :=
  M.toCore.HF_pairZeroBaseAt_spec e f

/-- Semantic package for a finite successor-recursion trace from `s` through
the segment `m ∪ {m}`. -/
def AdjunctionCore.SuccRecApprox {α : Type u} (M : AdjunctionCore α)
    (s f m : α) : Prop :=
  M.PairFunctional f ∧
  M.PairKeysBelowSucc f m ∧
  M.mem (M.kpair M.empty s) f ∧
  M.PairTotalBelowSucc f m ∧
  M.PairSuccStep f m

abbrev SuccRecApprox {α : Type} (M : AdjunctionModel α) (s f m : α) : Prop :=
  M.toCore.SuccRecApprox s f m

/-- Formula macro for `SuccRecApprox`: slot `f` is the graph of successor
iteration starting at slot `s`, defined on keys up to slot `m`. -/
def HF_succRecApproxAt (f s m : Nat) : Form :=
  fAnd (HF_pairFunctionalAt f)
    (fAnd (HF_pairKeysBelowSuccAt f m)
      (fAnd (HF_pairBaseAt f s)
        (fAnd (HF_pairTotalBelowSuccAt f m)
          (HF_pairSuccStepAt f m))))

/-- Formula macro: successor-recursion from slot `s` is total through slot `m`.
It existentially packages a recursion graph and its value at key `m`. -/
def HF_succRecTotalAt (s m : Nat) : Form :=
  fEx (fEx (fAnd
    (HF_succRecApproxAt 1 (s+2) (m+2))
    (HF_pairMemAt (m+2) 0 1)))

theorem AdjunctionCore.HF_succRecApproxAt_spec {α : Type u}
    (M : AdjunctionCore α)
    (e : Nat → α) (f s m : Nat) :
    Sat M.mem e (HF_succRecApproxAt f s m) ↔
      M.SuccRecApprox (e s) (e f) (e m) := by
  change
    (Sat M.mem e (HF_pairFunctionalAt f) ∧
      (Sat M.mem e (HF_pairKeysBelowSuccAt f m) ∧
        (Sat M.mem e (HF_pairBaseAt f s) ∧
          (Sat M.mem e (HF_pairTotalBelowSuccAt f m) ∧
            Sat M.mem e (HF_pairSuccStepAt f m))))) ↔
      M.PairFunctional (e f) ∧
        M.PairKeysBelowSucc (e f) (e m) ∧
          M.mem (M.kpair M.empty (e s)) (e f) ∧
            M.PairTotalBelowSucc (e f) (e m) ∧
              M.PairSuccStep (e f) (e m)
  rw [
    M.HF_pairFunctionalAt_spec e f,
    M.HF_pairKeysBelowSuccAt_spec e f m,
    M.HF_pairBaseAt_spec e f s,
    M.HF_pairTotalBelowSuccAt_spec e f m,
    M.HF_pairSuccStepAt_spec e f m]

theorem HF_succRecApproxAt_spec {α : Type} (M : AdjunctionModel α)
    (e : Nat → α) (f s m : Nat) :
    Sat M.mem e (HF_succRecApproxAt f s m) ↔
      SuccRecApprox M (e s) (e f) (e m) :=
  M.toCore.HF_succRecApproxAt_spec e f s m

/-- Formula macro: slot `a` is a subset of slot `b`. -/
def HF_subsetAt (a b : Nat) : Form :=
  fAll (fImp (fMem 0 (a+1)) (fMem 0 (b+1)))

theorem HF_subsetAt_spec {α : Type u} {mem : α → α → Prop}
    (e : Nat → α) (a b : Nat) :
    Sat mem e (HF_subsetAt a b) ↔ ∀ x, mem x (e a) → mem x (e b) :=
  Iff.rfl

/-- Formula macro: there is a subset of slot `a` containing exactly the
members satisfying `psi`.  The predicate `psi` reads its candidate element in
slot `0` and its old parameters from slots `1,2,...`; the subset witness is a
local implementation detail, skipped by `rSepParam`. -/
def HF_sepByAt (psi : Form) (a : Nat) : Form :=
  fEx (fAll
    (fIff
      (fMem 0 1)
      (fAnd (fMem 0 (a+2)) (rename rSepParam psi))))

theorem HF_sepByAt_spec {α : Type u} {mem : α → α → Prop}
    (psi : Form) (e : Nat → α) (a : Nat) :
    Sat mem e (HF_sepByAt psi a) ↔
      ∃ s, ∀ x, mem x s ↔ mem x (e a) ∧ Sat mem (scons x e) psi := by
  constructor
  · intro h
    rcases h with ⟨s, hs⟩
    refine ⟨s, fun x => ?_⟩
    have hx := (Sat_fIff (mem := mem)
      (e := scons x (scons s e))).mp (hs x)
    constructor
    · intro hxs
      have hbody := hx.mp hxs
      exact ⟨hbody.1, (Sat_rename_rSepParam psi e s x).mp hbody.2⟩
    · intro hxbody
      exact hx.mpr ⟨hxbody.1, (Sat_rename_rSepParam psi e s x).mpr hxbody.2⟩
  · intro h
    rcases h with ⟨s, hs⟩
    refine ⟨s, fun x => ?_⟩
    apply (Sat_fIff (mem := mem) (e := scons x (scons s e))).mpr
    constructor
    · intro hxs
      exact ⟨(hs x).mp hxs |>.1,
        (Sat_rename_rSepParam psi e s x).mpr ((hs x).mp hxs |>.2)⟩
    · intro hbody
      exact (hs x).mpr
        ⟨hbody.1, (Sat_rename_rSepParam psi e s x).mp hbody.2⟩

/-- Formula macro: slots `a` and `b` have a binary union. -/
def HF_binUnionAt (a b : Nat) : Form :=
  fEx (fAll
    (fIff
      (fMem 0 1)
      (fOr (fMem 0 (a+2)) (fMem 0 (b+2)))))

theorem HF_binUnionAt_spec {α : Type u} {mem : α → α → Prop}
    (e : Nat → α) (a b : Nat) :
    Sat mem e (HF_binUnionAt a b) ↔
      ∃ u, ∀ x, mem x u ↔ mem x (e a) ∨ mem x (e b) := by
  constructor
  · intro h
    rcases h with ⟨u, hu⟩
    refine ⟨u, fun x => ?_⟩
    exact (Sat_fIff (mem := mem) (e := scons x (scons u e))).mp (hu x)
  · intro h
    rcases h with ⟨u, hu⟩
    refine ⟨u, fun x => ?_⟩
    exact (Sat_fIff (mem := mem) (e := scons x (scons u e))).mpr (hu x)

/-- Formula macro: slot `a` has an object union. -/
def HF_unionAt (a : Nat) : Form :=
  fEx (fAll
    (fIff
      (fMem 0 1)
      (fEx (fAnd (fMem 0 (a+3)) (fMem 1 0)))))

theorem HF_unionAt_spec {α : Type u} {mem : α → α → Prop}
    (e : Nat → α) (a : Nat) :
    Sat mem e (HF_unionAt a) ↔
      ∃ u, ∀ x, mem x u ↔ ∃ v, mem v (e a) ∧ mem x v := by
  constructor
  · intro h
    rcases h with ⟨u, hu⟩
    refine ⟨u, fun x => ?_⟩
    exact (Sat_fIff (mem := mem) (e := scons x (scons u e))).mp (hu x)
  · intro h
    rcases h with ⟨u, hu⟩
    refine ⟨u, fun x => ?_⟩
    exact (Sat_fIff (mem := mem) (e := scons x (scons u e))).mpr (hu x)

/-- Semantic reading of transitivity for one object. -/
def TransitiveObj {α : Type u} (mem : α → α → Prop) (a : α) : Prop :=
  ∀ y, mem y a → ∀ x, mem x y → mem x a

/-- Formula macro: slot `a` is transitive. -/
def HF_transitiveAt (a : Nat) : Form :=
  fAll (fImp (fMem 0 (a+1))
    (fAll (fImp (fMem 0 1) (fMem 0 (a+2)))))

theorem HF_transitiveAt_spec {α : Type u} {mem : α → α → Prop}
    (e : Nat → α) (a : Nat) :
    Sat mem e (HF_transitiveAt a) ↔ TransitiveObj mem (e a) := by
  constructor
  · intro h y hy x hx
    exact h y hy x hx
  · intro h y hy x hx
    exact h y hy x hx

/-- Semantic reading of membership-totality on the elements of one object. -/
def MemTotalOn {α : Type u} (mem : α → α → Prop) (a : α) : Prop :=
  ∀ y, mem y a → ∀ z, mem z a → mem y z ∨ y = z ∨ mem z y

/-- Semantic reading of a finite membership chain: every element is
transitive, and membership is total on the elements.  Unlike `OrdinalLike`,
the chain object itself need not be transitive, so final segments of finite
ordinals are chain-like. -/
def ChainLike {α : Type u} (mem : α → α → Prop) (a : α) : Prop :=
  (∀ y, mem y a → TransitiveObj mem y) ∧ MemTotalOn mem a

/-- Formula macro: membership linearly orders the elements of slot `a`.
This is only the totality component; well-foundedness comes from HF induction. -/
def HF_memTotalOnAt (a : Nat) : Form :=
  fAll (fImp (fMem 0 (a+1))
    (fAll (fImp (fMem 0 (a+2))
      (fOr (fMem 1 0) (fOr (fEq 1 0) (fMem 0 1))))))

theorem HF_memTotalOnAt_spec {α : Type u} {mem : α → α → Prop}
    (e : Nat → α) (a : Nat) :
    Sat mem e (HF_memTotalOnAt a) ↔ MemTotalOn mem (e a) := by
  constructor
  · intro h y hy z hz
    exact h y hy z hz
  · intro h y hy z hz
    exact h y hy z hz

/-- Formula macro: slot `a` is chain-like. -/
def HF_chainLikeAt (a : Nat) : Form :=
  fAnd
    (fAll (fImp (fMem 0 (a+1)) (HF_transitiveAt 0)))
    (HF_memTotalOnAt a)

theorem HF_chainLikeAt_spec {α : Type u} {mem : α → α → Prop}
    (e : Nat → α) (a : Nat) :
    Sat mem e (HF_chainLikeAt a) ↔ ChainLike mem (e a) := by
  constructor
  · intro h
    exact ⟨(fun y hy =>
      (HF_transitiveAt_spec (scons y e) 0).mp (h.1 y hy)),
      (HF_memTotalOnAt_spec e a).mp h.2⟩
  · intro h
    exact ⟨(fun y hy =>
      (HF_transitiveAt_spec (scons y e) 0).mpr (h.1 y hy)),
      (HF_memTotalOnAt_spec e a).mpr h.2⟩

/-- Semantic reading of the finite-ordinal domain formula used by the
PA-in-HF interpretation. -/
def OrdinalLike {α : Type u} (mem : α → α → Prop) (a : α) : Prop :=
  TransitiveObj mem a ∧ (∀ y, mem y a → TransitiveObj mem y) ∧ MemTotalOn mem a

theorem OrdinalLike.of_mem {α : Type u} {mem : α → α → Prop}
    {a y : α} (ha : OrdinalLike mem a) (hy : mem y a) :
    OrdinalLike mem y := by
  refine ⟨ha.2.1 y hy, ?_, ?_⟩
  · intro z hz
    exact ha.2.1 z (ha.1 y hy z hz)
  · intro u hu z hz
    exact ha.2.2 u (ha.1 y hy u hu) z (ha.1 y hy z hz)

theorem OrdinalLike.empty {α : Type} (M : AdjunctionModel α) :
    OrdinalLike M.mem M.empty := by
  refine ⟨?_, ?_, ?_⟩
  · intro y hy
    exact False.elim (M.empty_spec y hy)
  · intro y hy
    exact False.elim (M.empty_spec y hy)
  · intro y hy
    exact False.elim (M.empty_spec y hy)

theorem OrdinalLike.adjoin_self {α : Type} (M : AdjunctionModel α)
    {a s : α} (ha : OrdinalLike M.mem a) (hs : s = M.adjoin a a) :
    OrdinalLike M.mem s := by
  subst s
  refine ⟨?_, ?_, ?_⟩
  · intro y hy x hx
    apply (M.adjoin_spec x a a).mpr
    rcases (M.adjoin_spec y a a).mp hy with hyin | hyeq
    · exact Or.inl (ha.1 y hyin x hx)
    · rw [hyeq] at hx
      exact Or.inl hx
  · intro y hy
    rcases (M.adjoin_spec y a a).mp hy with hyin | hyeq
    · exact ha.2.1 y hyin
    · rw [hyeq]
      exact ha.1
  · intro y hy z hz
    rcases (M.adjoin_spec y a a).mp hy with hyin | hyeq
    · rcases (M.adjoin_spec z a a).mp hz with hzin | hzeq
      · exact ha.2.2 y hyin z hzin
      · exact Or.inl (by rw [hzeq]; exact hyin)
    · rcases (M.adjoin_spec z a a).mp hz with hzin | hzeq
      · exact Or.inr (Or.inr (by rw [hyeq]; exact hzin))
      · exact Or.inr (Or.inl (by rw [hyeq, hzeq]))

/-- Formula macro: slot `a` is ordinal-like.  Over HF, where membership is
well-founded by set induction, this is intended to define the finite von
Neumann ordinals. -/
def HF_ordinalLikeAt (a : Nat) : Form :=
  fAnd (HF_transitiveAt a)
    (fAnd
      (fAll (fImp (fMem 0 (a+1)) (HF_transitiveAt 0)))
      (HF_memTotalOnAt a))

/-- Formula macro: successor-recursion from slot `s` is total through slot `m`
whenever slot `m` is ordinal-like. -/
def HF_succRecTotalOnOrdinalAt (s m : Nat) : Form :=
  fImp (HF_ordinalLikeAt m) (HF_succRecTotalAt s m)

/-- Formula macro: every nonempty object in slot `a` has a membership-maximal
member.  Maximal means no other member of `a` contains it. -/
def HF_memMaxAt (a : Nat) : Form :=
  fImp
    (fEx (fMem 0 (a+1)))
    (fEx
      (fAnd
        (fMem 0 (a+1))
        (fAll
          (fImp
            (fMem 0 (a+2))
            (fImp (fMem 1 0) fBot)))))

/-- Formula macro: every nonempty chain-like subset of slot `a` has a
membership-maximal member. -/
def HF_chainSubsetsMaxAt (a : Nat) : Form :=
  fAll
    (fImp
      (HF_subsetAt 0 (a+1))
      (fImp (HF_chainLikeAt 0) (HF_memMaxAt 0)))

theorem HF_ordinalLikeAt_spec {α : Type u} {mem : α → α → Prop}
    (e : Nat → α) (a : Nat) :
    Sat mem e (HF_ordinalLikeAt a) ↔ OrdinalLike mem (e a) := by
  constructor
  · intro h
    exact ⟨(HF_transitiveAt_spec e a).mp h.1,
      (fun y hy => (HF_transitiveAt_spec (scons y e) 0).mp (h.2.1 y hy)),
      (HF_memTotalOnAt_spec e a).mp h.2.2⟩
  · intro h
    exact ⟨(HF_transitiveAt_spec e a).mpr h.1,
      (fun y hy => (HF_transitiveAt_spec (scons y e) 0).mpr (h.2.1 y hy)),
      (HF_memTotalOnAt_spec e a).mpr h.2.2⟩

theorem HF_memMaxAt_spec {α : Type u} {mem : α → α → Prop}
    (e : Nat → α) (a : Nat) :
    Sat mem e (HF_memMaxAt a) ↔
      ((∃ x, mem x (e a)) →
        ∃ p, mem p (e a) ∧ ∀ q, mem q (e a) → ¬ mem p q) := by
  constructor
  · intro h hne
    rcases hne with ⟨x, hx⟩
    rcases h ⟨x, hx⟩ with ⟨p, hp, hmax⟩
    exact ⟨p, hp, fun q hq hpq => hmax q hq hpq⟩
  · intro h hneSat
    rcases hneSat with ⟨x, hx⟩
    rcases h ⟨x, hx⟩ with ⟨p, hp, hmax⟩
    exact ⟨p, hp, fun q hq hpq => hmax q hq hpq⟩

theorem HF_chainSubsetsMaxAt_spec {α : Type u} {mem : α → α → Prop}
    (e : Nat → α) (a : Nat) :
    Sat mem e (HF_chainSubsetsMaxAt a) ↔
      ∀ s, (∀ x, mem x s → mem x (e a)) →
        ChainLike mem s →
          ((∃ x, mem x s) →
            ∃ p, mem p s ∧ ∀ q, mem q s → ¬ mem p q) := by
  constructor
  · intro h s hsSub hsChain
    have hsSat := h s
    have hsSubSat : Sat mem (scons s e) (HF_subsetAt 0 (a+1)) :=
      (HF_subsetAt_spec (scons s e) 0 (a+1)).mpr hsSub
    have hChainSat : Sat mem (scons s e) (HF_chainLikeAt 0) :=
      (HF_chainLikeAt_spec (scons s e) 0).mpr hsChain
    exact (HF_memMaxAt_spec (scons s e) 0).mp (hsSat hsSubSat hChainSat)
  · intro h s hsSubSat hsChainSat
    have hsSub : ∀ x, mem x s → mem x (e a) :=
      (HF_subsetAt_spec (scons s e) 0 (a+1)).mp hsSubSat
    have hsChain : ChainLike mem s :=
      (HF_chainLikeAt_spec (scons s e) 0).mp hsChainSat
    exact (HF_memMaxAt_spec (scons s e) 0).mpr (h s hsSub hsChain)

/-! ### Free-variable support of the HF macros -/

theorem HF_emptyAt_free {i a : Nat} (h : Free i (HF_emptyAt a)) : i = a := by
  simp only [HF_emptyAt, Free] at h
  repeat first | omega | rcases h with h | h

theorem HF_adjoinAt_free {i c a b : Nat} (h : Free i (HF_adjoinAt c a b)) :
    i = c ∨ i = a ∨ i = b := by
  simp only [HF_adjoinAt, fIff, Free] at h
  repeat first | omega | rcases h with h | h

theorem HF_succAt_free {i s a : Nat} (h : Free i (HF_succAt s a)) :
    i = s ∨ i = a := by
  simp only [HF_succAt, HF_adjoinAt, fIff, Free] at h
  repeat first | omega | rcases h with h | h

theorem HF_singleAt_free {i a b : Nat} (h : Free i (HF_singleAt a b)) :
    i = a ∨ i = b := by
  simp only [HF_singleAt, fIff, Free] at h
  repeat first | omega | rcases h with h | h

theorem HF_upairAt_free {i a b c : Nat} (h : Free i (HF_upairAt a b c)) :
    i = a ∨ i = b ∨ i = c := by
  simp only [HF_upairAt, fIff, Free] at h
  repeat first | omega | rcases h with h | h

theorem HF_kpairAt_free {i p a b : Nat} (h : Free i (HF_kpairAt p a b)) :
    i = p ∨ i = a ∨ i = b := by
  simp only [HF_kpairAt, HF_singleAt, HF_upairAt, fIff, Free] at h
  repeat first | omega | rcases h with h | h

theorem HF_pairMemAt_free {i a b r : Nat} (h : Free i (HF_pairMemAt a b r)) :
    i = a ∨ i = b ∨ i = r := by
  simp only [HF_pairMemAt, HF_kpairAt, HF_singleAt, HF_upairAt, fIff, Free] at h
  repeat first | omega | rcases h with h | h

theorem HF_pairFunctionalAt_free {i f : Nat} (h : Free i (HF_pairFunctionalAt f)) :
    i = f := by
  simp only [HF_pairFunctionalAt, HF_pairMemAt, HF_kpairAt, HF_singleAt,
    HF_upairAt, fIff, Free] at h
  repeat first | omega | rcases h with h | h

theorem HF_pairKeysBelowSuccAt_free {i f m : Nat}
    (h : Free i (HF_pairKeysBelowSuccAt f m)) : i = f ∨ i = m := by
  simp only [HF_pairKeysBelowSuccAt, HF_pairMemAt, HF_kpairAt, HF_singleAt,
    HF_upairAt, fIff, Free] at h
  repeat first | omega | rcases h with h | h

theorem HF_pairTotalBelowSuccAt_free {i f m : Nat}
    (h : Free i (HF_pairTotalBelowSuccAt f m)) : i = f ∨ i = m := by
  simp only [HF_pairTotalBelowSuccAt, HF_pairMemAt, HF_kpairAt, HF_singleAt,
    HF_upairAt, fIff, Free] at h
  repeat first | omega | rcases h with h | h

theorem HF_pairSuccStepAt_free {i f m : Nat}
    (h : Free i (HF_pairSuccStepAt f m)) : i = f ∨ i = m := by
  simp only [HF_pairSuccStepAt, HF_pairMemAt, HF_kpairAt, HF_singleAt,
    HF_upairAt, HF_succAt, HF_adjoinAt, fIff, Free] at h
  repeat first | omega | rcases h with h | h

theorem HF_pairBaseAt_free {i f s : Nat} (h : Free i (HF_pairBaseAt f s)) :
    i = f ∨ i = s := by
  simp only [HF_pairBaseAt, HF_emptyAt, HF_pairMemAt, HF_kpairAt, HF_singleAt,
    HF_upairAt, fIff, Free] at h
  repeat first | omega | rcases h with h | h

theorem HF_pairZeroBaseAt_free {i f : Nat} (h : Free i (HF_pairZeroBaseAt f)) :
    i = f := by
  simp only [HF_pairZeroBaseAt, HF_emptyAt, HF_pairMemAt, HF_kpairAt,
    HF_singleAt, HF_upairAt, fIff, Free] at h
  repeat first | omega | rcases h with h | h

theorem HF_succRecApproxAt_free {i f s m : Nat}
    (h : Free i (HF_succRecApproxAt f s m)) : i = f ∨ i = s ∨ i = m := by
  simp only [HF_succRecApproxAt, Free] at h
  rcases h with h | h
  · have hf := HF_pairFunctionalAt_free h
    omega
  · rcases h with h | h
    · have hfm := HF_pairKeysBelowSuccAt_free h
      omega
    · rcases h with h | h
      · have hfs := HF_pairBaseAt_free h
        omega
      · rcases h with h | h
        · have hfm := HF_pairTotalBelowSuccAt_free h
          omega
        · have hfm := HF_pairSuccStepAt_free h
          omega

theorem HF_subsetAt_free {i a b : Nat} (h : Free i (HF_subsetAt a b)) :
    i = a ∨ i = b := by
  simp only [HF_subsetAt, Free] at h
  repeat first | omega | rcases h with h | h

theorem HF_transitiveAt_free {i a : Nat} (h : Free i (HF_transitiveAt a)) :
    i = a := by
  simp only [HF_transitiveAt, Free] at h
  repeat first | omega | rcases h with h | h

theorem HF_memTotalOnAt_free {i a : Nat} (h : Free i (HF_memTotalOnAt a)) :
    i = a := by
  simp only [HF_memTotalOnAt, Free] at h
  repeat first | omega | rcases h with h | h

theorem HF_ordinalLikeAt_free {i a : Nat} (h : Free i (HF_ordinalLikeAt a)) :
    i = a := by
  simp only [HF_ordinalLikeAt, HF_transitiveAt, HF_memTotalOnAt, Free] at h
  repeat first | omega | rcases h with h | h

/-- The first-order set-induction schema instance for `phi`, where `phi`
uses slot `0` as the element being proved and slots `1,2,...` as parameters. -/
def HF_induction_form (phi : Form) : Form :=
  fImp
    (fAll
      (fImp
        (fAll (fImp (fMem 0 1) (rename rSkipParam phi)))
        phi))
    (fAll phi)

/-- The finite-generation induction schema for hereditary finite sets.

If `phi` holds for every empty object and is preserved by one-point
adjunction, then `phi` holds for every object.  This is the finiteness content
missing from pure foundation-style set induction: ZF models satisfy
`HF_induction_form`, but not this schema. -/
def HF_finite_induction_form (phi : Form) : Form :=
  fImp
    (fAnd
      (fAll (fImp (HF_emptyAt 0) phi))
      (fAll (fAll (fAll
        (fImp
          (HF_adjoinAt 0 2 1)
          (fImp (rename rAdjStepOld phi) (rename rAdjStepNew phi)))))))
    (fAll phi)

theorem HF_finite_induction_form_spec {α : Type u} {mem : α → α → Prop}
    (phi : Form) (e : Nat → α) :
    Sat mem e (HF_finite_induction_form phi) ↔
      (((∀ z, (∀ x, ¬ mem x z) → Sat mem (scons z e) phi) ∧
        (∀ a b c, (∀ x, mem x c ↔ mem x a ∨ x = b) →
          Sat mem (scons a e) phi → Sat mem (scons c e) phi)) →
        ∀ a, Sat mem (scons a e) phi) := by
  constructor
  · intro h hgen
    apply h
    constructor
    · intro z hz
      exact hgen.1 z ((HF_emptyAt_spec (scons z e) 0).mp hz)
    · intro a b c hc hOld
      have hc' :
          ∀ x, mem x c ↔ mem x a ∨ x = b :=
        (HF_adjoinAt_spec (scons c (scons b (scons a e))) 0 2 1).mp hc
      have hOld' : Sat mem (scons a e) phi :=
        (Sat_rename_rAdjStepOld phi e a b c).mp hOld
      exact (Sat_rename_rAdjStepNew phi e a b c).mpr
        (hgen.2 a b c hc' hOld')
  · intro h hsyn
    apply h
    constructor
    · intro z hz
      exact hsyn.1 z ((HF_emptyAt_spec (scons z e) 0).mpr hz)
    · intro a b c hc hOld
      have hcSat :
          Sat mem (scons c (scons b (scons a e))) (HF_adjoinAt 0 2 1) :=
        (HF_adjoinAt_spec (scons c (scons b (scons a e))) 0 2 1).mpr hc
      have hOldSat :
          Sat mem (scons c (scons b (scons a e))) (rename rAdjStepOld phi) :=
        (Sat_rename_rAdjStepOld phi e a b c).mpr hOld
      have hNewSat := hsyn.2 a b c hcSat hOldSat
      exact (Sat_rename_rAdjStepNew phi e a b c).mp hNewSat

/-- The unsealed HF axiom schema. -/
def HFAx (f : Form) : Prop :=
  f = HF_empty_form ∨
  f = HF_extensionality_form ∨
  f = HF_adjoin_form ∨
  ∃ phi, f = HF_induction_form phi

/-- The sentence theory of HF, with every schema instance universally closed. -/
def HFAx_s (f : Form) : Prop :=
  f = sealF HF_empty_form ∨
  f = sealF HF_extensionality_form ∨
  f = sealF HF_adjoin_form ∨
  ∃ phi, f = sealF (HF_induction_form phi)

/-- The sentence theory of hereditary finite sets.

`HFAx_s` contains the extensionality/empty/adjunction axioms and
foundation-style set induction.  The additional finite-generation schema below
excludes infinite sets and is the axiom needed for the PA interpretation over
finite von Neumann ordinals. -/
def HFFinAx_s (f : Form) : Prop :=
  HFAx_s f ∨ ∃ phi, f = sealF (HF_finite_induction_form phi)

theorem Sentences_HF : Sentences HFAx_s := by
  intro f hf
  rcases hf with rfl | rfl | rfl | ⟨phi, rfl⟩ <;> exact Sentence_seal _

theorem Sentences_HFFin : Sentences HFFinAx_s := by
  intro f hf
  rcases hf with hf | ⟨phi, rfl⟩
  · exact Sentences_HF f hf
  · exact Sentence_seal _

theorem sat_HF_empty {α : Type} (M : AdjunctionModel α) (e : Nat → α) :
    Sat M.mem e HF_empty_form :=
  ⟨M.empty, fun x hx => M.empty_spec x hx⟩

theorem sat_HF_extensionality {α : Type} (M : AdjunctionModel α) (e : Nat → α) :
    Sat M.mem e HF_extensionality_form := by
  intro a b h
  apply M.extensional
  intro x
  exact (Sat_fIff (mem := M.mem)
    (e := scons x (scons b (scons a e)))).mp (h x)

theorem sat_HF_adjoin {α : Type} (M : AdjunctionModel α) (e : Nat → α) :
    Sat M.mem e HF_adjoin_form := by
  intro a b
  refine ⟨M.adjoin a b, fun x => ?_⟩
  exact (Sat_fIff (mem := M.mem)).mpr (M.adjoin_spec x a b)

theorem sat_HF_induction {α : Type} (M : AdjunctionModel α)
    (phi : Form) (e : Nat → α) :
    Sat M.mem e (HF_induction_form phi) := by
  intro hstep a
  exact M.set_induction (fun x => Sat M.mem (scons x e) phi)
    (fun x ih => hstep x (fun y hy =>
      (Sat_rename_rSkipParam phi e x y).mpr (ih y hy)))
    a

theorem sat_HF_model {α : Type} (M : AdjunctionModel α) (v : Nat → α) :
    ∀ g, HFAx_s g → Sat M.mem v g := by
  intro g hg
  rcases hg with rfl | rfl | rfl | ⟨phi, rfl⟩
  · exact (seal_valid (mem := M.mem) HF_empty_form).mpr (sat_HF_empty M) v
  · exact (seal_valid (mem := M.mem) HF_extensionality_form).mpr
      (sat_HF_extensionality M) v
  · exact (seal_valid (mem := M.mem) HF_adjoin_form).mpr (sat_HF_adjoin M) v
  · exact (seal_valid (mem := M.mem) (HF_induction_form phi)).mpr
      (sat_HF_induction M phi) v

theorem standard_sat_HF (v : Nat → Nat) :
    ∀ g, HFAx_s g → Sat Mem v g :=
  sat_HF_model standardModel v

/-- The finite prefix of the Ackermann-coded set `a` using only candidate
elements below `n`.  This gives an explicit adjunction construction of every
standard HF object, independent of any formula being interpreted. -/
def prefixBelow (a : Nat) : Nat → Nat
  | 0 => empty
  | n+1 => if a.testBit n then adjoin (prefixBelow a n) n else prefixBelow a n

theorem prefixBelow_succ_of_mem {a n : Nat} (h : Mem n a) :
    prefixBelow a (n+1) = adjoin (prefixBelow a n) n := by
  have hbit : a.testBit n = true := h
  simp [prefixBelow, hbit]

theorem prefixBelow_succ_of_not_mem {a n : Nat} (h : ¬ Mem n a) :
    prefixBelow a (n+1) = prefixBelow a n := by
  have hbit : a.testBit n = false := by
    cases hb : a.testBit n <;> simp [Mem, hb] at h ⊢
  simp [prefixBelow, hbit]

theorem mem_prefixBelow_iff {x a n : Nat} :
    Mem x (prefixBelow a n) ↔ x < n ∧ Mem x a := by
  induction n with
  | zero =>
      constructor
      · intro h
        exact False.elim (mem_empty x h)
      · intro h
        omega
  | succ n ih =>
      by_cases hn : Mem n a
      · rw [prefixBelow_succ_of_mem hn, mem_adjoin, ih]
        constructor
        · intro h
          rcases h with h | h
          · exact ⟨Nat.lt_succ_of_lt h.1, h.2⟩
          · subst x
            exact ⟨Nat.lt_succ_self n, hn⟩
        · intro h
          have hle : x ≤ n := Nat.lt_succ_iff.mp h.1
          rcases Nat.lt_or_eq_of_le hle with hlt | heq
          · exact Or.inl ⟨hlt, h.2⟩
          · exact Or.inr heq
      · rw [prefixBelow_succ_of_not_mem hn, ih]
        constructor
        · intro h
          exact ⟨Nat.lt_succ_of_lt h.1, h.2⟩
        · intro h
          have hle : x ≤ n := Nat.lt_succ_iff.mp h.1
          rcases Nat.lt_or_eq_of_le hle with hlt | heq
          · exact ⟨hlt, h.2⟩
          · exact False.elim (hn (by simpa [heq] using h.2))

theorem prefixBelow_self_eq (a : Nat) : prefixBelow a a = a := by
  apply ext
  intro x
  rw [mem_prefixBelow_iff]
  constructor
  · intro h
    exact h.2
  · intro h
    exact ⟨mem_lt h, h⟩

theorem sat_HF_finite_induction_standard (phi : Form) (e : Nat → Nat) :
    Sat Mem e (HF_finite_induction_form phi) := by
  apply (HF_finite_induction_form_spec phi e).mpr
  intro hgen a
  have hpref : ∀ n, Sat Mem (scons (prefixBelow a n) e) phi := by
    intro n
    induction n with
    | zero =>
        exact hgen.1 (prefixBelow a 0) (fun x hx => mem_empty x hx)
    | succ n ih =>
        by_cases hn : Mem n a
        · have hAdj :
            ∀ x, Mem x (prefixBelow a (n+1)) ↔
              Mem x (prefixBelow a n) ∨ x = n := by
            intro x
            rw [prefixBelow_succ_of_mem hn, mem_adjoin]
          exact hgen.2 (prefixBelow a n) n (prefixBelow a (n+1)) hAdj ih
        · simpa [prefixBelow_succ_of_not_mem hn] using ih
  simpa [prefixBelow_self_eq a] using hpref a

theorem standard_sat_HFFin (v : Nat → Nat) :
    ∀ g, HFFinAx_s g → Sat Mem v g := by
  intro g hg
  rcases hg with hg | ⟨phi, rfl⟩
  · exact standard_sat_HF v g hg
  · exact (seal_valid (mem := Mem) (HF_finite_induction_form phi)).mpr
      (sat_HF_finite_induction_standard phi) v

/-- Named membership of the sealed empty-set axiom in the HF theory. -/
theorem HFAx_s_empty : HFAx_s (sealF HF_empty_form) :=
  Or.inl rfl

/-- Named membership of the sealed extensionality axiom in the HF theory. -/
theorem HFAx_s_extensionality : HFAx_s (sealF HF_extensionality_form) :=
  Or.inr (Or.inl rfl)

/-- Named membership of the sealed adjunction axiom in the HF theory. -/
theorem HFAx_s_adjoin : HFAx_s (sealF HF_adjoin_form) :=
  Or.inr (Or.inr (Or.inl rfl))

/-- Named membership of a sealed set-induction instance in the HF theory. -/
theorem HFAx_s_induction (phi : Form) : HFAx_s (sealF (HF_induction_form phi)) :=
  Or.inr (Or.inr (Or.inr ⟨phi, rfl⟩))

theorem HFFinAx_s_of_HFAx_s {f : Form} (hf : HFAx_s f) : HFFinAx_s f :=
  Or.inl hf

/-- Named membership of a sealed finite-generation induction instance in the
hereditary-finite theory. -/
theorem HFFinAx_s_finite_induction (phi : Form) :
    HFFinAx_s (sealF (HF_finite_induction_form phi)) :=
  Or.inr ⟨phi, rfl⟩

theorem semantic_empty_of_HFAx_s {α : Type u} {mem : α → α → Prop}
    (v : Nat → α) (hHF : ∀ g, HFAx_s g → Sat mem v g) :
    ∃ e, ∀ x, ¬ mem x e :=
  extract HFAx_s v HF_empty_form hHF HFAx_s_empty v

theorem semantic_extensionality_of_HFAx_s {α : Type u} {mem : α → α → Prop}
    (v : Nat → α) (hHF : ∀ g, HFAx_s g → Sat mem v g) :
    ∀ a b, (∀ x, mem x a ↔ mem x b) → a = b := by
  have hExt : ∀ e, Sat mem e HF_extensionality_form :=
    extract HFAx_s v HF_extensionality_form hHF HFAx_s_extensionality
  intro a b hab
  exact hExt v a b (fun x =>
    (Sat_fIff (mem := mem) (e := scons x (scons b (scons a v)))).mpr (hab x))

theorem semantic_adjoin_of_HFAx_s {α : Type u} {mem : α → α → Prop}
    (v : Nat → α) (hHF : ∀ g, HFAx_s g → Sat mem v g) :
    ∀ a b, ∃ c, ∀ x, mem x c ↔ mem x a ∨ x = b := by
  have hAdj : ∀ e, Sat mem e HF_adjoin_form :=
    extract HFAx_s v HF_adjoin_form hHF HFAx_s_adjoin
  intro a b
  rcases hAdj v a b with ⟨c, hc⟩
  exact ⟨c, fun x =>
    (Sat_fIff (mem := mem) (e := scons x (scons c (scons b (scons a v))))).mp (hc x)⟩

theorem semantic_induction_schema_of_HFAx_s {α : Type u} {mem : α → α → Prop}
    (v : Nat → α) (hHF : ∀ g, HFAx_s g → Sat mem v g) (phi : Form) :
    ∀ e, Sat mem e (HF_induction_form phi) :=
  extract HFAx_s v (HF_induction_form phi) hHF (HFAx_s_induction phi)

theorem semantic_finite_induction_schema_of_HFFinAx_s {α : Type u}
    {mem : α → α → Prop}
    (v : Nat → α) (hHF : ∀ g, HFFinAx_s g → Sat mem v g) (phi : Form) :
    ∀ e, Sat mem e (HF_finite_induction_form phi) :=
  extract HFFinAx_s v (HF_finite_induction_form phi) hHF
    (HFFinAx_s_finite_induction phi)

theorem semantic_empty_of_HFFinAx_s {α : Type u} {mem : α → α → Prop}
    (v : Nat → α) (hHF : ∀ g, HFFinAx_s g → Sat mem v g) :
    ∃ e, ∀ x, ¬ mem x e :=
  semantic_empty_of_HFAx_s v
    (fun g hg => hHF g (HFFinAx_s_of_HFAx_s hg))

theorem semantic_extensionality_of_HFFinAx_s {α : Type u}
    {mem : α → α → Prop}
    (v : Nat → α) (hHF : ∀ g, HFFinAx_s g → Sat mem v g) :
    ∀ a b, (∀ x, mem x a ↔ mem x b) → a = b :=
  semantic_extensionality_of_HFAx_s v
    (fun g hg => hHF g (HFFinAx_s_of_HFAx_s hg))

theorem semantic_adjoin_of_HFFinAx_s {α : Type u} {mem : α → α → Prop}
    (v : Nat → α) (hHF : ∀ g, HFFinAx_s g → Sat mem v g) :
    ∀ a b, ∃ c, ∀ x, mem x c ↔ mem x a ∨ x = b :=
  semantic_adjoin_of_HFAx_s v
    (fun g hg => hHF g (HFFinAx_s_of_HFAx_s hg))

theorem semantic_induction_schema_of_HFFinAx_s {α : Type u}
    {mem : α → α → Prop}
    (v : Nat → α) (hHF : ∀ g, HFFinAx_s g → Sat mem v g) (phi : Form) :
    ∀ e, Sat mem e (HF_induction_form phi) :=
  semantic_induction_schema_of_HFAx_s v
    (fun g hg => hHF g (HFFinAx_s_of_HFAx_s hg)) phi

/-- First-order HF induction rules out self-membership in every semantic model
of the sealed HF theory. -/
theorem semantic_mem_irrefl_of_HFAx_s {α : Type u} {mem : α → α → Prop}
    (v : Nat → α) (hHF : ∀ g, HFAx_s g → Sat mem v g) :
    ∀ a, ¬ mem a a := by
  let phi : Form := fImp (fMem 0 0) fBot
  have hind := semantic_induction_schema_of_HFAx_s v hHF phi v
  have hall : ∀ a, Sat mem (scons a v) phi := by
    apply hind
    intro a ih haa
    exact ih a haa haa
  intro a haa
  exact hall a haa

/-- First-order semantic content of the sealed HF theory, without pretending
that first-order induction gives the second-order `AdjunctionModel.set_induction`
field. -/
structure FirstOrderHFModel (α : Type u) where
  mem : α → α → Prop
  extensional : ∀ a b, (∀ x, mem x a ↔ mem x b) → a = b
  empty_exists : ∃ e, ∀ x, ¬ mem x e
  adjoin_exists : ∀ a b, ∃ c, ∀ x, mem x c ↔ mem x a ∨ x = b
  induction_schema : ∀ phi e, Sat mem e (HF_induction_form phi)

/-- First-order HF model with chosen empty and adjunction witnesses.

This is deliberately weaker than `AdjunctionModel`: it carries the first-order
induction schema as a semantic axiom, not a meta-level set-induction principle.
It is the right bundle for constructing witnesses while discharging translated
axioms by completeness. -/
structure FirstOrderAdjunctionModel (α : Type u) where
  mem : α → α → Prop
  empty : α
  adjoin : α → α → α
  extensional : ∀ a b, (∀ x, mem x a ↔ mem x b) → a = b
  empty_spec : ∀ x, ¬ mem x empty
  adjoin_spec : ∀ x a b, mem x (adjoin a b) ↔ mem x a ∨ x = b
  induction_schema : ∀ phi e, Sat mem e (HF_induction_form phi)

/-- Forget the first-order induction schema and retain the common adjunction
algebra. -/
abbrev FirstOrderAdjunctionModel.toCore {α : Type u}
    (M : FirstOrderAdjunctionModel α) : AdjunctionCore α where
  mem := M.mem
  empty := M.empty
  adjoin := M.adjoin
  extensional := by
    intro a b h
    exact M.extensional a b h
  empty_spec := M.empty_spec
  adjoin_spec := M.adjoin_spec

/-- Chosen first-order HF model carrying the finite-generation induction
schema of hereditary finite sets. -/
structure FirstOrderFiniteAdjunctionModel (α : Type u) extends
    FirstOrderAdjunctionModel α where
  finite_induction_schema : ∀ phi e, Sat mem e (HF_finite_induction_form phi)

namespace FirstOrderAdjunctionModel

/-- First-order HF induction rules out self-membership in a chosen first-order
HF model. -/
theorem mem_irrefl {α : Type u} (M : FirstOrderAdjunctionModel α) (a : α) :
    ¬ M.mem a a := by
  let phi : Form := fImp (fMem 0 0) fBot
  have hind := M.induction_schema phi (fun _ => a)
  have hall : ∀ a, Sat M.mem (scons a (fun _ => a)) phi := by
    apply hind
    intro a ih haa
    exact ih a haa haa
  exact hall a

/-- First-order HF induction rules out two-cycles of membership. -/
theorem mem_asymm {α : Type u} (M : FirstOrderAdjunctionModel α) {a b : α}
    (hab : M.mem a b) : ¬ M.mem b a := by
  let phi : Form :=
    fAll (fImp (fMem 0 1) (fImp (fMem 1 0) fBot))
  let tail : Nat → α := fun _ => a
  have hind := M.induction_schema phi tail
  have hall : ∀ x, Sat M.mem (scons x tail) phi := by
    apply hind
    intro x ih y hyx hxy
    have hySat : Sat M.mem (scons y tail) phi :=
      (Sat_rename_rSkipParam phi tail x y).mp (ih y hyx)
    exact hySat x hxy hyx
  exact hall b a hab

theorem adjoin_self_mem {α : Type u} (M : FirstOrderAdjunctionModel α) (a : α) :
    M.mem a (M.adjoin a a) :=
  (M.adjoin_spec a a a).mpr (Or.inr rfl)

theorem adjoin_self_ne_self {α : Type u} (M : FirstOrderAdjunctionModel α)
    (a : α) : M.adjoin a a ≠ a := by
  intro h
  have ha : M.mem a (M.adjoin a a) := adjoin_self_mem M a
  rw [h] at ha
  exact mem_irrefl M a ha

theorem adjoin_self_not_mem_of_ordinalLike {α : Type u}
    (M : FirstOrderAdjunctionModel α) {a : α}
    (ha : OrdinalLike M.mem a) : ¬ M.mem (M.adjoin a a) a := by
  intro hsucc
  have ha_in_succ : M.mem a (M.adjoin a a) := adjoin_self_mem M a
  have haa : M.mem a a := ha.1 (M.adjoin a a) hsucc a ha_in_succ
  exact mem_irrefl M a haa

theorem adjoin_self_injective_on_ordinalLike {α : Type u}
    (M : FirstOrderAdjunctionModel α) {a b : α}
    (_ha : OrdinalLike M.mem a) (hb : OrdinalLike M.mem b)
    (h : M.adjoin a a = M.adjoin b b) : a = b := by
  have hasucc : M.mem a (M.adjoin b b) := by
    have : M.mem a (M.adjoin a a) := adjoin_self_mem M a
    simpa [h] using this
  rcases (M.adjoin_spec a b b).mp hasucc with hab | hab
  · have hbsucc : M.mem b (M.adjoin a a) := by
      have : M.mem b (M.adjoin b b) := adjoin_self_mem M b
      simpa [← h] using this
    rcases (M.adjoin_spec b a a).mp hbsucc with hba | hba
    · have hbb : M.mem b b := hb.1 a hab b hba
      exact False.elim (mem_irrefl M b hbb)
    · exact hba.symm
  · exact hab

/-- The chosen empty object is ordinal-like in every first-order adjunction
model. -/
theorem ordinalLike_empty {α : Type u} (M : FirstOrderAdjunctionModel α) :
    OrdinalLike M.mem M.empty := by
  refine ⟨?_, ?_, ?_⟩
  · intro y hy
    exact False.elim (M.empty_spec y hy)
  · intro y hy
    exact False.elim (M.empty_spec y hy)
  · intro y hy
    exact False.elim (M.empty_spec y hy)

/-- Self-adjunction preserves ordinal-likeness in every first-order adjunction
model. -/
theorem ordinalLike_adjoin_self {α : Type u}
    (M : FirstOrderAdjunctionModel α) {a s : α}
    (ha : OrdinalLike M.mem a) (hs : s = M.adjoin a a) :
    OrdinalLike M.mem s := by
  subst s
  refine ⟨?_, ?_, ?_⟩
  · intro y hy x hx
    apply (M.adjoin_spec x a a).mpr
    rcases (M.adjoin_spec y a a).mp hy with hyin | hyeq
    · exact Or.inl (ha.1 y hyin x hx)
    · rw [hyeq] at hx
      exact Or.inl hx
  · intro y hy
    rcases (M.adjoin_spec y a a).mp hy with hyin | hyeq
    · exact ha.2.1 y hyin
    · rw [hyeq]
      exact ha.1
  · intro y hy z hz
    rcases (M.adjoin_spec y a a).mp hy with hyin | hyeq
    · rcases (M.adjoin_spec z a a).mp hz with hzin | hzeq
      · exact ha.2.2 y hyin z hzin
      · exact Or.inl (by rw [hzeq]; exact hyin)
    · rcases (M.adjoin_spec z a a).mp hz with hzin | hzeq
      · exact Or.inr (Or.inr (by rw [hyeq]; exact hzin))
      · exact Or.inr (Or.inl (by rw [hyeq, hzeq]))

/-- A membership-maximal element of an ordinal-like object is its predecessor. -/
theorem ordinalLike_eq_succ_of_mem_max {α : Type u}
    (M : FirstOrderAdjunctionModel α) {a p : α}
    (ha : OrdinalLike M.mem a)
    (hp : M.mem p a)
    (hmax : ∀ q, M.mem q a → ¬ M.mem p q) :
    a = M.adjoin p p := by
  apply M.extensional
  intro x
  constructor
  · intro hx
    apply (M.adjoin_spec x p p).mpr
    rcases ha.2.2 x hx p hp with hxp | hxp | hpx
    · exact Or.inl hxp
    · exact Or.inr hxp
    · exact False.elim (hmax x hx hpx)
  · intro hx
    rcases (M.adjoin_spec x p p).mp hx with hxp | hxp
    · exact ha.1 p hp x hxp
    · rw [hxp]
      exact hp

/-- If every nonempty object has a membership-maximal element, then every
ordinal-like object is either empty or a successor of one of its members. -/
theorem ordinalLike_empty_or_succ_of_mem_max_exists {α : Type u}
    (M : FirstOrderAdjunctionModel α)
    (hMax : ∀ a, (∃ x, M.mem x a) →
      ∃ p, M.mem p a ∧ ∀ q, M.mem q a → ¬ M.mem p q)
    {a : α} (ha : OrdinalLike M.mem a) :
    a = M.empty ∨ ∃ p, M.mem p a ∧ a = M.adjoin p p := by
  by_cases hne : ∃ x, M.mem x a
  · rcases hMax a hne with ⟨p, hp, hmax⟩
    exact Or.inr ⟨p, hp, ordinalLike_eq_succ_of_mem_max M ha hp hmax⟩
  · left
    apply M.extensional
    intro x
    constructor
    · intro hx
      exact False.elim (hne ⟨x, hx⟩)
    · intro hx
      exact False.elim (M.empty_spec x hx)

/-- First-order-model compatibility names for the shared adjunction algebra. -/
abbrev single {α : Type u} (M : FirstOrderAdjunctionModel α) (a : α) : α :=
  AdjunctionCore.single M.toCore a

theorem single_spec {α : Type u} (M : FirstOrderAdjunctionModel α) (a x : α) :
    M.mem x (single M a) ↔ x = a :=
  AdjunctionCore.single_spec M.toCore a x

abbrev upair {α : Type u} (M : FirstOrderAdjunctionModel α) (a b : α) : α :=
  AdjunctionCore.upair M.toCore a b

theorem upair_spec {α : Type u} (M : FirstOrderAdjunctionModel α) (a b x : α) :
    M.mem x (upair M a b) ↔ x = a ∨ x = b :=
  AdjunctionCore.upair_spec M.toCore a b x

abbrev kpair {α : Type u} (M : FirstOrderAdjunctionModel α) (a b : α) : α :=
  AdjunctionCore.kpair M.toCore a b

theorem kpair_mem {α : Type u} (M : FirstOrderAdjunctionModel α) (a b q : α) :
    M.mem q (kpair M a b) ↔ q = single M a ∨ q = upair M a b :=
  AdjunctionCore.kpair_mem M.toCore a b q

theorem single_injective {α : Type u} (M : FirstOrderAdjunctionModel α) {a b : α}
    (h : single M a = single M b) : a = b :=
  AdjunctionCore.single_injective M.toCore h

theorem upair_eq_single {α : Type u} (M : FirstOrderAdjunctionModel α)
    {a b c : α} (h : upair M a b = single M c) : a = c ∧ b = c :=
  AdjunctionCore.upair_eq_single M.toCore h

theorem kpair_injective {α : Type u} (M : FirstOrderAdjunctionModel α)
    {a b c d : α} (h : kpair M a b = kpair M c d) : a = c ∧ b = d :=
  AdjunctionCore.kpair_injective M.toCore h

theorem HF_emptyAt_empty {α : Type u} (M : FirstOrderAdjunctionModel α)
    (e : Nat → α) (i : Nat) :
    Sat M.mem e (HF_emptyAt i) ↔ e i = M.empty :=
  AdjunctionCore.HF_emptyAt_empty M.toCore e i

theorem HF_adjoinAt_adjoin {α : Type u} (M : FirstOrderAdjunctionModel α)
    (e : Nat → α) (c a b : Nat) :
    Sat M.mem e (HF_adjoinAt c a b) ↔ e c = M.adjoin (e a) (e b) :=
  AdjunctionCore.HF_adjoinAt_adjoin M.toCore e c a b

theorem HF_succAt_spec {α : Type u} (M : FirstOrderAdjunctionModel α)
    (e : Nat → α) (s a : Nat) :
    Sat M.mem e (HF_succAt s a) ↔ e s = M.adjoin (e a) (e a) :=
  AdjunctionCore.HF_succAt_spec M.toCore e s a

theorem HF_singleAt_spec {α : Type u} (M : FirstOrderAdjunctionModel α)
    (e : Nat → α) (i j : Nat) :
    Sat M.mem e (HF_singleAt i j) ↔ e i = single M (e j) :=
  M.toCore.HF_singleAt_spec e i j

theorem HF_upairAt_spec {α : Type u} (M : FirstOrderAdjunctionModel α)
    (e : Nat → α) (i j k : Nat) :
    Sat M.mem e (HF_upairAt i j k) ↔ e i = upair M (e j) (e k) :=
  M.toCore.HF_upairAt_spec e i j k

theorem HF_kpairAt_spec {α : Type u} (M : FirstOrderAdjunctionModel α)
    (e : Nat → α) (p a b : Nat) :
    Sat M.mem e (HF_kpairAt p a b) ↔ e p = kpair M (e a) (e b) :=
  M.toCore.HF_kpairAt_spec e p a b

theorem HF_pairMemAt_spec {α : Type u} (M : FirstOrderAdjunctionModel α)
    (e : Nat → α) (a b r : Nat) :
    Sat M.mem e (HF_pairMemAt a b r) ↔
      M.mem (kpair M (e a) (e b)) (e r) :=
  M.toCore.HF_pairMemAt_spec e a b r

/-- A set of first-order-model ordered pairs is single-valued in its second
component. -/
abbrev PairFunctional {α : Type u} (M : FirstOrderAdjunctionModel α) (f : α) : Prop :=
  M.toCore.PairFunctional f

/-- Every first component of a pair in `f` is a member of `m ∪ {m}`. -/
abbrev PairKeysBelowSucc {α : Type u} (M : FirstOrderAdjunctionModel α) (f m : α) : Prop :=
  M.toCore.PairKeysBelowSucc f m

/-- Every element of `m ∪ {m}` appears as the first component of some pair in
`f`. -/
abbrev PairTotalBelowSucc {α : Type u} (M : FirstOrderAdjunctionModel α) (f m : α) : Prop :=
  M.toCore.PairTotalBelowSucc f m

/-- Successor-recursion step for a first-order-model pair set `f`. -/
abbrev PairSuccStep {α : Type u} (M : FirstOrderAdjunctionModel α) (f m : α) : Prop :=
  M.toCore.PairSuccStep f m

theorem HF_pairFunctionalAt_spec {α : Type u} (M : FirstOrderAdjunctionModel α)
    (e : Nat → α) (f : Nat) :
    Sat M.mem e (HF_pairFunctionalAt f) ↔ PairFunctional M (e f) :=
  M.toCore.HF_pairFunctionalAt_spec e f

theorem HF_pairKeysBelowSuccAt_spec {α : Type u} (M : FirstOrderAdjunctionModel α)
    (e : Nat → α) (f m : Nat) :
    Sat M.mem e (HF_pairKeysBelowSuccAt f m) ↔
      PairKeysBelowSucc M (e f) (e m) :=
  M.toCore.HF_pairKeysBelowSuccAt_spec e f m

theorem HF_pairTotalBelowSuccAt_spec {α : Type u} (M : FirstOrderAdjunctionModel α)
    (e : Nat → α) (f m : Nat) :
    Sat M.mem e (HF_pairTotalBelowSuccAt f m) ↔
      PairTotalBelowSucc M (e f) (e m) :=
  M.toCore.HF_pairTotalBelowSuccAt_spec e f m

theorem HF_pairSuccStepAt_spec {α : Type u} (M : FirstOrderAdjunctionModel α)
    (e : Nat → α) (f m : Nat) :
    Sat M.mem e (HF_pairSuccStepAt f m) ↔ PairSuccStep M (e f) (e m) :=
  M.toCore.HF_pairSuccStepAt_spec e f m

theorem HF_pairBaseAt_spec {α : Type u} (M : FirstOrderAdjunctionModel α)
    (e : Nat → α) (f s : Nat) :
    Sat M.mem e (HF_pairBaseAt f s) ↔
      M.mem (kpair M M.empty (e s)) (e f) :=
  M.toCore.HF_pairBaseAt_spec e f s

theorem HF_pairZeroBaseAt_spec {α : Type u} (M : FirstOrderAdjunctionModel α)
    (e : Nat → α) (f : Nat) :
    Sat M.mem e (HF_pairZeroBaseAt f) ↔
      M.mem (kpair M M.empty M.empty) (e f) :=
  M.toCore.HF_pairZeroBaseAt_spec e f

/-- Semantic package for a finite successor-recursion trace in a chosen
first-order HF model. -/
abbrev SuccRecApprox {α : Type u} (M : FirstOrderAdjunctionModel α) (s f m : α) : Prop :=
  M.toCore.SuccRecApprox s f m

/-- Total successor-recursion data through a key `m`: a trace plus its value at
`m`. -/
def SuccRecTotal {α : Type u} (M : FirstOrderAdjunctionModel α) (s m : α) : Prop :=
  ∃ f z, SuccRecApprox M s f m ∧ M.mem (kpair M m z) f

/-- The one-pair graph `{⟨0,s⟩}` used for successor recursion through zero. -/
def zeroSuccRecGraph {α : Type u} (M : FirstOrderAdjunctionModel α) (s : α) : α :=
  single M (kpair M M.empty s)

theorem zeroSuccRecGraph_base {α : Type u} (M : FirstOrderAdjunctionModel α)
    (s : α) :
    M.mem (kpair M M.empty s) (zeroSuccRecGraph M s) :=
  (single_spec M (kpair M M.empty s) (kpair M M.empty s)).mpr rfl

theorem zeroSuccRecGraph_succRecApprox {α : Type u}
    (M : FirstOrderAdjunctionModel α) (s : α) :
    SuccRecApprox M s (zeroSuccRecGraph M s) M.empty := by
  refine ⟨?functional, ?keys, zeroSuccRecGraph_base M s, ?total, ?step⟩
  · intro k y y' hky hky'
    have hky_eq : kpair M k y = kpair M M.empty s :=
      (single_spec M (kpair M M.empty s) (kpair M k y)).mp hky
    have hky'_eq : kpair M k y' = kpair M M.empty s :=
      (single_spec M (kpair M M.empty s) (kpair M k y')).mp hky'
    have hy : y = s := (kpair_injective M hky_eq).2
    have hy' : y' = s := (kpair_injective M hky'_eq).2
    rw [hy, hy']
  · intro k y hky
    have hk_eq : kpair M k y = kpair M M.empty s :=
      (single_spec M (kpair M M.empty s) (kpair M k y)).mp hky
    exact Or.inr (kpair_injective M hk_eq).1
  · intro k hk
    rcases hk with hk | hk
    · exact False.elim (M.empty_spec k hk)
    · subst k
      exact ⟨s, zeroSuccRecGraph_base M s⟩
  · intro k _t _y hkm _ _
    exact False.elim (M.empty_spec k hkm)

/-- Successor-recursion is total through zero. -/
theorem succRecTotal_empty {α : Type u}
    (M : FirstOrderAdjunctionModel α) (s : α) :
    SuccRecTotal M s M.empty := by
  exact ⟨zeroSuccRecGraph M s, s,
    zeroSuccRecGraph_succRecApprox M s,
    zeroSuccRecGraph_base M s⟩

/-- Extend a successor-recursion graph by the next pair
`⟨m+1, z+1⟩`. -/
def succRecGraphSucc {α : Type u} (M : FirstOrderAdjunctionModel α)
    (f m z : α) : α :=
  M.adjoin f (kpair M (M.adjoin m m) (M.adjoin z z))

theorem succRecGraphSucc_old {α : Type u} (M : FirstOrderAdjunctionModel α)
    {f m z p : α} (hp : M.mem p f) :
    M.mem p (succRecGraphSucc M f m z) :=
  (M.adjoin_spec p f (kpair M (M.adjoin m m) (M.adjoin z z))).mpr (Or.inl hp)

theorem succRecGraphSucc_new {α : Type u} (M : FirstOrderAdjunctionModel α)
    (f m z : α) :
    M.mem (kpair M (M.adjoin m m) (M.adjoin z z))
      (succRecGraphSucc M f m z) :=
  (M.adjoin_spec (kpair M (M.adjoin m m) (M.adjoin z z))
    f (kpair M (M.adjoin m m) (M.adjoin z z))).mpr (Or.inr rfl)

theorem succRecGraphSucc_succRecApprox {α : Type u}
    (M : FirstOrderAdjunctionModel α) {s f m z : α}
    (hm : OrdinalLike M.mem m)
    (hf : SuccRecApprox M s f m)
    (hz : M.mem (kpair M m z) f) :
    SuccRecApprox M s (succRecGraphSucc M f m z) (M.adjoin m m) := by
  rcases hf with ⟨hfun, hkeys, hbase, htotal, hstep⟩
  let sm := M.adjoin m m
  let sz := M.adjoin z z
  let newPair := kpair M sm sz
  let g := succRecGraphSucc M f m z
  have hsm_not_mem : ¬ M.mem sm m := by
    simpa [sm] using adjoin_self_not_mem_of_ordinalLike M hm
  have hsm_ne_m : sm ≠ m := by
    simpa [sm] using adjoin_self_ne_self M m
  have hmem_g : ∀ p, M.mem p g ↔ M.mem p f ∨ p = newPair := by
    intro p
    exact M.adjoin_spec p f newPair
  have old_key_ne_succ :
      ∀ {k y}, M.mem (kpair M k y) f → k ≠ sm := by
    intro k y hOld hk
    have hkBound := hkeys k y hOld
    rw [hk] at hkBound
    rcases hkBound with hmem | heq
    · exact hsm_not_mem hmem
    · exact hsm_ne_m heq
  have pair_old_of_mem_key :
      ∀ {k y}, M.mem k m → M.mem (kpair M k y) g →
        M.mem (kpair M k y) f := by
    intro k y hkm hkg
    rcases (hmem_g (kpair M k y)).mp hkg with hOld | hNew
    · exact hOld
    · have hk : k = sm := (kpair_injective M hNew).1
      rw [hk] at hkm
      exact False.elim (hsm_not_mem hkm)
  refine ⟨?functional, ?keys, ?base, ?total, ?step⟩
  · intro k y y' hky hky'
    rcases (hmem_g (kpair M k y)).mp hky with hOld | hNew
    · rcases (hmem_g (kpair M k y')).mp hky' with hOld' | hNew'
      · exact hfun k y y' hOld hOld'
      · have hk : k = sm := (kpair_injective M hNew').1
        exact False.elim (old_key_ne_succ hOld hk)
    · rcases (hmem_g (kpair M k y')).mp hky' with hOld' | hNew'
      · have hk : k = sm := (kpair_injective M hNew).1
        exact False.elim (old_key_ne_succ hOld' hk)
      · have hy : y = sz := (kpair_injective M hNew).2
        have hy' : y' = sz := (kpair_injective M hNew').2
        rw [hy, hy']
  · intro k y hky
    rcases (hmem_g (kpair M k y)).mp hky with hOld | hNew
    · rcases hkeys k y hOld with hkm | hkm
      · exact Or.inl ((M.adjoin_spec k m m).mpr (Or.inl hkm))
      · exact Or.inl ((M.adjoin_spec k m m).mpr (Or.inr hkm))
    · exact Or.inr (kpair_injective M hNew).1
  · exact succRecGraphSucc_old M hbase
  · intro k hk
    rcases hk with hksm | hksm
    · rcases (M.adjoin_spec k m m).mp hksm with hkm | hkm
      · rcases htotal k (Or.inl hkm) with ⟨y, hy⟩
        exact ⟨y, succRecGraphSucc_old M hy⟩
      · rcases htotal k (Or.inr hkm) with ⟨y, hy⟩
        exact ⟨y, succRecGraphSucc_old M hy⟩
    · subst k
      exact ⟨sz, succRecGraphSucc_new M f m z⟩
  · intro k t y hksm hkt hsky
    rcases (M.adjoin_spec k m m).mp hksm with hkm | hkm
    · have hktOld : M.mem (kpair M k t) f :=
        pair_old_of_mem_key hkm hkt
      have hskyOld : M.mem (kpair M (M.adjoin k k) y) f := by
        rcases (hmem_g (kpair M (M.adjoin k k) y)).mp hsky with hOld | hNew
        · exact hOld
        · have hsk : M.adjoin k k = sm := (kpair_injective M hNew).1
          have hkOrd : OrdinalLike M.mem k := OrdinalLike.of_mem hm hkm
          have hkm_eq : k = m :=
            adjoin_self_injective_on_ordinalLike M hkOrd hm (by simpa [sm] using hsk)
          rw [hkm_eq] at hkm
          exact False.elim (mem_irrefl M m hkm)
      exact hstep k t y hkm hktOld hskyOld
    · subst k
      have hktOld : M.mem (kpair M m t) f := by
        rcases (hmem_g (kpair M m t)).mp hkt with hOld | hNew
        · exact hOld
        · have hm_eq_sm : m = sm := (kpair_injective M hNew).1
          exact False.elim (hsm_ne_m hm_eq_sm.symm)
      have ht : t = z := hfun m t z hktOld hz
      rcases (hmem_g (kpair M sm y)).mp hsky with hOld | hNew
      · exact False.elim (old_key_ne_succ hOld rfl)
      · have hy : y = sz := (kpair_injective M hNew).2
        rw [ht, hy]

/-- If successor-recursion is total through an ordinal-like key `m`, it is total
through its successor. -/
theorem succRecTotal_succ {α : Type u}
    (M : FirstOrderAdjunctionModel α) {s m : α}
    (hm : OrdinalLike M.mem m)
    (ht : SuccRecTotal M s m) :
    SuccRecTotal M s (M.adjoin m m) := by
  rcases ht with ⟨f, z, hf, hz⟩
  exact ⟨succRecGraphSucc M f m z, M.adjoin z z,
    succRecGraphSucc_succRecApprox M hm hf hz,
    succRecGraphSucc_new M f m z⟩

theorem HF_succRecApproxAt_spec {α : Type u} (M : FirstOrderAdjunctionModel α)
    (e : Nat → α) (f s m : Nat) :
    Sat M.mem e (HF_succRecApproxAt f s m) ↔
      SuccRecApprox M (e s) (e f) (e m) :=
  M.toCore.HF_succRecApproxAt_spec e f s m

/-- Semantic reading of `HF_succRecTotalAt` in a chosen first-order adjunction
model. -/
theorem HF_succRecTotalAt_spec {α : Type u} (M : FirstOrderAdjunctionModel α)
    (e : Nat → α) (s m : Nat) :
    Sat M.mem e (HF_succRecTotalAt s m) ↔
      SuccRecTotal M (e s) (e m) := by
  constructor
  · intro h
    rcases h with ⟨f, z, hf, hz⟩
    have hf' := (HF_succRecApproxAt_spec M (scons z (scons f e))
      1 (s+2) (m+2)).mp hf
    have hz' := (HF_pairMemAt_spec M (scons z (scons f e))
      (m+2) 0 1).mp hz
    change SuccRecApprox M (e s) f (e m) at hf'
    change M.mem (kpair M (e m) z) f at hz'
    exact ⟨f, z, hf', hz'⟩
  · intro h
    rcases h with ⟨f, z, hf, hz⟩
    refine ⟨f, z, ?_, ?_⟩
    · apply (HF_succRecApproxAt_spec M (scons z (scons f e))
        1 (s+2) (m+2)).mpr
      change SuccRecApprox M (e s) f (e m)
      exact hf
    · apply (HF_pairMemAt_spec M (scons z (scons f e))
        (m+2) 0 1).mpr
      change M.mem (kpair M (e m) z) f
      exact hz

/-- Semantic reading of the ordinal-relativized successor-recursion totality
formula. -/
theorem HF_succRecTotalOnOrdinalAt_spec {α : Type u}
    (M : FirstOrderAdjunctionModel α) (e : Nat → α) (s m : Nat) :
    Sat M.mem e (HF_succRecTotalOnOrdinalAt s m) ↔
      (OrdinalLike M.mem (e m) → SuccRecTotal M (e s) (e m)) := by
  constructor
  · intro h hm
    exact (HF_succRecTotalAt_spec M e s m).mp
      (h ((HF_ordinalLikeAt_spec e m).mpr hm))
  · intro h hmSat
    exact (HF_succRecTotalAt_spec M e s m).mpr
      (h ((HF_ordinalLikeAt_spec e m).mp hmSat))

/-- If every ordinal-like object is either empty or a successor of one of its
members, first-order HF induction proves successor-recursion totality through
all ordinal-like keys. -/
theorem succRecTotal_of_ordinalLike_of_predecessor {α : Type u}
    (M : FirstOrderAdjunctionModel α)
    (hPred : ∀ a, OrdinalLike M.mem a →
      a = M.empty ∨ ∃ p, M.mem p a ∧ a = M.adjoin p p)
    (s m : α) (hm : OrdinalLike M.mem m) :
    SuccRecTotal M s m := by
  let phi : Form := HF_succRecTotalOnOrdinalAt 1 0
  let tail : Nat → α := fun _ => s
  have hind := M.induction_schema phi (scons s tail)
  have hall : ∀ a, Sat M.mem (scons a (scons s tail)) phi := by
    apply hind
    intro a ih
    apply (HF_succRecTotalOnOrdinalAt_spec M
      (scons a (scons s tail)) 1 0).mpr
    intro ha
    rcases hPred a ha with haEmpty | ⟨p, hpa, haSucc⟩
    · rw [haEmpty]
      exact succRecTotal_empty M s
    · have hpOrd : OrdinalLike M.mem p := OrdinalLike.of_mem ha hpa
      have hpSat : Sat M.mem (scons p (scons s tail)) phi :=
        (Sat_rename_rSkipParam phi (scons s tail) a p).mp (ih p hpa)
      have hpTotal : SuccRecTotal M s p := by
        simpa [phi, tail, scons] using
          ((HF_succRecTotalOnOrdinalAt_spec M
            (scons p (scons s tail)) 1 0).mp hpSat hpOrd)
      rw [haSucc]
      exact succRecTotal_succ M hpOrd hpTotal
  simpa [phi, tail, scons] using
    ((HF_succRecTotalOnOrdinalAt_spec M
      (scons m (scons s tail)) 1 0).mp (hall m) hm)

/-- A maximal-member principle for nonempty HF objects is enough to make
successor-recursion total on all ordinal-like keys. -/
theorem succRecTotal_of_ordinalLike_of_mem_max_exists {α : Type u}
    (M : FirstOrderAdjunctionModel α)
    (hMax : ∀ a, (∃ x, M.mem x a) →
      ∃ p, M.mem p a ∧ ∀ q, M.mem q a → ¬ M.mem p q)
    (s m : α) (hm : OrdinalLike M.mem m) :
    SuccRecTotal M s m := by
  apply succRecTotal_of_ordinalLike_of_predecessor M
  · intro a ha
    exact ordinalLike_empty_or_succ_of_mem_max_exists M hMax ha
  · exact hm

end FirstOrderAdjunctionModel

def firstOrderHFModel_of_HFAx_s {α : Type u} {mem : α → α → Prop}
    (v : Nat → α) (hHF : ∀ g, HFAx_s g → Sat mem v g) :
    FirstOrderHFModel α where
  mem := mem
  extensional := semantic_extensionality_of_HFAx_s v hHF
  empty_exists := semantic_empty_of_HFAx_s v hHF
  adjoin_exists := semantic_adjoin_of_HFAx_s v hHF
  induction_schema := semantic_induction_schema_of_HFAx_s v hHF

/-- Select concrete empty and adjunction witnesses from any semantic model of
the sealed HF theory. -/
noncomputable def firstOrderAdjunctionModel_of_HFAx_s {α : Type u}
    {mem : α → α → Prop}
    (v : Nat → α) (hHF : ∀ g, HFAx_s g → Sat mem v g) :
    FirstOrderAdjunctionModel α where
  mem := mem
  empty := Classical.choose (semantic_empty_of_HFAx_s v hHF)
  adjoin := fun a b => Classical.choose (semantic_adjoin_of_HFAx_s v hHF a b)
  extensional := semantic_extensionality_of_HFAx_s v hHF
  empty_spec := Classical.choose_spec (semantic_empty_of_HFAx_s v hHF)
  adjoin_spec := by
    intro x a b
    exact Classical.choose_spec (semantic_adjoin_of_HFAx_s v hHF a b) x
  induction_schema := semantic_induction_schema_of_HFAx_s v hHF

noncomputable def firstOrderFiniteAdjunctionModel_of_HFFinAx_s {α : Type u}
    {mem : α → α → Prop}
    (v : Nat → α) (hHF : ∀ g, HFFinAx_s g → Sat mem v g) :
    FirstOrderFiniteAdjunctionModel α where
  mem := mem
  empty := Classical.choose (semantic_empty_of_HFFinAx_s v hHF)
  adjoin := fun a b => Classical.choose (semantic_adjoin_of_HFFinAx_s v hHF a b)
  extensional := semantic_extensionality_of_HFFinAx_s v hHF
  empty_spec := Classical.choose_spec (semantic_empty_of_HFFinAx_s v hHF)
  adjoin_spec := by
    intro x a b
    exact Classical.choose_spec (semantic_adjoin_of_HFFinAx_s v hHF a b) x
  induction_schema := semantic_induction_schema_of_HFFinAx_s v hHF
  finite_induction_schema := semantic_finite_induction_schema_of_HFFinAx_s v hHF

namespace FirstOrderFiniteAdjunctionModel

theorem sepBy_exists {α : Type u} (M : FirstOrderFiniteAdjunctionModel α)
    (psi : Form) (e : Nat → α) :
    ∀ a, ∃ s, ∀ x,
      M.mem x s ↔ M.mem x a ∧ Sat M.mem (scons x e) psi := by
  let theta : Form := rename rSepParam psi
  let phi : Form := HF_sepByAt theta 0
  have hind := M.finite_induction_schema phi e
  have hall : ∀ a, Sat M.mem (scons a e) phi := by
    apply (HF_finite_induction_form_spec phi e).mp hind
    constructor
    · intro z hzEmpty
      apply (HF_sepByAt_spec theta (scons z e) 0).mpr
      refine ⟨M.empty, fun x => ?_⟩
      constructor
      · intro hx
        exact False.elim (M.empty_spec x hx)
      · intro hx
        exact False.elim (hzEmpty x hx.1)
    · intro a b c hc hOld
      rcases (HF_sepByAt_spec theta (scons a e) 0).mp hOld with ⟨s, hs⟩
      by_cases hb : Sat M.mem (scons b e) psi
      · apply (HF_sepByAt_spec theta (scons c e) 0).mpr
        refine ⟨M.adjoin s b, fun x => ?_⟩
        constructor
        · intro hx
          rcases (M.adjoin_spec x s b).mp hx with hxs | hxb
          · have hxOld := (hs x).mp hxs
            have hxPsi : Sat M.mem (scons x e) psi :=
              (Sat_rename_rSepParam psi e a x).mp hxOld.2
            exact ⟨(hc x).mpr (Or.inl hxOld.1),
              (Sat_rename_rSepParam psi e c x).mpr hxPsi⟩
          · subst x
            exact ⟨(hc b).mpr (Or.inr rfl),
              (Sat_rename_rSepParam psi e c b).mpr hb⟩
        · intro hx
          rcases (hc x).mp hx.1 with hxa | hxb
          · apply (M.adjoin_spec x s b).mpr
            left
            have hxPsi : Sat M.mem (scons x e) psi :=
              (Sat_rename_rSepParam psi e c x).mp hx.2
            exact (hs x).mpr
              ⟨hxa, (Sat_rename_rSepParam psi e a x).mpr hxPsi⟩
          · exact (M.adjoin_spec x s b).mpr (Or.inr hxb)
      · apply (HF_sepByAt_spec theta (scons c e) 0).mpr
        refine ⟨s, fun x => ?_⟩
        constructor
        · intro hxs
          have hxOld := (hs x).mp hxs
          have hxPsi : Sat M.mem (scons x e) psi :=
            (Sat_rename_rSepParam psi e a x).mp hxOld.2
          exact ⟨(hc x).mpr (Or.inl hxOld.1),
            (Sat_rename_rSepParam psi e c x).mpr hxPsi⟩
        · intro hx
          rcases (hc x).mp hx.1 with hxa | hxb
          · have hxPsi : Sat M.mem (scons x e) psi :=
              (Sat_rename_rSepParam psi e c x).mp hx.2
            exact (hs x).mpr
              ⟨hxa, (Sat_rename_rSepParam psi e a x).mpr hxPsi⟩
          · subst x
            have hb' : Sat M.mem (scons b e) psi :=
              (Sat_rename_rSepParam psi e c b).mp hx.2
            exact False.elim (hb hb')
  intro a
  rcases (HF_sepByAt_spec theta (scons a e) 0).mp (hall a) with ⟨s, hs⟩
  refine ⟨s, fun x => ?_⟩
  constructor
  · intro hxs
    have hx := (hs x).mp hxs
    have hxPsi : Sat M.mem (scons x e) psi :=
      (Sat_rename_rSepParam psi e a x).mp hx.2
    exact ⟨hx.1, hxPsi⟩
  · intro hx
    exact (hs x).mpr
      ⟨hx.1, (Sat_rename_rSepParam psi e a x).mpr hx.2⟩

theorem binUnion_exists {α : Type u} (M : FirstOrderFiniteAdjunctionModel α)
    (a b : α) :
    ∃ u, ∀ x, M.mem x u ↔ M.mem x a ∨ M.mem x b := by
  let phi : Form := HF_binUnionAt 1 0
  let tail : Nat → α := fun _ => a
  have hind := M.finite_induction_schema phi (scons a tail)
  have hall : ∀ b, Sat M.mem (scons b (scons a tail)) phi := by
    apply (HF_finite_induction_form_spec phi (scons a tail)).mp hind
    constructor
    · intro z hzEmpty
      apply (HF_binUnionAt_spec (scons z (scons a tail)) 1 0).mpr
      refine ⟨a, fun x => ?_⟩
      constructor
      · intro hxa
        exact Or.inl hxa
      · intro hx
        rcases hx with hxa | hxz
        · exact hxa
        · exact False.elim (hzEmpty x hxz)
    · intro old y c hc hOld
      rcases (HF_binUnionAt_spec (scons old (scons a tail)) 1 0).mp hOld
        with ⟨u, hu⟩
      apply (HF_binUnionAt_spec (scons c (scons a tail)) 1 0).mpr
      refine ⟨M.adjoin u y, fun x => ?_⟩
      constructor
      · intro hx
        rcases (M.adjoin_spec x u y).mp hx with hxu | hxy
        · rcases (hu x).mp hxu with hxa | hxold
          · exact Or.inl hxa
          · exact Or.inr ((hc x).mpr (Or.inl hxold))
        · subst x
          exact Or.inr ((hc y).mpr (Or.inr rfl))
      · intro hx
        rcases hx with hxa | hxc
        · apply (M.adjoin_spec x u y).mpr
          exact Or.inl ((hu x).mpr (Or.inl hxa))
        · rcases (hc x).mp hxc with hxold | hxy
          · apply (M.adjoin_spec x u y).mpr
            exact Or.inl ((hu x).mpr (Or.inr hxold))
          · exact (M.adjoin_spec x u y).mpr (Or.inr hxy)
  simpa [phi, tail, scons] using
    (HF_binUnionAt_spec (scons b (scons a tail)) 1 0).mp (hall b)

theorem union_exists {α : Type u} (M : FirstOrderFiniteAdjunctionModel α)
    (a : α) :
    ∃ u, ∀ x, M.mem x u ↔ ∃ v, M.mem v a ∧ M.mem x v := by
  let phi : Form := HF_unionAt 0
  let tail : Nat → α := fun _ => M.empty
  have hind := M.finite_induction_schema phi tail
  have hall : ∀ a, Sat M.mem (scons a tail) phi := by
    apply (HF_finite_induction_form_spec phi tail).mp hind
    constructor
    · intro z hzEmpty
      apply (HF_unionAt_spec (scons z tail) 0).mpr
      refine ⟨M.empty, fun x => ?_⟩
      constructor
      · intro hx
        exact False.elim (M.empty_spec x hx)
      · intro hx
        rcases hx with ⟨v, hvz, _⟩
        exact False.elim (hzEmpty v hvz)
    · intro old y c hc hOld
      rcases (HF_unionAt_spec (scons old tail) 0).mp hOld with ⟨u, hu⟩
      rcases binUnion_exists M u y with ⟨w, hw⟩
      apply (HF_unionAt_spec (scons c tail) 0).mpr
      refine ⟨w, fun x => ?_⟩
      constructor
      · intro hxw
        rcases (hw x).mp hxw with hxu | hxy
        · rcases (hu x).mp hxu with ⟨v, hvold, hxv⟩
          exact ⟨v, (hc v).mpr (Or.inl hvold), hxv⟩
        · exact ⟨y, (hc y).mpr (Or.inr rfl), hxy⟩
      · intro hx
        rcases hx with ⟨v, hvc, hxv⟩
        rcases (hc v).mp hvc with hvold | hvy
        · apply (hw x).mpr
          exact Or.inl ((hu x).mpr ⟨v, hvold, hxv⟩)
        · subst v
          exact (hw x).mpr (Or.inr hxv)
  simpa [phi, tail, scons] using
    (HF_unionAt_spec (scons a tail) 0).mp (hall a)

theorem chainSubsetsMax_exists {α : Type u}
    (M : FirstOrderFiniteAdjunctionModel α) :
    ∀ a s, (∀ x, M.mem x s → M.mem x a) →
      ChainLike M.mem s →
        (∃ x, M.mem x s) →
          ∃ p, M.mem p s ∧ ∀ q, M.mem q s → ¬ M.mem p q := by
  let phi : Form := HF_chainSubsetsMaxAt 0
  let tail : Nat → α := fun _ => M.empty
  have hind := M.finite_induction_schema phi tail
  have hall : ∀ a, Sat M.mem (scons a tail) phi := by
    apply (HF_finite_induction_form_spec phi tail).mp hind
    constructor
    · intro z hzEmpty
      apply (HF_chainSubsetsMaxAt_spec (scons z tail) 0).mpr
      intro s hsSub _hsChain hsNonempty
      rcases hsNonempty with ⟨x, hxs⟩
      exact False.elim (hzEmpty x (hsSub x hxs))
    · intro old y c hc hOld
      have oldP :
          ∀ s, (∀ x, M.mem x s → M.mem x old) →
            ChainLike M.mem s →
              (∃ x, M.mem x s) →
                ∃ p, M.mem p s ∧ ∀ q, M.mem q s → ¬ M.mem p q :=
        (HF_chainSubsetsMaxAt_spec (scons old tail) 0).mp hOld
      apply (HF_chainSubsetsMaxAt_spec (scons c tail) 0).mpr
      intro s hsSub hsChain hsNonempty
      rcases sepBy_exists M (fMem 0 1) (scons s tail) old with ⟨t, ht⟩
      have htSubOld : ∀ x, M.mem x t → M.mem x old := by
        intro x hxt
        exact ((ht x).mp hxt).1
      have htSubS : ∀ x, M.mem x t → M.mem x s := by
        intro x hxt
        exact ((ht x).mp hxt).2
      have htChain : ChainLike M.mem t := by
        refine ⟨?trans, ?total⟩
        · intro x hxt
          exact hsChain.1 x (htSubS x hxt)
        · intro x hxt z hzt
          exact hsChain.2 x (htSubS x hxt) z (htSubS z hzt)
      by_cases htne : ∃ x, M.mem x t
      · rcases oldP t htSubOld htChain htne with ⟨p, hpt, hpMaxT⟩
        have hps : M.mem p s := htSubS p hpt
        by_cases hys : M.mem y s
        · rcases hsChain.2 p hps y hys with hpy | hpy | hyp
          · refine ⟨y, hys, ?_⟩
            intro q hqs hyq
            rcases (hc q).mp (hsSub q hqs) with hqold | hqy
            · have hqt : M.mem q t := (ht q).mpr ⟨hqold, hqs⟩
              have htransq : TransitiveObj M.mem q := hsChain.1 q hqs
              have hpq : M.mem p q := htransq y hyq p hpy
              exact hpMaxT q hqt hpq
            · subst q
              exact FirstOrderAdjunctionModel.mem_irrefl M.toFirstOrderAdjunctionModel y hyq
          · subst p
            refine ⟨y, hys, ?_⟩
            intro q hqs hyq
            rcases (hc q).mp (hsSub q hqs) with hqold | hqy
            · have hqt : M.mem q t := (ht q).mpr ⟨hqold, hqs⟩
              exact hpMaxT q hqt hyq
            · subst q
              exact FirstOrderAdjunctionModel.mem_irrefl M.toFirstOrderAdjunctionModel y hyq
          · refine ⟨p, hps, ?_⟩
            intro q hqs hpq
            rcases (hc q).mp (hsSub q hqs) with hqold | hqy
            · have hqt : M.mem q t := (ht q).mpr ⟨hqold, hqs⟩
              exact hpMaxT q hqt hpq
            · subst q
              exact FirstOrderAdjunctionModel.mem_asymm
                M.toFirstOrderAdjunctionModel hyp hpq
        · refine ⟨p, hps, ?_⟩
          intro q hqs hpq
          rcases (hc q).mp (hsSub q hqs) with hqold | hqy
          · have hqt : M.mem q t := (ht q).mpr ⟨hqold, hqs⟩
            exact hpMaxT q hqt hpq
          · subst q
            exact hys hqs
      · rcases hsNonempty with ⟨p, hps⟩
        have hp_eq_y : p = y := by
          rcases (hc p).mp (hsSub p hps) with hpold | hpy
          · have hpt : M.mem p t := (ht p).mpr ⟨hpold, hps⟩
            exact False.elim (htne ⟨p, hpt⟩)
          · exact hpy
        refine ⟨p, hps, ?_⟩
        intro q hqs hpq
        have hq_eq_y : q = y := by
          rcases (hc q).mp (hsSub q hqs) with hqold | hqy
          · have hqt : M.mem q t := (ht q).mpr ⟨hqold, hqs⟩
            exact False.elim (htne ⟨q, hqt⟩)
          · exact hqy
        subst p
        subst q
        exact FirstOrderAdjunctionModel.mem_irrefl M.toFirstOrderAdjunctionModel y hpq
  intro a s hsSub hsChain hsNonempty
  exact (HF_chainSubsetsMaxAt_spec (scons a tail) 0).mp (hall a)
    s hsSub hsChain hsNonempty

theorem ordinalLike_empty_or_succ {α : Type u}
    (M : FirstOrderFiniteAdjunctionModel α)
    {a : α} (ha : OrdinalLike M.mem a) :
    a = M.empty ∨ ∃ p, M.mem p a ∧ a = M.adjoin p p := by
  by_cases hne : ∃ x, M.mem x a
  · have hChain : ChainLike M.mem a := ⟨ha.2.1, ha.2.2⟩
    rcases chainSubsetsMax_exists M a a (fun _ hx => hx) hChain hne with
      ⟨p, hp, hmax⟩
    exact Or.inr ⟨p, hp,
      FirstOrderAdjunctionModel.ordinalLike_eq_succ_of_mem_max
        M.toFirstOrderAdjunctionModel ha hp hmax⟩
  · left
    apply M.extensional
    intro x
    constructor
    · intro hx
      exact False.elim (hne ⟨x, hx⟩)
    · intro hx
      exact False.elim (M.empty_spec x hx)

theorem succRecTotal_of_ordinalLike {α : Type u}
    (M : FirstOrderFiniteAdjunctionModel α)
    (s m : α) (hm : OrdinalLike M.mem m) :
    FirstOrderAdjunctionModel.SuccRecTotal M.toFirstOrderAdjunctionModel s m := by
  apply FirstOrderAdjunctionModel.succRecTotal_of_ordinalLike_of_predecessor
    M.toFirstOrderAdjunctionModel
  · intro a ha
    exact ordinalLike_empty_or_succ M ha
  · exact hm

/-- In finite HF, a successor-recursion trace starting from an ordinal-like
base assigns ordinal-like values to all keys covered by the trace.

The induction is over the key whose value is read from the trace, not over the
ambient endpoint of the trace.  This makes the successor case reusable: the
value at `p+1` is the successor of the value at `p`, and the induction
hypothesis applies to `p` inside the same ambient trace. -/
theorem succRecApprox_value_ordinalLike {α : Type u}
    (M : FirstOrderFiniteAdjunctionModel α) {s f m z : α}
    (hs : OrdinalLike M.mem s) (hm : OrdinalLike M.mem m)
    (hf : FirstOrderAdjunctionModel.SuccRecApprox
      M.toFirstOrderAdjunctionModel s f m)
    (hz : M.mem (FirstOrderAdjunctionModel.kpair
      M.toFirstOrderAdjunctionModel m z) f) :
    OrdinalLike M.mem z := by
  let N := M.toFirstOrderAdjunctionModel
  let phi : Form :=
    fAll
      (fImp (fOr (fMem 1 0) (fEq 1 0))
        (fImp (HF_ordinalLikeAt 0)
          (fImp (HF_succRecApproxAt 3 2 0)
            (fAll (fImp (HF_pairMemAt 2 0 4) (HF_ordinalLikeAt 0))))))
  let tail : Nat → α := fun _ => M.empty
  have hind := M.induction_schema phi (scons s (scons f tail))
  have hall : ∀ k, Sat M.mem (scons k (scons s (scons f tail))) phi := by
    apply hind
    intro k ih
    intro m hkey hmSat hfSat z hpairSat
    let Em : Nat → α := scons m (scons k (scons s (scons f tail)))
    let Ez : Nat → α := scons z Em
    have hmOrd : OrdinalLike M.mem m :=
      (HF_ordinalLikeAt_spec Em 0).mp hmSat
    have hfApprox : FirstOrderAdjunctionModel.SuccRecApprox N s f m := by
      simpa [N, Em, tail, scons] using
        (FirstOrderAdjunctionModel.HF_succRecApproxAt_spec N Em 3 2 0).mp hfSat
    have hpair : N.mem (FirstOrderAdjunctionModel.kpair N k z) f := by
      simpa [N, Em, Ez, tail, scons] using
        (FirstOrderAdjunctionModel.HF_pairMemAt_spec N Ez 2 0 4).mp hpairSat
    have hkOrd : OrdinalLike M.mem k := by
      rcases hkey with hkm | hkm
      · change M.mem k m at hkm
        exact OrdinalLike.of_mem hmOrd hkm
      · change k = m at hkm
        subst k
        exact hmOrd
    rcases ordinalLike_empty_or_succ M hkOrd with hkEmpty | ⟨p, hpk, hkSucc⟩
    · rcases hfApprox with ⟨hfun, _hkeys, hbase, _htotal, _hstep⟩
      have hpairEmpty : N.mem (FirstOrderAdjunctionModel.kpair N N.empty z) f := by
        simpa [N, hkEmpty] using hpair
      have hz_eq_s : z = s := hfun N.empty z s hpairEmpty hbase
      apply (HF_ordinalLikeAt_spec Ez 0).mpr
      simpa [Ez, Em, hz_eq_s, N, scons] using hs
    · rcases hfApprox with ⟨_hfun, _hkeys, _hbase, htotal, hstep⟩
      have hpm : M.mem p m := by
        rcases hkey with hkm | hkm
        · change M.mem k m at hkm
          exact hmOrd.1 k hkm p hpk
        · change k = m at hkm
          simpa [hkm] using hpk
      rcases htotal p (Or.inl hpm) with ⟨t, hpt⟩
      have hpSat : Sat M.mem (scons p (scons s (scons f tail))) phi :=
        (Sat_rename_rSkipParam phi (scons s (scons f tail)) k p).mp (ih p hpk)
      let Emp : Nat → α := scons m (scons p (scons s (scons f tail)))
      let Etp : Nat → α := scons t Emp
      have hmSatP : Sat M.mem Emp (HF_ordinalLikeAt 0) :=
        (HF_ordinalLikeAt_spec Emp 0).mpr hmOrd
      have hfSatP : Sat M.mem Emp (HF_succRecApproxAt 3 2 0) := by
        apply (FirstOrderAdjunctionModel.HF_succRecApproxAt_spec N Emp 3 2 0).mpr
        exact ⟨_hfun, _hkeys, _hbase, htotal, hstep⟩
      have hptSat : Sat M.mem Etp (HF_pairMemAt 2 0 4) := by
        apply (FirstOrderAdjunctionModel.HF_pairMemAt_spec N Etp 2 0 4).mpr
        simpa [N, Emp, Etp, tail, scons] using hpt
      have htDomain : Sat M.mem Etp (HF_ordinalLikeAt 0) :=
        hpSat m (Or.inl hpm) hmSatP hfSatP t hptSat
      have htOrd : OrdinalLike M.mem t :=
        (HF_ordinalLikeAt_spec Etp 0).mp htDomain
      have hpairSucc : N.mem
          (FirstOrderAdjunctionModel.kpair N (N.adjoin p p) z) f := by
        simpa [N, hkSucc] using hpair
      have hz_eq_succ : z = N.adjoin t t := hstep p t z hpm hpt hpairSucc
      apply (HF_ordinalLikeAt_spec Ez 0).mpr
      exact FirstOrderAdjunctionModel.ordinalLike_adjoin_self N htOrd hz_eq_succ
  let Em : Nat → α := scons m (scons m (scons s (scons f tail)))
  let Ez : Nat → α := scons z Em
  have hmain : Sat M.mem (scons m (scons s (scons f tail))) phi := hall m
  have hmSat : Sat M.mem Em (HF_ordinalLikeAt 0) :=
    (HF_ordinalLikeAt_spec Em 0).mpr hm
  have hfSat : Sat M.mem Em (HF_succRecApproxAt 3 2 0) := by
    apply (FirstOrderAdjunctionModel.HF_succRecApproxAt_spec N Em 3 2 0).mpr
    simpa [N, Em, tail, scons] using hf
  have hzSat : Sat M.mem Ez (HF_pairMemAt 2 0 4) := by
    apply (FirstOrderAdjunctionModel.HF_pairMemAt_spec N Ez 2 0 4).mpr
    simpa [N, Em, Ez, tail, scons] using hz
  have hzDomain : Sat M.mem Ez (HF_ordinalLikeAt 0) :=
    hmain m (Or.inr rfl) hmSat hfSat z hzSat
  exact (HF_ordinalLikeAt_spec Ez 0).mp hzDomain

/-- In finite HF, successor-recursion traces with the same base have a unique
value at every ordinal-like key covered by both traces. -/
theorem succRecApprox_value_unique {α : Type u}
    (M : FirstOrderFiniteAdjunctionModel α) {s f g m z w : α}
    (hm : OrdinalLike M.mem m)
    (hf : FirstOrderAdjunctionModel.SuccRecApprox
      M.toFirstOrderAdjunctionModel s f m)
    (hz : M.mem (FirstOrderAdjunctionModel.kpair
      M.toFirstOrderAdjunctionModel m z) f)
    (hg : FirstOrderAdjunctionModel.SuccRecApprox
      M.toFirstOrderAdjunctionModel s g m)
    (hw : M.mem (FirstOrderAdjunctionModel.kpair
      M.toFirstOrderAdjunctionModel m w) g) :
    z = w := by
  let N := M.toFirstOrderAdjunctionModel
  let phi : Form :=
    fAll
      (fImp (fOr (fMem 1 0) (fEq 1 0))
        (fImp (HF_ordinalLikeAt 0)
          (fImp (HF_succRecApproxAt 3 2 0)
            (fImp (HF_succRecApproxAt 4 2 0)
              (fAll
                (fImp (HF_pairMemAt 2 0 4)
                  (fAll (fImp (HF_pairMemAt 3 0 6) (fEq 1 0)))))))))
  let tail : Nat → α := fun _ => M.empty
  have hind := M.induction_schema phi (scons s (scons f (scons g tail)))
  have hall : ∀ k, Sat M.mem (scons k (scons s (scons f (scons g tail)))) phi := by
    apply hind
    intro k ih
    intro m hkey hmSat hfSat hgSat z hzSat w hwSat
    let Em : Nat → α := scons m (scons k (scons s (scons f (scons g tail))))
    let Ez : Nat → α := scons z Em
    let Ewz : Nat → α := scons w Ez
    have hmOrd : OrdinalLike M.mem m :=
      (HF_ordinalLikeAt_spec Em 0).mp hmSat
    have hfApprox : FirstOrderAdjunctionModel.SuccRecApprox N s f m := by
      simpa [N, Em, tail, scons] using
        (FirstOrderAdjunctionModel.HF_succRecApproxAt_spec N Em 3 2 0).mp hfSat
    have hgApprox : FirstOrderAdjunctionModel.SuccRecApprox N s g m := by
      simpa [N, Em, tail, scons] using
        (FirstOrderAdjunctionModel.HF_succRecApproxAt_spec N Em 4 2 0).mp hgSat
    have hpairF : N.mem (FirstOrderAdjunctionModel.kpair N k z) f := by
      simpa [N, Em, Ez, tail, scons] using
        (FirstOrderAdjunctionModel.HF_pairMemAt_spec N Ez 2 0 4).mp hzSat
    have hpairG : N.mem (FirstOrderAdjunctionModel.kpair N k w) g := by
      simpa [N, Em, Ez, Ewz, tail, scons] using
        (FirstOrderAdjunctionModel.HF_pairMemAt_spec N Ewz 3 0 6).mp hwSat
    have hkOrd : OrdinalLike M.mem k := by
      rcases hkey with hkm | hkm
      · change M.mem k m at hkm
        exact OrdinalLike.of_mem hmOrd hkm
      · change k = m at hkm
        subst k
        exact hmOrd
    rcases ordinalLike_empty_or_succ M hkOrd with hkEmpty | ⟨p, hpk, hkSucc⟩
    · rcases hfApprox with ⟨hfunF, _hkeysF, hbaseF, _htotalF, _hstepF⟩
      rcases hgApprox with ⟨hfunG, _hkeysG, hbaseG, _htotalG, _hstepG⟩
      have hpairEmptyF : N.mem (FirstOrderAdjunctionModel.kpair N N.empty z) f := by
        simpa [N, hkEmpty] using hpairF
      have hpairEmptyG : N.mem (FirstOrderAdjunctionModel.kpair N N.empty w) g := by
        simpa [N, hkEmpty] using hpairG
      have hz_eq_s : z = s := hfunF N.empty z s hpairEmptyF hbaseF
      have hw_eq_s : w = s := hfunG N.empty w s hpairEmptyG hbaseG
      exact hz_eq_s.trans hw_eq_s.symm
    · rcases hfApprox with ⟨_hfunF, _hkeysF, _hbaseF, htotalF, hstepF⟩
      rcases hgApprox with ⟨_hfunG, _hkeysG, _hbaseG, htotalG, hstepG⟩
      have hpm : M.mem p m := by
        rcases hkey with hkm | hkm
        · change M.mem k m at hkm
          exact hmOrd.1 k hkm p hpk
        · change k = m at hkm
          simpa [hkm] using hpk
      rcases htotalF p (Or.inl hpm) with ⟨t, hpt⟩
      rcases htotalG p (Or.inl hpm) with ⟨u, hpu⟩
      have hpSat : Sat M.mem (scons p (scons s (scons f (scons g tail)))) phi :=
        (Sat_rename_rSkipParam phi (scons s (scons f (scons g tail))) k p).mp
          (ih p hpk)
      let Emp : Nat → α := scons m (scons p (scons s (scons f (scons g tail))))
      let Etp : Nat → α := scons t Emp
      let Eutp : Nat → α := scons u Etp
      have hmSatP : Sat M.mem Emp (HF_ordinalLikeAt 0) :=
        (HF_ordinalLikeAt_spec Emp 0).mpr hmOrd
      have hfSatP : Sat M.mem Emp (HF_succRecApproxAt 3 2 0) := by
        apply (FirstOrderAdjunctionModel.HF_succRecApproxAt_spec N Emp 3 2 0).mpr
        exact ⟨_hfunF, _hkeysF, _hbaseF, htotalF, hstepF⟩
      have hgSatP : Sat M.mem Emp (HF_succRecApproxAt 4 2 0) := by
        apply (FirstOrderAdjunctionModel.HF_succRecApproxAt_spec N Emp 4 2 0).mpr
        exact ⟨_hfunG, _hkeysG, _hbaseG, htotalG, hstepG⟩
      have hptSat : Sat M.mem Etp (HF_pairMemAt 2 0 4) := by
        apply (FirstOrderAdjunctionModel.HF_pairMemAt_spec N Etp 2 0 4).mpr
        simpa [N, Emp, Etp, tail, scons] using hpt
      have hpuSat : Sat M.mem Eutp (HF_pairMemAt 3 0 6) := by
        apply (FirstOrderAdjunctionModel.HF_pairMemAt_spec N Eutp 3 0 6).mpr
        simpa [N, Emp, Etp, Eutp, tail, scons] using hpu
      have htu : t = u :=
        hpSat m (Or.inl hpm) hmSatP hfSatP hgSatP t hptSat u hpuSat
      have hpairSuccF : N.mem
          (FirstOrderAdjunctionModel.kpair N (N.adjoin p p) z) f := by
        simpa [N, hkSucc] using hpairF
      have hpairSuccG : N.mem
          (FirstOrderAdjunctionModel.kpair N (N.adjoin p p) w) g := by
        simpa [N, hkSucc] using hpairG
      have hz_eq_succ : z = N.adjoin t t :=
        hstepF p t z hpm hpt hpairSuccF
      have hw_eq_succ : w = N.adjoin u u :=
        hstepG p u w hpm hpu hpairSuccG
      rw [hz_eq_succ, hw_eq_succ, htu]
      rfl
  let Em : Nat → α := scons m (scons m (scons s (scons f (scons g tail))))
  let Ez : Nat → α := scons z Em
  let Ewz : Nat → α := scons w Ez
  have hmain : Sat M.mem (scons m (scons s (scons f (scons g tail)))) phi := hall m
  have hmSat : Sat M.mem Em (HF_ordinalLikeAt 0) :=
    (HF_ordinalLikeAt_spec Em 0).mpr hm
  have hfSat : Sat M.mem Em (HF_succRecApproxAt 3 2 0) := by
    apply (FirstOrderAdjunctionModel.HF_succRecApproxAt_spec N Em 3 2 0).mpr
    simpa [N, Em, tail, scons] using hf
  have hgSat : Sat M.mem Em (HF_succRecApproxAt 4 2 0) := by
    apply (FirstOrderAdjunctionModel.HF_succRecApproxAt_spec N Em 4 2 0).mpr
    simpa [N, Em, tail, scons] using hg
  have hzSat : Sat M.mem Ez (HF_pairMemAt 2 0 4) := by
    apply (FirstOrderAdjunctionModel.HF_pairMemAt_spec N Ez 2 0 4).mpr
    simpa [N, Em, Ez, tail, scons] using hz
  have hwSat : Sat M.mem Ewz (HF_pairMemAt 3 0 6) := by
    apply (FirstOrderAdjunctionModel.HF_pairMemAt_spec N Ewz 3 0 6).mpr
    simpa [N, Em, Ez, Ewz, tail, scons] using hw
  exact hmain m (Or.inr rfl) hmSat hfSat hgSat z hzSat w hwSat

end FirstOrderFiniteAdjunctionModel

/-! ## The finite von Neumann ordinals inside Ackermann HF -/

/-- Ackermann code of the finite von Neumann ordinal `n`.

This is deliberately just the recursive set-theoretic construction:
`0 = ∅` and `n+1 = n ∪ {n}`.  The fact that it is an embedding, and the
description of its members, are separate theorems below. -/
def ordinalCode : Nat → Nat
  | 0 => empty
  | n+1 => adjoin (ordinalCode n) (ordinalCode n)

theorem ordinalCode_zero : ordinalCode 0 = empty := rfl

theorem ordinalCode_succ (n : Nat) :
    ordinalCode (n+1) = adjoin (ordinalCode n) (ordinalCode n) := rfl

theorem mem_ordinalCode_succ (x n : Nat) :
    Mem x (ordinalCode (n+1)) ↔ Mem x (ordinalCode n) ∨ x = ordinalCode n := by
  rw [ordinalCode_succ, mem_adjoin]

theorem mem_ordinalCode_iff (x n : Nat) :
    Mem x (ordinalCode n) ↔ ∃ k, k < n ∧ x = ordinalCode k := by
  induction n with
  | zero =>
      constructor
      · intro h
        exact False.elim (mem_empty x h)
      · intro h
        rcases h with ⟨k, hk, _⟩
        omega
  | succ n ih =>
      rw [mem_ordinalCode_succ]
      constructor
      · intro h
        rcases h with h | h
        · rcases ih.mp h with ⟨k, hk, hx⟩
          exact ⟨k, by omega, hx⟩
        · exact ⟨n, by omega, h⟩
      · intro h
        rcases h with ⟨k, hk, hx⟩
        have hle : k ≤ n := Nat.lt_succ_iff.mp hk
        rcases Nat.lt_or_eq_of_le hle with hlt | heq
        · exact Or.inl (ih.mpr ⟨k, hlt, hx⟩)
        · exact Or.inr (by subst heq; exact hx)

theorem ordinalCode_mem_of_lt {k n : Nat} (h : k < n) :
    Mem (ordinalCode k) (ordinalCode n) :=
  (mem_ordinalCode_iff (ordinalCode k) n).mpr ⟨k, h, rfl⟩

theorem ordinalCode_lt_of_lt {k n : Nat} (h : k < n) :
    ordinalCode k < ordinalCode n :=
  mem_lt (ordinalCode_mem_of_lt h)

theorem ordinalCode_transitive (n : Nat) : TransitiveObj Mem (ordinalCode n) := by
  intro y hy x hx
  rcases (mem_ordinalCode_iff y n).mp hy with ⟨k, hk, rfl⟩
  rcases (mem_ordinalCode_iff x k).mp hx with ⟨j, hj, rfl⟩
  exact ordinalCode_mem_of_lt (Nat.lt_trans hj hk)

theorem ordinalCode_members_transitive (n : Nat) :
    ∀ y, Mem y (ordinalCode n) → TransitiveObj Mem y := by
  intro y hy
  rcases (mem_ordinalCode_iff y n).mp hy with ⟨k, _hk, rfl⟩
  exact ordinalCode_transitive k

theorem ordinalCode_memTotalOn (n : Nat) : MemTotalOn Mem (ordinalCode n) := by
  intro y hy z hz
  rcases (mem_ordinalCode_iff y n).mp hy with ⟨j, _hj, rfl⟩
  rcases (mem_ordinalCode_iff z n).mp hz with ⟨k, _hk, rfl⟩
  rcases Nat.lt_trichotomy j k with hlt | heq | hgt
  · exact Or.inl (ordinalCode_mem_of_lt hlt)
  · exact Or.inr (Or.inl (by rw [heq]))
  · exact Or.inr (Or.inr (ordinalCode_mem_of_lt hgt))

theorem ordinalCode_ordinalLike (n : Nat) : OrdinalLike Mem (ordinalCode n) :=
  ⟨ordinalCode_transitive n, ordinalCode_members_transitive n, ordinalCode_memTotalOn n⟩

theorem HF_ordinalLikeAt_of_ordinalCode (e : Nat → Nat) (i n : Nat)
    (h : e i = ordinalCode n) : Sat Mem e (HF_ordinalLikeAt i) :=
  (HF_ordinalLikeAt_spec e i).mpr (by rw [h]; exact ordinalCode_ordinalLike n)

def IsOrdinalCode (a : Nat) : Prop := ∃ n, ordinalCode n = a

theorem ordinalLike_is_ordinalCode (a : Nat)
    (ha : OrdinalLike Mem a) : IsOrdinalCode a := by
  exact Nat.strongRecOn a (fun a ih ha => by
    by_cases hzero : a = empty
    · exact ⟨0, by rw [ordinalCode_zero, ← hzero]⟩
    · obtain ⟨m, hm, hmax⟩ := exists_max_mem_of_ne_empty hzero
      rcases ih m (mem_lt hm) (OrdinalLike.of_mem ha hm) with ⟨k, hk⟩
      refine ⟨k+1, ?_⟩
      apply ext
      intro x
      constructor
      · intro hx
        rcases (mem_ordinalCode_succ x k).mp hx with hxk | hxk
        · have hxm : Mem x m := by
            rwa [hk] at hxk
          exact ha.1 m hm x hxm
        · rw [hxk, hk]
          exact hm
      · intro hx
        rcases ih x (mem_lt hx) (OrdinalLike.of_mem ha hx) with ⟨j, hj⟩
        have hjle : j ≤ k := by
          have hnot : ¬ k < j := by
            intro hkj
            have hlt : m < x := by
              have hlt0 := ordinalCode_lt_of_lt hkj
              rwa [hk, hj] at hlt0
            exact Nat.not_lt_of_ge (hmax x hx) hlt
          omega
        rcases Nat.lt_or_eq_of_le hjle with hjlt | hjeq
        · apply (mem_ordinalCode_succ x k).mpr
          left
          rw [← hj]
          exact ordinalCode_mem_of_lt hjlt
        · apply (mem_ordinalCode_succ x k).mpr
          right
          rw [← hj, hjeq])
    ha

theorem HF_ordinalLikeAt_exact (e : Nat → Nat) (i : Nat) :
    Sat Mem e (HF_ordinalLikeAt i) ↔ IsOrdinalCode (e i) :=
  ⟨fun h => ordinalLike_is_ordinalCode (e i) ((HF_ordinalLikeAt_spec e i).mp h),
   fun h => by
    rcases h with ⟨n, hn⟩
    exact HF_ordinalLikeAt_of_ordinalCode e i n hn.symm⟩

theorem not_mem_self (a : Nat) : ¬ Mem a a := fun h =>
  Nat.lt_irrefl a (mem_lt h)

theorem ordinalCode_injective {m n : Nat}
    (h : ordinalCode m = ordinalCode n) : m = n := by
  rcases Nat.lt_trichotomy m n with hlt | heq | hgt
  · have hm : Mem (ordinalCode m) (ordinalCode n) := ordinalCode_mem_of_lt hlt
    rw [← h] at hm
    exact False.elim (not_mem_self (ordinalCode m) hm)
  · exact heq
  · have hn : Mem (ordinalCode n) (ordinalCode m) := ordinalCode_mem_of_lt hgt
    rw [h] at hn
    exact False.elim (not_mem_self (ordinalCode n) hn)

/-! ### Standard finite traces for successor recursion -/

/-- Iterate the HF successor operation `x ↦ x ∪ {x}` on an object. -/
def succIterObj (s : Nat) : Nat → Nat
  | 0 => s
  | n+1 => adjoin (succIterObj s n) (succIterObj s n)

theorem succIterObj_ordinalCode (m n : Nat) :
    succIterObj (ordinalCode m) n = ordinalCode (m + n) := by
  induction n with
  | zero =>
      simp [succIterObj]
  | succ n ih =>
      rw [succIterObj, ih, Nat.add_succ, ordinalCode_succ]

/-- The finite graph `{⟨0,s⟩, ⟨1,S s⟩, ..., ⟨n,S^n s⟩}` as an HF set. -/
def succRecTrace (s : Nat) : Nat → Nat
  | 0 => single standardModel (kpair standardModel empty s)
  | n+1 =>
      adjoin (succRecTrace s n)
        (kpair standardModel (ordinalCode (n+1)) (succIterObj s (n+1)))

theorem succRecTrace_mem_iff (s p n : Nat) :
    Mem p (succRecTrace s n) ↔
      ∃ k, k ≤ n ∧ p = kpair standardModel (ordinalCode k) (succIterObj s k) := by
  induction n with
  | zero =>
      constructor
      · intro hp
        have hp' := (single_spec standardModel (kpair standardModel empty s) p).mp hp
        exact ⟨0, by omega, by simpa [ordinalCode_zero, succIterObj] using hp'⟩
      · intro hp
        rcases hp with ⟨k, hk, hp⟩
        have hk0 : k = 0 := by omega
        subst k
        apply (single_spec standardModel (kpair standardModel empty s) p).mpr
        simpa [ordinalCode_zero, succIterObj] using hp
  | succ n ih =>
      rw [succRecTrace, mem_adjoin, ih]
      constructor
      · intro hp
        rcases hp with hp | hp
        · rcases hp with ⟨k, hk, hp⟩
          exact ⟨k, by omega, hp⟩
        · exact ⟨n+1, by omega, hp⟩
      · intro hp
        rcases hp with ⟨k, hk, hp⟩
        have hcases : k ≤ n ∨ k = n+1 := by omega
        rcases hcases with hle | heq
        · exact Or.inl ⟨k, hle, hp⟩
        · subst k
          exact Or.inr hp

theorem succRecTrace_pair_mem (s : Nat) {k n : Nat} (hk : k ≤ n) :
    Mem (kpair standardModel (ordinalCode k) (succIterObj s k)) (succRecTrace s n) :=
  (succRecTrace_mem_iff s _ n).mpr ⟨k, hk, rfl⟩

theorem succRecTrace_functional (s n : Nat) :
    PairFunctional standardModel (succRecTrace s n) := by
  intro k y y' hky hky'
  rcases (succRecTrace_mem_iff s _ n).mp hky with ⟨i, _hi, hpair_i⟩
  rcases (succRecTrace_mem_iff s _ n).mp hky' with ⟨j, _hj, hpair_j⟩
  have hcomp_i := kpair_injective standardModel hpair_i
  have hcomp_j := kpair_injective standardModel hpair_j
  have hij : i = j := by
    apply ordinalCode_injective
    exact hcomp_i.1.symm.trans hcomp_j.1
  rw [hcomp_i.2, hcomp_j.2, hij]

theorem succRecTrace_keysBelowSucc (s n : Nat) :
    PairKeysBelowSucc standardModel (succRecTrace s n) (ordinalCode n) := by
  intro k y hky
  rcases (succRecTrace_mem_iff s _ n).mp hky with ⟨i, hi, hpair_i⟩
  have hcomp_i := kpair_injective standardModel hpair_i
  rw [hcomp_i.1]
  rcases Nat.lt_or_eq_of_le hi with hlt | heq
  · exact Or.inl (ordinalCode_mem_of_lt hlt)
  · exact Or.inr (by rw [heq])

theorem succRecTrace_totalBelowSucc (s n : Nat) :
    PairTotalBelowSucc standardModel (succRecTrace s n) (ordinalCode n) := by
  intro k hk
  rcases hk with hmem | heq
  · rcases (mem_ordinalCode_iff k n).mp hmem with ⟨i, hi, rfl⟩
    exact ⟨succIterObj s i, succRecTrace_pair_mem s (Nat.le_of_lt hi)⟩
  · rw [heq]
    exact ⟨succIterObj s n, succRecTrace_pair_mem s (Nat.le_refl n)⟩

theorem succRecTrace_succStep (s n : Nat) :
    PairSuccStep standardModel (succRecTrace s n) (ordinalCode n) := by
  intro k t y hkm hkt hsy
  rcases (mem_ordinalCode_iff k n).mp hkm with ⟨i, _hi, hk⟩
  rcases (succRecTrace_mem_iff s _ n).mp hkt with ⟨j, _hj, hpair_j⟩
  have hcomp_j := kpair_injective standardModel hpair_j
  have hij : i = j := by
    apply ordinalCode_injective
    exact hk.symm.trans hcomp_j.1
  have ht : t = succIterObj s i := by
    rw [hcomp_j.2, ← hij]
  have hsucck : adjoin k k = ordinalCode (i+1) := by
    rw [hk, ordinalCode_succ]
  rcases (succRecTrace_mem_iff s _ n).mp hsy with ⟨l, _hl, hpair_l⟩
  have hcomp_l := kpair_injective standardModel hpair_l
  have hil : i+1 = l := by
    apply ordinalCode_injective
    exact hsucck.symm.trans hcomp_l.1
  have hy : y = succIterObj s (i+1) := by
    rw [hcomp_l.2, ← hil]
  rw [hy, ht, succIterObj]
  rfl

theorem succRecTrace_succRecApprox (s n : Nat) :
    SuccRecApprox standardModel s (succRecTrace s n) (ordinalCode n) := by
  refine ⟨succRecTrace_functional s n,
    succRecTrace_keysBelowSucc s n,
    ?_,
    succRecTrace_totalBelowSucc s n,
    succRecTrace_succStep s n⟩
  change Mem (kpair standardModel empty s) (succRecTrace s n)
  simpa [ordinalCode_zero, succIterObj] using
    (succRecTrace_pair_mem s (k := 0) (n := n) (Nat.zero_le n))

theorem succRecApprox_value_of_le (s f : Nat) :
    ∀ n N y,
      SuccRecApprox standardModel s f (ordinalCode N) →
      n ≤ N →
      Mem (kpair standardModel (ordinalCode n) y) f →
      y = succIterObj s n := by
  intro n
  induction n with
  | zero =>
      intro N y hA _hn hy
      rcases hA with ⟨hfun, _hkeys, hbase, _htotal, _hstep⟩
      have hbase' : Mem (kpair standardModel (ordinalCode 0) s) f := by
        simpa [standardModel, ordinalCode_zero] using hbase
      have hy_eq := hfun (ordinalCode 0) y s hy hbase'
      simpa [succIterObj] using hy_eq
  | succ n ih =>
      intro N y hA hn hy
      have hA' := hA
      rcases hA with ⟨_hfun, _hkeys, _hbase, htotal, hstep⟩
      have hnlt : n < N := by omega
      rcases htotal (ordinalCode n) (Or.inl (ordinalCode_mem_of_lt hnlt)) with ⟨t, ht⟩
      have htval := ih N t hA' (Nat.le_of_lt hnlt) ht
      have hysucc :
          Mem (kpair standardModel (adjoin (ordinalCode n) (ordinalCode n)) y) f := by
        rw [← ordinalCode_succ]
        exact hy
      have hstepval := hstep (ordinalCode n) t y
        (ordinalCode_mem_of_lt hnlt) ht hysucc
      rw [hstepval, htval, succIterObj]
      rfl

/-! ### Standard finite traces for multiplication recursion -/

/-- The finite graph `{⟨0,0⟩, ⟨1,m⟩, ..., ⟨n,m*n⟩}` as an HF set. -/
def mulRecTrace (m : Nat) : Nat → Nat
  | 0 => single standardModel (kpair standardModel empty empty)
  | n+1 =>
      adjoin (mulRecTrace m n)
        (kpair standardModel (ordinalCode (n+1)) (ordinalCode (m * (n+1))))

theorem mulRecTrace_mem_iff (m p n : Nat) :
    Mem p (mulRecTrace m n) ↔
      ∃ k, k ≤ n ∧ p = kpair standardModel (ordinalCode k) (ordinalCode (m * k)) := by
  induction n with
  | zero =>
      constructor
      · intro hp
        have hp' := (single_spec standardModel (kpair standardModel empty empty) p).mp hp
        exact ⟨0, by omega, by simpa [ordinalCode_zero] using hp'⟩
      · intro hp
        rcases hp with ⟨k, hk, hp⟩
        have hk0 : k = 0 := by omega
        subst k
        apply (single_spec standardModel (kpair standardModel empty empty) p).mpr
        simpa [ordinalCode_zero] using hp
  | succ n ih =>
      rw [mulRecTrace, mem_adjoin, ih]
      constructor
      · intro hp
        rcases hp with hp | hp
        · rcases hp with ⟨k, hk, hp⟩
          exact ⟨k, by omega, hp⟩
        · exact ⟨n+1, by omega, hp⟩
      · intro hp
        rcases hp with ⟨k, hk, hp⟩
        have hcases : k ≤ n ∨ k = n+1 := by omega
        rcases hcases with hle | heq
        · exact Or.inl ⟨k, hle, hp⟩
        · subst k
          exact Or.inr hp

theorem mulRecTrace_pair_mem (m : Nat) {k n : Nat} (hk : k ≤ n) :
    Mem (kpair standardModel (ordinalCode k) (ordinalCode (m * k))) (mulRecTrace m n) :=
  (mulRecTrace_mem_iff m _ n).mpr ⟨k, hk, rfl⟩

theorem mulRecTrace_functional (m n : Nat) :
    PairFunctional standardModel (mulRecTrace m n) := by
  intro k y y' hky hky'
  rcases (mulRecTrace_mem_iff m _ n).mp hky with ⟨i, _hi, hpair_i⟩
  rcases (mulRecTrace_mem_iff m _ n).mp hky' with ⟨j, _hj, hpair_j⟩
  have hcomp_i := kpair_injective standardModel hpair_i
  have hcomp_j := kpair_injective standardModel hpair_j
  have hij : i = j := by
    apply ordinalCode_injective
    exact hcomp_i.1.symm.trans hcomp_j.1
  rw [hcomp_i.2, hcomp_j.2, hij]

theorem mulRecTrace_keysBelowSucc (m n : Nat) :
    PairKeysBelowSucc standardModel (mulRecTrace m n) (ordinalCode n) := by
  intro k y hky
  rcases (mulRecTrace_mem_iff m _ n).mp hky with ⟨i, hi, hpair_i⟩
  have hcomp_i := kpair_injective standardModel hpair_i
  rw [hcomp_i.1]
  rcases Nat.lt_or_eq_of_le hi with hlt | heq
  · exact Or.inl (ordinalCode_mem_of_lt hlt)
  · exact Or.inr (by rw [heq])

theorem mulRecTrace_totalBelowSucc (m n : Nat) :
    PairTotalBelowSucc standardModel (mulRecTrace m n) (ordinalCode n) := by
  intro k hk
  rcases hk with hmem | heq
  · rcases (mem_ordinalCode_iff k n).mp hmem with ⟨i, hi, rfl⟩
    exact ⟨ordinalCode (m * i), mulRecTrace_pair_mem m (Nat.le_of_lt hi)⟩
  · rw [heq]
    exact ⟨ordinalCode (m * n), mulRecTrace_pair_mem m (Nat.le_refl n)⟩

/-! ### First PA-in-HF interpretation formulas already available -/

namespace PAInHF

/-- Domain formula for the PA interpretation in HF: finite ordinals. -/
def domainForm : Form := HF_ordinalLikeAt 0

/-- Graph formula for PA zero in HF.  Slot `0` is the candidate output. -/
def zeroGraph : Form := HF_emptyAt 0

/-- Graph formula for PA successor in HF.  Slot `0` is the output and slot `1`
is the input. -/
def succGraph : Form := HF_succAt 0 1

/-- Addition graph formula at arbitrary slots: `out = left + right`.  The
witness is a finite successor-recursion graph from `left` through `right`. -/
def addGraphAt (out left right : Nat) : Form :=
  fEx (fAnd (HF_succRecApproxAt 0 (left+1) (right+1))
    (HF_pairMemAt (right+1) (out+1) 0))

/-- Graph formula for PA addition in HF.  Slot `0` is the output, slot `1`
is the left input, and slot `2` is the right input. -/
def addGraph : Form := addGraphAt 0 1 2

/-- Step clause for multiplication recursion: if `f(k)=t` and `f(k+1)=y`,
then `y = t + a`, where `a` is the fixed left multiplicand. -/
def mulStepAt (f a m : Nat) : Form :=
  fAll (fAll (fAll
    (fImp
      (fMem 2 (m+3))
      (fImp
        (HF_pairMemAt 2 1 (f+3))
        (fAll
          (fImp
            (HF_succAt 0 3)
            (fImp
              (HF_pairMemAt 0 1 (f+4))
              (addGraphAt 1 2 (a+4)))))))))

/-- Formula macro for a finite multiplication-recursion trace.  Slot `f` is
the graph of `k ↦ a*k`, defined on keys up to slot `m`. -/
def mulRecApproxAt (f a m : Nat) : Form :=
  fAnd (HF_pairFunctionalAt f)
    (fAnd (HF_pairKeysBelowSuccAt f m)
      (fAnd (HF_pairZeroBaseAt f)
        (fAnd (HF_pairTotalBelowSuccAt f m)
          (mulStepAt f a m))))

/-- Multiplication graph formula at arbitrary slots: `out = left * right`. -/
def mulGraphAt (out left right : Nat) : Form :=
  fEx (fAnd (mulRecApproxAt 0 (left+1) (right+1))
    (HF_pairMemAt (right+1) (out+1) 0))

/-- Graph formula for PA multiplication in HF.  Slot `0` is the output, slot
`1` is the left input, and slot `2` is the right input. -/
def mulGraph : Form := mulGraphAt 0 1 2

/-- Totality formula for a multiplication-recursion trace.  Slot `a` is the
fixed left multiplicand and slot `m` is the right multiplicand/key. -/
def mulRecTotalAt (a m : Nat) : Form :=
  fEx (fEx (fAnd
    (mulRecApproxAt 1 (a+2) (m+2))
    (HF_pairMemAt (m+2) 0 1)))

/-- Multiplication-recursion totality, relativized to ordinal-like right
inputs.  The left multiplicand remains an explicit parameter. -/
def mulRecTotalOnOrdinalAt (a m : Nat) : Form :=
  fImp (HF_ordinalLikeAt m) (mulRecTotalAt a m)

/-- Semantic step clause for multiplication recursion in a chosen first-order
HF model: when `f(k)=t` and `f(k+1)=y`, the value `y` is obtained from an
addition trace for `t+a`. -/
def MulStep {α : Type u} (M : FirstOrderAdjunctionModel α)
    (f a m : α) : Prop :=
  ∀ k t y,
    M.mem k m →
    M.mem (FirstOrderAdjunctionModel.kpair M k t) f →
    M.mem (FirstOrderAdjunctionModel.kpair M (M.adjoin k k) y) f →
    ∃ g,
      FirstOrderAdjunctionModel.SuccRecApprox M t g a ∧
        M.mem (FirstOrderAdjunctionModel.kpair M a y) g

/-- Semantic package for a finite multiplication-recursion trace in a chosen
first-order HF model. -/
def MulRecApprox {α : Type u} (M : FirstOrderAdjunctionModel α)
    (a f m : α) : Prop :=
  FirstOrderAdjunctionModel.PairFunctional M f ∧
  FirstOrderAdjunctionModel.PairKeysBelowSucc M f m ∧
  M.mem (FirstOrderAdjunctionModel.kpair M M.empty M.empty) f ∧
  FirstOrderAdjunctionModel.PairTotalBelowSucc M f m ∧
  MulStep M f a m

/-- Total multiplication-recursion data through a key `m`: a trace plus its
value at `m`. -/
def MulRecTotal {α : Type u} (M : FirstOrderAdjunctionModel α)
    (a m : α) : Prop :=
  ∃ f z, MulRecApprox M a f m ∧
    M.mem (FirstOrderAdjunctionModel.kpair M m z) f

theorem domainForm_free {i : Nat} (h : Free i domainForm) : i = 0 := by
  exact HF_ordinalLikeAt_free h

theorem zeroGraph_free {i : Nat} (h : Free i zeroGraph) : i = 0 := by
  exact HF_emptyAt_free h

theorem succGraph_free {i : Nat} (h : Free i succGraph) : i = 0 ∨ i = 1 := by
  exact HF_succAt_free h

theorem addGraphAt_free {i out left right : Nat}
    (h : Free i (addGraphAt out left right)) : i = out ∨ i = left ∨ i = right := by
  simp only [addGraphAt, Free] at h
  rcases h with h | h
  · have hs := HF_succRecApproxAt_free h
    omega
  · have hp := HF_pairMemAt_free h
    omega

theorem addGraph_free {i : Nat} (h : Free i addGraph) : i = 0 ∨ i = 1 ∨ i = 2 := by
  exact addGraphAt_free h

theorem mulStepAt_free {i f a m : Nat} (h : Free i (mulStepAt f a m)) :
    i = f ∨ i = a ∨ i = m := by
  simp only [mulStepAt, Free] at h
  rcases h with h | h
  · omega
  · rcases h with h | h
    · have hp := HF_pairMemAt_free h
      omega
    · rcases h with h | h
      · have hs := HF_succAt_free h
        omega
      · rcases h with h | h
        · have hp := HF_pairMemAt_free h
          omega
        · have ha := addGraphAt_free h
          omega

theorem mulRecApproxAt_free {i f a m : Nat} (h : Free i (mulRecApproxAt f a m)) :
    i = f ∨ i = a ∨ i = m := by
  simp only [mulRecApproxAt, Free] at h
  rcases h with h | h
  · have hf := HF_pairFunctionalAt_free h
    omega
  · rcases h with h | h
    · have hfm := HF_pairKeysBelowSuccAt_free h
      omega
    · rcases h with h | h
      · have hf := HF_pairZeroBaseAt_free h
        omega
      · rcases h with h | h
        · have hfm := HF_pairTotalBelowSuccAt_free h
          omega
        · have hstep := mulStepAt_free h
          omega

theorem mulGraphAt_free {i out left right : Nat}
    (h : Free i (mulGraphAt out left right)) : i = out ∨ i = left ∨ i = right := by
  simp only [mulGraphAt, Free] at h
  rcases h with h | h
  · have hm := mulRecApproxAt_free h
    omega
  · have hp := HF_pairMemAt_free h
    omega

theorem mulGraph_free {i : Nat} (h : Free i mulGraph) : i = 0 ∨ i = 1 ∨ i = 2 := by
  exact mulGraphAt_free h

theorem mulStepAt_spec {α : Type u} (M : FirstOrderAdjunctionModel α)
    (e : Nat → α) (f a m : Nat) :
    Sat M.mem e (mulStepAt f a m) ↔ MulStep M (e f) (e a) (e m) := by
  constructor
  · intro h k t y hkm hkt hsky
    let sk := M.adjoin k k
    let Ekty := scons y (scons t (scons k e))
    let Eskty := scons sk Ekty
    have hktSat : Sat M.mem Ekty (HF_pairMemAt 2 1 (f+3)) := by
      apply (FirstOrderAdjunctionModel.HF_pairMemAt_spec M Ekty 2 1 (f+3)).mpr
      change M.mem (FirstOrderAdjunctionModel.kpair M k t) (e f)
      exact hkt
    have hskSat : Sat M.mem Eskty (HF_succAt 0 3) := by
      apply (FirstOrderAdjunctionModel.HF_succAt_spec M Eskty 0 3).mpr
      change sk = M.adjoin k k
      rfl
    have hskySat : Sat M.mem Eskty (HF_pairMemAt 0 1 (f+4)) := by
      apply (FirstOrderAdjunctionModel.HF_pairMemAt_spec M Eskty 0 1 (f+4)).mpr
      change M.mem (FirstOrderAdjunctionModel.kpair M sk y) (e f)
      exact hsky
    rcases h k t y hkm hktSat sk hskSat hskySat with ⟨g, hg, hy⟩
    have hg' := (FirstOrderAdjunctionModel.HF_succRecApproxAt_spec M
      (scons g Eskty) 0 3 (a+5)).mp hg
    have hy' := (FirstOrderAdjunctionModel.HF_pairMemAt_spec M
      (scons g Eskty) (a+5) 2 0).mp hy
    refine ⟨g, ?_, ?_⟩
    · change FirstOrderAdjunctionModel.SuccRecApprox M t g (e a) at hg'
      exact hg'
    · change M.mem (FirstOrderAdjunctionModel.kpair M (e a) y) g at hy'
      exact hy'
  · intro h k t y hkm hkt sk hsk hsky
    have hsk' : sk = M.adjoin k k :=
      (FirstOrderAdjunctionModel.HF_succAt_spec M
        (scons sk (scons y (scons t (scons k e)))) 0 3).mp hsk
    have hkt' : M.mem (FirstOrderAdjunctionModel.kpair M k t) (e f) := by
      exact (FirstOrderAdjunctionModel.HF_pairMemAt_spec M
        (scons y (scons t (scons k e))) 2 1 (f+3)).mp hkt
    have hsky' : M.mem
        (FirstOrderAdjunctionModel.kpair M (M.adjoin k k) y) (e f) := by
      have hp := (FirstOrderAdjunctionModel.HF_pairMemAt_spec M
        (scons sk (scons y (scons t (scons k e)))) 0 1 (f+4)).mp hsky
      rwa [hsk'] at hp
    rcases h k t y hkm hkt' hsky' with ⟨g, hg, hy⟩
    refine ⟨g, ?_, ?_⟩
    · apply (FirstOrderAdjunctionModel.HF_succRecApproxAt_spec M
        (scons g (scons sk (scons y (scons t (scons k e))))) 0 3 (a+5)).mpr
      change FirstOrderAdjunctionModel.SuccRecApprox M t g (e a)
      exact hg
    · apply (FirstOrderAdjunctionModel.HF_pairMemAt_spec M
        (scons g (scons sk (scons y (scons t (scons k e))))) (a+5) 2 0).mpr
      change M.mem (FirstOrderAdjunctionModel.kpair M (e a) y) g
      exact hy

theorem mulRecApproxAt_spec {α : Type u} (M : FirstOrderAdjunctionModel α)
    (e : Nat → α) (f a m : Nat) :
    Sat M.mem e (mulRecApproxAt f a m) ↔
      MulRecApprox M (e a) (e f) (e m) := by
  change
    (Sat M.mem e (HF_pairFunctionalAt f) ∧
      (Sat M.mem e (HF_pairKeysBelowSuccAt f m) ∧
        (Sat M.mem e (HF_pairZeroBaseAt f) ∧
          (Sat M.mem e (HF_pairTotalBelowSuccAt f m) ∧
            Sat M.mem e (mulStepAt f a m))))) ↔
      FirstOrderAdjunctionModel.PairFunctional M (e f) ∧
        FirstOrderAdjunctionModel.PairKeysBelowSucc M (e f) (e m) ∧
          M.mem (FirstOrderAdjunctionModel.kpair M M.empty M.empty) (e f) ∧
            FirstOrderAdjunctionModel.PairTotalBelowSucc M (e f) (e m) ∧
              MulStep M (e f) (e a) (e m)
  rw [
    FirstOrderAdjunctionModel.HF_pairFunctionalAt_spec M e f,
    FirstOrderAdjunctionModel.HF_pairKeysBelowSuccAt_spec M e f m,
    FirstOrderAdjunctionModel.HF_pairZeroBaseAt_spec M e f,
    FirstOrderAdjunctionModel.HF_pairTotalBelowSuccAt_spec M e f m,
    mulStepAt_spec M e f a m]

theorem mulRecTotalAt_spec {α : Type u} (M : FirstOrderAdjunctionModel α)
    (e : Nat → α) (a m : Nat) :
    Sat M.mem e (mulRecTotalAt a m) ↔
      MulRecTotal M (e a) (e m) := by
  constructor
  · intro h
    rcases h with ⟨f, z, hf, hz⟩
    have hf' := (mulRecApproxAt_spec M (scons z (scons f e))
      1 (a+2) (m+2)).mp hf
    have hz' := (FirstOrderAdjunctionModel.HF_pairMemAt_spec M
      (scons z (scons f e)) (m+2) 0 1).mp hz
    change MulRecApprox M (e a) f (e m) at hf'
    change M.mem (FirstOrderAdjunctionModel.kpair M (e m) z) f at hz'
    exact ⟨f, z, hf', hz'⟩
  · intro h
    rcases h with ⟨f, z, hf, hz⟩
    refine ⟨f, z, ?_, ?_⟩
    · apply (mulRecApproxAt_spec M (scons z (scons f e))
        1 (a+2) (m+2)).mpr
      change MulRecApprox M (e a) f (e m)
      exact hf
    · apply (FirstOrderAdjunctionModel.HF_pairMemAt_spec M
        (scons z (scons f e)) (m+2) 0 1).mpr
      change M.mem (FirstOrderAdjunctionModel.kpair M (e m) z) f
      exact hz

theorem mulRecTotalOnOrdinalAt_spec {α : Type u}
    (M : FirstOrderAdjunctionModel α) (e : Nat → α) (a m : Nat) :
    Sat M.mem e (mulRecTotalOnOrdinalAt a m) ↔
      (OrdinalLike M.mem (e m) → MulRecTotal M (e a) (e m)) := by
  constructor
  · intro h hm
    exact (mulRecTotalAt_spec M e a m).mp
      (h ((HF_ordinalLikeAt_spec e m).mpr hm))
  · intro h hmSat
    exact (mulRecTotalAt_spec M e a m).mpr
      (h ((HF_ordinalLikeAt_spec e m).mp hmSat))

theorem zeroMulRecGraph_mulRecApprox {α : Type u}
    (M : FirstOrderAdjunctionModel α) (a : α) :
    MulRecApprox M a (FirstOrderAdjunctionModel.zeroSuccRecGraph M M.empty) M.empty := by
  have hf : FirstOrderAdjunctionModel.SuccRecApprox M M.empty
      (FirstOrderAdjunctionModel.zeroSuccRecGraph M M.empty) M.empty :=
    FirstOrderAdjunctionModel.zeroSuccRecGraph_succRecApprox M M.empty
  rcases hf with ⟨hfun, hkeys, hbase, htotal, _hstep⟩
  refine ⟨hfun, hkeys, hbase, htotal, ?_⟩
  intro k _t _y hkm _ _
  exact False.elim (M.empty_spec k hkm)

theorem mulRecTotal_empty {α : Type u}
    (M : FirstOrderAdjunctionModel α) (a : α) :
    MulRecTotal M a M.empty := by
  exact ⟨FirstOrderAdjunctionModel.zeroSuccRecGraph M M.empty, M.empty,
    zeroMulRecGraph_mulRecApprox M a,
    FirstOrderAdjunctionModel.zeroSuccRecGraph_base M M.empty⟩

/-- Extend a multiplication-recursion graph by an arbitrary next value. -/
def mulRecGraphSucc {α : Type u} (M : FirstOrderAdjunctionModel α)
    (f m y : α) : α :=
  M.adjoin f (FirstOrderAdjunctionModel.kpair M (M.adjoin m m) y)

theorem mulRecGraphSucc_old {α : Type u} (M : FirstOrderAdjunctionModel α)
    {f m y p : α} (hp : M.mem p f) :
    M.mem p (mulRecGraphSucc M f m y) :=
  (M.adjoin_spec p f
    (FirstOrderAdjunctionModel.kpair M (M.adjoin m m) y)).mpr (Or.inl hp)

theorem mulRecGraphSucc_new {α : Type u} (M : FirstOrderAdjunctionModel α)
    (f m y : α) :
    M.mem (FirstOrderAdjunctionModel.kpair M (M.adjoin m m) y)
      (mulRecGraphSucc M f m y) :=
  (M.adjoin_spec (FirstOrderAdjunctionModel.kpair M (M.adjoin m m) y)
    f (FirstOrderAdjunctionModel.kpair M (M.adjoin m m) y)).mpr (Or.inr rfl)

theorem mulRecGraphSucc_mulRecApprox {α : Type u}
    (M : FirstOrderAdjunctionModel α) {a f m z y : α}
    (hm : OrdinalLike M.mem m)
    (hf : MulRecApprox M a f m)
    (hz : M.mem (FirstOrderAdjunctionModel.kpair M m z) f)
    (hadd : ∃ g,
      FirstOrderAdjunctionModel.SuccRecApprox M z g a ∧
        M.mem (FirstOrderAdjunctionModel.kpair M a y) g) :
    MulRecApprox M a (mulRecGraphSucc M f m y) (M.adjoin m m) := by
  rcases hf with ⟨hfun, hkeys, hbase, htotal, hstep⟩
  let sm := M.adjoin m m
  let newPair := FirstOrderAdjunctionModel.kpair M sm y
  let g := mulRecGraphSucc M f m y
  have hsm_not_mem : ¬ M.mem sm m := by
    simpa [sm] using
      FirstOrderAdjunctionModel.adjoin_self_not_mem_of_ordinalLike M hm
  have hsm_ne_m : sm ≠ m := by
    simpa [sm] using FirstOrderAdjunctionModel.adjoin_self_ne_self M m
  have hmem_g : ∀ p, M.mem p g ↔ M.mem p f ∨ p = newPair := by
    intro p
    exact M.adjoin_spec p f newPair
  have old_key_ne_succ :
      ∀ {k y'}, M.mem (FirstOrderAdjunctionModel.kpair M k y') f → k ≠ sm := by
    intro k y' hOld hk
    have hkBound := hkeys k y' hOld
    rw [hk] at hkBound
    rcases hkBound with hmem | heq
    · exact hsm_not_mem hmem
    · exact hsm_ne_m heq
  have pair_old_of_mem_key :
      ∀ {k y'}, M.mem k m →
        M.mem (FirstOrderAdjunctionModel.kpair M k y') g →
          M.mem (FirstOrderAdjunctionModel.kpair M k y') f := by
    intro k y' hkm hkg
    rcases (hmem_g (FirstOrderAdjunctionModel.kpair M k y')).mp hkg with
      hOld | hNew
    · exact hOld
    · have hk : k = sm := (FirstOrderAdjunctionModel.kpair_injective M hNew).1
      rw [hk] at hkm
      exact False.elim (hsm_not_mem hkm)
  refine ⟨?functional, ?keys, ?base, ?total, ?step⟩
  · intro k u v hku hkv
    rcases (hmem_g (FirstOrderAdjunctionModel.kpair M k u)).mp hku with
      hOld | hNew
    · rcases (hmem_g (FirstOrderAdjunctionModel.kpair M k v)).mp hkv with
        hOld' | hNew'
      · exact hfun k u v hOld hOld'
      · have hk : k = sm := (FirstOrderAdjunctionModel.kpair_injective M hNew').1
        exact False.elim (old_key_ne_succ hOld hk)
    · rcases (hmem_g (FirstOrderAdjunctionModel.kpair M k v)).mp hkv with
        hOld' | hNew'
      · have hk : k = sm := (FirstOrderAdjunctionModel.kpair_injective M hNew).1
        exact False.elim (old_key_ne_succ hOld' hk)
      · have hu : u = y := (FirstOrderAdjunctionModel.kpair_injective M hNew).2
        have hv : v = y := (FirstOrderAdjunctionModel.kpair_injective M hNew').2
        rw [hu, hv]
  · intro k u hku
    rcases (hmem_g (FirstOrderAdjunctionModel.kpair M k u)).mp hku with
      hOld | hNew
    · rcases hkeys k u hOld with hkm | hkm
      · exact Or.inl ((M.adjoin_spec k m m).mpr (Or.inl hkm))
      · exact Or.inl ((M.adjoin_spec k m m).mpr (Or.inr hkm))
    · exact Or.inr (FirstOrderAdjunctionModel.kpair_injective M hNew).1
  · exact mulRecGraphSucc_old M hbase
  · intro k hk
    rcases hk with hksm | hksm
    · rcases (M.adjoin_spec k m m).mp hksm with hkm | hkm
      · rcases htotal k (Or.inl hkm) with ⟨u, hu⟩
        exact ⟨u, mulRecGraphSucc_old M hu⟩
      · rcases htotal k (Or.inr hkm) with ⟨u, hu⟩
        exact ⟨u, mulRecGraphSucc_old M hu⟩
    · subst k
      exact ⟨y, mulRecGraphSucc_new M f m y⟩
  · intro k t out hksm hkt hsky
    rcases (M.adjoin_spec k m m).mp hksm with hkm | hkm
    · have hktOld : M.mem (FirstOrderAdjunctionModel.kpair M k t) f :=
        pair_old_of_mem_key hkm hkt
      have hskyOld :
          M.mem (FirstOrderAdjunctionModel.kpair M (M.adjoin k k) out) f := by
        rcases (hmem_g
            (FirstOrderAdjunctionModel.kpair M (M.adjoin k k) out)).mp hsky with
          hOld | hNew
        · exact hOld
        · have hsk : M.adjoin k k = sm :=
            (FirstOrderAdjunctionModel.kpair_injective M hNew).1
          have hkOrd : OrdinalLike M.mem k := OrdinalLike.of_mem hm hkm
          have hkm_eq : k = m :=
            FirstOrderAdjunctionModel.adjoin_self_injective_on_ordinalLike
              M hkOrd hm (by simpa [sm] using hsk)
          rw [hkm_eq] at hkm
          exact False.elim (FirstOrderAdjunctionModel.mem_irrefl M m hkm)
      exact hstep k t out hkm hktOld hskyOld
    · subst k
      have hktOld :
          M.mem (FirstOrderAdjunctionModel.kpair M m t) f := by
        rcases (hmem_g (FirstOrderAdjunctionModel.kpair M m t)).mp hkt with
          hOld | hNew
        · exact hOld
        · have hm_eq_sm : m = sm :=
            (FirstOrderAdjunctionModel.kpair_injective M hNew).1
          exact False.elim (hsm_ne_m hm_eq_sm.symm)
      have ht : t = z := hfun m t z hktOld hz
      rcases (hmem_g (FirstOrderAdjunctionModel.kpair M sm out)).mp hsky with
        hOld | hNew
      · exact False.elim (old_key_ne_succ hOld rfl)
      · have hout : out = y :=
          (FirstOrderAdjunctionModel.kpair_injective M hNew).2
        rw [ht, hout]
        exact hadd

theorem mulRecTotal_succ_of_addTotal {α : Type u}
    (M : FirstOrderAdjunctionModel α) {a m : α}
    (hm : OrdinalLike M.mem m)
    (hAddTotal : ∀ s, FirstOrderAdjunctionModel.SuccRecTotal M s a)
    (ht : MulRecTotal M a m) :
    MulRecTotal M a (M.adjoin m m) := by
  rcases ht with ⟨f, z, hf, hz⟩
  rcases hAddTotal z with ⟨g, y, hg, hy⟩
  exact ⟨mulRecGraphSucc M f m y, y,
    mulRecGraphSucc_mulRecApprox M hm hf hz ⟨g, hg, hy⟩,
    mulRecGraphSucc_new M f m y⟩

theorem mulRecTotal_of_ordinalLike_of_predecessor {α : Type u}
    (M : FirstOrderAdjunctionModel α)
    (hPred : ∀ a, OrdinalLike M.mem a →
      a = M.empty ∨ ∃ p, M.mem p a ∧ a = M.adjoin p p)
    (hAddTotal : ∀ s m, OrdinalLike M.mem m →
      FirstOrderAdjunctionModel.SuccRecTotal M s m)
    (a m : α) (ha : OrdinalLike M.mem a) (hm : OrdinalLike M.mem m) :
    MulRecTotal M a m := by
  let phi : Form := mulRecTotalOnOrdinalAt 1 0
  let tail : Nat → α := fun _ => a
  have hind := M.induction_schema phi (scons a tail)
  have hall : ∀ b, Sat M.mem (scons b (scons a tail)) phi := by
    apply hind
    intro b ih
    apply (mulRecTotalOnOrdinalAt_spec M
      (scons b (scons a tail)) 1 0).mpr
    intro hb
    rcases hPred b hb with hbEmpty | ⟨p, hpb, hbSucc⟩
    · rw [hbEmpty]
      exact mulRecTotal_empty M a
    · have hpOrd : OrdinalLike M.mem p := OrdinalLike.of_mem hb hpb
      have hpSat : Sat M.mem (scons p (scons a tail)) phi :=
        (Sat_rename_rSkipParam phi (scons a tail) b p).mp (ih p hpb)
      have hpTotal : MulRecTotal M a p := by
        simpa [phi, tail, scons] using
          ((mulRecTotalOnOrdinalAt_spec M
            (scons p (scons a tail)) 1 0).mp hpSat hpOrd)
      rw [hbSucc]
      exact mulRecTotal_succ_of_addTotal M hpOrd
        (fun s => hAddTotal s a ha) hpTotal
  simpa [phi, tail, scons] using
    ((mulRecTotalOnOrdinalAt_spec M
      (scons m (scons a tail)) 1 0).mp (hall m) hm)

theorem mulRecTotal_of_ordinalLike_finite_model {α : Type u}
    (M : FirstOrderFiniteAdjunctionModel α)
    (a m : α) (ha : OrdinalLike M.mem a) (hm : OrdinalLike M.mem m) :
    MulRecTotal M.toFirstOrderAdjunctionModel a m := by
  apply mulRecTotal_of_ordinalLike_of_predecessor M.toFirstOrderAdjunctionModel
  · intro b hb
    exact FirstOrderFiniteAdjunctionModel.ordinalLike_empty_or_succ M hb
  · intro s r hr
    exact FirstOrderFiniteAdjunctionModel.succRecTotal_of_ordinalLike M s r hr
  · exact ha
  · exact hm

/-- In finite HF, a multiplication-recursion trace with ordinal-like
multiplicand and endpoint assigns ordinal-like values to every covered key.

The multiplication step delegates to the successor-recursion closure theorem:
if the previous product `t` is ordinal-like, then the addition trace computing
`t + a` has an ordinal-like output. -/
theorem mulRecApprox_value_ordinalLike {α : Type u}
    (M : FirstOrderFiniteAdjunctionModel α) {a f m z : α}
    (ha : OrdinalLike M.mem a) (hm : OrdinalLike M.mem m)
    (hf : MulRecApprox M.toFirstOrderAdjunctionModel a f m)
    (hz : M.mem (FirstOrderAdjunctionModel.kpair
      M.toFirstOrderAdjunctionModel m z) f) :
    OrdinalLike M.mem z := by
  let N := M.toFirstOrderAdjunctionModel
  let phi : Form :=
    fAll
      (fImp (fOr (fMem 1 0) (fEq 1 0))
        (fImp (HF_ordinalLikeAt 0)
          (fImp (mulRecApproxAt 3 2 0)
            (fAll (fImp (HF_pairMemAt 2 0 4) (HF_ordinalLikeAt 0))))))
  let tail : Nat → α := fun _ => M.empty
  have hind := M.induction_schema phi (scons a (scons f tail))
  have hall : ∀ k, Sat M.mem (scons k (scons a (scons f tail))) phi := by
    apply hind
    intro k ih
    intro m hkey hmSat hfSat z hpairSat
    let Em : Nat → α := scons m (scons k (scons a (scons f tail)))
    let Ez : Nat → α := scons z Em
    have hmOrd : OrdinalLike M.mem m :=
      (HF_ordinalLikeAt_spec Em 0).mp hmSat
    have hfApprox : MulRecApprox N a f m := by
      simpa [N, Em, tail, scons] using
        (mulRecApproxAt_spec N Em 3 2 0).mp hfSat
    have hpair : N.mem (FirstOrderAdjunctionModel.kpair N k z) f := by
      simpa [N, Em, Ez, tail, scons] using
        (FirstOrderAdjunctionModel.HF_pairMemAt_spec N Ez 2 0 4).mp hpairSat
    have hkOrd : OrdinalLike M.mem k := by
      rcases hkey with hkm | hkm
      · change M.mem k m at hkm
        exact OrdinalLike.of_mem hmOrd hkm
      · change k = m at hkm
        subst k
        exact hmOrd
    rcases FirstOrderFiniteAdjunctionModel.ordinalLike_empty_or_succ M hkOrd with
      hkEmpty | ⟨p, hpk, hkSucc⟩
    · rcases hfApprox with ⟨hfun, _hkeys, hbase, _htotal, _hstep⟩
      have hpairEmpty : N.mem (FirstOrderAdjunctionModel.kpair N N.empty z) f := by
        simpa [N, hkEmpty] using hpair
      have hz_eq_empty : z = N.empty := hfun N.empty z N.empty hpairEmpty hbase
      apply (HF_ordinalLikeAt_spec Ez 0).mpr
      simpa [Ez, Em, hz_eq_empty, N, scons] using
        FirstOrderAdjunctionModel.ordinalLike_empty N
    · rcases hfApprox with ⟨_hfun, _hkeys, _hbase, htotal, hstep⟩
      have hpm : M.mem p m := by
        rcases hkey with hkm | hkm
        · change M.mem k m at hkm
          exact hmOrd.1 k hkm p hpk
        · change k = m at hkm
          simpa [hkm] using hpk
      rcases htotal p (Or.inl hpm) with ⟨t, hpt⟩
      have hpSat : Sat M.mem (scons p (scons a (scons f tail))) phi :=
        (Sat_rename_rSkipParam phi (scons a (scons f tail)) k p).mp (ih p hpk)
      let Emp : Nat → α := scons m (scons p (scons a (scons f tail)))
      let Etp : Nat → α := scons t Emp
      have hmSatP : Sat M.mem Emp (HF_ordinalLikeAt 0) :=
        (HF_ordinalLikeAt_spec Emp 0).mpr hmOrd
      have hfSatP : Sat M.mem Emp (mulRecApproxAt 3 2 0) := by
        apply (mulRecApproxAt_spec N Emp 3 2 0).mpr
        exact ⟨_hfun, _hkeys, _hbase, htotal, hstep⟩
      have hptSat : Sat M.mem Etp (HF_pairMemAt 2 0 4) := by
        apply (FirstOrderAdjunctionModel.HF_pairMemAt_spec N Etp 2 0 4).mpr
        simpa [N, Emp, Etp, tail, scons] using hpt
      have htDomain : Sat M.mem Etp (HF_ordinalLikeAt 0) :=
        hpSat m (Or.inl hpm) hmSatP hfSatP t hptSat
      have htOrd : OrdinalLike M.mem t :=
        (HF_ordinalLikeAt_spec Etp 0).mp htDomain
      have hpairSucc : N.mem
          (FirstOrderAdjunctionModel.kpair N (N.adjoin p p) z) f := by
        simpa [N, hkSucc] using hpair
      rcases hstep p t z hpm hpt hpairSucc with ⟨g, hgApprox, hgy⟩
      have hzOrd : OrdinalLike M.mem z :=
        FirstOrderFiniteAdjunctionModel.succRecApprox_value_ordinalLike
          M htOrd ha hgApprox hgy
      apply (HF_ordinalLikeAt_spec Ez 0).mpr
      exact hzOrd
  let Em : Nat → α := scons m (scons m (scons a (scons f tail)))
  let Ez : Nat → α := scons z Em
  have hmain : Sat M.mem (scons m (scons a (scons f tail))) phi := hall m
  have hmSat : Sat M.mem Em (HF_ordinalLikeAt 0) :=
    (HF_ordinalLikeAt_spec Em 0).mpr hm
  have hfSat : Sat M.mem Em (mulRecApproxAt 3 2 0) := by
    apply (mulRecApproxAt_spec N Em 3 2 0).mpr
    simpa [N, Em, tail, scons] using hf
  have hzSat : Sat M.mem Ez (HF_pairMemAt 2 0 4) := by
    apply (FirstOrderAdjunctionModel.HF_pairMemAt_spec N Ez 2 0 4).mpr
    simpa [N, Em, Ez, tail, scons] using hz
  have hzDomain : Sat M.mem Ez (HF_ordinalLikeAt 0) :=
    hmain m (Or.inr rfl) hmSat hfSat z hzSat
  exact (HF_ordinalLikeAt_spec Ez 0).mp hzDomain

/-- In finite HF, multiplication-recursion traces with the same multiplicand
have a unique value at every ordinal-like key covered by both traces. -/
theorem mulRecApprox_value_unique {α : Type u}
    (M : FirstOrderFiniteAdjunctionModel α) {a f g m z w : α}
    (ha : OrdinalLike M.mem a) (hm : OrdinalLike M.mem m)
    (hf : MulRecApprox M.toFirstOrderAdjunctionModel a f m)
    (hz : M.mem (FirstOrderAdjunctionModel.kpair
      M.toFirstOrderAdjunctionModel m z) f)
    (hg : MulRecApprox M.toFirstOrderAdjunctionModel a g m)
    (hw : M.mem (FirstOrderAdjunctionModel.kpair
      M.toFirstOrderAdjunctionModel m w) g) :
    z = w := by
  let N := M.toFirstOrderAdjunctionModel
  let phi : Form :=
    fAll
      (fImp (fOr (fMem 1 0) (fEq 1 0))
        (fImp (HF_ordinalLikeAt 0)
          (fImp (mulRecApproxAt 3 2 0)
            (fImp (mulRecApproxAt 4 2 0)
              (fAll
                (fImp (HF_pairMemAt 2 0 4)
                  (fAll (fImp (HF_pairMemAt 3 0 6) (fEq 1 0)))))))))
  let tail : Nat → α := fun _ => M.empty
  have hind := M.induction_schema phi (scons a (scons f (scons g tail)))
  have hall : ∀ k, Sat M.mem (scons k (scons a (scons f (scons g tail)))) phi := by
    apply hind
    intro k ih
    intro m hkey hmSat hfSat hgSat z hzSat w hwSat
    let Em : Nat → α := scons m (scons k (scons a (scons f (scons g tail))))
    let Ez : Nat → α := scons z Em
    let Ewz : Nat → α := scons w Ez
    have hmOrd : OrdinalLike M.mem m :=
      (HF_ordinalLikeAt_spec Em 0).mp hmSat
    have hfApprox : MulRecApprox N a f m := by
      simpa [N, Em, tail, scons] using
        (mulRecApproxAt_spec N Em 3 2 0).mp hfSat
    have hgApprox : MulRecApprox N a g m := by
      simpa [N, Em, tail, scons] using
        (mulRecApproxAt_spec N Em 4 2 0).mp hgSat
    have hpairF : N.mem (FirstOrderAdjunctionModel.kpair N k z) f := by
      simpa [N, Em, Ez, tail, scons] using
        (FirstOrderAdjunctionModel.HF_pairMemAt_spec N Ez 2 0 4).mp hzSat
    have hpairG : N.mem (FirstOrderAdjunctionModel.kpair N k w) g := by
      simpa [N, Em, Ez, Ewz, tail, scons] using
        (FirstOrderAdjunctionModel.HF_pairMemAt_spec N Ewz 3 0 6).mp hwSat
    have hkOrd : OrdinalLike M.mem k := by
      rcases hkey with hkm | hkm
      · change M.mem k m at hkm
        exact OrdinalLike.of_mem hmOrd hkm
      · change k = m at hkm
        subst k
        exact hmOrd
    rcases FirstOrderFiniteAdjunctionModel.ordinalLike_empty_or_succ M hkOrd with
      hkEmpty | ⟨p, hpk, hkSucc⟩
    · rcases hfApprox with ⟨hfunF, _hkeysF, hbaseF, _htotalF, _hstepF⟩
      rcases hgApprox with ⟨hfunG, _hkeysG, hbaseG, _htotalG, _hstepG⟩
      have hpairEmptyF : N.mem (FirstOrderAdjunctionModel.kpair N N.empty z) f := by
        simpa [N, hkEmpty] using hpairF
      have hpairEmptyG : N.mem (FirstOrderAdjunctionModel.kpair N N.empty w) g := by
        simpa [N, hkEmpty] using hpairG
      have hz_eq_empty : z = N.empty := hfunF N.empty z N.empty hpairEmptyF hbaseF
      have hw_eq_empty : w = N.empty := hfunG N.empty w N.empty hpairEmptyG hbaseG
      exact hz_eq_empty.trans hw_eq_empty.symm
    · rcases hfApprox with ⟨_hfunF, _hkeysF, _hbaseF, htotalF, hstepF⟩
      rcases hgApprox with ⟨_hfunG, _hkeysG, _hbaseG, htotalG, hstepG⟩
      have hpm : M.mem p m := by
        rcases hkey with hkm | hkm
        · change M.mem k m at hkm
          exact hmOrd.1 k hkm p hpk
        · change k = m at hkm
          simpa [hkm] using hpk
      rcases htotalF p (Or.inl hpm) with ⟨t, hpt⟩
      rcases htotalG p (Or.inl hpm) with ⟨u, hpu⟩
      have hpSat : Sat M.mem (scons p (scons a (scons f (scons g tail)))) phi :=
        (Sat_rename_rSkipParam phi (scons a (scons f (scons g tail))) k p).mp
          (ih p hpk)
      let Emp : Nat → α := scons m (scons p (scons a (scons f (scons g tail))))
      let Etp : Nat → α := scons t Emp
      let Eutp : Nat → α := scons u Etp
      have hmSatP : Sat M.mem Emp (HF_ordinalLikeAt 0) :=
        (HF_ordinalLikeAt_spec Emp 0).mpr hmOrd
      have hfSatP : Sat M.mem Emp (mulRecApproxAt 3 2 0) := by
        apply (mulRecApproxAt_spec N Emp 3 2 0).mpr
        exact ⟨_hfunF, _hkeysF, _hbaseF, htotalF, hstepF⟩
      have hgSatP : Sat M.mem Emp (mulRecApproxAt 4 2 0) := by
        apply (mulRecApproxAt_spec N Emp 4 2 0).mpr
        exact ⟨_hfunG, _hkeysG, _hbaseG, htotalG, hstepG⟩
      have hptSat : Sat M.mem Etp (HF_pairMemAt 2 0 4) := by
        apply (FirstOrderAdjunctionModel.HF_pairMemAt_spec N Etp 2 0 4).mpr
        simpa [N, Emp, Etp, tail, scons] using hpt
      have hpuSat : Sat M.mem Eutp (HF_pairMemAt 3 0 6) := by
        apply (FirstOrderAdjunctionModel.HF_pairMemAt_spec N Eutp 3 0 6).mpr
        simpa [N, Emp, Etp, Eutp, tail, scons] using hpu
      have htu : t = u :=
        hpSat m (Or.inl hpm) hmSatP hfSatP hgSatP t hptSat u hpuSat
      have hpairSuccF : N.mem
          (FirstOrderAdjunctionModel.kpair N (N.adjoin p p) z) f := by
        simpa [N, hkSucc] using hpairF
      have hpairSuccG : N.mem
          (FirstOrderAdjunctionModel.kpair N (N.adjoin p p) w) g := by
        simpa [N, hkSucc] using hpairG
      rcases hstepF p t z hpm hpt hpairSuccF with ⟨fAdd, hfAdd, hzAdd⟩
      rcases hstepG p u w hpm hpu hpairSuccG with ⟨gAdd, hgAdd, hwAdd⟩
      have hgAdd' : FirstOrderAdjunctionModel.SuccRecApprox N t gAdd a := by
        rwa [← htu] at hgAdd
      exact FirstOrderFiniteAdjunctionModel.succRecApprox_value_unique
        M ha hfAdd hzAdd hgAdd' hwAdd
  let Em : Nat → α := scons m (scons m (scons a (scons f (scons g tail))))
  let Ez : Nat → α := scons z Em
  let Ewz : Nat → α := scons w Ez
  have hmain : Sat M.mem (scons m (scons a (scons f (scons g tail)))) phi := hall m
  have hmSat : Sat M.mem Em (HF_ordinalLikeAt 0) :=
    (HF_ordinalLikeAt_spec Em 0).mpr hm
  have hfSat : Sat M.mem Em (mulRecApproxAt 3 2 0) := by
    apply (mulRecApproxAt_spec N Em 3 2 0).mpr
    simpa [N, Em, tail, scons] using hf
  have hgSat : Sat M.mem Em (mulRecApproxAt 4 2 0) := by
    apply (mulRecApproxAt_spec N Em 4 2 0).mpr
    simpa [N, Em, tail, scons] using hg
  have hzSat : Sat M.mem Ez (HF_pairMemAt 2 0 4) := by
    apply (FirstOrderAdjunctionModel.HF_pairMemAt_spec N Ez 2 0 4).mpr
    simpa [N, Em, Ez, tail, scons] using hz
  have hwSat : Sat M.mem Ewz (HF_pairMemAt 3 0 6) := by
    apply (FirstOrderAdjunctionModel.HF_pairMemAt_spec N Ewz 3 0 6).mpr
    simpa [N, Em, Ez, Ewz, tail, scons] using hw
  exact hmain m (Or.inr rfl) hmSat hfSat hgSat z hzSat w hwSat

theorem mulGraphAt_of_mulRecApprox_model {α : Type u}
    (M : FirstOrderAdjunctionModel α) (e : Nat → α)
    (out left right : Nat) {f : α}
    (hf : MulRecApprox M (e left) f (e right))
    (hout : M.mem (FirstOrderAdjunctionModel.kpair M (e right) (e out)) f) :
    Sat M.mem e (mulGraphAt out left right) := by
  refine ⟨f, ?_, ?_⟩
  · apply (mulRecApproxAt_spec M (scons f e)
      0 (left+1) (right+1)).mpr
    change MulRecApprox M (e left) f (e right)
    exact hf
  · apply (FirstOrderAdjunctionModel.HF_pairMemAt_spec M (scons f e)
      (right+1) (out+1) 0).mpr
    change M.mem (FirstOrderAdjunctionModel.kpair M (e right) (e out)) f
    exact hout

/-- In a finite first-order HF model, the multiplication graph is
single-valued on ordinal-like inputs. -/
theorem mulGraphAt_value_unique_finite_model {α : Type u}
    (M : FirstOrderFiniteAdjunctionModel α) (e : Nat → α)
    (out₁ out₂ left right : Nat)
    (hleft : OrdinalLike M.mem (e left))
    (hright : OrdinalLike M.mem (e right))
    (h₁ : Sat M.mem e (mulGraphAt out₁ left right))
    (h₂ : Sat M.mem e (mulGraphAt out₂ left right)) :
    e out₁ = e out₂ := by
  let N := M.toFirstOrderAdjunctionModel
  rcases h₁ with ⟨f, hfSat, hout₁Sat⟩
  rcases h₂ with ⟨g, hgSat, hout₂Sat⟩
  have hf : MulRecApprox N (e left) f (e right) := by
    simpa [N, scons] using
      (mulRecApproxAt_spec N (scons f e)
        0 (left+1) (right+1)).mp hfSat
  have hpair₁ : N.mem (FirstOrderAdjunctionModel.kpair N (e right) (e out₁)) f := by
    simpa [N, scons] using
      (FirstOrderAdjunctionModel.HF_pairMemAt_spec N (scons f e)
        (right+1) (out₁+1) 0).mp hout₁Sat
  have hg : MulRecApprox N (e left) g (e right) := by
    simpa [N, scons] using
      (mulRecApproxAt_spec N (scons g e)
        0 (left+1) (right+1)).mp hgSat
  have hpair₂ : N.mem (FirstOrderAdjunctionModel.kpair N (e right) (e out₂)) g := by
    simpa [N, scons] using
      (FirstOrderAdjunctionModel.HF_pairMemAt_spec N (scons g e)
        (right+1) (out₂+1) 0).mp hout₂Sat
  exact mulRecApprox_value_unique M hleft hright hf hpair₁ hg hpair₂

/-- Cross-environment single-valuedness for multiplication graphs whose inputs
agree. -/
theorem mulGraphAt_outputs_eq_finite_model {α : Type u}
    (M : FirstOrderFiniteAdjunctionModel α)
    (e₁ e₂ : Nat → α)
    (out₁ out₂ left₁ left₂ right₁ right₂ : Nat)
    (hleft : e₁ left₁ = e₂ left₂)
    (hright : e₁ right₁ = e₂ right₂)
    (hleftOrd : OrdinalLike M.mem (e₁ left₁))
    (hrightOrd : OrdinalLike M.mem (e₁ right₁))
    (h₁ : Sat M.mem e₁ (mulGraphAt out₁ left₁ right₁))
    (h₂ : Sat M.mem e₂ (mulGraphAt out₂ left₂ right₂)) :
    e₁ out₁ = e₂ out₂ := by
  let N := M.toFirstOrderAdjunctionModel
  rcases h₁ with ⟨f, hfSat, hout₁Sat⟩
  rcases h₂ with ⟨g, hgSat, hout₂Sat⟩
  have hf : MulRecApprox N (e₁ left₁) f (e₁ right₁) := by
    simpa [N, scons] using
      (mulRecApproxAt_spec N (scons f e₁)
        0 (left₁+1) (right₁+1)).mp hfSat
  have hpair₁ : N.mem
      (FirstOrderAdjunctionModel.kpair N (e₁ right₁) (e₁ out₁)) f := by
    simpa [N, scons] using
      (FirstOrderAdjunctionModel.HF_pairMemAt_spec N (scons f e₁)
        (right₁+1) (out₁+1) 0).mp hout₁Sat
  have hg : MulRecApprox N (e₁ left₁) g (e₁ right₁) := by
    have hgRaw : MulRecApprox N (e₂ left₂) g (e₂ right₂) := by
      simpa [N, scons] using
        (mulRecApproxAt_spec N (scons g e₂)
          0 (left₂+1) (right₂+1)).mp hgSat
    simpa [hleft, hright] using hgRaw
  have hpair₂ : N.mem
      (FirstOrderAdjunctionModel.kpair N (e₁ right₁) (e₂ out₂)) g := by
    have hpairRaw : N.mem
        (FirstOrderAdjunctionModel.kpair N (e₂ right₂) (e₂ out₂)) g := by
      simpa [N, scons] using
        (FirstOrderAdjunctionModel.HF_pairMemAt_spec N (scons g e₂)
          (right₂+1) (out₂+1) 0).mp hout₂Sat
    simpa [hright] using hpairRaw
  exact mulRecApprox_value_unique M hleftOrd hrightOrd hf hpair₁ hg hpair₂

theorem mulGraphAt_succ_right_of_mulRecApprox_model {α : Type u}
    (M : FirstOrderAdjunctionModel α) (e : Nat → α)
    (out left rightSucc right : Nat) {f z g y : α}
    (hrightOrd : OrdinalLike M.mem (e right))
    (hrightSucc : e rightSucc = M.adjoin (e right) (e right))
    (hout : e out = y)
    (hf : MulRecApprox M (e left) f (e right))
    (hz : M.mem (FirstOrderAdjunctionModel.kpair M (e right) z) f)
    (hg : FirstOrderAdjunctionModel.SuccRecApprox M z g (e left))
    (hy : M.mem (FirstOrderAdjunctionModel.kpair M (e left) y) g) :
    Sat M.mem e (mulGraphAt out left rightSucc) := by
  let h := mulRecGraphSucc M f (e right) y
  apply mulGraphAt_of_mulRecApprox_model M e out left rightSucc (f := h)
  · change MulRecApprox M (e left) h (e rightSucc)
    rw [hrightSucc]
    exact mulRecGraphSucc_mulRecApprox M hrightOrd hf hz ⟨g, hg, hy⟩
  · change M.mem (FirstOrderAdjunctionModel.kpair M (e rightSucc) (e out)) h
    rw [hrightSucc, hout]
    exact mulRecGraphSucc_new M f (e right) y

theorem addGraphAt_zero_right_model {α : Type u}
    (M : FirstOrderAdjunctionModel α) (e : Nat → α)
    (out left right : Nat) (hout : e out = e left) (hright : e right = M.empty) :
    Sat M.mem e (addGraphAt out left right) := by
  let f := FirstOrderAdjunctionModel.zeroSuccRecGraph M (e left)
  refine ⟨f, ?_, ?_⟩
  · apply (FirstOrderAdjunctionModel.HF_succRecApproxAt_spec M (scons f e)
      0 (left+1) (right+1)).mpr
    change FirstOrderAdjunctionModel.SuccRecApprox M (e left) f (e right)
    rw [hright]
    exact FirstOrderAdjunctionModel.zeroSuccRecGraph_succRecApprox M (e left)
  · apply (FirstOrderAdjunctionModel.HF_pairMemAt_spec M (scons f e)
      (right+1) (out+1) 0).mpr
    change M.mem (FirstOrderAdjunctionModel.kpair M (e right) (e out)) f
    rw [hright, hout]
    exact FirstOrderAdjunctionModel.zeroSuccRecGraph_base M (e left)

/-- Build an addition graph from explicit successor-recursion trace data. -/
theorem addGraphAt_of_succRecApprox_model {α : Type u}
    (M : FirstOrderAdjunctionModel α) (e : Nat → α)
    (out left right : Nat) {f : α}
    (hf : FirstOrderAdjunctionModel.SuccRecApprox M (e left) f (e right))
    (hout : M.mem (FirstOrderAdjunctionModel.kpair M (e right) (e out)) f) :
    Sat M.mem e (addGraphAt out left right) := by
  refine ⟨f, ?_, ?_⟩
  · apply (FirstOrderAdjunctionModel.HF_succRecApproxAt_spec M (scons f e)
      0 (left+1) (right+1)).mpr
    change FirstOrderAdjunctionModel.SuccRecApprox M (e left) f (e right)
    exact hf
  · apply (FirstOrderAdjunctionModel.HF_pairMemAt_spec M (scons f e)
      (right+1) (out+1) 0).mpr
    change M.mem (FirstOrderAdjunctionModel.kpair M (e right) (e out)) f
    exact hout

/-- In a finite first-order HF model, the addition graph is single-valued on
ordinal-like right inputs. -/
theorem addGraphAt_value_unique_finite_model {α : Type u}
    (M : FirstOrderFiniteAdjunctionModel α) (e : Nat → α)
    (out₁ out₂ left right : Nat)
    (hright : OrdinalLike M.mem (e right))
    (h₁ : Sat M.mem e (addGraphAt out₁ left right))
    (h₂ : Sat M.mem e (addGraphAt out₂ left right)) :
    e out₁ = e out₂ := by
  let N := M.toFirstOrderAdjunctionModel
  rcases h₁ with ⟨f, hfSat, hout₁Sat⟩
  rcases h₂ with ⟨g, hgSat, hout₂Sat⟩
  have hf : FirstOrderAdjunctionModel.SuccRecApprox N (e left) f (e right) := by
    simpa [N, scons] using
      (FirstOrderAdjunctionModel.HF_succRecApproxAt_spec N (scons f e)
        0 (left+1) (right+1)).mp hfSat
  have hpair₁ : N.mem (FirstOrderAdjunctionModel.kpair N (e right) (e out₁)) f := by
    simpa [N, scons] using
      (FirstOrderAdjunctionModel.HF_pairMemAt_spec N (scons f e)
        (right+1) (out₁+1) 0).mp hout₁Sat
  have hg : FirstOrderAdjunctionModel.SuccRecApprox N (e left) g (e right) := by
    simpa [N, scons] using
      (FirstOrderAdjunctionModel.HF_succRecApproxAt_spec N (scons g e)
        0 (left+1) (right+1)).mp hgSat
  have hpair₂ : N.mem (FirstOrderAdjunctionModel.kpair N (e right) (e out₂)) g := by
    simpa [N, scons] using
      (FirstOrderAdjunctionModel.HF_pairMemAt_spec N (scons g e)
        (right+1) (out₂+1) 0).mp hout₂Sat
  exact FirstOrderFiniteAdjunctionModel.succRecApprox_value_unique
    M hright hf hpair₁ hg hpair₂

/-- Cross-environment single-valuedness for addition graphs whose inputs
agree. -/
theorem addGraphAt_outputs_eq_finite_model {α : Type u}
    (M : FirstOrderFiniteAdjunctionModel α)
    (e₁ e₂ : Nat → α)
    (out₁ out₂ left₁ left₂ right₁ right₂ : Nat)
    (hleft : e₁ left₁ = e₂ left₂)
    (hright : e₁ right₁ = e₂ right₂)
    (hrightOrd : OrdinalLike M.mem (e₁ right₁))
    (h₁ : Sat M.mem e₁ (addGraphAt out₁ left₁ right₁))
    (h₂ : Sat M.mem e₂ (addGraphAt out₂ left₂ right₂)) :
    e₁ out₁ = e₂ out₂ := by
  let N := M.toFirstOrderAdjunctionModel
  rcases h₁ with ⟨f, hfSat, hout₁Sat⟩
  rcases h₂ with ⟨g, hgSat, hout₂Sat⟩
  have hf : FirstOrderAdjunctionModel.SuccRecApprox
      N (e₁ left₁) f (e₁ right₁) := by
    simpa [N, scons] using
      (FirstOrderAdjunctionModel.HF_succRecApproxAt_spec N (scons f e₁)
        0 (left₁+1) (right₁+1)).mp hfSat
  have hpair₁ : N.mem
      (FirstOrderAdjunctionModel.kpair N (e₁ right₁) (e₁ out₁)) f := by
    simpa [N, scons] using
      (FirstOrderAdjunctionModel.HF_pairMemAt_spec N (scons f e₁)
        (right₁+1) (out₁+1) 0).mp hout₁Sat
  have hg : FirstOrderAdjunctionModel.SuccRecApprox
      N (e₁ left₁) g (e₁ right₁) := by
    have hgRaw : FirstOrderAdjunctionModel.SuccRecApprox
        N (e₂ left₂) g (e₂ right₂) := by
      simpa [N, scons] using
        (FirstOrderAdjunctionModel.HF_succRecApproxAt_spec N (scons g e₂)
          0 (left₂+1) (right₂+1)).mp hgSat
    simpa [hleft, hright] using hgRaw
  have hpair₂ : N.mem
      (FirstOrderAdjunctionModel.kpair N (e₁ right₁) (e₂ out₂)) g := by
    have hpairRaw : N.mem
        (FirstOrderAdjunctionModel.kpair N (e₂ right₂) (e₂ out₂)) g := by
      simpa [N, scons] using
        (FirstOrderAdjunctionModel.HF_pairMemAt_spec N (scons g e₂)
          (right₂+1) (out₂+1) 0).mp hout₂Sat
    simpa [hright] using hpairRaw
  exact FirstOrderFiniteAdjunctionModel.succRecApprox_value_unique
    M hrightOrd hf hpair₁ hg hpair₂

theorem addGraphAt_succ_right_of_addGraphAt_model {α : Type u}
    (M : FirstOrderAdjunctionModel α) (e : Nat → α)
    (outSucc out left rightSucc right : Nat)
    (hrightOrd : OrdinalLike M.mem (e right))
    (hrightSucc : e rightSucc = M.adjoin (e right) (e right))
    (houtSucc : e outSucc = M.adjoin (e out) (e out))
    (hadd : Sat M.mem e (addGraphAt out left right)) :
    Sat M.mem e (addGraphAt outSucc left rightSucc) := by
  rcases hadd with ⟨f, hf, hout⟩
  have hf' := (FirstOrderAdjunctionModel.HF_succRecApproxAt_spec M (scons f e)
    0 (left+1) (right+1)).mp hf
  have hout' := (FirstOrderAdjunctionModel.HF_pairMemAt_spec M (scons f e)
    (right+1) (out+1) 0).mp hout
  change FirstOrderAdjunctionModel.SuccRecApprox M (e left) f (e right) at hf'
  change M.mem (FirstOrderAdjunctionModel.kpair M (e right) (e out)) f at hout'
  let g := FirstOrderAdjunctionModel.succRecGraphSucc M f (e right) (e out)
  refine ⟨g, ?_, ?_⟩
  · apply (FirstOrderAdjunctionModel.HF_succRecApproxAt_spec M (scons g e)
      0 (left+1) (rightSucc+1)).mpr
    change FirstOrderAdjunctionModel.SuccRecApprox M (e left) g (e rightSucc)
    rw [hrightSucc]
    exact FirstOrderAdjunctionModel.succRecGraphSucc_succRecApprox M hrightOrd hf' hout'
  · apply (FirstOrderAdjunctionModel.HF_pairMemAt_spec M (scons g e)
      (rightSucc+1) (outSucc+1) 0).mpr
    change M.mem (FirstOrderAdjunctionModel.kpair M (e rightSucc) (e outSucc)) g
    rw [hrightSucc, houtSucc]
    exact FirstOrderAdjunctionModel.succRecGraphSucc_new M f (e right) (e out)

/-- Extend an addition graph through the successor of the right input from
explicit predecessor trace data, without requiring the predecessor output to
occupy a slot in the current environment. -/
theorem addGraphAt_succ_right_of_succRecApprox_model {α : Type u}
    (M : FirstOrderAdjunctionModel α) (e : Nat → α)
    (outSucc left rightSucc right : Nat) {f z : α}
    (hrightOrd : OrdinalLike M.mem (e right))
    (hrightSucc : e rightSucc = M.adjoin (e right) (e right))
    (houtSucc : e outSucc = M.adjoin z z)
    (hf : FirstOrderAdjunctionModel.SuccRecApprox M (e left) f (e right))
    (hout : M.mem (FirstOrderAdjunctionModel.kpair M (e right) z) f) :
    Sat M.mem e (addGraphAt outSucc left rightSucc) := by
  let g := FirstOrderAdjunctionModel.succRecGraphSucc M f (e right) z
  apply addGraphAt_of_succRecApprox_model M e outSucc left rightSucc
      (f := g)
  · change FirstOrderAdjunctionModel.SuccRecApprox M (e left) g (e rightSucc)
    rw [hrightSucc]
    exact FirstOrderAdjunctionModel.succRecGraphSucc_succRecApprox M hrightOrd hf hout
  · change M.mem (FirstOrderAdjunctionModel.kpair M (e rightSucc) (e outSucc)) g
    rw [hrightSucc, houtSucc]
    exact FirstOrderAdjunctionModel.succRecGraphSucc_new M f (e right) z

theorem mulStepAt_empty_model {α : Type u}
    (M : FirstOrderAdjunctionModel α) (e : Nat → α)
    (f a m : Nat) (hm : e m = M.empty) :
    Sat M.mem e (mulStepAt f a m) := by
  intro k _t _y hkm
  change M.mem k (e m) at hkm
  rw [hm] at hkm
  exact False.elim (M.empty_spec k hkm)

theorem mulGraphAt_zero_right_model {α : Type u}
    (M : FirstOrderAdjunctionModel α) (e : Nat → α)
    (out left right : Nat) (hout : e out = M.empty) (hright : e right = M.empty) :
    Sat M.mem e (mulGraphAt out left right) := by
  let f := FirstOrderAdjunctionModel.zeroSuccRecGraph M M.empty
  have hf : FirstOrderAdjunctionModel.SuccRecApprox M M.empty f M.empty :=
    FirstOrderAdjunctionModel.zeroSuccRecGraph_succRecApprox M M.empty
  refine ⟨f, ?_, ?_⟩
  · rcases hf with ⟨hfun, hkeys, hbase, htotal, _hstep⟩
    change
      Sat M.mem (scons f e) (HF_pairFunctionalAt 0) ∧
        (Sat M.mem (scons f e) (HF_pairKeysBelowSuccAt 0 (right+1)) ∧
          (Sat M.mem (scons f e) (HF_pairZeroBaseAt 0) ∧
            (Sat M.mem (scons f e) (HF_pairTotalBelowSuccAt 0 (right+1)) ∧
              Sat M.mem (scons f e) (mulStepAt 0 (left+1) (right+1)))))
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact (FirstOrderAdjunctionModel.HF_pairFunctionalAt_spec M (scons f e) 0).mpr hfun
    · apply (FirstOrderAdjunctionModel.HF_pairKeysBelowSuccAt_spec M
        (scons f e) 0 (right+1)).mpr
      simpa [scons, hright] using hkeys
    · exact (FirstOrderAdjunctionModel.HF_pairZeroBaseAt_spec M (scons f e) 0).mpr hbase
    · apply (FirstOrderAdjunctionModel.HF_pairTotalBelowSuccAt_spec M
        (scons f e) 0 (right+1)).mpr
      simpa [scons, hright] using htotal
    · apply mulStepAt_empty_model M (scons f e) 0 (left+1) (right+1)
      simpa [scons] using hright
  · apply (FirstOrderAdjunctionModel.HF_pairMemAt_spec M (scons f e)
      (right+1) (out+1) 0).mpr
    change M.mem (FirstOrderAdjunctionModel.kpair M (e right) (e out)) f
    rw [hright, hout]
    exact FirstOrderAdjunctionModel.zeroSuccRecGraph_base M M.empty

theorem domain_ordinalCode (n : Nat) (e : Nat → Nat) :
    Sat Mem (scons (ordinalCode n) e) domainForm :=
  HF_ordinalLikeAt_of_ordinalCode (scons (ordinalCode n) e) 0 n rfl

theorem domain_exact (e : Nat → Nat) :
    Sat Mem e domainForm ↔ IsOrdinalCode (e 0) :=
  HF_ordinalLikeAt_exact e 0

theorem zeroGraph_ordinalCode (e : Nat → Nat) :
    Sat Mem (scons (ordinalCode 0) e) zeroGraph := by
  apply (HF_emptyAt_empty standardModel (scons (ordinalCode 0) e) 0).mpr
  rfl

theorem zeroGraph_exact_on_ordinalCode (n : Nat) (e : Nat → Nat) :
    Sat Mem (scons (ordinalCode n) e) zeroGraph ↔ n = 0 := by
  constructor
  · intro h
    have hz := (HF_emptyAt_empty standardModel (scons (ordinalCode n) e) 0).mp h
    apply ordinalCode_injective
    rw [ordinalCode_zero]
    exact hz
  · intro h
    subst h
    exact zeroGraph_ordinalCode e

theorem succGraph_ordinalCode (n : Nat) (e : Nat → Nat) :
    Sat Mem (scons (ordinalCode (n+1)) (scons (ordinalCode n) e)) succGraph := by
  apply (HF_succAt_spec standardModel
    (scons (ordinalCode (n+1)) (scons (ordinalCode n) e)) 0 1).mpr
  exact ordinalCode_succ n

theorem succGraph_exact_on_ordinalCodes (m n : Nat) (e : Nat → Nat) :
    Sat Mem (scons (ordinalCode m) (scons (ordinalCode n) e)) succGraph ↔
      m = n + 1 := by
  constructor
  · intro h
    have hs := (HF_succAt_spec standardModel
      (scons (ordinalCode m) (scons (ordinalCode n) e)) 0 1).mp h
    apply ordinalCode_injective
    rw [ordinalCode_succ]
    exact hs
  · intro h
    subst h
    exact succGraph_ordinalCode n e

theorem addGraph_ordinalCode (m n : Nat) (e : Nat → Nat) :
    Sat Mem
      (scons (ordinalCode (m+n)) (scons (ordinalCode m) (scons (ordinalCode n) e)))
      addGraph := by
  let f := succRecTrace (ordinalCode m) n
  refine ⟨f, ?_, ?_⟩
  · exact (HF_succRecApproxAt_spec standardModel
      (scons f (scons (ordinalCode (m+n))
        (scons (ordinalCode m) (scons (ordinalCode n) e)))) 0 2 3).mpr
      (succRecTrace_succRecApprox (ordinalCode m) n)
  · apply (HF_pairMemAt_spec standardModel
      (scons f (scons (ordinalCode (m+n))
        (scons (ordinalCode m) (scons (ordinalCode n) e)))) 3 1 0).mpr
    have hp := succRecTrace_pair_mem (ordinalCode m) (k := n) (n := n) (Nat.le_refl n)
    change Mem (kpair standardModel (ordinalCode n) (ordinalCode (m+n))) f
    simpa [f, succIterObj_ordinalCode] using hp

theorem addGraphAt_ordinalCode (out left right m n : Nat) (e : Nat → Nat)
    (hout : e out = ordinalCode (m+n))
    (hleft : e left = ordinalCode m)
    (hright : e right = ordinalCode n) :
    Sat Mem e (addGraphAt out left right) := by
  let f := succRecTrace (ordinalCode m) n
  refine ⟨f, ?_, ?_⟩
  · apply (HF_succRecApproxAt_spec standardModel (scons f e)
      0 (left+1) (right+1)).mpr
    change SuccRecApprox standardModel (e left) f (e right)
    rw [hleft, hright]
    exact succRecTrace_succRecApprox (ordinalCode m) n
  · apply (HF_pairMemAt_spec standardModel (scons f e) (right+1) (out+1) 0).mpr
    change Mem (kpair standardModel (e right) (e out)) f
    rw [hout, hright]
    have hp := succRecTrace_pair_mem (ordinalCode m) (k := n) (n := n) (Nat.le_refl n)
    simpa [f, succIterObj_ordinalCode] using hp

theorem addGraphAt_value_of_ordinalInputs (out left right m n : Nat) (e : Nat → Nat)
    (hleft : e left = ordinalCode m)
    (hright : e right = ordinalCode n)
    (h : Sat Mem e (addGraphAt out left right)) :
    e out = ordinalCode (m+n) := by
  rcases h with ⟨f, hf, hpair⟩
  have hf' := (HF_succRecApproxAt_spec standardModel (scons f e)
    0 (left+1) (right+1)).mp hf
  have hpair' := (HF_pairMemAt_spec standardModel (scons f e)
    (right+1) (out+1) 0).mp hpair
  change SuccRecApprox standardModel (e left) f (e right) at hf'
  change Mem (kpair standardModel (e right) (e out)) f at hpair'
  rw [hleft, hright] at hf'
  rw [hright] at hpair'
  have hval := succRecApprox_value_of_le (ordinalCode m) f n n (e out)
    hf' (Nat.le_refl n) hpair'
  rw [hval, succIterObj_ordinalCode]

theorem addGraphAt_exact_on_ordinalCodes (out left right r m n : Nat) (e : Nat → Nat)
    (hout : e out = ordinalCode r)
    (hleft : e left = ordinalCode m)
    (hright : e right = ordinalCode n) :
    Sat Mem e (addGraphAt out left right) ↔ r = m + n := by
  constructor
  · intro h
    have hval := addGraphAt_value_of_ordinalInputs out left right m n e hleft hright h
    apply ordinalCode_injective
    rw [← hout, hval]
  · intro h
    subst h
    exact addGraphAt_ordinalCode out left right m n e
      (by rw [hout]) hleft hright

theorem addGraph_exact_on_ordinalCodes (r m n : Nat) (e : Nat → Nat) :
    Sat Mem
      (scons (ordinalCode r) (scons (ordinalCode m) (scons (ordinalCode n) e)))
      addGraph ↔ r = m + n := by
  constructor
  · intro h
    rcases h with ⟨f, hf, hout⟩
    have hf' := (HF_succRecApproxAt_spec standardModel
      (scons f (scons (ordinalCode r)
        (scons (ordinalCode m) (scons (ordinalCode n) e)))) 0 2 3).mp hf
    have hout' := (HF_pairMemAt_spec standardModel
      (scons f (scons (ordinalCode r)
        (scons (ordinalCode m) (scons (ordinalCode n) e)))) 3 1 0).mp hout
    have hval := succRecApprox_value_of_le (ordinalCode m) f n n (ordinalCode r)
      hf' (Nat.le_refl n) hout'
    apply ordinalCode_injective
    rw [hval, succIterObj_ordinalCode]
  · intro h
    subst h
    exact addGraph_ordinalCode m n e

theorem mulRecApproxAt_value_of_le (m N f outDummy : Nat) (e : Nat → Nat) :
    ∀ n y,
      Sat Mem
        (scons f (scons outDummy (scons (ordinalCode m) (scons (ordinalCode N) e))))
        (mulRecApproxAt 0 2 3) →
      n ≤ N →
      Mem (kpair standardModel (ordinalCode n) y) f →
      y = ordinalCode (m*n) := by
  intro n
  induction n with
  | zero =>
      intro y hA _hn hy
      let E := scons f (scons outDummy (scons (ordinalCode m) (scons (ordinalCode N) e)))
      change Sat Mem E (mulRecApproxAt 0 2 3) at hA
      rcases hA with ⟨hfunSat, _hkeysSat, hzeroSat, _htotalSat, _hstepSat⟩
      have hfun := (HF_pairFunctionalAt_spec standardModel E 0).mp hfunSat
      change PairFunctional standardModel f at hfun
      have hbase := (HF_pairZeroBaseAt_spec standardModel E 0).mp hzeroSat
      change Mem (kpair standardModel empty empty) f at hbase
      have hbase' : Mem (kpair standardModel (ordinalCode 0) (ordinalCode 0)) f := by
        simpa [ordinalCode_zero] using hbase
      have hy_eq := hfun (ordinalCode 0) y (ordinalCode 0) hy hbase'
      simpa [ordinalCode_zero] using hy_eq
  | succ n ih =>
      intro y hA hn hy
      let E := scons f (scons outDummy (scons (ordinalCode m) (scons (ordinalCode N) e)))
      change Sat Mem E (mulRecApproxAt 0 2 3) at hA
      have hA' := hA
      rcases hA with ⟨_hfunSat, _hkeysSat, _hzeroSat, htotalSat, hstepSat⟩
      have htotal := (HF_pairTotalBelowSuccAt_spec standardModel E 0 3).mp htotalSat
      change PairTotalBelowSucc standardModel f (ordinalCode N) at htotal
      have hnlt : n < N := by omega
      rcases htotal (ordinalCode n) (Or.inl (ordinalCode_mem_of_lt hnlt)) with ⟨t, ht⟩
      have htval := ih t hA' (Nat.le_of_lt hnlt) ht
      let Ekty := scons y (scons t (scons (ordinalCode n) E))
      let Eskty := scons (ordinalCode (n+1)) Ekty
      have hktSat : Sat Mem Ekty (HF_pairMemAt 2 1 3) := by
        apply (HF_pairMemAt_spec standardModel Ekty 2 1 3).mpr
        change Mem (kpair standardModel (ordinalCode n) t) f
        exact ht
      have hskSat : Sat Mem Eskty (HF_succAt 0 3) := by
        apply (HF_succAt_spec standardModel Eskty 0 3).mpr
        change ordinalCode (n+1) = adjoin (ordinalCode n) (ordinalCode n)
        exact ordinalCode_succ n
      have hskySat : Sat Mem Eskty (HF_pairMemAt 0 1 4) := by
        apply (HF_pairMemAt_spec standardModel Eskty 0 1 4).mpr
        change Mem (kpair standardModel (ordinalCode (n+1)) y) f
        exact hy
      have haddSat := hstepSat (ordinalCode n) t y
        (ordinalCode_mem_of_lt hnlt) hktSat (ordinalCode (n+1)) hskSat hskySat
      have hyval := addGraphAt_value_of_ordinalInputs 1 2 6 (m*n) m Eskty
        (by
          show t = ordinalCode (m*n)
          exact htval)
        (by rfl)
        haddSat
      change y = ordinalCode (m*n + m) at hyval
      rw [hyval, Nat.mul_succ]

theorem mulGraph_ordinalCode (m n : Nat) (e : Nat → Nat) :
    Sat Mem
      (scons (ordinalCode (m*n)) (scons (ordinalCode m) (scons (ordinalCode n) e)))
      mulGraph := by
  let f := mulRecTrace m n
  let E := scons f
    (scons (ordinalCode (m*n)) (scons (ordinalCode m) (scons (ordinalCode n) e)))
  refine ⟨f, ?_, ?_⟩
  · change Sat Mem E (mulRecApproxAt 0 2 3)
    constructor
    · exact (HF_pairFunctionalAt_spec standardModel E 0).mpr (mulRecTrace_functional m n)
    · constructor
      · apply (HF_pairKeysBelowSuccAt_spec standardModel E 0 3).mpr
        change PairKeysBelowSucc standardModel f (ordinalCode n)
        exact mulRecTrace_keysBelowSucc m n
      · constructor
        · apply (HF_pairZeroBaseAt_spec standardModel E 0).mpr
          change Mem (kpair standardModel empty empty) f
          simpa [f, ordinalCode_zero] using
            (mulRecTrace_pair_mem m (k := 0) (n := n) (Nat.zero_le n))
        · constructor
          · apply (HF_pairTotalBelowSuccAt_spec standardModel E 0 3).mpr
            change PairTotalBelowSucc standardModel f (ordinalCode n)
            exact mulRecTrace_totalBelowSucc m n
          · intro k t y hkm hkt sk hsk hsky
            let Ekty := scons y (scons t (scons k E))
            let Eskty := scons sk Ekty
            have hkt' : Mem (kpair standardModel k t) f := by
              have h := (HF_pairMemAt_spec standardModel Ekty 2 1 3).mp hkt
              change Mem (kpair standardModel k t) f at h
              exact h
            have hsky' : Mem (kpair standardModel sk y) f := by
              have h := (HF_pairMemAt_spec standardModel Eskty 0 1 4).mp hsky
              change Mem (kpair standardModel sk y) f at h
              exact h
            have hsk' : sk = adjoin k k := by
              have h := (HF_succAt_spec standardModel Eskty 0 3).mp hsk
              change sk = adjoin k k at h
              exact h
            rcases (mem_ordinalCode_iff k n).mp hkm with ⟨i, hi, hk⟩
            rcases (mulRecTrace_mem_iff m _ n).mp hkt' with ⟨j, _hj, hpair_j⟩
            have hcomp_j := kpair_injective standardModel hpair_j
            have hij : i = j := by
              apply ordinalCode_injective
              exact hk.symm.trans hcomp_j.1
            have ht : t = ordinalCode (m * i) := by
              rw [hcomp_j.2, ← hij]
            have hskcode : sk = ordinalCode (i+1) := by
              rw [hsk', hk, ordinalCode_succ]
            rcases (mulRecTrace_mem_iff m _ n).mp hsky' with ⟨l, _hl, hpair_l⟩
            have hcomp_l := kpair_injective standardModel hpair_l
            have hil : i+1 = l := by
              apply ordinalCode_injective
              exact hskcode.symm.trans hcomp_l.1
            have hy : y = ordinalCode (m * (i+1)) := by
              rw [hcomp_l.2, ← hil]
            apply addGraphAt_ordinalCode 1 2 6 (m * i) m Eskty
            · show y = ordinalCode (m * i + m)
              rw [hy, Nat.mul_succ]
            · show t = ordinalCode (m * i)
              exact ht
            · rfl
  · apply (HF_pairMemAt_spec standardModel E 3 1 0).mpr
    change Mem (kpair standardModel (ordinalCode n) (ordinalCode (m*n))) f
    exact mulRecTrace_pair_mem m (Nat.le_refl n)

theorem mulGraph_exact_on_ordinalCodes (r m n : Nat) (e : Nat → Nat) :
    Sat Mem
      (scons (ordinalCode r) (scons (ordinalCode m) (scons (ordinalCode n) e)))
      mulGraph ↔ r = m * n := by
  constructor
  · intro h
    rcases h with ⟨f, hf, hout⟩
    have hout' := (HF_pairMemAt_spec standardModel
      (scons f (scons (ordinalCode r) (scons (ordinalCode m) (scons (ordinalCode n) e))))
      3 1 0).mp hout
    change Mem (kpair standardModel (ordinalCode n) (ordinalCode r)) f at hout'
    have hval := mulRecApproxAt_value_of_le m n f (ordinalCode r) e n (ordinalCode r)
      hf (Nat.le_refl n) hout'
    exact ordinalCode_injective hval
  · intro h
    subst h
    exact mulGraph_ordinalCode m n e

theorem mulGraph_value_of_ordinalInputs (m n : Nat) (e : Nat → Nat)
    (hleft : e 1 = ordinalCode m)
    (hright : e 2 = ordinalCode n)
    (h : Sat Mem e mulGraph) :
    e 0 = ordinalCode (m*n) := by
  rcases h with ⟨f, hf, hout⟩
  let tail : Nat → Nat := fun k => e (k+3)
  let eCanon : Nat → Nat :=
    scons f (scons (e 0) (scons (ordinalCode m) (scons (ordinalCode n) tail)))
  have heq : ∀ k, eCanon k = scons f e k := by
    intro k
    rcases k with _ | k
    · rfl
    rcases k with _ | k
    · rfl
    rcases k with _ | k
    · exact hleft.symm
    rcases k with _ | k
    · exact hright.symm
    · simp [eCanon, tail, scons]
  have hfCanon : Sat Mem eCanon (mulRecApproxAt 0 2 3) :=
    (Sat_ext (mulRecApproxAt 0 2 3) eCanon (scons f e) heq).mpr hf
  have hout' := (HF_pairMemAt_spec standardModel (scons f e) 3 1 0).mp hout
  change Mem (kpair standardModel (e 2) (e 0)) f at hout'
  rw [hright] at hout'
  exact mulRecApproxAt_value_of_le m n f (e 0) tail n (e 0)
    hfCanon (Nat.le_refl n) hout'

/-- In any adjunction model, the HF empty set is in the interpreted PA
domain. -/
theorem domain_empty_model {α : Type} (M : AdjunctionModel α) (e : Nat → α) :
    Sat M.mem (scons M.empty e) domainForm := by
  apply (HF_ordinalLikeAt_spec (scons M.empty e) 0).mpr
  exact OrdinalLike.empty M

/-- In any adjunction model, the HF empty set realizes the PA-in-HF zero
graph. -/
theorem zeroGraph_empty_model {α : Type} (M : AdjunctionModel α) (e : Nat → α) :
    Sat M.mem (scons M.empty e) zeroGraph := by
  apply (HF_emptyAt_empty M (scons M.empty e) 0).mpr
  rfl

/-- In any adjunction model, self-adjunction realizes the PA-in-HF successor
graph. -/
theorem succGraph_adjoin_self_model {α : Type} (M : AdjunctionModel α)
    (a : α) (e : Nat → α) :
    Sat M.mem (scons (M.adjoin a a) (scons a e)) succGraph := by
  apply (HF_succAt_spec M (scons (M.adjoin a a) (scons a e)) 0 1).mpr
  rfl

/-- In any adjunction model, self-adjunction preserves the interpreted PA
domain. -/
theorem domain_adjoin_self_model {α : Type} (M : AdjunctionModel α)
    (a : α) (e : Nat → α)
    (ha : Sat M.mem (scons a e) domainForm) :
    Sat M.mem (scons (M.adjoin a a) e) domainForm := by
  apply (HF_ordinalLikeAt_spec (scons (M.adjoin a a) e) 0).mpr
  have ha' := (HF_ordinalLikeAt_spec (scons a e) 0).mp ha
  exact OrdinalLike.adjoin_self M ha' rfl

/-- The carrier of the PA interpretation inside an adjunction model. -/
def Domain {α : Type} (M : AdjunctionModel α) : Type :=
  {a : α // OrdinalLike M.mem a}

/-- Zero of the interpreted PA domain. -/
def domainZero {α : Type} (M : AdjunctionModel α) : Domain M :=
  ⟨M.empty, OrdinalLike.empty M⟩

/-- Successor of the interpreted PA domain. -/
def domainSucc {α : Type} (M : AdjunctionModel α) (a : Domain M) : Domain M :=
  ⟨M.adjoin a.val a.val, OrdinalLike.adjoin_self M a.property rfl⟩

theorem domainZero_val {α : Type} (M : AdjunctionModel α) :
    (domainZero M).val = M.empty :=
  rfl

theorem domainSucc_val {α : Type} (M : AdjunctionModel α) (a : Domain M) :
    (domainSucc M a).val = M.adjoin a.val a.val :=
  rfl

/-- Self-adjunction is never empty. -/
theorem adjoin_self_ne_empty_model {α : Type} (M : AdjunctionModel α) (a : α) :
    M.adjoin a a ≠ M.empty := by
  intro h
  have ha : M.mem a (M.adjoin a a) := (M.adjoin_spec a a a).mpr (Or.inr rfl)
  rw [h] at ha
  exact M.empty_spec a ha

/-- Self-adjunction is injective on ordinal-like objects. -/
theorem adjoin_self_injective_on_ordinalLike_model {α : Type}
    (M : AdjunctionModel α) {a b : α}
    (_ha : OrdinalLike M.mem a) (hb : OrdinalLike M.mem b)
    (h : M.adjoin a a = M.adjoin b b) : a = b := by
  have hasucc : M.mem a (M.adjoin b b) := by
    have : M.mem a (M.adjoin a a) := (M.adjoin_spec a a a).mpr (Or.inr rfl)
    simpa [h] using this
  rcases (M.adjoin_spec a b b).mp hasucc with hab | hab
  · have hbsucc : M.mem b (M.adjoin a a) := by
      have : M.mem b (M.adjoin b b) := (M.adjoin_spec b b b).mpr (Or.inr rfl)
      simpa [← h] using this
    rcases (M.adjoin_spec b a a).mp hbsucc with hba | hba
    · have hbb : M.mem b b := hb.1 a hab b hba
      exact False.elim (M.mem_irrefl b hbb)
    · exact hba.symm
  · exact hab

/-- Successor is injective on the interpreted PA domain. -/
theorem domainSucc_injective_model {α : Type} (M : AdjunctionModel α)
    {a b : Domain M} (h : domainSucc M a = domainSucc M b) : a = b := by
  apply Subtype.ext
  apply adjoin_self_injective_on_ordinalLike_model M a.property b.property
  exact congrArg Subtype.val h

/-- No successor in the interpreted PA domain is zero. -/
theorem domainSucc_ne_zero_model {α : Type} (M : AdjunctionModel α)
    (a : Domain M) : domainSucc M a ≠ domainZero M := by
  intro h
  exact adjoin_self_ne_empty_model M a.val (congrArg Subtype.val h)

/-- Every element of the interpreted PA carrier satisfies the domain formula. -/
theorem domainElement_domainForm_model {α : Type} (M : AdjunctionModel α)
    (a : Domain M) (e : Nat → α) :
    Sat M.mem (scons a.val e) domainForm := by
  apply (HF_ordinalLikeAt_spec (scons a.val e) 0).mpr
  exact a.property

/-- The interpreted zero satisfies the PA-in-HF domain formula. -/
theorem domainZero_domainForm_model {α : Type} (M : AdjunctionModel α)
    (e : Nat → α) :
    Sat M.mem (scons (domainZero M).val e) domainForm :=
  domainElement_domainForm_model M (domainZero M) e

/-- The interpreted zero realizes the PA-in-HF zero graph. -/
theorem domainZero_zeroGraph_model {α : Type} (M : AdjunctionModel α)
    (e : Nat → α) :
    Sat M.mem (scons (domainZero M).val e) zeroGraph := by
  simpa [domainZero_val] using zeroGraph_empty_model M e

/-- The interpreted successor satisfies the PA-in-HF domain formula. -/
theorem domainSucc_domainForm_model {α : Type} (M : AdjunctionModel α)
    (a : Domain M) (e : Nat → α) :
    Sat M.mem (scons (domainSucc M a).val e) domainForm :=
  domainElement_domainForm_model M (domainSucc M a) e

/-- The interpreted successor realizes the PA-in-HF successor graph. -/
theorem domainSucc_succGraph_model {α : Type} (M : AdjunctionModel α)
    (a : Domain M) (e : Nat → α) :
    Sat M.mem (scons (domainSucc M a).val (scons a.val e)) succGraph := by
  simpa [domainSucc_val] using succGraph_adjoin_self_model M a.val e

/-- In any adjunction model, the PA-in-HF zero graph lands in the interpreted
PA domain. -/
theorem zeroGraph_domain_model {α : Type} (M : AdjunctionModel α) (e : Nat → α)
    (hz : Sat M.mem e zeroGraph) : Sat M.mem e domainForm := by
  apply (HF_ordinalLikeAt_spec e 0).mpr
  have hz' := (HF_emptyAt_empty M e 0).mp hz
  rw [hz']
  exact OrdinalLike.empty M

/-- Standard Ackermann-HF specialization of `zeroGraph_domain_model`. -/
theorem zeroGraph_domain (e : Nat → Nat)
    (hz : Sat Mem e zeroGraph) : Sat Mem e domainForm :=
  zeroGraph_domain_model standardModel e hz

/-- In any adjunction model, the PA-in-HF successor graph preserves the
interpreted PA domain. -/
theorem succGraph_preserves_domain_model {α : Type} (M : AdjunctionModel α) (e : Nat → α)
    (hin : Sat M.mem e (HF_ordinalLikeAt 1))
    (hs : Sat M.mem e succGraph) :
    Sat M.mem e domainForm := by
  apply (HF_ordinalLikeAt_spec e 0).mpr
  have hin' := (HF_ordinalLikeAt_spec e 1).mp hin
  have hs' := (HF_succAt_spec M e 0 1).mp hs
  exact OrdinalLike.adjoin_self M hin' hs'

/-- Standard Ackermann-HF specialization of
`succGraph_preserves_domain_model`. -/
theorem succGraph_preserves_domain (e : Nat → Nat)
    (hin : Sat Mem e (HF_ordinalLikeAt 1))
    (hs : Sat Mem e succGraph) :
    Sat Mem e domainForm :=
  succGraph_preserves_domain_model standardModel e hin hs

end PAInHF

/-- The interpreted PA domain inside Ackermann HF: the finite von Neumann
ordinals, represented by their Ackermann codes. -/
def OrdinalHF : Type := {a : Nat // IsOrdinalCode a}

def ordinalOfNat (n : Nat) : OrdinalHF := ⟨ordinalCode n, ⟨n, rfl⟩⟩

noncomputable def natOfOrdinal (a : OrdinalHF) : Nat := a.property.choose

theorem ordinalOfNat_val (n : Nat) :
    (ordinalOfNat n).val = ordinalCode n := rfl

theorem natOfOrdinal_spec (a : OrdinalHF) :
    ordinalCode (natOfOrdinal a) = a.val :=
  a.property.choose_spec

theorem natOfOrdinal_ordinalOfNat (n : Nat) :
    natOfOrdinal (ordinalOfNat n) = n :=
  ordinalCode_injective (natOfOrdinal_spec (ordinalOfNat n))

theorem ordinalOfNat_natOfOrdinal (a : OrdinalHF) :
    ordinalOfNat (natOfOrdinal a) = a := by
  apply Subtype.ext
  exact natOfOrdinal_spec a

end AckermannHF

end SetTheory
