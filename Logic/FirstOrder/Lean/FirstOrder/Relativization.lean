/-
  Relativization.lean

  Generic relativization for the one-relation first-order language of
  `FirstOrder.Fol`.  A point belongs to the relativized domain exactly when
  it has no self-loop.  Universal and existential quantifiers are guarded by
  that predicate; atoms and propositional connectives are left unchanged.
-/
import FirstOrder.Fol

namespace SetTheory

open Form

/-! ## Syntactic relativization to the loop-free part of a structure -/

/-- The formula saying that variable `i` has no membership self-loop. -/
def loopFreeAt (i : Nat) : Form := fImp (fMem i i) fBot

/-- Relativize every quantifier to the elements satisfying `loopFreeAt`.

The distinguished bound variable is De Bruijn variable zero. -/
def relativize : Form → Form
  | fMem i j => fMem i j
  | fEq i j  => fEq i j
  | fBot     => fBot
  | fImp a b => fImp (relativize a) (relativize b)
  | fAnd a b => fAnd (relativize a) (relativize b)
  | fOr a b  => fOr (relativize a) (relativize b)
  | fAll a   => fAll (fImp (loopFreeAt 0) (relativize a))
  | fEx a    => fEx (fAnd (loopFreeAt 0) (relativize a))

/-- Relativization commutes with De Bruijn renaming. -/
theorem relativize_rename (f : Form) (r : Nat → Nat) :
    relativize (rename r f) = rename r (relativize f) := by
  induction f generalizing r with
  | fMem i j => rfl
  | fEq i j => rfl
  | fBot => rfl
  | fImp a b iha ihb => simp [rename, relativize, iha, ihb]
  | fAnd a b iha ihb => simp [rename, relativize, iha, ihb]
  | fOr a b iha ihb => simp [rename, relativize, iha, ihb]
  | fAll a ih => simp [rename, relativize, loopFreeAt, up, ih]
  | fEx a ih => simp [rename, relativize, loopFreeAt, up, ih]

@[simp] theorem Free_loopFreeAt (n i : Nat) :
    Free n (loopFreeAt i) ↔ n = i := by
  simp [loopFreeAt, Free]

/-- Relativization neither introduces nor removes free variables. -/
theorem Free_relativize (n : Nat) (f : Form) :
    Free n (relativize f) ↔ Free n f := by
  induction f generalizing n with
  | fMem i j => rfl
  | fEq i j => rfl
  | fBot => rfl
  | fImp a b iha ihb => simp [relativize, Free, iha, ihb]
  | fAnd a b iha ihb => simp [relativize, Free, iha, ihb]
  | fOr a b iha ihb => simp [relativize, Free, iha, ihb]
  | fAll a ih => simp [relativize, Free, ih]
  | fEx a ih => simp [relativize, Free, ih]

/-- In particular, relativization preserves and reflects closedness. -/
theorem Sentence_relativize_iff (f : Form) :
    Sentence (relativize f) ↔ Sentence f := by
  constructor
  · intro h n hn
    exact h n ((Free_relativize n f).mpr hn)
  · intro h n hn
    exact h n ((Free_relativize n f).mp hn)

theorem Sentence_relativize {f : Form} (hf : Sentence f) :
    Sentence (relativize f) :=
  (Sentence_relativize_iff f).2 hf

/-! ## The induced loop-free substructure -/

section Semantics

universe u
variable {V : Type u}

/-- The subtype of elements having no self-loop. -/
def RelDomain (mem : V → V → Prop) := {x : V // ¬ mem x x}

/-- Membership restricted to the loop-free subtype. -/
def relDomainMem (mem : V → V → Prop) :
    RelDomain mem → RelDomain mem → Prop :=
  fun x y => mem x.1 y.1

variable {mem : V → V → Prop}

@[simp] theorem Sat_loopFreeAt (e : Nat → V) (i : Nat) :
    Sat mem e (loopFreeAt i) ↔ ¬ mem (e i) (e i) :=
  Iff.rfl

/-- Coercing a cons environment from the subtype commutes pointwise with
consing in the ambient structure. -/
private theorem relDomainVal_scons (d : RelDomain mem)
    (e : Nat → RelDomain mem) (n : Nat) :
    (scons d e n).1 = scons d.1 (fun k => (e k).1) n := by
  cases n <;> rfl

/-- Satisfaction transport along that pointwise equality, in the form used by
both quantifier cases of `Sat_relativize`. -/
private theorem Sat_scons_val (a : Form) (d : RelDomain mem)
    (e : Nat → RelDomain mem) :
    Sat mem (scons d.1 fun n => (e n).1) a ↔
      Sat mem (fun n => (scons d e n).1) a :=
  Sat_ext a _ _ (fun n => (relDomainVal_scons d e n).symm)

/-- Fundamental semantic theorem for loop-free relativization.

Evaluating the relativized formula in the ambient structure is equivalent to
evaluating the original formula in the induced loop-free substructure. -/
theorem Sat_relativize (f : Form) : ∀ e : Nat → RelDomain mem,
    Sat mem (fun n => (e n).1) (relativize f) ↔
      Sat (relDomainMem mem) e f := by
  induction f with
  | fMem i j =>
      intro e
      exact Iff.rfl
  | fEq i j =>
      intro e
      show (e i).1 = (e j).1 ↔ e i = e j
      constructor
      · exact Subtype.ext
      · intro h
        exact congrArg Subtype.val h
  | fBot =>
      intro e
      exact Iff.rfl
  | fImp a b iha ihb =>
      intro e
      simp only [relativize, Sat]
      rw [iha e, ihb e]
  | fAnd a b iha ihb =>
      intro e
      simp only [relativize, Sat]
      rw [iha e, ihb e]
  | fOr a b iha ihb =>
      intro e
      simp only [relativize, Sat]
      rw [iha e, ihb e]
  | fAll a ih =>
      intro e
      simp only [relativize, Sat]
      constructor
      · intro h d
        exact (ih (scons d e)).mp ((Sat_scons_val (relativize a) d e).mp (h d.1 d.2))
      · intro h d hd
        let d' : RelDomain mem := ⟨d, hd⟩
        exact (Sat_scons_val (relativize a) d' e).mpr
          ((ih (scons d' e)).mpr (h d'))
  | fEx a ih =>
      intro e
      simp only [relativize, Sat]
      constructor
      · rintro ⟨d, hd, ha⟩
        let d' : RelDomain mem := ⟨d, hd⟩
        exact ⟨d', (ih (scons d' e)).mp ((Sat_scons_val (relativize a) d' e).mp ha)⟩
      · rintro ⟨d, ha⟩
        exact ⟨d.1, d.2, (Sat_scons_val (relativize a) d e).mpr
          ((ih (scons d e)).mpr ha)⟩

end Semantics

end SetTheory
