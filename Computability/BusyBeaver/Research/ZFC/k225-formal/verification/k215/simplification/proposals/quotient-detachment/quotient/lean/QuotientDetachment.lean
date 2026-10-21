import BusyBeaver.ZFC.Code254

/-!
A tag-insensitive detachment rule for the actual base-four code semantics.
This is a theorem about validity under all valuations. It is deliberately
not a pointwise inference rule under one fixed valuation.
-/
namespace SetTheory.BusyBeaver.ZFC.QuotientDetachment
open Code254

universe u
variable {V : Type u}

def Valid (mem : V → V → Prop) (n : Nat) : Prop :=
  ∀ e : Nat → V, Tarski.Sat mem e (dec n)

/-- Erasing the two constructor bits from the major premise remains sound
for theorem validity in an irreflexive model with two distinct elements. -/
theorem quotient_detachment
    (mem : V → V → Prop) (hirr : ∀ x, ¬ mem x x)
    (x y : V) (hxy : x ≠ y) {a b h : Nat}
    (ha : Valid mem a) (hh : Valid mem h)
    (pair_eq : h / 4 = P a b) : Valid mem b := by
  have hmod : h % 4 < 4 := Nat.mod_lt h (by decide)
  have hsplit := Nat.mod_add_div h 4
  rcases (show h % 4 = 0 ∨ h % 4 = 1 ∨ h % 4 = 2 ∨ h % 4 = 3 by omega) with h0 | h1 | h2 | h3
  · have eh : h = wim a b := by unfold wim; omega
    intro e
    exact (sat_wim mem e a b).mp (eh ▸ hh e) (ha e)
  · have eh : h = wel a b := by unfold wel; omega
    have bad := (sat_wel mem (fun _ => x) a b).mp (eh ▸ hh (fun _ => x))
    exact False.elim (hirr x bad)
  · have eh : h = wal a b := by unfold wal; omega
    intro e
    have hb := (sat_wal mem e a b).mp (eh ▸ hh e) (e a)
    have he : Tarski.update e a (e a) = e := by
      funext i
      unfold Tarski.update
      split <;> simp_all
    exact he ▸ hb
  · have eh : h = weq a b := by unfold weq; omega
    by_cases hab : a = b
    · exact hab ▸ ha
    · let e : Nat → V := fun i => if i = a then x else y
      have heq := (sat_weq mem e a b).mp (eh ▸ hh e)
      have hba : b ≠ a := Ne.symm hab
      have bad : x = y := by simpa [e, hba] using heq
      exact False.elim (hxy bad)

/-- The existing calculus is admitted as the base of a finite-derivation
closure; base constructors expand into proofs using the original seed rules. -/
inductive QClosure : Nat → Prop
  | base {n} : C254 n → QClosure n
  | detachment {a b h} : QClosure a → QClosure h → h / 4 = P a b → QClosure b
  | gen (a) {b} : QClosure b → QClosure (wal a b)

/-- Explicit semantic assumptions, matching the original soundness interface. -/
theorem qclosure_sound
    (mem : V → V → Prop) (hirr : ∀ x, ¬ mem x x)
    (x y : V) (hxy : x ≠ y)
    (bundles : ∀ a b c, c ≠ a → c ≠ b → ∀ e : Nat → V,
      Tarski.Sat mem e (dec (bundle a b c)))
    {n} (hn : QClosure n) : Valid mem n := by
  induction hn with
  | base h => exact c254_sound mem hirr bundles h
  | detachment _ _ heq ih1 ih2 =>
      exact quotient_detachment mem hirr x y hxy ih1 ih2 heq
  | gen a _ ih =>
      intro e
      apply (sat_wal mem e a _).mpr
      intro d
      exact ih (Tarski.update e a d)

/-- A nontrivial decoded-bundle model rules out the unchanged falsity code. -/
theorem qclosure_no_false
    (mem : V → V → Prop) (hirr : ∀ x, ¬ mem x x)
    (x y : V) (hxy : x ≠ y)
    (bundles : ∀ a b c, c ≠ a → c ≠ b → ∀ e : Nat → V,
      Tarski.Sat mem e (dec (bundle a b c))) : ¬ QClosure F := by
  intro h
  exact sat_F mem hirr (fun _ => x)
    (qclosure_sound mem hirr x y hxy bundles h (fun _ => x))

/-- The two-element assumption cannot be dropped, even with irreflexivity.
In a singleton: code 0 is true, code 11 is Eq(0,1), and code 1 is false. -/
theorem singleton_obstruction :
    Valid (fun (_ _ : Unit) => False) 0 ∧
    Valid (fun (_ _ : Unit) => False) 11 ∧
    11 / 4 = P 0 1 ∧
    ¬ Valid (fun (_ _ : Unit) => False) 1 := by
  refine ⟨?_, ?_, by decide, ?_⟩
  · intro e
    rw [dec_zero]
    exact sat_T0 _ e
  · intro e
    change Tarski.Sat _ e (dec (weq 0 1))
    apply (sat_weq _ e 0 1).mpr
    exact Subsingleton.elim _ _
  · intro h
    exact sat_F _ (by intro z hz; exact hz) (fun _ => ()) (h (fun _ => ()))

/-- Likewise, even in a two-element structure, a single valuation is not
an adequate invariant for tag-insensitive detachment. -/
theorem pointwise_obstruction :
    Tarski.Sat (fun (_ _ : Bool) => False) (fun _ => false) (dec 0) ∧
    Tarski.Sat (fun (_ _ : Bool) => False) (fun _ => false) (dec 11) ∧
    11 / 4 = P 0 1 ∧
    ¬ Tarski.Sat (fun (_ _ : Bool) => False) (fun _ => false) (dec 1) := by
  refine ⟨?_, ?_, by decide, ?_⟩
  · rw [dec_zero]; exact sat_T0 _ _
  · change Tarski.Sat _ _ (dec (weq 0 1))
    exact (sat_weq _ _ 0 1).mpr rfl
  · exact sat_F _ (by intro z hz; exact hz) _

#print axioms quotient_detachment
#print axioms qclosure_sound
#print axioms qclosure_no_false
#print axioms singleton_obstruction
#print axioms pointwise_obstruction
end SetTheory.BusyBeaver.ZFC.QuotientDetachment
