import QuotientDetachment
import BusyBeaver.ZFC.KCode222

namespace SetTheory.BusyBeaver.ZFC.Quotient222
open Code254 KCode222 QuotientDetachment

/-- Closing the existing, calibrated numeric calculus under tag-insensitive
inference. Base proofs are finite and expand to the unchanged original seeds. -/
inductive Q222 : Nat → Prop
  | base {n} : C222 n → Q222 n
  | detachment {a b h} : Q222 a → Q222 h → h / 4 = P a b → Q222 b
  | gen (a) {b} : Q222 b → Q222 (wal a b)

universe u
variable {V : Type u}

theorem q222_sound
    (mem : V → V → Prop) (hirr : ∀ x, ¬ mem x x)
    (x y : V) (hxy : x ≠ y)
    (bundles : ∀ a b c, c ≠ a → c ≠ b → ∀ e : Nat → V,
      Tarski.Sat mem e (dec (bundle222 a b c)))
    {n} (hn : Q222 n) : Valid mem n := by
  induction hn with
  | base h => exact c222_sound mem hirr bundles h
  | detachment _ _ heq ih1 ih2 =>
      exact quotient_detachment mem hirr x y hxy ih1 ih2 heq
  | gen a _ ih =>
      intro e
      apply (sat_wal mem e a _).mpr
      intro d
      exact ih (Tarski.update e a d)

theorem q222_no_false
    (mem : V → V → Prop) (hirr : ∀ x, ¬ mem x x)
    (x y : V) (hxy : x ≠ y)
    (bundles : ∀ a b c, c ≠ a → c ≠ b → ∀ e : Nat → V,
      Tarski.Sat mem e (dec (bundle222 a b c))) : ¬ Q222 F := by
  intro h
  exact sat_F mem hirr (fun _ => x)
    (q222_sound mem hirr x y hxy bundles h (fun _ => x))

theorem original_refutation_preserved (h : C222 F) : Q222 F := .base h

#print axioms q222_sound
#print axioms q222_no_false
#print axioms original_refutation_preserved
end SetTheory.BusyBeaver.ZFC.Quotient222
