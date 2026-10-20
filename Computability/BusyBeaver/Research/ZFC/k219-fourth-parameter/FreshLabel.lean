import Std

/- Conditional algebraic facts for the proposed R(A,B) fourth parameter.
   The native support bound and a completeness theorem are NOT formalized here. -/
namespace FreshLabel

def row {V : Type} (imp : V → V → V) (a b c u : V) : V :=
  imp (imp (imp c u) a) (imp (imp a c) (imp b c))

/-- The literal formula-code label b is fresh from its own nonzero formula.
    Updating that label to the value at label zero makes R(0,b) irreflexive,
    without changing the value of formula b. The freshness condition is an
    explicit premise, not an assumed syntactic substitution principle. -/
theorem implies_truth_of_fresh_label {D V : Type}
    (imp : V → V → V) (r : D → D → V) (falseValue truth : V)
    (b : Nat) (nonzero : b ≠ 0) (eval : (Nat → D) → V)
    (diagonal : ∀ x, r x x = falseValue)
    (truth_false : imp truth falseValue = falseValue)
    (false_truth : imp falseValue truth = truth)
    (truth_truth : imp truth truth = truth)
    (mp : ∀ x, imp truth x = truth → x = truth)
    (fresh : ∀ s d, eval (fun i => if i = b then d else s i) = eval s)
    (valid : ∀ s, row imp truth (eval s) truth (r (s 0) (s b)) = truth) :
    ∀ s, imp (eval s) truth = truth := by
  intro s
  let modified : Nat → D := fun i => if i = b then s 0 else s i
  have zero_ne : 0 ≠ b := Ne.symm nonzero
  have atom : r (modified 0) (modified b) = falseValue := by
    simp only [modified, if_neg zero_ne, if_pos rfl, diagonal]
  have unchanged : eval modified = eval s := fresh s (s 0)
  have h := valid modified
  rw [atom, unchanged] at h
  simp only [row, truth_false, false_truth, truth_truth] at h
  exact mp _ (mp _ h)

/-- Project the bare negative K component from its literal bundle.
    No Boolean-output assumption on b (the quantified core) is used. -/
theorem negative_core_of_bundle {V : Type} (imp : V → V → V)
    (neg : V → V) (truth : V)
    (neg_iff : ∀ x, neg x = truth ↔ x ≠ truth)
    (implies_truth : ∀ x, imp x truth = truth)
    (a b : V) (bundle : neg (imp a b) = truth) : neg b = truth := by
  apply (neg_iff b).mpr
  intro hb
  have h := (neg_iff (imp a b)).mp bundle
  exact h (hb ▸ implies_truth a)

#print axioms implies_truth_of_fresh_label
#print axioms negative_core_of_bundle

end FreshLabel
