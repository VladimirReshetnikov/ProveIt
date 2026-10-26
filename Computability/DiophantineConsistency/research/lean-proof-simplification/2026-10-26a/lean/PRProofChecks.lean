import DiophantineConsistency.PRCode
import DiophantineConsistency.ScalarPROptimizer

/-! Candidate proof replacements at commit 60e9c5d620c6.
These definitions retain exactly the old executable program values.
Compilation status is recorded separately; this file does not claim a build.
-/

namespace DiophantineConsistency.ProofSimplification

def scalarPrec {f g : Nat → Nat}
    (p : ScalarPRCode.Realizes f) (q : ScalarPRCode.Realizes g) :
    ScalarPRCode.Realizes (Nat.unpaired (fun z n =>
      n.rec (f z) (fun i acc => g (Nat.pair z (Nat.pair i acc))))) := by
  refine ⟨.prec p.val q.val, ?_⟩
  intro packed
  simp only [ScalarPRCode.eval, Nat.unpaired, p.property, q.property]

theorem scalarPrec_val {f g : Nat → Nat}
    (p : ScalarPRCode.Realizes f) (q : ScalarPRCode.Realizes g) :
    (scalarPrec p q).val = (ScalarPRCode.Realizes.prec p q).val := rfl

def vectorPrec {n : Nat} {f : List.Vector Nat n → Nat}
    {g : List.Vector Nat (n + 2) → Nat}
    (p : PRCode.Realizes f) (q : PRCode.Realizes g) :
    PRCode.Realizes (fun v : List.Vector Nat (n + 1) =>
      v.head.rec (f v.tail) (fun i acc => g (i ::ᵥ acc ::ᵥ v.tail))) := by
  refine ⟨.prec p.val q.val, ?_⟩
  intro v
  simp only [PRCode.eval, p.property, q.property]

theorem vectorPrec_val {n : Nat} {f : List.Vector Nat n → Nat}
    {g : List.Vector Nat (n + 2) → Nat}
    (p : PRCode.Realizes f) (q : PRCode.Realizes g) :
    (vectorPrec p q).val = (PRCode.Realizes.prec p q).val := rfl

theorem eval_optimize_short (c : ScalarPRCode) (n : Nat) :
    c.optimize.eval n = c.eval n := by
  induction c generalizing n with
  | zero | succ | left | right => rfl
  | pair f g hf hg =>
    simp only [ScalarPRCode.optimize, ScalarPRCode.eval_smartPair,
      ScalarPRCode.eval, hf, hg]
  | comp f g hf hg =>
    simp only [ScalarPRCode.optimize, ScalarPRCode.eval_smartComp,
      ScalarPRCode.eval, hf, hg]
  | prec f g hf hg =>
    simp only [ScalarPRCode.optimize, ScalarPRCode.eval_smartPrec,
      ScalarPRCode.eval, hf, hg]

#print axioms scalarPrec
#print axioms vectorPrec
#print axioms eval_optimize_short
#print axioms ScalarPRCode.Realizes.prec
#print axioms PRCode.Realizes.prec
#print axioms ScalarPRCode.eval_optimize

end DiophantineConsistency.ProofSimplification
