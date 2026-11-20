import CubeTests
import SplitPrimes
import TaylorPackets
import SymmetricPrefixes

/-! Certified counterexamples to the new tests, directly in object iPRA.
The decoding function is used only together with a proof of UniversalZero. -/
namespace RiemannIPRA.UniversalCriteria
open LeanProofs.ConciseIPRA RHCounterexamples CubeTests Discrete

def block : {n : Nat} → Fm PTm n → Block n
  | _, .eq t _ => .test t
  | _, .all a => .bind (block a)
  | _, _ => .test PTm.zero

theorem recover {n} {a : Fm PTm n} (ha : UniversalZero a) : (block a).form = a := by
  induction ha with
  | matrix => rfl
  | binder _ ih => exact congrArg Fm.all ih

theorem scheduled {a : Fm PTm 0} (ha : UniversalZero a) (g : PR 1) :
    Prf PRAAx [] (Fm.iff a ((block a).schedule g)) := by
  have p := schedule_iff (block a) g
  rw [recover ha] at p
  exact p

theorem firstFailure {a : Fm PTm 0} (ha : UniversalZero a) :
    Prf PRAAx [] (Fm.iff (counter a) (block a).firstRadius) := by
  have p := failure_iff_first_radius (block a)
  rw [recover ha] at p
  exact p

theorem five (f : Family) (m : PR 5) : UniversalZero (f.close m) := by
  cases f with
  | riemann => exact .binder (.matrix _)
  | dirichlet => exact .binder (.binder (.matrix _))
  | dedekind => exact .binder (.binder (.binder (.binder (.binder (.matrix _)))))

theorem eight (f : Family) (m : PR 8) : UniversalZero (f.close8 m) := by
  cases f with
  | riemann => exact .binder (.binder (.binder (.binder (.matrix _))))
  | dirichlet => exact .binder (.binder (.binder (.binder (.binder (.matrix _)))))
  | dedekind => exact .binder (.binder (.binder (.binder (.binder (.binder (.binder (.binder (.matrix _))))))))

theorem taylorScheduled (f : Family) (s : Taylor.Schedule) (g : PR 1) :
    Prf PRAAx [] (Fm.iff (Taylor.statement f s) ((block (Taylor.statement f s)).schedule g)) :=
  scheduled (eight f _) g

theorem taylorFirstFailure (f : Family) (s : Taylor.Schedule) :
    Prf PRAAx [] (Fm.iff (counter (Taylor.statement f s)) (block (Taylor.statement f s)).firstRadius) :=
  firstFailure (eight f _)

theorem splitFirstFailure :
    Prf PRAAx [] (Fm.iff (counter SplitPrimes.unaryERH) (block SplitPrimes.unaryERH).firstRadius) :=
  firstFailure (five .riemann _)

theorem symmetricScheduled (f : Family) (s : SymmetricPrefixes.Test) (g : PR 1) :
    Prf PRAAx [] (Fm.iff (SymmetricPrefixes.statement f s)
      ((block (SymmetricPrefixes.statement f s)).schedule g)) :=
  scheduled (five f _) g

end RiemannIPRA.UniversalCriteria
