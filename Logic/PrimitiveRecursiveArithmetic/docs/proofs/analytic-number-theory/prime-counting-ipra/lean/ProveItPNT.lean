import IPRADerivations.AnalyticNumberTheory.FinalPNT

/-!
Optional module for use in the repository-root ProveIt Lake project at
revision a9c0f1949be61679ed2e219b97dc42ecb7ae91a9 (Lean 4.32.0). Run
lake build IPRADerivations.AnalyticNumberTheory.FinalPNT
then lake env lean /path/to/ProveItPNT.lean from that repository root. The type below is an
object-logic sequent. The cutoff is the exact upstream cutoff, prior to
the simplification by the recurrence V in the report.
-/
namespace LeanProofs.IPRA.AnalyticNumberTheory.PrimeCountingReuse

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.FinalPNT (Fn An Nk arith_pnt)
open LeanProofs.IPRA.AnalyticNumberTheory.PiTheta (Pi)
open LeanProofs.IPRA.AnalyticNumberTheory.AbsDiff (absd)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

theorem arithmeticPNT {n : ℕ} {Γ : List (Fm PTm n)} {k m : PTm n}
    (hk : Γ ⊢[PRAAx] le one k) (hm : Γ ⊢[PRAAx] le (Nk k) m) :
    Γ ⊢[PRAAx] le (k * absd (Pi m zero * An m) (m * Fn m)) (m * Fn m) :=
  arith_pnt hk hm

end LeanProofs.IPRA.AnalyticNumberTheory.PrimeCountingReuse
