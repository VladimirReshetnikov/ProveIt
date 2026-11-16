import KernelCompiler

/-! Generated proof-carrying topological schedule.
Domain-specific local derivations are explicit theorem arguments. -/

namespace LeanProofs.ConciseIPRA.KernelFiniteUse.Generated

open Syn
open scoped Fm
open LeanProofs.ConciseIPRA.KernelFiniteUse

theorem compile_generated
    {n : Nat} {Γ : List (Fm PTm n)}
    {A0 A1 A2 A3 A4 : Fm PTm n}
    (h0 : ([] : List (Fm PTm n)) ++ Γ ⊢[PRAAx] A0)
    (h1 : [A0] ++ Γ ⊢[PRAAx] A1)
    (h2 : [A1, A0] ++ Γ ⊢[PRAAx] A2)
    (h3 : [A2, A1, A0] ++ Γ ⊢[PRAAx] A3)
    (h4 : [A3, A2, A1, A0] ++ Γ ⊢[PRAAx] A4) :
    Γ ⊢[PRAAx] A4 := by
  let s0 : ProofBuild Γ [] := ProofBuild.nil
  let s1 : ProofBuild Γ [A0] := ProofBuild.step s0 h0
  let s2 : ProofBuild Γ [A1, A0] := ProofBuild.step s1 h1
  let s3 : ProofBuild Γ [A2, A1, A0] := ProofBuild.step s2 h2
  let s4 : ProofBuild Γ [A3, A2, A1, A0] := ProofBuild.step s3 h3
  let s5 : ProofBuild Γ [A4, A3, A2, A1, A0] := ProofBuild.step s4 h4
  exact s5.get (by simp)

end LeanProofs.ConciseIPRA.KernelFiniteUse.Generated
