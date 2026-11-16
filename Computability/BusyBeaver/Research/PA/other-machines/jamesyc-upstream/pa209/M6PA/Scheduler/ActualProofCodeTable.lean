module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.ActualProofCodeLocality
@[expose] public section
open M6.Arithmetic.PA
namespace M6.PA.NativeCalculus.ActualBasis.Code
open M6.Source M6.Source.Cantor M6.Source.Enumeration

/-- Finite data recursion: each round evaluates every code up to the fixed
bound using only the preceding finite table. No recursive function value is
stored. This is an explicit supplier for later primitive-recursive coding. -/
def table (bound : Nat) : Nat → List (Option Nat)
  | 0 => List.replicate (bound+1) none
  | fuel+1 =>
      let previous := table bound fuel
      (List.range (bound+1)).map fun n =>
        let p := decode n
        ruleCheck (fun k => previous.getD k none) p.1 p.2

theorem table_lookup (bound fuel n : Nat) (hn : n≤bound) :
    (table bound fuel).getD n none = check fuel n := by
  induction fuel generalizing n with
  | zero => simp [table,check,List.getD,show n<bound+1 by omega]
  | succ fuel ih =>
      simp only [table,List.getD,List.getElem?_map,
        List.getElem?_range (show n<bound+1 by omega),Option.map_some,Option.getD_some,check]
      apply ruleCheck_congr
      intro k hk
      exact ih k (Nat.le_trans hk (Nat.le_trans (decode_bounds n).2 hn))

def tableVerify (certificate : Nat) : Option Nat :=
  let p := decode certificate
  (table p.2 p.1).getD p.2 none

theorem tableVerify_eq (certificate : Nat) : tableVerify certificate = verify certificate := by
  exact table_lookup _ _ _ (Nat.le_refl _)

#print axioms table_lookup
#print axioms tableVerify_eq
end M6.PA.NativeCalculus.ActualBasis.Code

