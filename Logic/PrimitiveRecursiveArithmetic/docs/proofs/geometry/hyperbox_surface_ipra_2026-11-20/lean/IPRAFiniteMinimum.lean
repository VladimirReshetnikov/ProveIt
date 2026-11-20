import IPRADerivations.Core.SearchParameters

/-! Object-level minimization of a coded route cost with a search bound. The
    numeral C can encode failure. Each valid route of interest has score < C. -/
namespace Hyperbox.IPRA.Optimization
open LeanProofs.ConciseIPRA
open LeanProofs.IPRA
open Syn
open scoped Fm
open LeanProofs.ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)
open LeanProofs.IPRA.Search.Finite (applyBody)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def priceTest (f : PTm 2) : PTm 3 :=
  monus (inst2 f (var 0) (var 2)) (var 1)

/-- First code < N whose cost under parameter x does not exceed b, or N. -/
def winnerAt (f : PTm 2) (N b x : PTm n) : PTm n :=
  Search.Finite.mu (priceTest f) N ![b,x]

private theorem price_body (f : PTm 2) (i b x : PTm n) :
    (applyBody (priceTest f) i ![b,x] ≐ zero) = le (inst2 f i x) b := by
  simp [priceTest, applyBody, le]

def budgetTest (f : PTm 2) : PTm 3 :=
  monus (succ (winnerAt f (var 1) (var 0) (var 2))) (var 1)

/-- Smallest budget < C that admits a route, or C. -/
def minBudget (f : PTm 2) (C N x : PTm n) : PTm n :=
  Search.Finite.mu (budgetTest f) C ![N,x]

def argmin (f : PTm 2) (C N x : PTm n) : PTm n := winnerAt f N (minBudget f C N x) x

private theorem budget_body (f : PTm 2) (b N x : PTm n) :
    (applyBody (budgetTest f) b ![N,x] ≐ zero) = lt (winnerAt f N b x) N := by
  simp [budgetTest, applyBody, winnerAt, le, lt]
  congr 2

private theorem winner_found {f : PTm 2} {i b N x : PTm n}
    (hi : Γ ⊢[PRAAx] lt i N) (hp : Γ ⊢[PRAAx] le (inst2 f i x) b) :
    Γ ⊢[PRAAx] lt (winnerAt f N b x) N := by
  rw [← price_body] at hp
  exact .andE₁ (Search.Finite.search_found hp hi)

private theorem winner_score {f : PTm 2} {b N x : PTm n}
    (hw : Γ ⊢[PRAAx] lt (winnerAt f N b x) N) :
    Γ ⊢[PRAAx] le (inst2 f (winnerAt f N b x) x) b := by
  rw [← price_body]
  exact .impE (.andE₁ (.andE₂ (Search.Finite.search_spec (priceTest f) N b ![b,x]))) hw

private theorem minimum_found {f : PTm 2} {i C N x : PTm n}
    (hi : Γ ⊢[PRAAx] lt i N) (hp : Γ ⊢[PRAAx] lt (inst2 f i x) C) :
    Γ ⊢[PRAAx] lt (minBudget f C N x) C ⋏
      (lt (argmin f C N x) N ⋏ le (minBudget f C N x) (inst2 f i x)) := by
  have hw := winner_found hi (le_refl (inst2 f i x))
  rw [← budget_body] at hw
  have ho := Search.Finite.search_found hw hp
  refine .andI (.andE₁ ho) (.andI ?_ (.andE₂ (.andE₂ ho)))
  have e := Prf.andE₁ (Prf.andE₂ ho)
  rw [budget_body] at e
  exact e

/-- Any competitor of cost < C implies an attaining code and a value no larger
    than that competitor's. This is a derivation in the syntax of iPRA. -/
theorem attained_minimum {f : PTm 2} {i C N x : PTm n}
    (hi : Γ ⊢[PRAAx] lt i N) (hp : Γ ⊢[PRAAx] lt (inst2 f i x) C) :
    Γ ⊢[PRAAx] lt (argmin f C N x) N ⋏
      ((inst2 f (argmin f C N x) x ≐ minBudget f C N x) ⋏
        le (minBudget f C N x) (inst2 f i x)) := by
  have ho := minimum_found hi hp
  have ha := Prf.andE₁ (Prf.andE₂ ho)
  have hs := winner_score ha
  have hc := lt_of_le_of_lt hs (Prf.andE₁ ho)
  have hlow := Prf.andE₂ (Prf.andE₂ (minimum_found ha hc))
  exact .andI ha (.andI (le_antisymm hs hlow) (.andE₂ (.andE₂ ho)))

end Hyperbox.IPRA.Optimization
