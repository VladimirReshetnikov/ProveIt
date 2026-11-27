import IPRADerivations.Core.Order

/-! Imported from the packet `analysis/constructive_computable_analysis_ipra_2026-11-20`, `lean/ZeroObject.lean`: the namespace is placed under `LeanProofs.IPRA.Analysis` and the `#print axioms` lines are dropped (the library audits axioms in `Checks/Axioms.lean`). -/

/-!
The three-way guard and signed endpoint conclusions, after multiplying
all observations by a common positive denominator and shifting zero to K.
The offsets need not be minimal. Each of the seven numbers is internal.
-/
namespace LeanProofs.IPRA.Analysis.Observation.ZeroObject

open_ipra

variable {n : ℕ} {Γ : List (Fm PTm n)}

def localLaws (C h Lm Um Lu Uv : PTm n) : Fm PTm n :=
  (le Lm (C+h) ⋏ le C (Um+h)) ⋏ (le (Lu+h) C ⋏ le (C+h) Uv)

/-- A branch guard paired with the sign obligation for its new endpoint(s). -/
def admissibleBranch (K C h Lm Um Lu Uv : PTm n) : Fm PTm n :=
  (le (K+h) C ⋏ le K Um) ⋎
    (((lt C (K+h) ⋏ le (C+h) K) ⋏ le Lm K) ⋎
     ((lt C (K+h) ⋏ lt K (C+h)) ⋏ (le Lu K ⋏ le K Uv)))

theorem branches (K C h Lm Um Lu Uv : PTm n)
    (laws : Γ ⊢[PRAAx] localLaws C h Lm Um Lu Uv) :
    Γ ⊢[PRAAx] admissibleBranch K C h Lm Um Lu Uv := by
  refine .orE (lt_or_le C (K+h)) ?_ ?_
  · refine .orE (lt_or_le K (C+h)) ?_ ?_
    · exact .orI₂ (.orI₂ (.andI (.andI Prf.hyp1 Prf.hyp0)
        (.andI (le_of_add_le_add_right (le_trans laws.andE₂.andE₁.wk.wk (le_of_lt Prf.hyp1)))
          (le_trans (le_of_lt Prf.hyp0) laws.andE₂.andE₂.wk.wk))))
    · exact .orI₂ (.orI₁ (.andI (.andI Prf.hyp1 Prf.hyp0)
        (le_trans laws.andE₁.andE₁.wk.wk Prf.hyp0)))
  · exact .orI₁ (.andI Prf.hyp0
      (le_of_add_le_add_right (le_trans Prf.hyp0 laws.andE₁.andE₂.wk)))


def body : Fm PTm 7 :=
  localLaws (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
    admissibleBranch (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)

def sentence : Fm PTm 0 := .all (.all (.all (.all (.all (.all (.all body))))))

theorem branches_closed : [] ⊢[PRAAx] sentence := by
  unfold sentence
  repeat' apply Prf.allI
  exact .impI (branches _ _ _ _ _ _ _ Prf.hyp0)

end LeanProofs.IPRA.Analysis.Observation.ZeroObject
